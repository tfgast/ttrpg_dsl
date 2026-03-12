//! Integration tests for condition state field declarations and inheritance.
//!
//! Verifies the checker's state field type-checking, the post-collect merge
//! pass for inherited state fields, and error detection for conflicts.

use std::collections::VecDeque;

use rustc_hash::FxHashMap;
use ttrpg_ast::diagnostic::Severity;
use ttrpg_ast::{FileId, Name};
use ttrpg_interp::Interpreter;
use ttrpg_interp::adapter::StateAdapter;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::StateProvider;
use ttrpg_interp::value::Value;

fn setup(source: &str) -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    let (program, parse_errors) = ttrpg_parser::parse(source, FileId::SYNTH);
    assert!(
        parse_errors.is_empty(),
        "parse errors: {:?}",
        parse_errors.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    let mut lower_diags = Vec::new();
    let program = ttrpg_parser::lower_moves(program, &mut lower_diags);
    assert!(
        lower_diags.is_empty(),
        "lowering errors: {:?}",
        lower_diags.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    let result = ttrpg_checker::check(&program);
    let errors: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .collect();
    assert!(
        errors.is_empty(),
        "checker errors: {:?}",
        errors.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    (program, result)
}

fn setup_expect_errors(source: &str) -> Vec<String> {
    let (program, parse_errors) = ttrpg_parser::parse(source, FileId::SYNTH);
    assert!(
        parse_errors.is_empty(),
        "parse errors: {:?}",
        parse_errors.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    let mut lower_diags = Vec::new();
    let program = ttrpg_parser::lower_moves(program, &mut lower_diags);
    let result = ttrpg_checker::check(&program);
    result
        .diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .map(|d| d.message.clone())
        .collect()
}

// ── Basic state field declarations ──────────────────────────────

#[test]
fn condition_own_state_fields_check() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Poisoned(potency: int = 1) on bearer: Character {
        state {
            ticks: int = 0
            total_damage: int = potency
        }
        on_apply {
            state.ticks = 1
            state.total_damage = state.total_damage + 1
        }
    }
}
"#;
    let (_program, result) = setup(source);
    let cond_info = result.env.conditions.get("Poisoned").unwrap();
    assert_eq!(cond_info.own_state_fields.len(), 2);
    assert_eq!(cond_info.merged_state_fields.len(), 2);
}

// ── Inherited state fields ──────────────────────────────────────

#[test]
fn child_inherits_parent_state_fields() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Burning(damage_per_tick: int = 1) on bearer: Character {
        state {
            ticks_elapsed: int = 0
            total_damage: int = 0
        }
    }
    condition IntenseBurning extends Burning on bearer: Character {
        state {
            spread_count: int = 0
        }
    }
}
"#;
    let (_program, result) = setup(source);
    let parent_info = result.env.conditions.get("Burning").unwrap();
    assert_eq!(parent_info.own_state_fields.len(), 2);
    assert_eq!(parent_info.merged_state_fields.len(), 2);

    let child_info = result.env.conditions.get("IntenseBurning").unwrap();
    assert_eq!(child_info.own_state_fields.len(), 1);
    // Merged: 2 from parent + 1 own = 3
    assert_eq!(child_info.merged_state_fields.len(), 3);
    // Ancestor order: parent fields first, then child
    assert_eq!(child_info.merged_state_fields[0].0, "ticks_elapsed");
    assert_eq!(child_info.merged_state_fields[1].0, "total_damage");
    assert_eq!(child_info.merged_state_fields[2].0, "spread_count");
}

#[test]
fn child_accesses_inherited_state_in_lifecycle() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Burning(damage_per_tick: int = 1) on bearer: Character {
        state {
            ticks_elapsed: int = 0
        }
        on_apply {
            state.ticks_elapsed = 1
        }
    }
    condition IntenseBurning extends Burning on bearer: Character {
        state {
            spread_count: int = 0
        }
        on_apply {
            // Can read inherited state field
            state.spread_count = state.ticks_elapsed
        }
    }
}
"#;
    let (_program, _result) = setup(source);
}

#[test]
fn grandchild_inherits_through_chain() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Base on bearer: Character {
        state { a: int = 0 }
    }
    condition Mid extends Base on bearer: Character {
        state { b: int = 0 }
    }
    condition Leaf extends Mid on bearer: Character {
        state { c: int = 0 }
    }
}
"#;
    let (_program, result) = setup(source);
    let leaf = result.env.conditions.get("Leaf").unwrap();
    assert_eq!(leaf.merged_state_fields.len(), 3);
    assert_eq!(leaf.merged_state_fields[0].0, "a");
    assert_eq!(leaf.merged_state_fields[1].0, "b");
    assert_eq!(leaf.merged_state_fields[2].0, "c");
}

// ── Error cases ──────────────────────────────────────────────────

#[test]
fn child_redeclares_parent_state_field_error() {
    let errors = setup_expect_errors(
        r#"
system "test" {
    entity Character { HP: int }
    condition Parent on bearer: Character {
        state { x: int = 0 }
    }
    condition Child extends Parent on bearer: Character {
        state { x: int = 1 }
    }
}
"#,
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("redeclares inherited state field")),
        "expected redeclaration error, got: {:?}",
        errors
    );
}

#[test]
fn sibling_parent_field_conflict_error() {
    let errors = setup_expect_errors(
        r#"
system "test" {
    entity Character { HP: int }
    condition ParentA on bearer: Character {
        state { x: int = 0 }
    }
    condition ParentB on bearer: Character {
        state { x: int = 0 }
    }
    condition Child extends ParentA, ParentB on bearer: Character {}
}
"#,
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("conflicting state field") || e.contains("state field `x`")),
        "expected sibling parent conflict error, got: {:?}",
        errors
    );
}

#[test]
fn disallowed_type_in_state_field_error() {
    let errors = setup_expect_errors(
        r#"
system "test" {
    entity Character { HP: int }
    condition Bad on bearer: Character {
        state { c: Condition = Prone }
    }
    condition Prone on bearer: Character {}
}
"#,
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("cannot have type") && e.contains("disallowed")),
        "expected disallowed type error, got: {:?}",
        errors
    );
}

#[test]
fn state_default_type_mismatch_error() {
    let errors = setup_expect_errors(
        r#"
system "test" {
    entity Character { HP: int }
    condition Bad on bearer: Character {
        state { x: int = "hello" }
    }
}
"#,
    );
    assert!(
        errors.iter().any(|e| e.contains("default has type")),
        "expected type mismatch error, got: {:?}",
        errors
    );
}

#[test]
fn no_state_fields_condition_no_extends() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Prone on bearer: Character {}
}
"#;
    let (_program, result) = setup(source);
    let info = result.env.conditions.get("Prone").unwrap();
    assert!(info.own_state_fields.is_empty());
    assert!(info.merged_state_fields.is_empty());
}

// ── Reserved identifier tests ────────────────────────────────────

#[test]
fn state_as_receiver_name_error() {
    let errors = setup_expect_errors(
        r#"
system "test" {
    entity Character { HP: int }
    condition Bad on state: Character {}
}
"#,
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("state") && e.contains("shadows")),
        "expected reserved name error, got: {:?}",
        errors
    );
}

#[test]
fn state_as_param_name_error() {
    let errors = setup_expect_errors(
        r#"
system "test" {
    entity Character { HP: int }
    condition Bad(state: int) on bearer: Character {}
}
"#,
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("state") && e.contains("shadows")),
        "expected reserved name error, got: {:?}",
        errors
    );
}

#[test]
fn parent_default_params_materialized_in_child() {
    // When IntenseBurning extends Burning(damage_per_tick: int = 3),
    // the child instance should have damage_per_tick=3 available.
    let source = r#"
system "test" {
    entity Character {
        HP: int
        last_damage: int
    }
    condition Burning(damage_per_tick: int = 3) on bearer: Character {
        on_apply {
            bearer.last_damage = damage_per_tick
        }
    }
    condition IntenseBurning extends Burning on bearer: Character {
        on_apply {
            // Parent on_apply already set last_damage to damage_per_tick
            // Child can also access inherited param
            bearer.last_damage = bearer.last_damage + damage_per_tick
        }
    }
}
"#;
    let (_program, _result) = setup(source);
}

#[test]
fn self_as_receiver_name_error() {
    let errors = setup_expect_errors(
        r#"
system "test" {
    entity Character { HP: int }
    condition Bad on self: Character {}
}
"#,
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("self") && e.contains("shadows")),
        "expected reserved name error, got: {:?}",
        errors
    );
}

#[test]
fn state_readable_in_modify_body() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    derive calc_hp(target: Character) -> int { target.HP }
    condition Buffed on bearer: Character {
        state {
            stacks: int = 1
        }
        modify calc_hp(target: bearer) {
            result = result + state.stacks
        }
    }
}
"#;
    let (_program, _result) = setup(source);
}

#[test]
fn state_readable_in_modify_selector() {
    let source = r#"
system "test" {
    tag attack_resolution
    entity Character { HP: int }
    derive base_attack(target: Character) -> int #attack_resolution { target.HP }
    condition Weakened on bearer: Character {
        state {
            penalty: int = 1
        }
        modify [#attack_resolution](target: bearer) {
            result = result - state.penalty
        }
    }
}
"#;
    let (_program, _result) = setup(source);
}

#[test]
fn self_as_param_name_error() {
    let errors = setup_expect_errors(
        r#"
system "test" {
    entity Character { HP: int }
    condition Bad(self: int) on bearer: Character {}
}
"#,
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("self") && e.contains("shadows")),
        "expected reserved name error, got: {:?}",
        errors
    );
}

// ── Runtime integration tests ────────────────────────────────────

struct ScriptedHandler {
    script: VecDeque<Response>,
    log: Vec<Effect>,
}

impl ScriptedHandler {
    fn new() -> Self {
        ScriptedHandler {
            script: VecDeque::new(),
            log: Vec::new(),
        }
    }
}

impl EffectHandler for ScriptedHandler {
    fn handle(&mut self, effect: Effect) -> Response {
        self.log.push(effect);
        self.script.pop_front().unwrap_or(Response::Acknowledged)
    }
}

fn make_character(state: &mut GameState, hp: i64) -> ttrpg_interp::state::EntityRef {
    let mut fields = FxHashMap::default();
    fields.insert("HP".into(), Value::Int(hp));
    state.add_entity("Character", fields)
}

/// Run a function on an entity, returning the mutated state and effect log.
///
/// Takes ownership of `state` and returns it (possibly mutated) alongside the log,
/// because `StateAdapter::new()` consumes the state.
fn run_function(
    source: &str,
    function_name: &str,
    state: GameState,
    entity: ttrpg_interp::state::EntityRef,
) -> (GameState, Vec<Effect>) {
    let (program, check_result) = setup(source);
    let interp = Interpreter::new(&program, &check_result.env).unwrap();
    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |adapted_state, handler| {
        interp
            .evaluate_function(
                adapted_state,
                handler,
                function_name,
                vec![Value::Entity(entity)],
            )
            .unwrap();
    });
    (adapter.into_inner(), handler.log)
}

#[test]
fn state_defaults_initialized_in_apply_condition() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Poisoned on bearer: Character {
        state {
            ticks: int = 0
            total_damage: int = 42
        }
    }
    function do_apply(target: Character) {
        apply_condition(target, Poisoned, Duration.Indefinite)
    }
}
"#;
    let mut state = GameState::new();
    let entity = make_character(&mut state, 100);
    let (state, _log) = run_function(source, "do_apply", state, entity);

    // Check that state_fields are stored on the condition instance
    // (ApplyCondition effect is intercepted by StateAdapter, so check state directly)
    let conds = state.read_conditions(&entity).unwrap();
    assert_eq!(conds.len(), 1);
    assert_eq!(conds[0].state_fields.len(), 2);
    let key_ticks: Name = "ticks".into();
    let key_total: Name = "total_damage".into();
    assert_eq!(conds[0].state_fields.get(&key_ticks), Some(&Value::Int(0)));
    assert_eq!(conds[0].state_fields.get(&key_total), Some(&Value::Int(42)));
}

#[test]
fn state_mutated_in_on_apply() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Poisoned on bearer: Character {
        state {
            ticks: int = 0
        }
        on_apply {
            state.ticks = 5
        }
    }
    function do_apply(target: Character) {
        apply_condition(target, Poisoned, Duration.Indefinite)
    }
}
"#;
    let mut state = GameState::new();
    let entity = make_character(&mut state, 100);
    let (state, _log) = run_function(source, "do_apply", state, entity);

    // on_apply set ticks to 5 — this should be in the final state_fields
    let conds = state.read_conditions(&entity).unwrap();
    let key: Name = "ticks".into();
    assert_eq!(conds[0].state_fields.get(&key), Some(&Value::Int(5)));
}

#[test]
fn inherited_state_sharing_in_on_apply() {
    // Parent sets state.x = 10 in on_apply, child reads it and sets state.y = state.x + 1
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Parent on bearer: Character {
        state {
            x: int = 0
        }
        on_apply {
            state.x = 10
        }
    }
    condition Child extends Parent on bearer: Character {
        state {
            y: int = 0
        }
        on_apply {
            // Parent on_apply already ran — state.x is 10
            state.y = state.x + 1
        }
    }
    function do_apply(target: Character) {
        apply_condition(target, Child, Duration.Indefinite)
    }
}
"#;
    let mut state = GameState::new();
    let entity = make_character(&mut state, 100);
    let (state, _log) = run_function(source, "do_apply", state, entity);

    let conds = state.read_conditions(&entity).unwrap();
    assert_eq!(
        conds[0].state_fields.get::<Name>(&"x".into()),
        Some(&Value::Int(10))
    );
    assert_eq!(
        conds[0].state_fields.get::<Name>(&"y".into()),
        Some(&Value::Int(11))
    );
}

#[test]
fn state_mutated_in_periodic() {
    let source = r#"
system "test" {
    tag round_end
    entity Character { HP: int }
    condition Ticking on bearer: Character {
        state {
            count: int = 0
        }
        on_apply {
            state.count = 1
        }
        periodic #round_end {
            state.count = state.count + 1
        }
    }
    function do_apply(target: Character) {
        apply_condition(target, Ticking, Duration.Indefinite)
    }
    function do_tick(target: Character) {
        process_periodic_conditions([target], "round_end")
    }
}
"#;
    let mut state = GameState::new();
    let entity = make_character(&mut state, 100);
    let (state, _log) = run_function(source, "do_apply", state, entity);

    // After on_apply: count = 1
    let conds = state.read_conditions(&entity).unwrap();
    assert_eq!(
        conds[0].state_fields.get::<Name>(&"count".into()),
        Some(&Value::Int(1))
    );

    // After periodic: count = 2
    let (state, _log) = run_function(source, "do_tick", state, entity);

    let conds = state.read_conditions(&entity).unwrap();
    assert_eq!(
        conds[0].state_fields.get::<Name>(&"count".into()),
        Some(&Value::Int(2))
    );

    // Second tick: count = 3
    let (state, _log) = run_function(source, "do_tick", state, entity);
    let conds = state.read_conditions(&entity).unwrap();
    assert_eq!(
        conds[0].state_fields.get::<Name>(&"count".into()),
        Some(&Value::Int(3))
    );
}

#[test]
fn state_readable_in_on_remove_runtime() {
    // Set state in on_apply, verify it's available in on_remove via side effect
    let source = r#"
system "test" {
    entity Character {
        HP: int
        last_tick_count: int
    }
    condition Ticking on bearer: Character {
        state {
            count: int = 0
        }
        on_apply {
            state.count = 42
        }
        on_remove {
            // Write state value to entity field for test verification
            bearer.last_tick_count = state.count
        }
    }
    function do_apply(target: Character) {
        apply_condition(target, Ticking, Duration.Indefinite)
    }
    function do_remove(target: Character) {
        remove_condition(target, Ticking)
    }
}
"#;
    let mut state = GameState::new();
    let mut fields = FxHashMap::default();
    fields.insert("HP".into(), Value::Int(100));
    fields.insert("last_tick_count".into(), Value::Int(0));
    let entity = state.add_entity("Character", fields);

    let (state, _log) = run_function(source, "do_apply", state, entity);
    let (state, _log) = run_function(source, "do_remove", state, entity);

    // on_remove should have written state.count (42) to bearer.last_tick_count
    let val = state.read_field(&entity, "last_tick_count").unwrap();
    assert_eq!(val, Value::Int(42));
}

#[test]
fn state_default_references_params() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Scaled(potency: int = 5) on bearer: Character {
        state {
            initial_potency: int = potency
        }
    }
    function do_apply(target: Character) {
        apply_condition(target, Scaled(potency: 10), Duration.Indefinite)
    }
}
"#;
    let mut state = GameState::new();
    let entity = make_character(&mut state, 100);
    let (state, _log) = run_function(source, "do_apply", state, entity);

    let conds = state.read_conditions(&entity).unwrap();
    assert_eq!(
        conds[0].state_fields.get::<Name>(&"initial_potency".into()),
        Some(&Value::Int(10))
    );
}

#[test]
fn no_state_fields_no_effect() {
    // Conditions without state fields should not emit SetConditionState
    let source = r#"
system "test" {
    tag round_end
    entity Character { HP: int }
    condition Simple on bearer: Character {
        periodic #round_end {
            bearer.HP = bearer.HP - 1
        }
    }
    function do_apply(target: Character) {
        apply_condition(target, Simple, Duration.Indefinite)
    }
    function do_tick(target: Character) {
        process_periodic_conditions([target], "round_end")
    }
}
"#;
    let mut state = GameState::new();
    let entity = make_character(&mut state, 100);
    let (state, _log) = run_function(source, "do_apply", state, entity);
    let (_state, log) = run_function(source, "do_tick", state, entity);

    // No SetConditionState should be emitted for stateless conditions
    let set_state = log
        .iter()
        .find(|e| matches!(e, Effect::SetConditionState { .. }));
    assert!(
        set_state.is_none(),
        "should not emit SetConditionState for stateless condition"
    );
}

// ── Typed conditions() overload ────────────────────────────────

#[test]
fn typed_conditions_basic_check() {
    // 2-arg conditions(entity, CondName) should type-check
    setup(
        r#"
system "test" {
    entity Character { HP: int }
    condition Poisoned(potency: int = 1) on bearer: Character {
        state {
            ticks: int = 0
        }
    }
    derive check_it(target: Character) -> bool {
        let cs = conditions(target, Poisoned)
        len(cs) > 0
    }
}
"#,
    );
}

#[test]
fn typed_conditions_param_access_check() {
    // Accessing condition parameters through typed results
    setup(
        r#"
system "test" {
    entity Character { HP: int }
    condition Poisoned(potency: int = 1) on bearer: Character {
        state {
            ticks: int = 0
        }
    }
    derive get_potency(target: Character) -> int {
        let cs = conditions(target, Poisoned)
        if len(cs) > 0 {
            first(cs).unwrap().potency
        } else {
            0
        }
    }
}
"#,
    );
}

#[test]
fn typed_conditions_state_access_check() {
    // Accessing state fields through .state.field
    setup(
        r#"
system "test" {
    entity Character { HP: int }
    condition Poisoned(potency: int = 1) on bearer: Character {
        state {
            ticks: int = 0
        }
    }
    derive get_ticks(target: Character) -> int {
        let cs = conditions(target, Poisoned)
        if len(cs) > 0 {
            first(cs).unwrap().state.ticks
        } else {
            0
        }
    }
}
"#,
    );
}

#[test]
fn typed_conditions_base_fields_accessible() {
    // Base ActiveCondition fields (name, id, duration, etc.) should still work
    setup(
        r#"
system "test" {
    entity Character { HP: int }
    condition Poisoned on bearer: Character {}
    derive get_id(target: Character) -> int {
        let cs = conditions(target, Poisoned)
        if len(cs) > 0 {
            first(cs).unwrap().id
        } else {
            0
        }
    }
}
"#,
    );
}

#[test]
fn typed_conditions_unknown_field_error() {
    let errors = setup_expect_errors(
        r#"
system "test" {
    entity Character { HP: int }
    condition Poisoned on bearer: Character {}
    derive bad(target: Character) -> int {
        let cs = conditions(target, Poisoned)
        first(cs).unwrap().nonexistent
    }
}
"#,
    );
    assert!(
        errors.iter().any(|e| e.contains("no field `nonexistent`")),
        "expected field error, got: {errors:?}"
    );
}

#[test]
fn typed_conditions_state_on_stateless_error() {
    let errors = setup_expect_errors(
        r#"
system "test" {
    entity Character { HP: int }
    condition Poisoned on bearer: Character {}
    derive bad(target: Character) -> int {
        let cs = conditions(target, Poisoned)
        first(cs).unwrap().state.ticks
    }
}
"#,
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("has no state fields") || e.contains("no field `state`")),
        "expected state error, got: {errors:?}"
    );
}

#[test]
fn typed_conditions_not_a_condition_error() {
    let errors = setup_expect_errors(
        r#"
system "test" {
    entity Character { HP: int }
    derive bad(target: Character) -> bool {
        len(conditions(target, NotACondition)) > 0
    }
}
"#,
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("not a known condition") || e.contains("undefined")),
        "expected unknown condition error, got: {errors:?}"
    );
}

#[test]
fn typed_conditions_compatible_with_remove_condition() {
    // TypedActiveCondition should be compatible with remove_condition's Condition param
    setup(
        r#"
system "test" {
    entity Character { HP: int }
    condition Poisoned on bearer: Character {}
    function remove_first_poison(target: Character) {
        let cs = conditions(target, Poisoned)
        if len(cs) > 0 {
            remove_condition(target, first(cs).unwrap())
        }
    }
}
"#,
    );
}

#[test]
fn typed_conditions_runtime_params_and_state() {
    // Full runtime test: apply condition with params and state, then read them back
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Poisoned(potency: int) on bearer: Character {
        state {
            ticks: int = 0
        }
        on_apply {
            state.ticks = potency * 2
        }
    }
    function do_apply(target: Character) {
        apply_condition(target, Poisoned(potency: 5), Duration.Indefinite)
    }
    function read_params(target: Character) {
        let cs = conditions(target, Poisoned)
        let c = first(cs).unwrap()
        // Access param and state, verify they're correct via HP mutation
        target.HP = c.potency
    }
    function read_state(target: Character) {
        let cs = conditions(target, Poisoned)
        let c = first(cs).unwrap()
        target.HP = c.state.ticks
    }
}
"#;
    let mut state = GameState::new();
    let entity = make_character(&mut state, 100);
    let (state, _log) = run_function(source, "do_apply", state, entity);

    // Read param: potency = 5
    let (state, _log) = run_function(source, "read_params", state, entity);
    let hp = state.read_field(&entity, "HP").unwrap();
    assert_eq!(hp, Value::Int(5), "should read potency param = 5");

    // Read state: ticks = potency * 2 = 10
    let (state, _log) = run_function(source, "read_state", state, entity);
    let hp = state.read_field(&entity, "HP").unwrap();
    assert_eq!(hp, Value::Int(10), "should read state.ticks = 10");
}

#[test]
fn typed_conditions_filters_by_name() {
    // Ensure 2-arg conditions() only returns matching conditions
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Poisoned on bearer: Character {}
    condition Stunned on bearer: Character {}
    function do_apply(target: Character) {
        apply_condition(target, Poisoned, Duration.Indefinite)
        apply_condition(target, Stunned, Duration.Indefinite)
    }
    function count_poisoned(target: Character) {
        target.HP = len(conditions(target, Poisoned))
    }
    function count_stunned(target: Character) {
        target.HP = len(conditions(target, Stunned))
    }
}
"#;
    let mut state = GameState::new();
    let entity = make_character(&mut state, 100);
    let (state, _log) = run_function(source, "do_apply", state, entity);

    let (state, _log) = run_function(source, "count_poisoned", state, entity);
    let hp = state.read_field(&entity, "HP").unwrap();
    assert_eq!(hp, Value::Int(1), "should have exactly 1 Poisoned");

    let (state, _log) = run_function(source, "count_stunned", state, entity);
    let hp = state.read_field(&entity, "HP").unwrap();
    assert_eq!(hp, Value::Int(1), "should have exactly 1 Stunned");
}
