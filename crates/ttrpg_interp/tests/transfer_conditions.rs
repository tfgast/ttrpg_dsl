//! Integration tests for transfer_conditions builtin.

use std::collections::{BTreeMap, VecDeque};

use rustc_hash::FxHashMap;
use ttrpg_ast::FileId;
use ttrpg_ast::diagnostic::Severity;
use ttrpg_interp::Interpreter;
use ttrpg_interp::adapter::StateAdapter;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::{StateProvider, WritableState};
use ttrpg_interp::value::Value;

// ── Setup ──────────────────────────────────────────────────────

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
    assert!(parse_errors.is_empty());
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

fn make_entity(state: &mut GameState, type_name: &str, hp: i64) -> ttrpg_interp::state::EntityRef {
    let mut fields = FxHashMap::default();
    fields.insert("hp".into(), Value::Int(hp));
    state.add_entity(type_name, fields)
}

fn add_tagged_condition(
    state: &mut GameState,
    entity: &ttrpg_interp::state::EntityRef,
    name: &str,
    tags: &[&str],
) {
    state.add_condition(
        entity,
        ttrpg_interp::state::ActiveCondition {
            id: 0,
            name: name.into(),
            params: BTreeMap::default(),
            bearer: *entity,
            gained_at: 0,
            duration: Value::Str("indefinite".into()),
            invocation: None,
            applied_at: 0,
            source: Value::Void,
            tags: tags.iter().map(|t| (*t).into()).collect(),
        },
    );
}

// ═══════════════════════════════════════════════════════════════
// 1. Basic transfer: tagged condition moves from source to target
// ═══════════════════════════════════════════════════════════════

#[test]
fn basic_transfer_moves_tagged_condition() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    tag transferable
    condition Blessed on bearer: entity stacking all {
        tags: #transferable
    }
    function do_transfer(a: entity, b: entity) {
        transfer_conditions(a, b, "transferable")
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let a = make_entity(&mut state, "Character", 20);
    let b = make_entity(&mut state, "Character", 20);
    add_tagged_condition(&mut state, &a, "Blessed", &["transferable"]);

    assert_eq!(state.read_conditions(&a).unwrap().len(), 1);
    assert!(state.read_conditions(&b).unwrap_or_default().is_empty());

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, handler| {
        interp
            .evaluate_function(
                state,
                handler,
                "do_transfer",
                vec![Value::Entity(a), Value::Entity(b)],
            )
            .unwrap();
    });

    let state = adapter.into_inner();
    assert!(
        state.read_conditions(&a).unwrap_or_default().is_empty(),
        "A should have no conditions after transfer"
    );
    let b_conds = state.read_conditions(&b).unwrap();
    assert_eq!(b_conds.len(), 1, "B should have the transferred condition");
    assert_eq!(b_conds[0].name.as_str(), "Blessed");
}

// ═══════════════════════════════════════════════════════════════
// 2. Non-matching tags stay on source
// ═══════════════════════════════════════════════════════════════

#[test]
fn non_matching_tags_stay_on_source() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    tag transferable
    tag physical
    condition Blessed on bearer: entity stacking all {
        tags: #transferable
    }
    condition Regeneration on bearer: entity stacking all {
        tags: #physical
    }
    function do_transfer(a: entity, b: entity) {
        transfer_conditions(a, b, "transferable")
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let a = make_entity(&mut state, "Character", 20);
    let b = make_entity(&mut state, "Character", 20);
    add_tagged_condition(&mut state, &a, "Blessed", &["transferable"]);
    add_tagged_condition(&mut state, &a, "Regeneration", &["physical"]);

    assert_eq!(state.read_conditions(&a).unwrap().len(), 2);

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, handler| {
        interp
            .evaluate_function(
                state,
                handler,
                "do_transfer",
                vec![Value::Entity(a), Value::Entity(b)],
            )
            .unwrap();
    });

    let state = adapter.into_inner();
    let a_conds = state.read_conditions(&a).unwrap();
    assert_eq!(a_conds.len(), 1);
    assert_eq!(a_conds[0].name.as_str(), "Regeneration");

    let b_conds = state.read_conditions(&b).unwrap();
    assert_eq!(b_conds.len(), 1);
    assert_eq!(b_conds[0].name.as_str(), "Blessed");
}

// ═══════════════════════════════════════════════════════════════
// 4. Round-trip transfer preserves identity
// ═══════════════════════════════════════════════════════════════

#[test]
fn round_trip_transfer_preserves_identity() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    tag transferable
    condition Blessed on bearer: entity stacking all {
        tags: #transferable
    }
    function transfer_to(a: entity, b: entity) {
        transfer_conditions(a, b, "transferable")
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let a = make_entity(&mut state, "Character", 20);
    let b = make_entity(&mut state, "Character", 20);

    state.add_condition(
        &a,
        ttrpg_interp::state::ActiveCondition {
            id: 0,
            name: "Blessed".into(),
            params: BTreeMap::default(),
            bearer: a,
            gained_at: 42,
            duration: Value::Str("indefinite".into()),
            invocation: Some(ttrpg_interp::state::InvocationId(99)),
            applied_at: 10,
            source: Value::Str("divine".into()),
            tags: std::collections::BTreeSet::from(["transferable".into()]),
        },
    );

    let original_id = state.read_conditions(&a).unwrap()[0].id;
    let original_gained_at = state.read_conditions(&a).unwrap()[0].gained_at;

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();

    // Transfer A -> B
    adapter.run(&mut handler, |state, handler| {
        interp
            .evaluate_function(
                state,
                handler,
                "transfer_to",
                vec![Value::Entity(a), Value::Entity(b)],
            )
            .unwrap();
    });

    // Transfer B -> A
    adapter.run(&mut handler, |state, handler| {
        interp
            .evaluate_function(
                state,
                handler,
                "transfer_to",
                vec![Value::Entity(b), Value::Entity(a)],
            )
            .unwrap();
    });

    let state = adapter.into_inner();
    let a_conds = state.read_conditions(&a).unwrap();
    assert_eq!(a_conds.len(), 1, "A should have the condition back");
    assert_eq!(a_conds[0].name.as_str(), "Blessed");
    assert_eq!(a_conds[0].id, original_id, "ID preserved through round-trip");
    assert_eq!(
        a_conds[0].gained_at, original_gained_at,
        "gained_at preserved through round-trip"
    );
    assert_eq!(
        a_conds[0].invocation,
        Some(ttrpg_interp::state::InvocationId(99)),
        "invocation preserved"
    );
    assert_eq!(a_conds[0].source, Value::Str("divine".into()), "source preserved");
}

// ═══════════════════════════════════════════════════════════════
// 6. Params preserved through transfer
// ═══════════════════════════════════════════════════════════════

#[test]
fn params_preserved_through_transfer() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    tag transferable
    condition Cursed(severity: int) on bearer: entity stacking all {
        tags: #transferable
    }
    function do_transfer(a: entity, b: entity) {
        transfer_conditions(a, b, "transferable")
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let a = make_entity(&mut state, "Character", 20);
    let b = make_entity(&mut state, "Character", 20);

    let mut params = std::collections::BTreeMap::new();
    params.insert("severity".into(), Value::Int(5));

    state.add_condition(
        &a,
        ttrpg_interp::state::ActiveCondition {
            id: 0,
            name: "Cursed".into(),
            params: params.clone(),
            bearer: a,
            gained_at: 0,
            duration: Value::Str("indefinite".into()),
            invocation: None,
            applied_at: 0,
            source: Value::Void,
            tags: std::collections::BTreeSet::from(["transferable".into()]),
        },
    );

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, handler| {
        interp
            .evaluate_function(
                state,
                handler,
                "do_transfer",
                vec![Value::Entity(a), Value::Entity(b)],
            )
            .unwrap();
    });

    let state = adapter.into_inner();
    let b_conds = state.read_conditions(&b).unwrap();
    assert_eq!(b_conds.len(), 1);
    assert_eq!(b_conds[0].params.get("severity"), Some(&Value::Int(5)));
}

// ═══════════════════════════════════════════════════════════════
// 7. Empty transfer is a no-op
// ═══════════════════════════════════════════════════════════════

#[test]
fn empty_transfer_is_noop() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    tag transferable
    function do_transfer(a: entity, b: entity) {
        transfer_conditions(a, b, "transferable")
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let a = make_entity(&mut state, "Character", 20);
    let b = make_entity(&mut state, "Character", 20);

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, handler| {
        interp
            .evaluate_function(
                state,
                handler,
                "do_transfer",
                vec![Value::Entity(a), Value::Entity(b)],
            )
            .unwrap();
    });
}

// ═══════════════════════════════════════════════════════════════
// 9. Tag validation: checker rejects undeclared tag string literals
// ═══════════════════════════════════════════════════════════════

#[test]
fn checker_rejects_undeclared_tag() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    function do_transfer(a: Character, b: Character) {
        transfer_conditions(a, b, "nonexistent")
    }
}
"#;
    let errors = setup_expect_errors(source);
    assert!(
        errors.iter().any(|e| e.contains("undeclared tag")),
        "expected undeclared tag error, got: {errors:?}"
    );
}

// ═══════════════════════════════════════════════════════════════
// 10. No gate effects emitted during transfer
// ═══════════════════════════════════════════════════════════════

#[test]
fn no_gate_effects_during_transfer() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    tag transferable
    condition Blessed on bearer: entity stacking all {
        tags: #transferable
    }
    function do_transfer(a: entity, b: entity) {
        transfer_conditions(a, b, "transferable")
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let a = make_entity(&mut state, "Character", 20);
    let b = make_entity(&mut state, "Character", 20);
    add_tagged_condition(&mut state, &a, "Blessed", &["transferable"]);

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, handler| {
        interp
            .evaluate_function(
                state,
                handler,
                "do_transfer",
                vec![Value::Entity(a), Value::Entity(b)],
            )
            .unwrap();
    });

    let gate_count = handler
        .log
        .iter()
        .filter(|e| {
            matches!(
                e,
                Effect::ConditionApplyGate { .. } | Effect::ConditionRemovalGate { .. }
            )
        })
        .count();
    assert_eq!(gate_count, 0, "transfer should not emit gate effects");
}

// ═══════════════════════════════════════════════════════════════
// 11. Same-entity transfer is a no-op
// ═══════════════════════════════════════════════════════════════

#[test]
fn same_entity_transfer_is_noop() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    tag transferable
    condition Blessed on bearer: entity stacking all {
        tags: #transferable
    }
    function self_transfer(a: entity) {
        transfer_conditions(a, a, "transferable")
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let a = make_entity(&mut state, "Character", 20);
    add_tagged_condition(&mut state, &a, "Blessed", &["transferable"]);

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, handler| {
        interp
            .evaluate_function(
                state,
                handler,
                "self_transfer",
                vec![Value::Entity(a)],
            )
            .unwrap();
    });

    let state = adapter.into_inner();
    assert_eq!(
        state.read_conditions(&a).unwrap().len(),
        1,
        "condition should still be on A"
    );
}

// ═══════════════════════════════════════════════════════════════
// 5. Lifecycle block: transfer inside on_remove
// ═══════════════════════════════════════════════════════════════

#[test]
fn transfer_in_on_remove_lifecycle_block() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    entity Monster { hp: int }
    tag transferable

    condition Blessed on bearer: entity stacking all {
        tags: #transferable
    }

    condition Polymorphed(original: Character) on bearer: Monster
        stacking first
    {
        on_remove {
            transfer_conditions(bearer, original, "transferable")
        }
    }

    function apply_poly(form: Monster, original: Character) {
        apply_condition(form, Polymorphed(original: original), Duration.Indefinite)
    }
    function remove_poly(form: Monster, original: Character) {
        remove_condition(form, Polymorphed(original: original))
    }
}
"#;
    let (program, result) = setup(source);
    let mut state = GameState::new();
    let c = make_entity(&mut state, "Character", 20);
    let m = make_entity(&mut state, "Monster", 20);

    // Apply Blessed on the monster form (manually, gets auto-assigned id from state)
    add_tagged_condition(&mut state, &m, "Blessed", &["transferable"]);

    // Start interpreter condition counter above what state has already assigned
    // (GameState auto-assigns id=1 for Blessed, so start at 100 to avoid collision)
    let interp = Interpreter::new_with_counters(&program, &result.env, 1, 100).unwrap();

    // Apply Polymorphed condition on the monster
    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, handler| {
        interp
            .evaluate_function(
                state,
                handler,
                "apply_poly",
                vec![Value::Entity(m), Value::Entity(c)],
            )
            .unwrap();
    });

    // Remove Polymorphed — on_remove should transfer Blessed to Character
    adapter.run(&mut handler, |state, handler| {
        interp
            .evaluate_function(
                state,
                handler,
                "remove_poly",
                vec![Value::Entity(m), Value::Entity(c)],
            )
            .unwrap();
    });

    let state = adapter.into_inner();

    // Character should now have Blessed
    let c_conds = state.read_conditions(&c).unwrap_or_default();
    let blessed = c_conds.iter().find(|c| c.name == "Blessed");
    assert!(
        blessed.is_some(),
        "Character should have Blessed after on_remove transfer"
    );

    // Monster should not have Blessed (transferred away) — may still have Polymorphed remnants
    let m_conds = state.read_conditions(&m).unwrap_or_default();
    let m_blessed = m_conds.iter().find(|c| c.name == "Blessed");
    assert!(m_blessed.is_none(), "Monster should not have Blessed");
}

// ═══════════════════════════════════════════════════════════════
// 8. Self-exclusion: removing condition is not transferred
// ═══════════════════════════════════════════════════════════════

#[test]
fn self_exclusion_in_on_remove() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    entity Monster { hp: int }
    tag transferable

    condition Polymorphed(original: Character) on bearer: Monster
        stacking first
    {
        tags: #transferable
        on_remove {
            transfer_conditions(bearer, original, "transferable")
        }
    }

    function apply_poly(form: Monster, original: Character) {
        apply_condition(form, Polymorphed(original: original), Duration.Indefinite)
    }
    function remove_poly(form: Monster, original: Character) {
        remove_condition(form, Polymorphed(original: original))
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let c = make_entity(&mut state, "Character", 20);
    let m = make_entity(&mut state, "Monster", 20);

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();

    // Apply Polymorphed
    adapter.run(&mut handler, |state, handler| {
        interp
            .evaluate_function(
                state,
                handler,
                "apply_poly",
                vec![Value::Entity(m), Value::Entity(c)],
            )
            .unwrap();
    });

    // Remove Polymorphed — on_remove transfers #transferable conditions.
    // Polymorphed itself has #transferable, but should be EXCLUDED (self-exclusion).
    adapter.run(&mut handler, |state, handler| {
        interp
            .evaluate_function(
                state,
                handler,
                "remove_poly",
                vec![Value::Entity(m), Value::Entity(c)],
            )
            .unwrap();
    });

    let state = adapter.into_inner();
    // Character should NOT have Polymorphed (it was excluded from transfer)
    let c_conds = state.read_conditions(&c).unwrap_or_default();
    let c_poly = c_conds.iter().find(|c| c.name == "Polymorphed");
    assert!(
        c_poly.is_none(),
        "Character should NOT have Polymorphed — it's the removing condition"
    );
}

// ═══════════════════════════════════════════════════════════════
// 16. Bearer type skip: on bearer: Character skipped for Monster
// ═══════════════════════════════════════════════════════════════

#[test]
fn bearer_type_incompatible_stays_on_source() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    entity Monster { hp: int }
    tag transferable
    condition CharOnly on bearer: Character stacking all {
        tags: #transferable
    }
    condition ForAll on bearer: entity stacking all {
        tags: #transferable
    }
    function do_transfer(a: entity, b: entity) {
        transfer_conditions(a, b, "transferable")
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let c = make_entity(&mut state, "Character", 20);
    let m = make_entity(&mut state, "Monster", 20);

    add_tagged_condition(&mut state, &c, "CharOnly", &["transferable"]);
    add_tagged_condition(&mut state, &c, "ForAll", &["transferable"]);

    // Build receiver type map for bearer type checking
    let mut receiver_types = FxHashMap::default();
    for (name, info) in &result.env.conditions {
        receiver_types.insert(name.clone(), info.receiver_type.clone());
    }

    let mut adapter = StateAdapter::new(state);
    adapter.set_condition_receiver_types(receiver_types);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, handler| {
        interp
            .evaluate_function(
                state,
                handler,
                "do_transfer",
                vec![Value::Entity(c), Value::Entity(m)],
            )
            .unwrap();
    });

    let state = adapter.into_inner();
    // Character should retain CharOnly (incompatible with Monster)
    let c_conds = state.read_conditions(&c).unwrap();
    assert_eq!(c_conds.len(), 1);
    assert_eq!(c_conds[0].name.as_str(), "CharOnly");

    // Monster should have ForAll (compatible — on bearer: entity)
    let m_conds = state.read_conditions(&m).unwrap();
    assert_eq!(m_conds.len(), 1);
    assert_eq!(m_conds[0].name.as_str(), "ForAll");
}
