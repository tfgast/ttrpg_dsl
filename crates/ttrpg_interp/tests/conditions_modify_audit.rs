//! Spec audit: conditions and modify system.
//!
//! Tests the full pipeline (parse → lower → check → interpret) verifying
//! the condition/modify system against 02_scoping.ttrpg requirements:
//!
//! 1. Phase 1 + Phase 2 mixed in a single modify body
//! 2. Conflict resolution: oldest-first pipeline ordering, last-writer-wins
//! 3. Cost modification: cost=free, cost=token replacement, checker rejects
//!    param/result overrides in cost modify bodies
//! 4. Suppress clauses: reaction suppression at runtime, hooks NOT suppressible
//! 5. modify_applied: user-defined override takes precedence
//! 6. Condition extends clause behavior (inheritance, ordering, diamond dedup)
//! 7. Parameterized conditions: params stored on ActiveCondition, matching on remove

use std::collections::{BTreeMap, HashMap, VecDeque};

use ttrpg_ast::diagnostic::Severity;
use ttrpg_ast::FileId;
use ttrpg_interp::adapter::StateAdapter;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::StateProvider;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

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
    if !parse_errors.is_empty() {
        return parse_errors.iter().map(|d| d.message.clone()).collect();
    }
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

// ── ScriptedHandler ────────────────────────────────────────────

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

    #[allow(dead_code)]
    fn with_responses(responses: Vec<Response>) -> Self {
        ScriptedHandler {
            script: responses.into(),
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

// ═══════════════════════════════════════════════════════════════
// 1. Phase 1 + Phase 2 mixed in a single modify body
// ═══════════════════════════════════════════════════════════════

#[test]
fn mixed_phase1_and_phase2_in_single_modify_body() {
    // Spec: "A single modify body can contain both phases; the runtime
    //        partitions them." (03_canonical_grammar.ttrpg lines 301-304)
    let source = r#"
system "test" {
    entity Character { HP: int }

    derive compute(target: Character, bonus: int) -> int {
        bonus * 2
    }

    condition Mixed on bearer: Character {
        modify compute(target: bearer) {
            // Phase 1: override input parameter
            bonus = bonus + 10
            // Phase 2: modify the result
            result = result + 1
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(10));
    let entity = state.add_entity("Character", fields);

    state.apply_condition(
        &entity,
        "Mixed",
        BTreeMap::new(),
        Value::None,
        None,
    );

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();

    let val = adapter.run(&mut handler, |state, eff_handler| {
        interp.evaluate_derive(
            state,
            eff_handler,
            "compute",
            vec![Value::Entity(entity), Value::Int(5)],
        )
    });

    // Phase 1: bonus = 5 + 10 = 15
    // Body:    15 * 2 = 30
    // Phase 2: 30 + 1 = 31
    assert_eq!(val.unwrap(), Value::Int(31));
}

#[test]
fn mixed_phases_with_conditional() {
    // Verify Phase 1 and Phase 2 work inside if/else blocks
    let source = r#"
system "test" {
    entity Character { HP: int }

    derive compute(target: Character, bonus: int) -> int {
        bonus * 2
    }

    condition ConditionalMixed on bearer: Character {
        modify compute(target: bearer) {
            if bonus > 0 {
                bonus = bonus + 5
                result = result + 100
            } else {
                result = result - 1
            }
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(10));
    let entity = state.add_entity("Character", fields);

    state.apply_condition(
        &entity,
        "ConditionalMixed",
        BTreeMap::new(),
        Value::None,
        None,
    );

    let adapter = StateAdapter::new(state);

    // bonus > 0 path
    let mut handler = ScriptedHandler::new();
    let val = adapter.run(&mut handler, |state, eff_handler| {
        interp.evaluate_derive(
            state,
            eff_handler,
            "compute",
            vec![Value::Entity(entity), Value::Int(3)],
        )
    });
    // Phase 1: bonus = 3 + 5 = 8
    // Body:    8 * 2 = 16
    // Phase 2: 16 + 100 = 116
    assert_eq!(val.unwrap(), Value::Int(116));

    // bonus <= 0 path
    let mut handler = ScriptedHandler::new();
    let val = adapter.run(&mut handler, |state, eff_handler| {
        interp.evaluate_derive(
            state,
            eff_handler,
            "compute",
            vec![Value::Entity(entity), Value::Int(0)],
        )
    });
    // Phase 1: no change, bonus = 0
    // Body:    0 * 2 = 0
    // Phase 2: 0 - 1 = -1
    assert_eq!(val.unwrap(), Value::Int(-1));
}

// ═══════════════════════════════════════════════════════════════
// 2. Conflict resolution: oldest-first ordering, last-writer-wins
// ═══════════════════════════════════════════════════════════════

#[test]
fn multiple_conditions_oldest_first_last_writer_wins() {
    // Spec: "modifiers are applied in the order the conditions were gained
    //        by the entity (oldest first)... Last writer wins."
    let source = r#"
system "test" {
    entity Character { HP: int }

    derive compute(target: Character, val: int) -> int {
        val
    }

    condition First on bearer: Character {
        modify compute(target: bearer) {
            val = 100
        }
    }

    condition Second on bearer: Character {
        modify compute(target: bearer) {
            val = 200
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(10));
    let entity = state.add_entity("Character", fields);

    // Apply First, then Second — Second is newer, so it writes last
    state.apply_condition(&entity, "First", BTreeMap::new(), Value::None, None);
    state.apply_condition(&entity, "Second", BTreeMap::new(), Value::None, None);

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();

    let val = adapter.run(&mut handler, |state, eff_handler| {
        interp.evaluate_derive(
            state,
            eff_handler,
            "compute",
            vec![Value::Entity(entity), Value::Int(0)],
        )
    });

    // First sets val=100, then Second sets val=200 (last writer wins)
    assert_eq!(val.unwrap(), Value::Int(200));
}

#[test]
fn pipeline_model_each_modifier_sees_previous_output() {
    // Spec: "Each modifier sees the parameter value left by the previous
    //        modifier (pipeline model, not independent evaluation)."
    let source = r#"
system "test" {
    entity Character { HP: int }

    derive compute(target: Character, val: int) -> int {
        val
    }

    condition Adder on bearer: Character {
        modify compute(target: bearer) {
            val = val + 10
        }
    }

    condition Doubler on bearer: Character {
        modify compute(target: bearer) {
            val = val * 2
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(10));
    let entity = state.add_entity("Character", fields);

    // Apply Adder first, then Doubler
    state.apply_condition(&entity, "Adder", BTreeMap::new(), Value::None, None);
    state.apply_condition(&entity, "Doubler", BTreeMap::new(), Value::None, None);

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();

    let val = adapter.run(&mut handler, |state, eff_handler| {
        interp.evaluate_derive(
            state,
            eff_handler,
            "compute",
            vec![Value::Entity(entity), Value::Int(5)],
        )
    });

    // Adder: val = 5 + 10 = 15
    // Doubler sees 15: val = 15 * 2 = 30
    assert_eq!(val.unwrap(), Value::Int(30));
}

#[test]
fn within_condition_clauses_in_declaration_order() {
    // Spec: "Within a single condition, clauses are applied in
    //        declaration order."
    let source = r#"
system "test" {
    entity Character { HP: int }

    derive compute(target: Character, val: int) -> int {
        val
    }

    condition MultiClause on bearer: Character {
        // First clause: add 10
        modify compute(target: bearer) {
            val = val + 10
        }
        // Second clause: multiply by 3
        modify compute(target: bearer) {
            val = val * 3
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(10));
    let entity = state.add_entity("Character", fields);

    state.apply_condition(
        &entity,
        "MultiClause",
        BTreeMap::new(),
        Value::None,
        None,
    );

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();

    let val = adapter.run(&mut handler, |state, eff_handler| {
        interp.evaluate_derive(
            state,
            eff_handler,
            "compute",
            vec![Value::Entity(entity), Value::Int(5)],
        )
    });

    // First clause: val = 5 + 10 = 15
    // Second clause: val = 15 * 3 = 45
    assert_eq!(val.unwrap(), Value::Int(45));
}

// ═══════════════════════════════════════════════════════════════
// 3. Cost modification
// ═══════════════════════════════════════════════════════════════

#[test]
fn cost_modify_replaces_cost_token() {
    // Spec: "modify Dash.cost(actor: bearer) { cost = bonus_action }"
    // Changes an action's cost from one token to another.
    let source = r#"
system "test" {
    entity Character { HP: int }

    action Dash on actor: Character () {
        cost { action }
        resolve {
            actor.HP += 0
        }
    }

    condition CunningAction on bearer: Character {
        modify Dash.cost(actor: bearer) {
            cost = bonus_action
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(10));
    let entity = state.add_entity("Character", fields);

    state.apply_condition(
        &entity,
        "CunningAction",
        BTreeMap::new(),
        Value::None,
        None,
    );

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();

    adapter.run(&mut handler, |state, eff_handler| {
        interp.execute_action(state, eff_handler, "Dash", entity, vec![])
    }).unwrap();

    // Should deduct bonus_action instead of action
    let deduct_effects: Vec<_> = handler
        .log
        .iter()
        .filter_map(|e| match e {
            Effect::DeductCost { token, budget_field, .. } => Some((token.clone(), budget_field.clone())),
            _ => None,
        })
        .collect();

    assert_eq!(deduct_effects.len(), 1);
    assert_eq!(deduct_effects[0].0.as_str(), "bonus_action");
    assert_eq!(deduct_effects[0].1.as_str(), "bonus_actions");
}

#[test]
fn cost_modify_makes_action_free() {
    // Spec: "cost = free — waive the cost entirely"
    let source = r#"
system "test" {
    entity Character { HP: int }

    action Dash on actor: Character () {
        cost { action }
        resolve {
            actor.HP += 0
        }
    }

    condition FreeDash on bearer: Character {
        modify Dash.cost(actor: bearer) {
            cost = free
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(10));
    let entity = state.add_entity("Character", fields);

    state.apply_condition(
        &entity,
        "FreeDash",
        BTreeMap::new(),
        Value::None,
        None,
    );

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();

    adapter.run(&mut handler, |state, eff_handler| {
        interp.execute_action(state, eff_handler, "Dash", entity, vec![])
    }).unwrap();

    // No DeductCost effect should be emitted
    let has_deduct = handler
        .log
        .iter()
        .any(|e| matches!(e, Effect::DeductCost { .. }));
    assert!(!has_deduct, "cost=free should suppress DeductCost effects");
}

#[test]
fn cost_modify_conditional_free() {
    // Spec: "if/else for conditional cost changes"
    let source = r#"
system "test" {
    entity Character { HP: int }

    action Dash on actor: Character () {
        cost { action }
        resolve {
            actor.HP += 0
        }
    }

    condition MaybeFree on bearer: Character {
        modify Dash.cost(actor: bearer) {
            if bearer.HP > 5 {
                cost = free
            }
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();

    // HP > 5: should be free
    let mut state = GameState::new();
    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(10));
    let entity = state.add_entity("Character", fields);
    state.apply_condition(&entity, "MaybeFree", BTreeMap::new(), Value::None, None);

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, eff_handler| {
        interp.execute_action(state, eff_handler, "Dash", entity, vec![])
    }).unwrap();

    let has_deduct = handler.log.iter().any(|e| matches!(e, Effect::DeductCost { .. }));
    assert!(!has_deduct, "HP > 5 should make action free");

    // HP <= 5: should cost normally
    let mut state2 = GameState::new();
    let mut fields2 = HashMap::new();
    fields2.insert("HP".into(), Value::Int(3));
    let entity2 = state2.add_entity("Character", fields2);
    state2.apply_condition(&entity2, "MaybeFree", BTreeMap::new(), Value::None, None);

    let adapter2 = StateAdapter::new(state2);
    let mut handler2 = ScriptedHandler::new();
    adapter2.run(&mut handler2, |state, eff_handler| {
        interp.execute_action(state, eff_handler, "Dash", entity2, vec![])
    }).unwrap();

    let has_deduct2 = handler2.log.iter().any(|e| matches!(e, Effect::DeductCost { .. }));
    assert!(has_deduct2, "HP <= 5 should still cost an action");
}

#[test]
fn cost_modify_rejects_param_override() {
    // Spec: "Cost modify bodies reject parameter overrides (param = expr)"
    let errors = setup_expect_errors(r#"
system "test" {
    entity Character { HP: int }
    action Dash on actor: Character () {
        cost { action }
        resolve { actor.HP += 0 }
    }
    condition Bad on bearer: Character {
        modify Dash.cost(actor: bearer) {
            actor = bearer
        }
    }
}
"#);
    assert!(
        !errors.is_empty(),
        "param override in cost modify body should produce checker error"
    );
}

#[test]
fn cost_modify_rejects_result_override() {
    // Spec: "Cost modify bodies reject result rewrites (result.field = expr)"
    let errors = setup_expect_errors(r#"
system "test" {
    entity Character { HP: int }
    action Dash on actor: Character () {
        cost { action }
        resolve { actor.HP += 0 }
    }
    condition Bad on bearer: Character {
        modify Dash.cost(actor: bearer) {
            result.foo = 1
        }
    }
}
"#);
    assert!(
        !errors.is_empty(),
        "result override in cost modify body should produce checker error"
    );
}

#[test]
fn cost_modify_target_must_be_action_or_reaction() {
    // Spec: "The target must be an action or reaction (not a derive or mechanic)"
    let errors = setup_expect_errors(r#"
system "test" {
    entity Character { HP: int }
    derive compute(target: Character) -> int { 42 }
    condition Bad on bearer: Character {
        modify compute.cost(target: bearer) {
            cost = free
        }
    }
}
"#);
    assert!(
        !errors.is_empty(),
        ".cost modify on a derive should produce checker error"
    );
}

// ═══════════════════════════════════════════════════════════════
// 4. Suppress clauses
// ═══════════════════════════════════════════════════════════════

#[test]
fn suppress_blocks_reaction_triggering() {
    // Spec: "Conditions can suppress reactions (but not hooks)"
    let source = r#"
system "test" {
    entity Character { HP: int }

    event entity_leaves_reach(reactor: Character, entity: Character) {}

    reaction OpportunityAttack on attacker: Character (
        trigger: entity_leaves_reach(reactor: attacker)
    ) {
        cost { reaction }
        resolve {
            attacker.HP += 0
        }
    }

    condition Disengaging on bearer: Character {
        suppress entity_leaves_reach(entity: bearer)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(10));
    let attacker = state.add_entity("Character", fields.clone());
    let mover = state.add_entity("Character", fields);

    // Without Disengaging: reaction should trigger
    let payload = Value::Struct {
        name: "__event_entity_leaves_reach".into(),
        fields: {
            let mut f = BTreeMap::new();
            f.insert("reactor".into(), Value::Entity(attacker));
            f.insert("entity".into(), Value::Entity(mover));
            f
        },
    };

    let result_no_cond = interp
        .what_triggers(&state, "entity_leaves_reach", payload.clone(), &[attacker])
        .unwrap();
    assert_eq!(
        result_no_cond.triggerable.len(),
        1,
        "without Disengaging, reaction should be triggerable"
    );
    assert!(
        result_no_cond.suppressed.is_empty(),
        "nothing should be suppressed"
    );

    // With Disengaging on the mover: reaction should be suppressed
    state.apply_condition(
        &mover,
        "Disengaging",
        BTreeMap::new(),
        Value::None,
        None,
    );

    let result_with_cond = interp
        .what_triggers(&state, "entity_leaves_reach", payload, &[attacker])
        .unwrap();
    assert!(
        result_with_cond.triggerable.is_empty(),
        "with Disengaging, reaction should be suppressed"
    );
    assert_eq!(
        result_with_cond.suppressed.len(),
        1,
        "reaction should appear in suppressed list"
    );
}

#[test]
fn suppress_does_not_affect_hooks() {
    // Spec: "Hooks are NOT suppressible — they always fire"
    let source = r#"
system "test" {
    entity Character { HP: int }

    event entity_leaves_reach(entity: Character) {}

    hook TrackLeave on target: Character (
        trigger: entity_leaves_reach(entity: target)
    ) {
        target.HP += 0
    }

    condition Disengaging on bearer: Character {
        suppress entity_leaves_reach(entity: bearer)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(10));
    let entity = state.add_entity("Character", fields);

    // Apply suppress condition
    state.apply_condition(
        &entity,
        "Disengaging",
        BTreeMap::new(),
        Value::None,
        None,
    );

    let payload = Value::Struct {
        name: "__event_entity_leaves_reach".into(),
        fields: {
            let mut f = BTreeMap::new();
            f.insert("entity".into(), Value::Entity(entity));
            f
        },
    };

    // Hook should still match despite suppression
    let hook_result = interp
        .what_hooks(&state, "entity_leaves_reach", payload, &[entity])
        .unwrap();
    assert_eq!(
        hook_result.hooks.len(),
        1,
        "hooks should fire even when suppress clause matches"
    );
}

// ═══════════════════════════════════════════════════════════════
// 5. modify_applied: user-defined override takes precedence
// ═══════════════════════════════════════════════════════════════

#[test]
fn user_defined_modify_applied_overrides_builtin() {
    // Spec: "User-defined events with the name modify_applied take
    //        precedence over the built-in"
    let source = r#"
system "test" {
    entity Character { HP: int }

    event modify_applied(bearer: Character, condition: string) {
        target_fn: string
        custom_field: int
    }
}
"#;
    let (_program, result) = setup(source);

    let event_info = &result.env.events["modify_applied"];
    // User-defined version should have the extra custom_field
    assert_eq!(event_info.fields.len(), 2, "user-defined version should have 2 fields");
    let field_names: Vec<_> = event_info.fields.iter().map(|(n, _)| n.as_str()).collect();
    assert!(field_names.contains(&"target_fn"), "should still have target_fn");
    assert!(field_names.contains(&"custom_field"), "should have custom_field from user definition");
    // Should NOT be marked as builtin
    assert!(!event_info.builtin, "user-defined event should override builtin");
}

// ═══════════════════════════════════════════════════════════════
// 6. Condition extends clause behavior
// ═══════════════════════════════════════════════════════════════

#[test]
fn extends_inherits_parent_modify_clauses() {
    // Spec: "Child condition inherits ALL modify/suppress clauses from parents"
    // Spec: "Clauses applied in ancestor order" (parents first, then child)
    let source = r#"
system "test" {
    entity Character { HP: int }

    derive compute(target: Character, val: int) -> int {
        val
    }

    condition Parent on bearer: Character {
        modify compute(target: bearer) {
            val = val + 10
        }
    }

    condition Child extends Parent on bearer: Character {
        modify compute(target: bearer) {
            val = val * 2
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(10));
    let entity = state.add_entity("Character", fields);

    // Only apply Child — it should inherit Parent's modify clause
    state.apply_condition(&entity, "Child", BTreeMap::new(), Value::None, None);

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();

    let val = adapter.run(&mut handler, |state, eff_handler| {
        interp.evaluate_derive(
            state,
            eff_handler,
            "compute",
            vec![Value::Entity(entity), Value::Int(5)],
        )
    });

    // Parent clause first: val = 5 + 10 = 15
    // Child clause second: val = 15 * 2 = 30
    assert_eq!(val.unwrap(), Value::Int(30));
}

#[test]
fn extends_inherits_suppress_clauses() {
    // Spec: "Child condition inherits ALL modify/suppress clauses from parents"
    let source = r#"
system "test" {
    entity Character { HP: int }

    event entity_leaves_reach(reactor: Character, entity: Character) {}

    reaction OpportunityAttack on attacker: Character (
        trigger: entity_leaves_reach(reactor: attacker)
    ) {
        cost { reaction }
        resolve { attacker.HP += 0 }
    }

    condition Incapacitated on bearer: Character {
        suppress entity_leaves_reach(entity: bearer)
    }

    condition Stunned extends Incapacitated on bearer: Character {}
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(10));
    let attacker = state.add_entity("Character", fields.clone());
    let mover = state.add_entity("Character", fields);

    // Apply Stunned (which extends Incapacitated) — should inherit suppress
    state.apply_condition(&mover, "Stunned", BTreeMap::new(), Value::None, None);

    let payload = Value::Struct {
        name: "__event_entity_leaves_reach".into(),
        fields: {
            let mut f = BTreeMap::new();
            f.insert("reactor".into(), Value::Entity(attacker));
            f.insert("entity".into(), Value::Entity(mover));
            f
        },
    };

    let result = interp
        .what_triggers(&state, "entity_leaves_reach", payload, &[attacker])
        .unwrap();
    assert!(
        result.triggerable.is_empty(),
        "Stunned (extends Incapacitated) should inherit suppress clause"
    );
}

#[test]
fn extends_ancestor_order_parents_before_child() {
    // Spec: "Ancestor chain collected via DFS post-order (parents first, then child)"
    let source = r#"
system "test" {
    entity Character { HP: int }

    derive compute(target: Character, val: int) -> int {
        val
    }

    condition Grandparent on bearer: Character {
        modify compute(target: bearer) {
            val = val + 1
        }
    }

    condition Parent extends Grandparent on bearer: Character {
        modify compute(target: bearer) {
            val = val * 10
        }
    }

    condition Child extends Parent on bearer: Character {
        modify compute(target: bearer) {
            val = val + 1000
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(10));
    let entity = state.add_entity("Character", fields);

    state.apply_condition(&entity, "Child", BTreeMap::new(), Value::None, None);

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();

    let val = adapter.run(&mut handler, |state, eff_handler| {
        interp.evaluate_derive(
            state,
            eff_handler,
            "compute",
            vec![Value::Entity(entity), Value::Int(0)],
        )
    });

    // Grandparent first: val = 0 + 1 = 1
    // Parent second:     val = 1 * 10 = 10
    // Child third:       val = 10 + 1000 = 1010
    assert_eq!(val.unwrap(), Value::Int(1010));
}

#[test]
fn extends_diamond_deduplication() {
    // Spec: "Diamond inheritance deduplication via HashSet"
    //
    //       Base
    //      /    \
    //   Left   Right
    //      \    /
    //      Diamond
    //
    // Base's clause should apply only once despite two paths.
    let source = r#"
system "test" {
    entity Character { HP: int }

    derive compute(target: Character, val: int) -> int {
        val
    }

    condition Base on bearer: Character {
        modify compute(target: bearer) {
            val = val + 1
        }
    }

    condition Left extends Base on bearer: Character {
        modify compute(target: bearer) {
            val = val * 10
        }
    }

    condition Right extends Base on bearer: Character {
        modify compute(target: bearer) {
            val = val + 100
        }
    }

    condition Diamond extends Left, Right on bearer: Character {
        modify compute(target: bearer) {
            val = val + 5000
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(10));
    let entity = state.add_entity("Character", fields);

    state.apply_condition(&entity, "Diamond", BTreeMap::new(), Value::None, None);

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();

    let val = adapter.run(&mut handler, |state, eff_handler| {
        interp.evaluate_derive(
            state,
            eff_handler,
            "compute",
            vec![Value::Entity(entity), Value::Int(0)],
        )
    });

    // DFS post-order: Left walks Base first, then Left itself.
    // Right tries Base (already visited, skip), then Right itself.
    // Then Diamond itself.
    // Order: Base, Left, Right, Diamond
    //   Base:    val = 0 + 1 = 1
    //   Left:    val = 1 * 10 = 10
    //   Right:   val = 10 + 100 = 110
    //   Diamond: val = 110 + 5000 = 5110
    assert_eq!(val.unwrap(), Value::Int(5110));
}

// ═══════════════════════════════════════════════════════════════
// 7. Parameterized conditions: matching on remove
// ═══════════════════════════════════════════════════════════════

#[test]
fn remove_condition_by_name_removes_all_instances() {
    // Spec: "remove_condition without args removes all matching"
    // Use a non-parameterized condition so bare name works
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Blessed on bearer: Character {}
    action ClearBlessing on actor: Character () {
        cost free
        resolve {
            remove_condition(actor, Blessed)
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(10));
    let entity = state.add_entity("Character", fields);

    // Apply two Blessed conditions
    state.apply_condition(&entity, "Blessed", BTreeMap::new(), Value::None, None);
    state.apply_condition(&entity, "Blessed", BTreeMap::new(), Value::None, None);

    assert_eq!(state.read_conditions(&entity).unwrap().len(), 2);

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();

    adapter.run(&mut handler, |state, eff_handler| {
        interp.execute_action(state, eff_handler, "ClearBlessing", entity, vec![])
    }).unwrap();

    let state = adapter.into_inner();
    // Both Blessed conditions should be removed (bare name removes all matching)
    assert_eq!(
        state.read_conditions(&entity).unwrap().len(),
        0,
        "remove_condition with bare name should remove all instances"
    );
}

#[test]
fn remove_condition_with_params_removes_only_matching() {
    // Spec: "with args removes only matching params"
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Frightened(source: Character) on bearer: Character {}
    action ClearFearFrom on actor: Character (from: Character) {
        cost free
        resolve {
            remove_condition(actor, Frightened(source: from))
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(10));
    let entity = state.add_entity("Character", fields.clone());
    let source1 = state.add_entity("Character", fields.clone());
    let source2 = state.add_entity("Character", fields);

    let mut params1 = BTreeMap::new();
    params1.insert("source".into(), Value::Entity(source1));
    state.apply_condition(&entity, "Frightened", params1, Value::None, None);

    let mut params2 = BTreeMap::new();
    params2.insert("source".into(), Value::Entity(source2));
    state.apply_condition(&entity, "Frightened", params2, Value::None, None);

    assert_eq!(state.read_conditions(&entity).unwrap().len(), 2);

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();

    adapter.run(&mut handler, |state, eff_handler| {
        interp.execute_action(
            state,
            eff_handler,
            "ClearFearFrom",
            entity,
            vec![Value::Entity(source1)],
        )
    }).unwrap();

    let state = adapter.into_inner();
    // Only the Frightened from source1 should be removed
    let remaining = state.read_conditions(&entity).unwrap();
    assert_eq!(
        remaining.len(),
        1,
        "should remove only the condition matching params"
    );
    assert_eq!(
        remaining[0].params.get("source"),
        Some(&Value::Entity(source2)),
        "remaining condition should be from source2"
    );
}

#[test]
fn remove_condition_by_active_condition_id() {
    // Spec: "ActiveCondition instance (removes by unique id for precise removal)"
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Blessed on bearer: Character {}
    action RemoveFirst on actor: Character () {
        cost free
        resolve {
            let conds = conditions(actor)
            if len(conds) > 0 {
                remove_condition(actor, conds[0])
            }
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(10));
    let entity = state.add_entity("Character", fields);

    // Apply two Blessed conditions
    state.apply_condition(&entity, "Blessed", BTreeMap::new(), Value::None, None);
    state.apply_condition(&entity, "Blessed", BTreeMap::new(), Value::None, None);

    assert_eq!(state.read_conditions(&entity).unwrap().len(), 2);

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();

    adapter.run(&mut handler, |state, eff_handler| {
        interp.execute_action(state, eff_handler, "RemoveFirst", entity, vec![])
    }).unwrap();

    let state = adapter.into_inner();
    // Only the first Blessed should be removed (by id), leaving one
    assert_eq!(
        state.read_conditions(&entity).unwrap().len(),
        1,
        "remove_condition by ActiveCondition should remove exactly one instance"
    );
}
