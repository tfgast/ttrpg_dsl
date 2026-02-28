//! Hook integration tests.
//!
//! Tests the full pipeline (parse → check → interpret) for hook declarations,
//! exercising event matching, execution, and the fire_hooks API.

use std::collections::{BTreeMap, HashMap, VecDeque};

use ttrpg_ast::diagnostic::Severity;
use ttrpg_ast::FileId;
use ttrpg_interp::effect::{ActionKind, Effect, EffectHandler, Response};
use ttrpg_interp::state::{ActiveCondition, EntityRef, StateProvider};
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

// ── TestState ──────────────────────────────────────────────────

struct TestState {
    fields: HashMap<(u64, String), Value>,
    conditions: HashMap<u64, Vec<ActiveCondition>>,
    turn_budgets: HashMap<u64, BTreeMap<ttrpg_ast::Name, Value>>,
    enabled_options: Vec<ttrpg_ast::Name>,
}

impl TestState {
    fn new() -> Self {
        TestState {
            fields: HashMap::new(),
            conditions: HashMap::new(),
            turn_budgets: HashMap::new(),
            enabled_options: Vec::new(),
        }
    }
}

impl StateProvider for TestState {
    fn read_field(&self, entity: &EntityRef, field: &str) -> Option<Value> {
        self.fields.get(&(entity.0, field.to_string())).cloned()
    }
    fn read_conditions(&self, entity: &EntityRef) -> Option<Vec<ActiveCondition>> {
        self.conditions.get(&entity.0).cloned()
    }
    fn read_turn_budget(&self, entity: &EntityRef) -> Option<BTreeMap<ttrpg_ast::Name, Value>> {
        self.turn_budgets.get(&entity.0).cloned()
    }
    fn read_enabled_options(&self) -> Vec<ttrpg_ast::Name> {
        self.enabled_options.clone()
    }
    fn position_eq(&self, _a: &Value, _b: &Value) -> bool {
        false
    }
    fn distance(&self, _a: &Value, _b: &Value) -> Option<i64> {
        None
    }
}

fn make_payload(event_name: &str, fields: Vec<(&str, Value)>) -> Value {
    let mut map = BTreeMap::new();
    for (name, val) in fields {
        map.insert(ttrpg_ast::Name::from(name), val);
    }
    Value::Struct {
        name: format!("__event_{}", event_name).into(),
        fields: map,
    }
}

// ── Tests ──────────────────────────────────────────────────────

#[test]
fn hook_fires_on_matching_event() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    event damage(target: Character) {}
    hook OnDamage on target: Character (trigger: damage(target: target)) {
        target.HP -= 1
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = TestState::new();
    state.fields.insert((1, "HP".into()), Value::Int(20));
    state.conditions.insert(1, vec![]);

    let payload = make_payload("damage", vec![("target", Value::Entity(EntityRef(1)))]);

    // Query which hooks match
    let hook_result = interp
        .what_hooks(&state, "damage", payload.clone(), &[EntityRef(1)])
        .unwrap();

    assert_eq!(hook_result.hooks.len(), 1);
    assert_eq!(hook_result.hooks[0].name, "OnDamage");
    assert_eq!(hook_result.hooks[0].target, EntityRef(1));

    // Execute the hook
    let mut handler = ScriptedHandler::new();
    let val = interp
        .execute_hook(&state, &mut handler, "OnDamage", EntityRef(1), payload)
        .unwrap();
    assert_eq!(val, Value::None); // assignment returns None

    // Verify effect sequence: ActionStarted(Hook), MutateField, ActionCompleted
    assert_eq!(handler.log.len(), 3);
    assert!(matches!(
        &handler.log[0],
        Effect::ActionStarted { name, kind: ActionKind::Hook { event, .. }, .. }
        if name == "OnDamage" && event == "damage"
    ));
    assert!(matches!(&handler.log[1], Effect::MutateField { .. }));
    assert!(matches!(&handler.log[2], Effect::ActionCompleted { name, .. } if name == "OnDamage"));
}

#[test]
fn hook_skips_non_matching_entity() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    event damage(target: Character) {}
    hook OnDamage on target: Character (trigger: damage(target: target)) {
        target.HP -= 1
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = TestState::new();

    // Payload targets entity(1), but candidate is entity(2)
    let payload = make_payload("damage", vec![("target", Value::Entity(EntityRef(1)))]);

    let hook_result = interp
        .what_hooks(&state, "damage", payload, &[EntityRef(2)])
        .unwrap();

    assert_eq!(hook_result.hooks.len(), 0);
}

#[test]
fn hook_can_mutate_entity_field() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    event heal(target: Character) {}
    hook OnHeal on target: Character (trigger: heal(target: target)) {
        target.HP += 5
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = TestState::new();
    state.fields.insert((1, "HP".into()), Value::Int(10));
    state.conditions.insert(1, vec![]);

    let payload = make_payload("heal", vec![("target", Value::Entity(EntityRef(1)))]);

    let mut handler = ScriptedHandler::new();
    interp
        .execute_hook(&state, &mut handler, "OnHeal", EntityRef(1), payload)
        .unwrap();

    // Should have MutateField effect
    assert!(handler
        .log
        .iter()
        .any(|e| matches!(e, Effect::MutateField { .. })));
}

#[test]
fn hook_declaration_order_preserved() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    event damage(target: Character) {}
    hook First on target: Character (trigger: damage(target: target)) {
        1
    }
    hook Second on target: Character (trigger: damage(target: target)) {
        2
    }
    hook Third on target: Character (trigger: damage(target: target)) {
        3
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = TestState::new();
    state.fields.insert((1, "HP".into()), Value::Int(20));
    state.conditions.insert(1, vec![]);

    let payload = make_payload("damage", vec![("target", Value::Entity(EntityRef(1)))]);

    let hook_result = interp
        .what_hooks(&state, "damage", payload, &[EntityRef(1)])
        .unwrap();

    assert_eq!(hook_result.hooks.len(), 3);
    assert_eq!(hook_result.hooks[0].name, "First");
    assert_eq!(hook_result.hooks[1].name, "Second");
    assert_eq!(hook_result.hooks[2].name, "Third");
}

#[test]
fn hook_not_suppressed_by_conditions() {
    // Hooks should NOT be affected by condition suppression (only reactions are)
    let source = r#"
system "test" {
    entity Character { HP: int }
    event damage(target: Character) {}
    hook OnDamage on target: Character (trigger: damage(target: target)) {
        target.HP -= 1
    }
    condition Stunned on bearer: Character {
        suppress damage(target: bearer)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = TestState::new();
    state.fields.insert((1, "HP".into()), Value::Int(20));
    // Entity 1 has Stunned condition
    state.conditions.insert(
        1,
        vec![ActiveCondition {
            id: 100,
            name: "Stunned".into(),
            params: BTreeMap::new(),
            bearer: EntityRef(1),
            gained_at: 1,
            duration: Value::None,
            invocation: None,
        }],
    );

    let payload = make_payload("damage", vec![("target", Value::Entity(EntityRef(1)))]);

    // Hook should still match — suppression only affects reactions
    let hook_result = interp
        .what_hooks(&state, "damage", payload, &[EntityRef(1)])
        .unwrap();

    assert_eq!(hook_result.hooks.len(), 1);
    assert_eq!(hook_result.hooks[0].name, "OnDamage");
}

#[test]
fn hook_veto_returns_none() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    event damage(target: Character) {}
    hook OnDamage on target: Character (trigger: damage(target: target)) {
        target.HP -= 1
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = TestState::new();
    state.fields.insert((1, "HP".into()), Value::Int(20));
    state.conditions.insert(1, vec![]);

    let payload = make_payload("damage", vec![("target", Value::Entity(EntityRef(1)))]);

    // Host vetoes the hook
    let mut handler = ScriptedHandler::with_responses(vec![Response::Vetoed]);
    let val = interp
        .execute_hook(&state, &mut handler, "OnDamage", EntityRef(1), payload)
        .unwrap();
    assert_eq!(val, Value::None);

    // Only ActionStarted + ActionCompleted
    assert_eq!(handler.log.len(), 2);
    assert!(matches!(&handler.log[0], Effect::ActionStarted { .. }));
    assert!(matches!(&handler.log[1], Effect::ActionCompleted { .. }));
}

#[test]
fn hook_no_cost_deduction() {
    // Hooks should never emit DeductCost
    let source = r#"
system "test" {
    entity Character { HP: int }
    event damage(target: Character) {}
    hook OnDamage on target: Character (trigger: damage(target: target)) {
        42
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = TestState::new();
    state.fields.insert((1, "HP".into()), Value::Int(20));
    state.conditions.insert(1, vec![]);

    let payload = make_payload("damage", vec![("target", Value::Entity(EntityRef(1)))]);

    let mut handler = ScriptedHandler::new();
    let val = interp
        .execute_hook(&state, &mut handler, "OnDamage", EntityRef(1), payload)
        .unwrap();
    assert_eq!(val, Value::Int(42));

    // Verify no DeductCost
    assert!(!handler
        .log
        .iter()
        .any(|e| matches!(e, Effect::DeductCost { .. })));
    // Only ActionStarted + ActionCompleted
    assert_eq!(handler.log.len(), 2);
}

#[test]
fn fire_hooks_executes_all_matching() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    event damage(target: Character) {}
    hook First on target: Character (trigger: damage(target: target)) {
        1
    }
    hook Second on target: Character (trigger: damage(target: target)) {
        2
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = TestState::new();
    state.fields.insert((1, "HP".into()), Value::Int(20));
    state.conditions.insert(1, vec![]);

    let payload = make_payload("damage", vec![("target", Value::Entity(EntityRef(1)))]);

    let mut handler = ScriptedHandler::new();
    let results = interp
        .fire_hooks(&state, &mut handler, "damage", payload, &[EntityRef(1)])
        .unwrap();

    assert_eq!(results.len(), 2);
    assert_eq!(results[0].0, "First");
    assert_eq!(results[0].2, Value::Int(1));
    assert_eq!(results[1].0, "Second");
    assert_eq!(results[1].2, Value::Int(2));
}

#[test]
fn hook_trigger_payload_accessible() {
    // Verify that `trigger` struct is available in the hook resolve block
    let source = r#"
system "test" {
    entity Character { HP: int }
    event damage(target: Character, amount: int) {}
    hook OnDamage on target: Character (trigger: damage(target: target)) {
        trigger.amount
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = TestState::new();
    state.fields.insert((1, "HP".into()), Value::Int(20));
    state.conditions.insert(1, vec![]);

    let payload = make_payload(
        "damage",
        vec![
            ("target", Value::Entity(EntityRef(1))),
            ("amount", Value::Int(15)),
        ],
    );

    let mut handler = ScriptedHandler::new();
    let val = interp
        .execute_hook(&state, &mut handler, "OnDamage", EntityRef(1), payload)
        .unwrap();
    assert_eq!(val, Value::Int(15));
}

#[test]
fn undefined_hook_errors() {
    let source = r#"
system "test" {
    entity Character { HP: int }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();

    let err = interp
        .execute_hook(
            &state,
            &mut handler,
            "Nonexistent",
            EntityRef(1),
            Value::None,
        )
        .unwrap_err();
    assert!(err.message.contains("undefined hook"));
}

#[test]
fn hook_turn_actor_save_restore() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    event damage(target: Character) {}
    hook OnDamage on target: Character (trigger: damage(target: target)) {
        1
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = TestState::new();
    state.fields.insert((1, "HP".into()), Value::Int(20));
    state.conditions.insert(1, vec![]);

    let payload = make_payload("damage", vec![("target", Value::Entity(EntityRef(1)))]);

    // Execute hook and verify it doesn't corrupt state
    let mut handler = ScriptedHandler::new();
    let val = interp
        .execute_hook(&state, &mut handler, "OnDamage", EntityRef(1), payload)
        .unwrap();
    assert_eq!(val, Value::Int(1));
}
