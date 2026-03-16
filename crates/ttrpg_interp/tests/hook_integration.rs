//! Hook integration tests.
//!
//! Entity-facing runtime coverage has moved to `tests/hooks.ttrpg-cli`.
//! These Rust tests keep direct interpreter/effect-handler behavior that still
//! depends on `execute_hook`/`fire_hooks` APIs.

use std::collections::{BTreeMap, HashMap, VecDeque};

use ttrpg_ast::FileId;
use ttrpg_ast::diagnostic::Severity;
use ttrpg_interp::Interpreter;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::state::{ActiveCondition, EntityRef, StateProvider};
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
    fn position_eq(&self, _a: u64, _b: u64) -> bool {
        false
    }
    fn distance(&self, _a: u64, _b: u64) -> Option<i64> {
        None
    }
}

fn make_payload(event_name: &str, fields: Vec<(&str, Value)>) -> Value {
    let mut map = BTreeMap::new();
    for (name, val) in fields {
        map.insert(ttrpg_ast::Name::from(name), val);
    }
    Value::Struct {
        name: format!("__event_{event_name}").into(),
        fields: map,
    }
}

// ── Tests ──────────────────────────────────────────────────────

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
    assert_eq!(val, Value::Void);

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

    let mut handler = ScriptedHandler::new();
    let val = interp
        .execute_hook(&state, &mut handler, "OnDamage", EntityRef(1), payload)
        .unwrap();
    assert_eq!(val, Value::Void);

    // Verify no DeductCost
    assert!(
        !handler
            .log
            .iter()
            .any(|e| matches!(e, Effect::DeductCost { .. }))
    );
    // ActionStarted + MutateField + ActionCompleted (no DeductCost)
    assert_eq!(handler.log.len(), 3);
}

#[test]
#[allow(deprecated)]
fn fire_hooks_executes_all_matching() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    event damage(target: Character) {}
    hook First on target: Character (trigger: damage(target: target)) {
        target.HP -= 1
    }
    hook Second on target: Character (trigger: damage(target: target)) {
        target.HP -= 2
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
    assert_eq!(results[0].2, Value::Void);
    assert_eq!(results[1].0, "Second");
    assert_eq!(results[1].2, Value::Void);
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
            Value::Void,
        )
        .unwrap_err();
    assert!(err.message.contains("undefined hook"));
}
