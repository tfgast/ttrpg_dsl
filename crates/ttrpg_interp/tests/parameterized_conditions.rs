//! Integration tests for parameterized conditions.
//!
//! Verifies named argument resolution and default parameter materialization
//! through the full pipeline (parse → check → interpret).

use std::collections::{BTreeMap, HashMap};

use ttrpg_ast::FileId;
use ttrpg_ast::diagnostic::Severity;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
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

struct MinimalHandler;

impl EffectHandler for MinimalHandler {
    fn handle(&mut self, _effect: Effect) -> Response {
        Response::Acknowledged
    }
}

struct TestState {
    fields: HashMap<(u64, String), Value>,
    conditions: HashMap<u64, Vec<ActiveCondition>>,
}

impl TestState {
    fn new() -> Self {
        TestState {
            fields: HashMap::new(),
            conditions: HashMap::new(),
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
    fn read_turn_budget(&self, _entity: &EntityRef) -> Option<BTreeMap<ttrpg_ast::Name, Value>> {
        None
    }
    fn read_enabled_options(&self) -> Vec<ttrpg_ast::Name> {
        vec![]
    }
    fn position_eq(&self, _a: &Value, _b: &Value) -> bool {
        false
    }
    fn distance(&self, _a: &Value, _b: &Value) -> Option<i64> {
        None
    }
}

// ── Tests ──────────────────────────────────────────────────────

#[test]
fn condition_named_arg_resolved_by_name() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Frightened(source: Character) on bearer: Character {}
    mechanic scare(actor: Character) -> Condition {
        Frightened(source: actor)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = TestState::new();
    state.fields.insert((1, "HP".into()), Value::Int(10));
    state.conditions.insert(1, vec![]);
    let mut handler = MinimalHandler;

    let val = interp
        .evaluate_mechanic(&state, &mut handler, "scare", vec![Value::Entity(EntityRef(1))])
        .unwrap();

    // The condition should have args keyed by the declared param name "source"
    match val {
        Value::Condition { name, args } => {
            assert_eq!(name, "Frightened");
            assert_eq!(args.get("source"), Some(&Value::Entity(EntityRef(1))));
        }
        other => panic!("expected Condition value, got {:?}", other),
    }
}

#[test]
fn condition_positional_arg_maps_to_declared_name() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Frightened(source: Character) on bearer: Character {}
    mechanic scare(actor: Character) -> Condition {
        Frightened(actor)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = TestState::new();
    state.fields.insert((1, "HP".into()), Value::Int(10));
    state.conditions.insert(1, vec![]);
    let mut handler = MinimalHandler;

    let val = interp
        .evaluate_mechanic(&state, &mut handler, "scare", vec![Value::Entity(EntityRef(1))])
        .unwrap();

    match val {
        Value::Condition { name, args } => {
            assert_eq!(name, "Frightened");
            // Positional arg should be stored under "source", not some other name
            assert_eq!(args.get("source"), Some(&Value::Entity(EntityRef(1))));
            assert_eq!(args.len(), 1);
        }
        other => panic!("expected Condition value, got {:?}", other),
    }
}

#[test]
fn condition_default_param_materialized_when_omitted() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Weakened(level: int = 1) on bearer: Character {}
    mechanic weaken() -> Condition {
        Weakened
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = TestState::new();
    let mut handler = MinimalHandler;

    let val = interp
        .evaluate_mechanic(&state, &mut handler, "weaken", vec![])
        .unwrap();

    match val {
        Value::Condition { name, args } => {
            assert_eq!(name, "Weakened");
            // Default should be materialized: level = 1
            assert_eq!(args.get("level"), Some(&Value::Int(1)));
        }
        other => panic!("expected Condition value, got {:?}", other),
    }
}

#[test]
fn condition_default_param_overridden_by_explicit_arg() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Weakened(level: int = 1) on bearer: Character {}
    mechanic weaken_hard() -> Condition {
        Weakened(3)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = TestState::new();
    let mut handler = MinimalHandler;

    let val = interp
        .evaluate_mechanic(&state, &mut handler, "weaken_hard", vec![])
        .unwrap();

    match val {
        Value::Condition { name, args } => {
            assert_eq!(name, "Weakened");
            assert_eq!(args.get("level"), Some(&Value::Int(3)));
        }
        other => panic!("expected Condition value, got {:?}", other),
    }
}

#[test]
fn condition_mixed_required_and_default_params() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Cursed(source: Character, severity: int = 1) on bearer: Character {}
    mechanic curse(actor: Character) -> Condition {
        Cursed(actor)
    }
    mechanic curse_hard(actor: Character) -> Condition {
        Cursed(actor, 3)
    }
    mechanic curse_named(actor: Character) -> Condition {
        Cursed(source: actor, severity: 5)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = TestState::new();
    state.fields.insert((1, "HP".into()), Value::Int(10));
    state.conditions.insert(1, vec![]);
    let mut handler = MinimalHandler;

    // Only required arg — default should be filled
    let val = interp
        .evaluate_mechanic(&state, &mut handler, "curse", vec![Value::Entity(EntityRef(1))])
        .unwrap();
    match val {
        Value::Condition { args, .. } => {
            assert_eq!(args.get("source"), Some(&Value::Entity(EntityRef(1))));
            assert_eq!(args.get("severity"), Some(&Value::Int(1)));
        }
        other => panic!("expected Condition, got {:?}", other),
    }

    // Both args positional
    let val = interp
        .evaluate_mechanic(&state, &mut handler, "curse_hard", vec![Value::Entity(EntityRef(1))])
        .unwrap();
    match val {
        Value::Condition { args, .. } => {
            assert_eq!(args.get("source"), Some(&Value::Entity(EntityRef(1))));
            assert_eq!(args.get("severity"), Some(&Value::Int(3)));
        }
        other => panic!("expected Condition, got {:?}", other),
    }

    // Both args named
    let val = interp
        .evaluate_mechanic(&state, &mut handler, "curse_named", vec![Value::Entity(EntityRef(1))])
        .unwrap();
    match val {
        Value::Condition { args, .. } => {
            assert_eq!(args.get("source"), Some(&Value::Entity(EntityRef(1))));
            assert_eq!(args.get("severity"), Some(&Value::Int(5)));
        }
        other => panic!("expected Condition, got {:?}", other),
    }
}
