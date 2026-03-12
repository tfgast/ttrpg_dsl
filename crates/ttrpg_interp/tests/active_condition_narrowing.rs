//! Integration tests for `is ActiveCondition<CondName>` narrowing.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use ttrpg_ast::diagnostic::Severity;
use ttrpg_ast::{FileId, Name};
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

struct MinimalHandler;
impl EffectHandler for MinimalHandler {
    fn handle(&mut self, _: Effect) -> Response {
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
    fn position_eq(&self, _a: u64, _b: u64) -> bool {
        false
    }
    fn distance(&self, _a: u64, _b: u64) -> Option<i64> {
        None
    }
}

fn make_condition(name: &str) -> ActiveCondition {
    ActiveCondition {
        id: 1,
        name: Name::from(name),
        params: BTreeMap::new(),
        bearer: EntityRef(1),
        gained_at: 0,
        duration: Value::Void,
        invocation: None,
        applied_at: 0,
        source: Value::Void,
        tags: BTreeSet::new(),
        state_fields: BTreeMap::new(),
    }
}

// ── Runtime is checks ──────────────────────────────────────────

#[test]
fn is_typed_active_condition_true() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Prone on bearer: Character {}
    derive check(actor: Character) -> bool {
        let conds = conditions(actor)
        if len(conds) > 0 {
            let c = conds[0]
            c is ActiveCondition<Prone>
        } else {
            false
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = TestState::new();
    state.fields.insert((1, "HP".into()), Value::Int(10));
    state.conditions.insert(1, vec![make_condition("Prone")]);
    let mut handler = MinimalHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "check",
            vec![Value::Entity(EntityRef(1))],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(true));
}

#[test]
fn is_typed_active_condition_false() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Prone on bearer: Character {}
    condition Stunned on bearer: Character {}
    derive check(actor: Character) -> bool {
        let conds = conditions(actor)
        if len(conds) > 0 {
            let c = conds[0]
            c is ActiveCondition<Prone>
        } else {
            false
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = TestState::new();
    state.fields.insert((1, "HP".into()), Value::Int(10));
    state.conditions.insert(1, vec![make_condition("Stunned")]);
    let mut handler = MinimalHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "check",
            vec![Value::Entity(EntityRef(1))],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(false));
}

// ── Narrowing gives typed access to condition params ───────────

#[test]
fn narrowing_enables_param_access() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Frightened(origin: Character) on bearer: Character {}
    derive get_origin(actor: Character) -> Character {
        let conds = conditions(actor)
        let c = conds[0]
        if c is ActiveCondition<Frightened> {
            c.origin
        } else {
            actor
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = TestState::new();
    state.fields.insert((1, "HP".into()), Value::Int(10));
    state.fields.insert((2, "HP".into()), Value::Int(20));
    let mut cond = make_condition("Frightened");
    cond.params
        .insert(Name::from("origin"), Value::Entity(EntityRef(2)));
    state.conditions.insert(1, vec![cond]);
    let mut handler = MinimalHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "get_origin",
            vec![Value::Entity(EntityRef(1))],
        )
        .unwrap();
    assert_eq!(val, Value::Entity(EntityRef(2)));
}

#[test]
fn param_access_without_narrowing_is_error() {
    // Accessing a param field without narrowing is a checker error
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Weakened(level: int) on bearer: Character {}
    derive get_level(actor: Character) -> int {
        let conds = conditions(actor)
        let c = conds[0]
        c.level
    }
}
"#;
    let errors = setup_expect_errors(source);
    assert!(
        errors.iter().any(|e| e.contains("narrow with")),
        "expected error suggesting narrowing, got: {errors:?}"
    );
}

// ── Checker error cases ────────────────────────────────────────

#[test]
fn is_active_condition_requires_typed_target() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Prone on bearer: Character {}
    derive check(actor: Character) -> bool {
        let conds = conditions(actor)
        let c = conds[0]
        c is int
    }
}
"#;
    let errors = setup_expect_errors(source);
    assert!(
        errors
            .iter()
            .any(|e| e.contains("ActiveCondition") && e.contains("is")),
        "expected error about is on ActiveCondition, got: {errors:?}"
    );
}

#[test]
fn is_typed_active_condition_on_wrong_type_rejected() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Prone on bearer: Character {}
    derive check(actor: Character) -> bool {
        let x = 42
        x is ActiveCondition<Prone>
    }
}
"#;
    let errors = setup_expect_errors(source);
    assert!(
        !errors.is_empty(),
        "expected checker error for is ActiveCondition<Prone> on int"
    );
}
