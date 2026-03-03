//! Integration tests for function block interpretation.

use std::collections::BTreeMap;

use rustc_hash::FxHashMap;
use ttrpg_ast::diagnostic::Severity;
use ttrpg_ast::{FileId, Name};
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

struct NoopHandler;
impl EffectHandler for NoopHandler {
    fn handle(&mut self, _: Effect) -> Response {
        Response::Acknowledged
    }
}

/// Records all effects for inspection.
struct RecordingHandler {
    effects: Vec<Effect>,
}

impl RecordingHandler {
    fn new() -> Self {
        Self {
            effects: Vec::new(),
        }
    }
}

impl EffectHandler for RecordingHandler {
    fn handle(&mut self, effect: Effect) -> Response {
        self.effects.push(effect);
        Response::Acknowledged
    }
}

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

// ── Basic evaluation via public API ─────────────────────────────

#[test]
fn evaluate_function_returns_value() {
    let source = r#"
system "test" {
    function add(a: int, b: int) -> int {
        a + b
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_function(
            &state,
            &mut handler,
            "add",
            vec![Value::Int(3), Value::Int(7)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(10));
}

#[test]
fn evaluate_function_with_default_param() {
    let source = r#"
system "test" {
    function add(a: int, b: int = 10) -> int {
        a + b
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_function(&state, &mut handler, "add", vec![Value::Int(5)])
        .unwrap();
    assert_eq!(val, Value::Int(15));
}

#[test]
fn evaluate_function_undefined_errors() {
    let source = r#"
system "test" {
    function add(a: int, b: int) -> int { a + b }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let err = interp
        .evaluate_function(&state, &mut handler, "nonexistent", vec![])
        .unwrap_err();
    assert!(err.message.contains("undefined function"));
}

// ── Function calling function ───────────────────────────────────

#[test]
fn function_calls_function() {
    let source = r#"
system "test" {
    function double(x: int) -> int { x * 2 }
    function quadruple(x: int) -> int { double(double(x)) }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_function(&state, &mut handler, "quadruple", vec![Value::Int(3)])
        .unwrap();
    assert_eq!(val, Value::Int(12));
}

// ── Function called from action resolve block ───────────────────

#[test]
fn function_called_from_action() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    function compute_heal(base: int) -> int { base * 2 }
    action Heal on actor: Character (target: Character) {
        resolve {
            target.hp += compute_heal(3)
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut actor_fields = FxHashMap::default();
    actor_fields.insert(Name::from("hp"), Value::Int(10));
    let actor = state.add_entity("Character", actor_fields);

    let mut target_fields = FxHashMap::default();
    target_fields.insert(Name::from("hp"), Value::Int(5));
    let target = state.add_entity("Character", target_fields);

    let mut turn_budget = BTreeMap::new();
    turn_budget.insert(Name::from("actions"), Value::Int(1));
    turn_budget.insert(Name::from("bonus_actions"), Value::Int(1));
    turn_budget.insert(Name::from("reactions"), Value::Int(1));
    turn_budget.insert(Name::from("movement"), Value::Int(30));
    state.set_turn_budget(&actor, turn_budget);

    let mut handler = RecordingHandler::new();
    interp
        .execute_action(
            &state,
            &mut handler,
            "Heal",
            actor,
            vec![Value::Entity(target)],
        )
        .unwrap();

    // Verify ActionStarted/ActionCompleted lifecycle effects fired
    let action_started = handler
        .effects
        .iter()
        .any(|e| matches!(e, Effect::ActionStarted { .. }));
    let action_completed = handler
        .effects
        .iter()
        .any(|e| matches!(e, Effect::ActionCompleted { .. }));
    assert!(action_started, "expected ActionStarted effect");
    assert!(action_completed, "expected ActionCompleted effect");

    // Verify the mutation: target.hp should be 5 + compute_heal(3) = 5 + 6 = 11
    let mutate = handler
        .effects
        .iter()
        .find(|e| matches!(e, Effect::MutateField { entity, .. } if *entity == target));
    assert!(
        mutate.is_some(),
        "expected MutateField effect for target.hp"
    );
    if let Some(Effect::MutateField { value, .. }) = mutate {
        assert_eq!(*value, Value::Int(6));
    }
}

// ── Void-returning function ─────────────────────────────────────

#[test]
fn void_function_returns_none() {
    let source = r#"
system "test" {
    function noop() {
        let x = 1
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_function(&state, &mut handler, "noop", vec![])
        .unwrap();
    assert_eq!(val, Value::None);
}
