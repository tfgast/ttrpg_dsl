//! Integration tests for the `return` statement.
//!
//! Tests the full pipeline (parse → lower → check → interpret) for `return`,
//! verifying early exit behavior in functions and actions.

use std::collections::BTreeMap;

use rustc_hash::FxHashMap;
use ttrpg_ast::diagnostic::Severity;
use ttrpg_ast::FileId;
use ttrpg_interp::adapter::StateAdapter;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
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

struct LogHandler {
    log: Vec<Effect>,
}

impl LogHandler {
    fn new() -> Self {
        Self { log: Vec::new() }
    }
}

impl EffectHandler for LogHandler {
    fn handle(&mut self, effect: Effect) -> Response {
        self.log.push(effect);
        Response::Acknowledged
    }
}

fn standard_turn_budget() -> BTreeMap<ttrpg_ast::Name, Value> {
    let mut b = BTreeMap::new();
    b.insert("actions".into(), Value::Int(1));
    b.insert("bonus_actions".into(), Value::Int(1));
    b.insert("reactions".into(), Value::Int(1));
    b.insert("free_object_interactions".into(), Value::Int(1));
    b
}

// ── Tests: return in function ──────────────────────────────────

#[test]
fn return_early_from_function() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    function clamp(x: int, lo: int, hi: int) -> int {
        if x < lo { return lo }
        if x > hi { return hi }
        x
    }
    action TestClamp on actor: Character () {
        resolve {
            actor.HP = clamp(actor.HP, 0, 100)
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();

    // Test value above hi — should return hi (100)
    let mut state = GameState::new();
    let mut fields = FxHashMap::default();
    fields.insert("HP".into(), Value::Int(150));
    let actor = state.add_entity("Character", fields);
    state.set_turn_budget(&actor, standard_turn_budget());

    let adapter = StateAdapter::new(state);
    let mut handler = LogHandler::new();
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(state, eff_handler, "TestClamp", actor, vec![])
            .unwrap();
        assert_eq!(state.read_field(&actor, "HP"), Some(Value::Int(100)));
    });

    // Test value below lo — should return lo (0)
    let mut state = GameState::new();
    let mut fields = FxHashMap::default();
    fields.insert("HP".into(), Value::Int(-5));
    let actor = state.add_entity("Character", fields);
    state.set_turn_budget(&actor, standard_turn_budget());

    let adapter = StateAdapter::new(state);
    let mut handler = LogHandler::new();
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(state, eff_handler, "TestClamp", actor, vec![])
            .unwrap();
        assert_eq!(state.read_field(&actor, "HP"), Some(Value::Int(0)));
    });

    // Test value in range — should return x (50)
    let mut state = GameState::new();
    let mut fields = FxHashMap::default();
    fields.insert("HP".into(), Value::Int(50));
    let actor = state.add_entity("Character", fields);
    state.set_turn_budget(&actor, standard_turn_budget());

    let adapter = StateAdapter::new(state);
    let mut handler = LogHandler::new();
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(state, eff_handler, "TestClamp", actor, vec![])
            .unwrap();
        assert_eq!(state.read_field(&actor, "HP"), Some(Value::Int(50)));
    });
}

#[test]
fn return_from_for_loop() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    function find_first_positive(xs: list<int>) -> int {
        for x in xs {
            if x > 0 {
                return x
            }
        }
        -1
    }
    action TestFind on actor: Character () {
        resolve {
            actor.HP = find_first_positive([-3, -1, 0, 7, 42])
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();

    let mut state = GameState::new();
    let mut fields = FxHashMap::default();
    fields.insert("HP".into(), Value::Int(0));
    let actor = state.add_entity("Character", fields);
    state.set_turn_budget(&actor, standard_turn_budget());

    let adapter = StateAdapter::new(state);
    let mut handler = LogHandler::new();
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(state, eff_handler, "TestFind", actor, vec![])
            .unwrap();
        assert_eq!(state.read_field(&actor, "HP"), Some(Value::Int(7)));
    });
}

#[test]
fn bare_return_in_action() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    action GuardedHeal on actor: Character (target: Character) {
        resolve {
            if target.HP >= 100 {
                return
            }
            target.HP += 10
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();

    // Target at full HP — should NOT heal
    let mut state = GameState::new();
    let mut actor_fields = FxHashMap::default();
    actor_fields.insert("HP".into(), Value::Int(50));
    let actor = state.add_entity("Character", actor_fields);

    let mut tarread_fields = FxHashMap::default();
    tarread_fields.insert("HP".into(), Value::Int(100));
    let target = state.add_entity("Character", tarread_fields);
    state.set_turn_budget(&actor, standard_turn_budget());

    let adapter = StateAdapter::new(state);
    let mut handler = LogHandler::new();
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "GuardedHeal",
                actor,
                vec![Value::Entity(target)],
            )
            .unwrap();
        assert_eq!(state.read_field(&target, "HP"), Some(Value::Int(100)));
    });

    // Target at low HP — should heal
    let mut state = GameState::new();
    let mut actor_fields = FxHashMap::default();
    actor_fields.insert("HP".into(), Value::Int(50));
    let actor = state.add_entity("Character", actor_fields);

    let mut tarread_fields = FxHashMap::default();
    tarread_fields.insert("HP".into(), Value::Int(20));
    let target = state.add_entity("Character", tarread_fields);
    state.set_turn_budget(&actor, standard_turn_budget());

    let adapter = StateAdapter::new(state);
    let mut handler = LogHandler::new();
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "GuardedHeal",
                actor,
                vec![Value::Entity(target)],
            )
            .unwrap();
        assert_eq!(state.read_field(&target, "HP"), Some(Value::Int(30)));
    });
}

// ── Tests: checker rejects return in wrong contexts ────────────

#[test]
fn return_rejected_in_derive() {
    let errors = setup_expect_errors(
        r#"
system "test" {
    derive foo(x: int) -> int {
        return x
    }
}
"#,
    );
    assert!(
        errors.iter().any(|e| e.contains("return is not allowed")),
        "expected error about return not allowed, got: {errors:?}"
    );
}

#[test]
fn return_rejected_in_mechanic() {
    let errors = setup_expect_errors(
        r#"
system "test" {
    mechanic foo(x: int) -> int {
        return x
    }
}
"#,
    );
    assert!(
        errors.iter().any(|e| e.contains("return is not allowed")),
        "expected error about return not allowed, got: {errors:?}"
    );
}

#[test]
fn return_type_mismatch() {
    let errors = setup_expect_errors(
        r#"
system "test" {
    function foo(x: int) -> int {
        return "hello"
    }
}
"#,
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("return value has type string")),
        "expected type mismatch error, got: {errors:?}"
    );
}

#[test]
fn bare_return_in_value_returning_function() {
    let errors = setup_expect_errors(
        r#"
system "test" {
    function foo(x: int) -> int {
        return
    }
}
"#,
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("bare `return`")),
        "expected bare return error, got: {errors:?}"
    );
}
