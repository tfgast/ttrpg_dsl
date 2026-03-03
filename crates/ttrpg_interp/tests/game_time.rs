//! Integration tests for `game_time()` and `advance_time()` builtins.
//!
//! Covers: default value, advancing in functions, read accessibility,
//! runtime error inside action scope, adapter application to GameState.

use std::collections::VecDeque;

use rustc_hash::FxHashMap;
use ttrpg_ast::diagnostic::Severity;
use ttrpg_ast::{FileId, Name};
use ttrpg_interp::adapter::StateAdapter;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::StateProvider;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

// ── Setup ──────────────────────────────────────────────────────

fn compile(source: &str) -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
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

// ── Scripted handler ───────────────────────────────────────────

struct ScriptedHandler {
    script: VecDeque<Response>,
    log: Vec<Effect>,
}

impl ScriptedHandler {
    fn ack_all() -> Self {
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

// ── game_time() returns zero by default ────────────────────────

#[test]
fn game_time_returns_zero_by_default() {
    let source = r#"
system "test" {
    function read_time() -> int {
        game_time()
    }
}
"#;
    let (program, result) = compile(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::ack_all();

    let val = adapter
        .run(&mut handler, |s, h| {
            interp.evaluate_function(s, h, "read_time", vec![])
        })
        .unwrap();
    assert_eq!(val, Value::Int(0));
}

// ── advance_time then game_time ────────────────────────────────

#[test]
fn advance_time_then_game_time() {
    let source = r#"
system "test" {
    function tick_and_read() -> int {
        advance_time(5)
        game_time()
    }
}
"#;
    let (program, result) = compile(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::ack_all();

    let val = adapter
        .run(&mut handler, |s, h| {
            interp.evaluate_function(s, h, "tick_and_read", vec![])
        })
        .unwrap();
    assert_eq!(val, Value::Int(5));
}

// ── multiple advance_time calls accumulate ─────────────────────

#[test]
fn advance_time_accumulates() {
    let source = r#"
system "test" {
    function multi_tick() -> int {
        advance_time(3)
        advance_time(7)
        game_time()
    }
}
"#;
    let (program, result) = compile(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::ack_all();

    let val = adapter
        .run(&mut handler, |s, h| {
            interp.evaluate_function(s, h, "multi_tick", vec![])
        })
        .unwrap();
    assert_eq!(val, Value::Int(10));
}

// ── game_time readable after advance then action ───────────────

#[test]
fn game_time_readable_after_action() {
    let source = r#"
system "test" {
    entity Character { hp: int }

    action Noop on actor: Character () {
        cost free
        resolve {}
    }

    function tick_action_read(c: Character) -> int {
        advance_time(3)
        c.Noop()
        game_time()
    }
}
"#;
    let (program, result) = compile(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let entity = state.add_entity("Character", {
        let mut f = FxHashMap::default();
        f.insert(Name::from("hp"), Value::Int(10));
        f
    });
    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::ack_all();

    let val = adapter
        .run(&mut handler, |s, h| {
            interp.evaluate_function(s, h, "tick_action_read", vec![Value::Entity(entity)])
        })
        .unwrap();
    assert_eq!(val, Value::Int(3));
}

// ── action calling advance_time → runtime error ────────────────

#[test]
fn advance_time_errors_inside_action() {
    let source = r#"
system "test" {
    entity Character { hp: int }

    function do_advance() {
        advance_time(1)
    }

    action BadAction on actor: Character () {
        cost free
        resolve {
            do_advance()
        }
    }

    function run(c: Character) {
        c.BadAction()
    }
}
"#;
    let (program, result) = compile(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let entity = state.add_entity("Character", {
        let mut f = FxHashMap::default();
        f.insert(Name::from("hp"), Value::Int(10));
        f
    });
    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::ack_all();

    let err = adapter
        .run(&mut handler, |s, h| {
            interp.evaluate_function(s, h, "run", vec![Value::Entity(entity)])
        })
        .unwrap_err();
    assert!(
        err.message.contains("cannot be called during action"),
        "expected action-scope error, got: {}",
        err.message
    );
}

// ── adapter correctly applies AdvanceTime to GameState ──────────

#[test]
fn adapter_applies_advance_time_to_game_state() {
    let source = r#"
system "test" {
    function tick() {
        advance_time(42)
    }
}
"#;
    let (program, result) = compile(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::ack_all();

    adapter
        .run(&mut handler, |s, h| {
            interp.evaluate_function(s, h, "tick", vec![])
        })
        .unwrap();

    let final_state = adapter.into_inner();
    assert_eq!(final_state.game_time(), 42);
}

// ── applied_at stamped from game_time on conditions ──────────

#[test]
fn condition_applied_at_reflects_game_time() {
    let source = r#"
system "test" {
    entity Character { hp: int }

    enum Duration { indefinite }

    action Mark on actor: Character () {
        cost free
        resolve {
            apply_condition(actor, Prone, Duration.indefinite)
        }
    }

    condition Prone on bearer: Character {}

    function apply_at_time(c: Character) {
        advance_time(10)
        c.Mark()
    }
}
"#;
    let (program, result) = compile(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let entity = state.add_entity("Character", {
        let mut f = FxHashMap::default();
        f.insert(Name::from("hp"), Value::Int(10));
        f
    });
    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::ack_all();

    adapter
        .run(&mut handler, |s, h| {
            interp.evaluate_function(s, h, "apply_at_time", vec![Value::Entity(entity)])
        })
        .unwrap();

    let final_state = adapter.into_inner();
    let conds = final_state.read_conditions(&entity).unwrap();
    assert_eq!(conds.len(), 1);
    assert_eq!(conds[0].name, "Prone");
    assert_eq!(
        conds[0].applied_at, 10,
        "applied_at should reflect game_time at application"
    );
}

// ── applied_at is zero when no advance_time called ───────────

#[test]
fn condition_applied_at_zero_by_default() {
    let source = r#"
system "test" {
    entity Character { hp: int }

    enum Duration { indefinite }

    action Mark on actor: Character () {
        cost free
        resolve {
            apply_condition(actor, Prone, Duration.indefinite)
        }
    }

    condition Prone on bearer: Character {}

    function apply_no_time(c: Character) {
        c.Mark()
    }
}
"#;
    let (program, result) = compile(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let entity = state.add_entity("Character", {
        let mut f = FxHashMap::default();
        f.insert(Name::from("hp"), Value::Int(10));
        f
    });
    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::ack_all();

    adapter
        .run(&mut handler, |s, h| {
            interp.evaluate_function(s, h, "apply_no_time", vec![Value::Entity(entity)])
        })
        .unwrap();

    let final_state = adapter.into_inner();
    let conds = final_state.read_conditions(&entity).unwrap();
    assert_eq!(conds.len(), 1);
    assert_eq!(conds[0].applied_at, 0);
}
