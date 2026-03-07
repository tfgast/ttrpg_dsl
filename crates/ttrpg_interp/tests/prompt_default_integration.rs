//! Integration tests for the `default { ... }` body on prompts.

use std::collections::VecDeque;

use ttrpg_ast::diagnostic::Severity;
use ttrpg_ast::FileId;
use ttrpg_interp::adapter::StateAdapter;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

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

fn compile_expect_errors(source: &str) -> Vec<String> {
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

struct ScriptedHandler {
    script: VecDeque<Response>,
}

impl ScriptedHandler {
    fn with_responses(responses: Vec<Response>) -> Self {
        ScriptedHandler {
            script: responses.into(),
        }
    }
}

impl EffectHandler for ScriptedHandler {
    fn handle(&mut self, _effect: Effect) -> Response {
        self.script.pop_front().unwrap_or(Response::Acknowledged)
    }
}

// ── Tests ──────────────────────────────────────────────────────

#[test]
fn prompt_default_body_evaluated_on_use_default() {
    let (program, result) = compile(
        r#"
system "test" {
    prompt pick_number(base: int) -> int {
        hint: "Pick a number"
        default {
            base + 10
        }
    }

    derive test_it(x: int) -> int {
        pick_number(x)
    }
}
"#,
    );

    let interp = Interpreter::new(&program, &result.env).unwrap();
    let gs = GameState::new();
    let adapter = StateAdapter::new(gs);
    let mut handler = ScriptedHandler::with_responses(vec![Response::UseDefault]);

    let val = adapter
        .run(&mut handler, |state, h| {
            interp.evaluate_derive(state, h, "test_it", vec![Value::Int(5)])
        })
        .unwrap();
    assert_eq!(val, Value::Int(15));
}

#[test]
fn prompt_default_not_evaluated_when_host_answers() {
    let (program, result) = compile(
        r#"
system "test" {
    prompt pick_number(base: int) -> int {
        hint: "Pick"
        default {
            base + 10
        }
    }

    derive test_it(x: int) -> int {
        pick_number(x)
    }
}
"#,
    );

    let interp = Interpreter::new(&program, &result.env).unwrap();
    let gs = GameState::new();
    let adapter = StateAdapter::new(gs);
    let mut handler =
        ScriptedHandler::with_responses(vec![Response::PromptResult(Value::Int(99))]);

    let val = adapter
        .run(&mut handler, |state, h| {
            interp.evaluate_derive(state, h, "test_it", vec![Value::Int(5)])
        })
        .unwrap();
    assert_eq!(val, Value::Int(99));
}

#[test]
fn prompt_use_default_without_default_body_errors() {
    let (program, result) = compile(
        r#"
system "test" {
    prompt pick_number(base: int) -> int {
        hint: "Pick"
    }

    derive test_it(x: int) -> int {
        pick_number(x)
    }
}
"#,
    );

    let interp = Interpreter::new(&program, &result.env).unwrap();
    let gs = GameState::new();
    let adapter = StateAdapter::new(gs);
    let mut handler = ScriptedHandler::with_responses(vec![Response::UseDefault]);

    let err = adapter
        .run(&mut handler, |state, h| {
            interp.evaluate_derive(state, h, "test_it", vec![Value::Int(5)])
        })
        .unwrap_err();
    assert!(
        err.message.contains("no default body"),
        "Expected 'no default body' error, got: {}",
        err.message
    );
}

#[test]
fn prompt_default_type_mismatch_caught_by_checker() {
    let errors = compile_expect_errors(
        r#"
system "test" {
    prompt pick_number(base: int) -> int {
        hint: "Pick"
        default {
            "wrong type"
        }
    }
}
"#,
    );
    assert!(
        errors.iter().any(|e| e.contains("default body has type")),
        "Expected type mismatch error, got: {errors:?}"
    );
}

#[test]
fn prompt_default_with_suggest_and_use_default() {
    // When host returns UseDefault, default body is used even if suggest exists
    let (program, result) = compile(
        r#"
system "test" {
    prompt pick_number(base: int) -> int {
        hint: "Pick"
        suggest: base + 1
        default {
            base + 100
        }
    }

    derive test_it(x: int) -> int {
        pick_number(x)
    }
}
"#,
    );

    let interp = Interpreter::new(&program, &result.env).unwrap();
    let gs = GameState::new();
    let adapter = StateAdapter::new(gs);
    let mut handler = ScriptedHandler::with_responses(vec![Response::UseDefault]);

    let val = adapter
        .run(&mut handler, |state, h| {
            interp.evaluate_derive(state, h, "test_it", vec![Value::Int(5)])
        })
        .unwrap();
    assert_eq!(val, Value::Int(105));
}
