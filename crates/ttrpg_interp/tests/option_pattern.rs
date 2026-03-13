//! Tests for `some(x)` / `none` pattern matching on `option<T>` values.
//!
//! Runtime coverage moved to tests/option_pattern.ttrpg-cli
//! Only Value::Void tests remain here (they test a Rust internal).

use ttrpg_ast::FileId;
use ttrpg_ast::diagnostic::Severity;
use ttrpg_interp::Interpreter;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::Value;

struct NoopHandler;
impl EffectHandler for NoopHandler {
    fn handle(&mut self, _: Effect) -> Response {
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

#[test]
fn unwrap_on_value_none_errors() {
    let source = r#"
system "test" {
    derive f(x: option<int>) -> int {
        x.unwrap()
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let err = interp
        .evaluate_derive(&state, &mut handler, "f", vec![Value::Void])
        .unwrap_err();
    assert!(
        format!("{err}").contains("unwrap()"),
        "expected unwrap error, got: {err}"
    );
}

#[test]
fn unwrap_or_on_value_none_returns_default() {
    let source = r#"
system "test" {
    derive f(x: option<int>) -> int {
        x.unwrap_or(99)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "f", vec![Value::Void])
        .unwrap();
    assert_eq!(val, Value::Int(99));
}
