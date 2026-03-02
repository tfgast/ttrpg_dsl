//! Snapshot tests for interpreter output.
//!
//! These tests capture interpreter results (Value Debug output, error messages,
//! and effect logs) as snapshots. Run `cargo insta review` after changes to
//! update snapshots interactively.

use ttrpg_ast::diagnostic::Severity;
use ttrpg_ast::FileId;
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

// ═══════════════════════════════════════════════════════════════
// Derive return values
// ═══════════════════════════════════════════════════════════════

#[test]
fn derive_returns_int() {
    let source = r#"
system "test" {
    derive add(a: int, b: int) -> int { a + b }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "add",
            vec![Value::Int(3), Value::Int(4)],
        )
        .unwrap();
    insta::assert_debug_snapshot!(val);
}

#[test]
fn derive_returns_list() {
    let source = r#"
system "test" {
    derive make_list(n: int) -> list<int> {
        [i * 2 for i in 0..n]
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;
    let val = interp
        .evaluate_derive(&state, &mut handler, "make_list", vec![Value::Int(5)])
        .unwrap();
    insta::assert_debug_snapshot!(val);
}

#[test]
fn derive_returns_struct() {
    let source = r#"
system "test" {
    struct Point { x: int, y: int }
    derive origin() -> Point { Point { x: 0, y: 0 } }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;
    let val = interp
        .evaluate_derive(&state, &mut handler, "origin", vec![])
        .unwrap();
    insta::assert_debug_snapshot!(val);
}

#[test]
fn derive_returns_enum_variant() {
    let source = r#"
system "test" {
    enum Shape { circle, square }
    derive pick() -> Shape { Shape.circle }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;
    let val = interp
        .evaluate_derive(&state, &mut handler, "pick", vec![])
        .unwrap();
    insta::assert_debug_snapshot!(val);
}

#[test]
fn derive_returns_map() {
    let source = r#"
system "test" {
    derive scores() -> map<string, int> {
        let m: map<string, int> = {}
        m
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;
    let val = interp
        .evaluate_derive(&state, &mut handler, "scores", vec![])
        .unwrap();
    insta::assert_debug_snapshot!(val);
}

// ═══════════════════════════════════════════════════════════════
// Error cases
// ═══════════════════════════════════════════════════════════════

#[test]
fn runtime_error_undefined_derive() {
    let source = r#"
system "test" {
    derive dummy() -> int { 0 }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;
    let err = interp
        .evaluate_derive(&state, &mut handler, "nonexistent", vec![])
        .unwrap_err();
    insta::assert_snapshot!(err.to_string());
}

#[test]
fn runtime_error_wrong_arg_count() {
    let source = r#"
system "test" {
    derive add(a: int, b: int) -> int { a + b }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;
    let err = interp
        .evaluate_derive(&state, &mut handler, "add", vec![Value::Int(10)])
        .unwrap_err();
    insta::assert_snapshot!(err.to_string());
}

// ═══════════════════════════════════════════════════════════════
// Conditional logic
// ═══════════════════════════════════════════════════════════════

#[test]
fn derive_with_conditional() {
    let source = r#"
system "test" {
    derive classify(x: int) -> string {
        if x > 0 { "positive" }
        else if x < 0 { "negative" }
        else { "zero" }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let positive = interp
        .evaluate_derive(&state, &mut handler, "classify", vec![Value::Int(5)])
        .unwrap();
    let negative = interp
        .evaluate_derive(&state, &mut handler, "classify", vec![Value::Int(-3)])
        .unwrap();
    let zero = interp
        .evaluate_derive(&state, &mut handler, "classify", vec![Value::Int(0)])
        .unwrap();
    insta::assert_debug_snapshot!("positive", positive);
    insta::assert_debug_snapshot!("negative", negative);
    insta::assert_debug_snapshot!("zero", zero);
}
