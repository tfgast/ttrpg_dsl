//! Integration tests for `const` declarations.
//!
//! Tests the full pipeline: parse → lower → check → interpret, verifying
//! that consts are properly parsed, type-checked, and evaluated at runtime.

use ttrpg_ast::diagnostic::Severity;
use ttrpg_ast::FileId;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
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

fn compile_errors(source: &str) -> Vec<String> {
    let (program, parse_errors) = ttrpg_parser::parse(source, FileId::SYNTH);
    if !parse_errors.is_empty() {
        return parse_errors.iter().map(|d| d.message.clone()).collect();
    }
    let mut lower_diags = Vec::new();
    let program = ttrpg_parser::lower_moves(program, &mut lower_diags);
    if !lower_diags.is_empty() {
        return lower_diags.iter().map(|d| d.message.clone()).collect();
    }
    let result = ttrpg_checker::check(&program);
    result
        .diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .map(|d| d.message.clone())
        .collect()
}

struct NullHandler;
impl EffectHandler for NullHandler {
    fn handle(&mut self, _effect: Effect) -> Response {
        Response::Acknowledged
    }
}

// ── Basic const with int literal ────────────────────────────────

#[test]
fn const_int_literal() {
    let source = r#"
system "test" {
    const MAX_LEVEL = 20

    derive get_max() -> int { MAX_LEVEL }
}
"#;
    let (program, result) = compile(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;
    let val = interp
        .evaluate_derive(&state, &mut handler, "get_max", vec![])
        .unwrap();
    assert_eq!(val, Value::Int(20));
}

// ── Const with string literal ────────────────────────────────────

#[test]
fn const_string_literal() {
    let source = r#"
system "test" {
    const GREETING = "hello"

    derive greet() -> string { GREETING }
}
"#;
    let (program, result) = compile(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;
    let val = interp
        .evaluate_derive(&state, &mut handler, "greet", vec![])
        .unwrap();
    assert_eq!(val, Value::Str("hello".into()));
}

// ── Const referencing another const ──────────────────────────────

#[test]
fn const_references_other_const() {
    let source = r#"
system "test" {
    const BASE = 10
    const DERIVED = BASE + 5

    derive get_derived() -> int { DERIVED }
}
"#;
    let (program, result) = compile(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;
    let val = interp
        .evaluate_derive(&state, &mut handler, "get_derived", vec![])
        .unwrap();
    assert_eq!(val, Value::Int(15));
}

// ── Const with struct literal ────────────────────────────────────

#[test]
fn const_struct_literal() {
    let source = r#"
system "test" {
    struct SpellDef {
        name: string
        level: int
    }

    const CURE = SpellDef { name: "Cure Light Wounds", level: 1 }

    derive spell_name() -> string { CURE.name }
    derive spell_level() -> int { CURE.level }
}
"#;
    let (program, result) = compile(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let name = interp
        .evaluate_derive(&state, &mut handler, "spell_name", vec![])
        .unwrap();
    assert_eq!(name, Value::Str("Cure Light Wounds".into()));

    let level = interp
        .evaluate_derive(&state, &mut handler, "spell_level", vec![])
        .unwrap();
    assert_eq!(level, Value::Int(1));
}

// ── Const with enum variant ──────────────────────────────────────

#[test]
fn const_enum_variant() {
    let source = r#"
system "test" {
    enum School { Evocation, Necromancy, Abjuration }

    const DEFAULT_SCHOOL = Necromancy

    derive get_school() -> School { DEFAULT_SCHOOL }
}
"#;
    let (program, result) = compile(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;
    let val = interp
        .evaluate_derive(&state, &mut handler, "get_school", vec![])
        .unwrap();
    match val {
        Value::EnumVariant { variant, .. } => assert_eq!(variant.as_str(), "Necromancy"),
        other => panic!("expected enum variant, got {other:?}"),
    }
}

// ── Const with type annotation ───────────────────────────────────

#[test]
fn const_with_type_annotation() {
    let source = r#"
system "test" {
    const X: int = 42

    derive get_x() -> int { X }
}
"#;
    let (program, result) = compile(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;
    let val = interp
        .evaluate_derive(&state, &mut handler, "get_x", vec![])
        .unwrap();
    assert_eq!(val, Value::Int(42));
}

// ── Const with list literal ──────────────────────────────────────

#[test]
fn const_list_literal() {
    let source = r#"
system "test" {
    const LEVELS: list<int> = [1, 2, 3]

    derive count() -> int { len(LEVELS) }
}
"#;
    let (program, result) = compile(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;
    let val = interp
        .evaluate_derive(&state, &mut handler, "count", vec![])
        .unwrap();
    assert_eq!(val, Value::Int(3));
}

// ── Error: type mismatch ─────────────────────────────────────────

#[test]
fn const_type_mismatch_error() {
    let source = r#"
system "test" {
    const X: string = 42
}
"#;
    let errors = compile_errors(source);
    assert!(
        errors.iter().any(|e| e.contains("declared as string") && e.contains("type int")),
        "expected type mismatch error, got: {errors:?}"
    );
}

// ── Error: assignment to const ───────────────────────────────────

#[test]
fn const_assign_error() {
    let source = r#"
system "test" {
    const X = 10

    derive test() -> int {
        X = 20
        X
    }
}
"#;
    let errors = compile_errors(source);
    assert!(
        errors.iter().any(|e| e.contains("cannot assign to const")),
        "expected assignment-to-const error, got: {errors:?}"
    );
}

// ── Error: duplicate const ───────────────────────────────────────

#[test]
fn const_duplicate_error() {
    let source = r#"
system "test" {
    const X = 10
    const X = 20
}
"#;
    let errors = compile_errors(source);
    assert!(
        errors.iter().any(|e| e.contains("duplicate const")),
        "expected duplicate const error, got: {errors:?}"
    );
}

// ── Const used in expression ─────────────────────────────────────

#[test]
fn const_in_arithmetic_expression() {
    let source = r#"
system "test" {
    const BASE = 10
    const BONUS = 3

    derive total() -> int { BASE * 2 + BONUS }
}
"#;
    let (program, result) = compile(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;
    let val = interp
        .evaluate_derive(&state, &mut handler, "total", vec![])
        .unwrap();
    assert_eq!(val, Value::Int(23));
}

// ── Local let shadows const ──────────────────────────────────────

#[test]
fn local_let_shadows_const() {
    let source = r#"
system "test" {
    const X = 10

    derive test() -> int {
        let X = 99
        X
    }
}
"#;
    let (program, result) = compile(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;
    let val = interp
        .evaluate_derive(&state, &mut handler, "test", vec![])
        .unwrap();
    assert_eq!(val, Value::Int(99));
}
