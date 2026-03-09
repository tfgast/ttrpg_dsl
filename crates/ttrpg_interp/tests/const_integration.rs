//! Integration tests for `const` declarations.
//!
//! Runtime const evaluation coverage has moved to `tests/const.ttrpg-cli`.
//! These Rust tests now keep only checker-only rejection cases.

use ttrpg_ast::diagnostic::Severity;
use ttrpg_ast::FileId;

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
        errors
            .iter()
            .any(|e| e.contains("declared as string") && e.contains("type int")),
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
