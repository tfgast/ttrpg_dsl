//! Integration tests for the `return` statement.
//!
//! Runtime early-exit coverage has moved to `tests/return.ttrpg-cli`.
//! These Rust tests now keep only checker-only rejection cases.

use ttrpg_ast::diagnostic::Severity;
use ttrpg_ast::FileId;

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
        errors.iter().any(|e| e.contains("bare `return`")),
        "expected bare return error, got: {errors:?}"
    );
}
