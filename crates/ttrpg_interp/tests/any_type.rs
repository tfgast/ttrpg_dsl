// Runtime coverage moved to tests/any_type.ttrpg-cli
//!
//! Checker-error tests for the `any` type with `is` guard narrowing.

use ttrpg_ast::FileId;
use ttrpg_ast::diagnostic::Severity;

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

// ── error cases ──────────────────────────────────────────────────

#[test]
fn is_on_non_any_non_entity_is_error() {
    let errors = setup_expect_errors(
        r#"
system "test" {
    derive check() -> bool {
        let x: int = 42
        x is int
    }
}
"#,
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("`is` can only be used with")),
        "expected error about `is` on int, got: {errors:?}"
    );
}

#[test]
fn is_any_is_error() {
    let errors = setup_expect_errors(
        r#"
system "test" {
    derive check() -> bool {
        let x: any = to_any(42)
        x is any
    }
}
"#,
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("`is any` is not meaningful")),
        "expected error about `is any`, got: {errors:?}"
    );
}
