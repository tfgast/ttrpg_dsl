//! Integration tests for the `default { ... }` body on prompts.
//!
//! Runtime prompt/default coverage has moved to `tests/prompt_default.ttrpg-cli`.
//! This Rust test keeps only the checker-only type validation.

use ttrpg_ast::diagnostic::Severity;
use ttrpg_ast::FileId;

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

// ── Tests ──────────────────────────────────────────────────────

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
