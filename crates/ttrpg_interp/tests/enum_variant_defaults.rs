//! Integration tests for enum variant field defaults (checker error cases).
//!
//! Runtime coverage moved to tests/enum_variant_defaults.ttrpg-cli

use ttrpg_ast::FileId;
use ttrpg_ast::diagnostic::Severity;

// ── Setup ──────────────────────────────────────────────────────

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

// ── Required field after default is an error ───────────────────

#[test]
fn required_field_after_default_is_error() {
    let src = r#"
        system "test" {
            enum Bad {
                Variant(a: int = 0, b: string)
            }
        }
    "#;
    let errors = compile_errors(src);
    assert!(
        errors
            .iter()
            .any(|e| e.contains("default") && e.contains("must come last")),
        "expected error about defaults coming last, got: {errors:?}"
    );
}

// ── Missing required field (no default) is still an error ──────

#[test]
fn missing_required_field_is_still_error() {
    let src = r#"
        system "test" {
            enum Weapon {
                Sword(name: string, magic_bonus: int = 0)
            }
            derive bad() -> Weapon {
                Sword()
            }
        }
    "#;
    let errors = compile_errors(src);
    assert!(
        errors.iter().any(|e| e.contains("missing required field")),
        "expected missing required field error, got: {errors:?}"
    );
}
