//! Integration tests for `table` declarations: checker error cases.
//!
//! Runtime coverage moved to tests/table_lookup.ttrpg-cli
//!
//! Tests below verify that the type checker correctly rejects malformed
//! tables (key/value type mismatches, ranges on non-int params, wildcard
//! ordering warnings).

use ttrpg_ast::FileId;
use ttrpg_ast::diagnostic::Severity;

// ── Type checker rejects mismatched key types ─────────────────

#[test]
fn table_type_error_key_mismatch() {
    let source = r#"
    system "test" {
        enum Ability { STR, DEX }
        table bad_table(x: Ability) -> int {
            1 => 10
        }
    }
    "#;

    let (program, parse_errors) = ttrpg_parser::parse(source, FileId::SYNTH);
    assert!(parse_errors.is_empty());
    let mut lower_diags = Vec::new();
    let program = ttrpg_parser::lower_moves(program, &mut lower_diags);
    let result = ttrpg_checker::check(&program);
    let errors: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .collect();
    assert!(
        !errors.is_empty(),
        "expected type error for int key on Ability param"
    );
    assert!(
        errors
            .iter()
            .any(|d| d.message.contains("table key has type")),
        "expected 'table key has type' error, got: {:?}",
        errors.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

// ── Type checker rejects mismatched value types ───────────────

#[test]
fn table_type_error_value_mismatch() {
    let source = r#"
    system "test" {
        table bad_table(x: int) -> int {
            1 => "hello"
        }
    }
    "#;

    let (program, parse_errors) = ttrpg_parser::parse(source, FileId::SYNTH);
    assert!(parse_errors.is_empty());
    let mut lower_diags = Vec::new();
    let program = ttrpg_parser::lower_moves(program, &mut lower_diags);
    let result = ttrpg_checker::check(&program);
    let errors: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .collect();
    assert!(
        !errors.is_empty(),
        "expected type error for string value on int return"
    );
    assert!(
        errors
            .iter()
            .any(|d| d.message.contains("table entry value has type")),
        "expected 'table entry value has type' error, got: {:?}",
        errors.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

// ── Wildcard-not-last produces warning ────────────────────────

#[test]
fn table_wildcard_not_last_warns() {
    let source = r#"
    system "test" {
        table bad(x: int) -> int {
            _ => 0,
            1 => 10
        }
    }
    "#;

    let (program, parse_errors) = ttrpg_parser::parse(source, FileId::SYNTH);
    assert!(parse_errors.is_empty());
    let mut lower_diags = Vec::new();
    let program = ttrpg_parser::lower_moves(program, &mut lower_diags);
    let result = ttrpg_checker::check(&program);
    let warnings: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Warning)
        .collect();
    assert!(
        warnings
            .iter()
            .any(|d| d.message.contains("unreachable table entry")),
        "expected 'unreachable table entry' warning, got: {:?}",
        warnings.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

#[test]
fn table_wildcard_last_no_warning() {
    let source = r#"
    system "test" {
        table ok(x: int) -> int {
            1 => 10,
            _ => 0
        }
    }
    "#;

    let (program, parse_errors) = ttrpg_parser::parse(source, FileId::SYNTH);
    assert!(parse_errors.is_empty());
    let mut lower_diags = Vec::new();
    let program = ttrpg_parser::lower_moves(program, &mut lower_diags);
    let result = ttrpg_checker::check(&program);
    let warnings: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Warning)
        .collect();
    assert!(
        warnings.is_empty(),
        "expected no warnings for wildcard-last table, got: {:?}",
        warnings.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

// ── Type checker rejects range on non-int param ───────────────

#[test]
fn table_type_error_range_on_non_int() {
    let source = r#"
    system "test" {
        enum Ability { STR, DEX }
        table bad_table(x: Ability) -> int {
            STR..=DEX => 10
        }
    }
    "#;

    let (program, parse_errors) = ttrpg_parser::parse(source, FileId::SYNTH);
    assert!(parse_errors.is_empty());
    let mut lower_diags = Vec::new();
    let program = ttrpg_parser::lower_moves(program, &mut lower_diags);
    let result = ttrpg_checker::check(&program);
    let errors: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .collect();
    assert!(
        !errors.is_empty(),
        "expected type error for range on Ability param"
    );
    assert!(
        errors
            .iter()
            .any(|d| d.message.contains("range keys are only valid for int")),
        "expected 'range keys are only valid for int' error, got: {:?}",
        errors.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}
