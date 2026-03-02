//! Snapshot tests for checker diagnostic rendering.
//!
//! These tests capture the full rendered diagnostic output for representative
//! error and warning cases. Run `cargo insta review` after changes to update
//! snapshots interactively.

use ttrpg_ast::diagnostic::{Severity, SourceMap};
use ttrpg_ast::FileId;

fn render_errors(source: &str) -> String {
    let (program, parse_errors) = ttrpg_parser::parse(source, FileId::SYNTH);
    assert!(parse_errors.is_empty(), "unexpected parse errors");
    let mut lower_diags = Vec::new();
    let program = ttrpg_parser::lower_moves(program, &mut lower_diags);
    assert!(lower_diags.is_empty(), "unexpected lowering errors");
    let result = ttrpg_checker::check(&program);
    let sm = SourceMap::new(source);
    result
        .diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .map(|d| sm.render(d))
        .collect::<Vec<_>>()
        .join("\n\n")
}

fn render_all_diagnostics(source: &str) -> String {
    let (program, parse_errors) = ttrpg_parser::parse(source, FileId::SYNTH);
    assert!(parse_errors.is_empty(), "unexpected parse errors");
    let mut lower_diags = Vec::new();
    let program = ttrpg_parser::lower_moves(program, &mut lower_diags);
    assert!(lower_diags.is_empty(), "unexpected lowering errors");
    let result = ttrpg_checker::check(&program);
    let sm = SourceMap::new(source);
    result
        .diagnostics
        .iter()
        .map(|d| sm.render(d))
        .collect::<Vec<_>>()
        .join("\n\n")
}

// ═══════════════════════════════════════════════════════════════
// Type errors
// ═══════════════════════════════════════════════════════════════

#[test]
fn type_mismatch_return() {
    let source = r#"
system "test" {
    derive foo(x: int) -> bool { x }
}
"#;
    insta::assert_snapshot!(render_errors(source));
}

#[test]
fn undefined_variable() {
    let source = r#"
system "test" {
    derive foo(x: int) -> int { y }
}
"#;
    insta::assert_snapshot!(render_errors(source));
}

#[test]
fn duplicate_type_declaration() {
    let source = r#"
system "test" {
    enum Foo { A, B }
    enum Foo { C, D }
}
"#;
    insta::assert_snapshot!(render_errors(source));
}

#[test]
fn duplicate_function_declaration() {
    let source = r#"
system "test" {
    derive foo(x: int) -> int { x }
    derive foo(y: int) -> int { y }
}
"#;
    insta::assert_snapshot!(render_errors(source));
}

#[test]
fn dice_in_comparison() {
    let source = r#"
system "test" {
    derive foo() -> bool {
        let x: DiceExpr = 1d20
        x >= 15
    }
}
"#;
    insta::assert_snapshot!(render_errors(source));
}

#[test]
fn wrong_argument_type() {
    let source = r#"
system "test" {
    derive double(x: int) -> int { x * 2 }
    derive caller() -> int { double("hello") }
}
"#;
    insta::assert_snapshot!(render_errors(source));
}

#[test]
fn binary_op_type_mismatch() {
    let source = r#"
system "test" {
    derive bad(x: int, y: string) -> int { x + y }
}
"#;
    insta::assert_snapshot!(render_errors(source));
}

// ═══════════════════════════════════════════════════════════════
// Multiple errors in one source
// ═══════════════════════════════════════════════════════════════

#[test]
fn multiple_errors() {
    let source = r#"
system "test" {
    derive a(x: int) -> bool { x }
    derive b() -> int { unknown_var }
    derive c(x: int) -> int { x + "bad" }
}
"#;
    insta::assert_snapshot!(render_errors(source));
}

// ═══════════════════════════════════════════════════════════════
// All diagnostics (errors + warnings together)
// ═══════════════════════════════════════════════════════════════

#[test]
fn mixed_errors_and_warnings() {
    let source = r#"
system "test" {
    derive foo(x: int) -> bool { x }
}
"#;
    // This may produce both warnings and errors depending on the checker's behavior.
    // If it only produces errors, the snapshot will still be useful.
    insta::assert_snapshot!(render_all_diagnostics(source));
}
