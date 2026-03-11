//! OSE thief skills integration test.
//!
//! Verifies that ose/ose_thief.ttrpg (combined with ose/ose_core.ttrpg)
//! parses, lowers, type-checks, and has expected declarations.
//!
//! Runtime derive/mechanic tests have been moved to ose/tests/ose_thief.ttrpg-cli.

use ttrpg_ast::FileId;
use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_ast::diagnostic::Severity;

// ── Setup ──────────────────────────────────────────────────────

/// Compile ose_core + ose_thief as a single combined source.
fn compile_ose_thief() -> ttrpg_ast::ast::Program {
    let core_source = include_str!("../../../ose/ose_core.ttrpg");
    let thief_source = include_str!("../../../ose/ose_thief.ttrpg");
    let source = format!("{core_source}\n{thief_source}");

    let (program, parse_errors) = ttrpg_parser::parse(&source, FileId::SYNTH);
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
    program
}

/// Collect all DeclKind items from all system blocks named "OSE".
fn get_ose_decls(program: &ttrpg_ast::ast::Program) -> Vec<&ttrpg_ast::Spanned<DeclKind>> {
    let mut decls = Vec::new();
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node
            && sys.name == "OSE"
        {
            decls.extend(sys.decls.iter());
        }
    }
    decls
}

// ── Parse & typecheck ──────────────────────────────────────────

#[test]
fn ose_thief_parses_and_typechecks() {
    let program = compile_ose_thief();
    // Should have at least two system "OSE" blocks (core + thief)
    let ose_count = program
        .items
        .iter()
        .filter(|item| matches!(&item.node, TopLevel::System(sys) if sys.name == "OSE"))
        .count();
    assert!(
        ose_count >= 2,
        "expected at least 2 system 'OSE' blocks, got {ose_count}"
    );
}

#[test]
fn ose_thief_has_expected_declarations() {
    let program = compile_ose_thief();
    let decls = get_ose_decls(&program);

    // Count thief-specific declarations (from ose_thief.ttrpg)
    let tables: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Table(t) => Some(&*t.name),
            _ => None,
        })
        .collect();
    assert!(
        tables.contains(&"skill_chance"),
        "missing table skill_chance"
    );

    let mechanics: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Mechanic(m) => Some(&*m.name),
            _ => None,
        })
        .collect();
    assert!(
        mechanics.contains(&"thief_skill_check"),
        "missing mechanic thief_skill_check"
    );
    assert!(
        mechanics.contains(&"hear_noise_check"),
        "missing mechanic hear_noise_check"
    );

    let derives: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Derive(d) => Some(&*d.name),
            _ => None,
        })
        .collect();
    assert!(
        derives.contains(&"backstab_multiplier"),
        "missing derive backstab_multiplier"
    );
    assert!(
        derives.contains(&"has_thief_skills"),
        "missing derive has_thief_skills"
    );
    assert!(
        derives.contains(&"can_backstab"),
        "missing derive can_backstab"
    );
}
