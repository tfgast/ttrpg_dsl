//! OSE wilderness travel integration tests.
//!
//! Verifies that ose/ose_wilderness.ttrpg parses, lowers, and type-checks.
//!
//! Runtime derive/mechanic tests have been moved to
//! ose/tests/ose_wilderness.ttrpg-cli.

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_ast::diagnostic::Severity;

fn compile_ose_wilderness() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    let source = include_str!("../../../ose/ose_wilderness.ttrpg");
    let (program, parse_errors) = ttrpg_parser::parse(source, ttrpg_ast::FileId::SYNTH);
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

#[test]
fn ose_wilderness_parses_and_typechecks() {
    let (program, _) = compile_ose_wilderness();
    let has_system = program
        .items
        .iter()
        .any(|item| matches!(&item.node, TopLevel::System(sys) if sys.name == "OSE Wilderness"));
    assert!(has_system, "expected system named OSE Wilderness");
}

#[test]
fn ose_wilderness_has_expected_decls() {
    let (program, _) = compile_ose_wilderness();
    let mut has_terrain_enum = false;
    let mut table_count = 0;
    let mut has_lost_check = false;
    let mut has_starvation_penalty = false;

    for item in &program.items {
        if let TopLevel::System(sys) = &item.node
            && sys.name == "OSE Wilderness"
        {
            for decl in &sys.decls {
                match &decl.node {
                    DeclKind::Enum(e) if e.name == "WildernessTerrainKind" => {
                        has_terrain_enum = true;
                        assert_eq!(e.variants.len(), 11);
                    }
                    DeclKind::Table(_) => table_count += 1,
                    DeclKind::Mechanic(m) if m.name == "terrain_lost_check" => {
                        has_lost_check = true;
                    }
                    DeclKind::Derive(d) if d.name == "starvation_penalty" => {
                        has_starvation_penalty = true;
                    }
                    _ => {}
                }
            }
        }
    }

    assert!(has_terrain_enum, "missing WildernessTerrainKind enum");
    assert!(table_count >= 4, "expected terrain property tables");
    assert!(has_lost_check, "missing terrain_lost_check mechanic");
    assert!(has_starvation_penalty, "missing starvation_penalty derive");
}
