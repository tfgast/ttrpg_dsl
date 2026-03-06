//! OSE Combat & Morale integration tests.
//!
//! Verifies that ose/ose_combat.ttrpg parses, lowers, type-checks, and
//! has expected declarations.
//!
//! Runtime derive/mechanic/table tests have been moved to
//! ose/tests/ose_combat.ttrpg-cli.

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_ast::diagnostic::Severity;
use ttrpg_ast::FileId;

// ── Setup ──────────────────────────────────────────────────────

fn compile_ose_combat() -> ttrpg_ast::ast::Program {
    let source = include_str!("../../../ose/ose_combat.ttrpg");
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
    program
}

fn get_decls(program: &ttrpg_ast::ast::Program) -> &[ttrpg_ast::Spanned<DeclKind>] {
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            return &sys.decls;
        }
    }
    panic!("no system block found");
}

// ── Parsing & type checking ────────────────────────────────────

#[test]
fn ose_combat_parses_and_typechecks() {
    let program = compile_ose_combat();
    let has_system = program
        .items
        .iter()
        .any(|item| matches!(&item.node, TopLevel::System(sys) if sys.name == "OSE Combat"));
    assert!(has_system, "expected system named 'OSE Combat'");
}

#[test]
fn ose_combat_has_enums() {
    let program = compile_ose_combat();
    let decls = get_decls(&program);
    let enums: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Enum(e) => Some((&*e.name, e.variants.len())),
            _ => None,
        })
        .collect();
    assert!(enums.contains(&("AttackOutcome", 2)));
    assert!(enums.contains(&("MoraleOutcome", 2)));
    assert!(enums.contains(&("ReactionOutcome", 5)));
    assert!(enums.contains(&("CombatPhase", 8)));
    assert!(enums.contains(&("InitiativeWinner", 3)));
    assert!(enums.contains(&("PhaseActorSlot", 5)));
    assert_eq!(enums.len(), 9, "expected 9 enums");
}

#[test]
fn ose_combat_has_tables() {
    let program = compile_ose_combat();
    let decls = get_decls(&program);
    let tables: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Table(t) => Some(&*t.name),
            _ => None,
        })
        .collect();
    assert!(tables.contains(&"monster_thac0"));
    assert!(tables.contains(&"reaction_outcome"));
    assert_eq!(tables.len(), 2, "expected 2 tables");
}

#[test]
fn ose_combat_has_derives() {
    let program = compile_ose_combat();
    let decls = get_decls(&program);
    let derives: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Derive(d) => Some(&*d.name),
            _ => None,
        })
        .collect();
    assert!(derives.contains(&"target_number"));
    assert!(derives.contains(&"calc_ac"));
    assert!(derives.contains(&"missile_range_mod"));
    assert_eq!(derives.len(), 11, "expected 11 derives");
}

#[test]
fn ose_combat_has_mechanics() {
    let program = compile_ose_combat();
    let decls = get_decls(&program);
    let mechanics: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Mechanic(m) => Some(&*m.name),
            _ => None,
        })
        .collect();
    assert!(mechanics.contains(&"attack_roll"));
    assert!(mechanics.contains(&"morale_check"));
    assert!(mechanics.contains(&"reaction_roll"));
    assert_eq!(mechanics.len(), 13, "expected 13 mechanics");
}
