//! OSRIC Turn Undead integration test — AST structure checks only.
//!
//! Runtime value checks (table lookups, alignment helpers, effective turning
//! level, resolve_turn_undead mechanic) have been moved to
//! osric/tests/osric_turn_undead.ttrpg-cli.
//! These tests verify AST structure that CLI scripts cannot inspect.

use ttrpg_ast::ast::{DeclKind, TopLevel};

mod osric_common;
use osric_common::*;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_turn_undead() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

fn get_turn_undead_decls(program: &ttrpg_ast::ast::Program) -> &[ttrpg_ast::Spanned<DeclKind>] {
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSRIC Turn Undead" {
                return &sys.decls;
            }
        }
    }
    panic!("no system block named 'OSRIC Turn Undead' found");
}

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn osric_turn_undead_parses_and_typechecks() {
    let (program, _) = compile_osric_turn_undead();
    let has_system = program
        .items
        .iter()
        .any(|item| matches!(&item.node, TopLevel::System(sys) if sys.name == "OSRIC Turn Undead"));
    assert!(has_system, "expected system named 'OSRIC Turn Undead'");
}

// ── Structure verification ─────────────────────────────────────

#[test]
fn has_expected_enums() {
    let (program, _) = compile_osric_turn_undead();
    let decls = get_turn_undead_decls(&program);
    let enums: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Enum(e) => Some(e.name.to_string()),
            _ => None,
        })
        .collect();
    assert!(enums.contains(&"TurnOutcome".to_string()));
}

#[test]
fn has_expected_tables() {
    let (program, _) = compile_osric_turn_undead();
    let decls = get_turn_undead_decls(&program);
    let tables: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Table(t) => Some(t.name.to_string()),
            _ => None,
        })
        .collect();
    assert!(
        tables.contains(&"turn_undead_table".to_string()),
        "missing turn_undead_table, got: {tables:?}"
    );
}

#[test]
fn has_expected_derives() {
    let (program, _) = compile_osric_turn_undead();
    let decls = get_turn_undead_decls(&program);
    let derives: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Derive(d) => Some(d.name.to_string()),
            _ => None,
        })
        .collect();
    for expected in [
        "is_evil_alignment",
        "effective_turning_level",
        "character_can_turn",
    ] {
        assert!(
            derives.contains(&expected.to_string()),
            "missing derive: {expected}, got: {derives:?}"
        );
    }
}

#[test]
fn has_expected_mechanics() {
    let (program, _) = compile_osric_turn_undead();
    let decls = get_turn_undead_decls(&program);
    let mechanics: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Mechanic(m) => Some(m.name.to_string()),
            _ => None,
        })
        .collect();
    for expected in [
        "resolve_turn_undead",
        "roll_number_turned",
        "roll_number_destroyed",
        "roll_number_destroyed_star",
        "evil_control_check",
    ] {
        assert!(
            mechanics.contains(&expected.to_string()),
            "missing mechanic: {expected}, got: {mechanics:?}"
        );
    }
}

#[test]
fn has_turn_undead_action() {
    let (program, _) = compile_osric_turn_undead();
    let decls = get_turn_undead_decls(&program);
    let actions: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Action(a) => Some(a.name.to_string()),
            _ => None,
        })
        .collect();
    assert!(
        actions.contains(&"TurnUndeadAction".to_string()),
        "missing TurnUndeadAction, got: {actions:?}"
    );
}
