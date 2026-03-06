//! OSRIC spell integration test — AST structure checks only.
//!
//! Runtime value checks (spell slot progression, WIS bonus, max_spell_level,
//! has_wis_bonus derives, and MemoriseSpell/ForgetSpell/CastSpell actions)
//! have been moved to osric/tests/osric_spells.ttrpg-cli.
//! These tests verify AST structure that CLI scripts cannot inspect.

use ttrpg_ast::ast::{DeclKind, TopLevel};

mod osric_common;
use osric_common::*;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_spells() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn osric_spells_parses_and_typechecks() {
    let (program, _) = compile_osric_spells();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSRIC"));
    assert!(system_names.contains(&"OSRIC Classes"));
    assert!(system_names.contains(&"OSRIC Spells"));
}

// ── Table declaration structure ────────────────────────────────

#[test]
fn osric_spells_has_all_tables() {
    let (program, _) = compile_osric_spells();

    let mut table_names = Vec::new();
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSRIC Spells" {
                for decl in &sys.decls {
                    if let DeclKind::Table(t) = &decl.node {
                        table_names.push(t.name.to_string());
                    }
                }
            }
        }
    }

    let expected = [
        "cleric_slots",
        "druid_slots",
        "magic_user_slots",
        "illusionist_slots",
        "wis_bonus_slots",
    ];
    for name in &expected {
        assert!(
            table_names.iter().any(|n| n == name),
            "missing table: {name}, got: {table_names:?}"
        );
    }
    assert_eq!(
        table_names.len(),
        expected.len(),
        "expected {} tables, got: {table_names:?}",
        expected.len()
    );
}

#[test]
fn osric_spells_has_dispatch_derives() {
    let (program, _) = compile_osric_spells();

    let mut derive_names = Vec::new();
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSRIC Spells" {
                for decl in &sys.decls {
                    if let DeclKind::Derive(f) = &decl.node {
                        derive_names.push(f.name.to_string());
                    }
                }
            }
        }
    }

    let expected = [
        "spell_slots_for",
        "max_spell_level",
        "has_wis_bonus",
        "total_spell_slots",
    ];
    for name in &expected {
        assert!(
            derive_names.iter().any(|n| n == name),
            "missing derive: {name}, got: {derive_names:?}"
        );
    }
}

// MemoriseSpell/ForgetSpell/CastSpell action tests have been moved to
// osric/tests/osric_spells.ttrpg-cli.
