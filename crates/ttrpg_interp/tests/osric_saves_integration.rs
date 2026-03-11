//! OSRIC saving throw integration test — AST structure checks only.
//!
//! Runtime value checks (per-class saving throws, ResistSpell action) have
//! been moved to osric/tests/osric_saves.ttrpg-cli.
//! These tests verify AST structure that CLI scripts cannot inspect.

use ttrpg_ast::ast::{DeclKind, TopLevel};

mod osric_common;
use osric_common::*;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_saves() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn osric_saves_parses_and_typechecks() {
    let (program, _) = compile_osric_saves();
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
    assert!(system_names.contains(&"OSRIC Saves"));
}

// ── Table declaration structure ────────────────────────────────

#[test]
fn osric_saves_has_all_tables() {
    let (program, _) = compile_osric_saves();

    let mut table_names = Vec::new();
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node
            && sys.name == "OSRIC Saves"
        {
            for decl in &sys.decls {
                if let DeclKind::Table(t) = &decl.node {
                    table_names.push(t.name.as_str());
                }
            }
        }
    }

    let expected = [
        "fighter_saves",
        "paladin_saves",
        "cleric_saves",
        "druid_saves",
        "thief_saves",
        "magic_user_saves",
        "illusionist_saves",
        "monk_saves",
        "monster_saves_normal",
        "monster_saves_nonintelligent",
    ];
    for name in &expected {
        assert!(
            table_names.contains(name),
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
fn osric_saves_has_dispatch_derive() {
    let (program, _) = compile_osric_saves();

    let mut found = false;
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node
            && sys.name == "OSRIC Saves"
        {
            for decl in &sys.decls {
                if let DeclKind::Derive(f) = &decl.node
                    && f.name == "saving_throws_for"
                {
                    assert_eq!(f.params.len(), 2, "saving_throws_for should take 2 params");
                    found = true;
                }
            }
        }
    }
    assert!(found, "expected saving_throws_for derive");
}

// ── Table entry counts ─────────────────────────────────────────

#[test]
fn osric_saves_table_entry_counts() {
    let (program, _) = compile_osric_saves();

    let expected_counts = [
        ("fighter_saves", 11), // 0, 1-2, 3-4, 5-6, 7-8, 9-10, 11-12, 13-14, 15-16, 17-18, _
        ("paladin_saves", 10), // 1-2, 3-4, 5-6, 7-8, 9-10, 11-12, 13-14, 15-16, 17-18, _
        ("cleric_saves", 7),   // 1-3, 4-6, 7-9, 10-12, 13-15, 16-18, _
        ("druid_saves", 5),    // 1-3, 4-6, 7-9, 10-12, _
        ("thief_saves", 5),    // 1-4, 5-8, 9-12, 13-16, _
        ("magic_user_saves", 4), // 1-5, 6-10, 11-15, _
        ("illusionist_saves", 4), // 1-5, 6-10, 11-15, _
        ("monk_saves", 5),     // 1-4, 5-8, 9-12, 13-16, _
    ];

    for item in &program.items {
        if let TopLevel::System(sys) = &item.node
            && sys.name == "OSRIC Saves"
        {
            for decl in &sys.decls {
                if let DeclKind::Table(t) = &decl.node
                    && let Some(&(_, expected)) = expected_counts
                        .iter()
                        .find(|(name, _)| *name == t.name.as_str())
                {
                    assert_eq!(
                        t.entries.len(),
                        expected,
                        "{} should have {} entries, got {}",
                        t.name,
                        expected,
                        t.entries.len()
                    );
                }
            }
        }
    }
}

// ResistSpell action tests have been moved to osric/tests/osric_saves.ttrpg-cli.
