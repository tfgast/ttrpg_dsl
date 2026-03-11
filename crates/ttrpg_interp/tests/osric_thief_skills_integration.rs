//! OSRIC thief skill integration test — AST structure checks only.
//!
//! Runtime value checks (table lookups, derive evaluation, mechanic rolls)
//! have been moved to osric/tests/osric_thief_skills.ttrpg-cli.
//! These tests verify AST structure that CLI scripts cannot inspect.

use ttrpg_ast::ast::{DeclKind, TopLevel};

mod osric_common;
use osric_common::*;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_thief_skills() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn osric_thief_skills_parses_and_typechecks() {
    let (program, _) = compile_osric_thief_skills();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSRIC Thief Skills"));
}

// ── Structure: expected tables, derives, mechanics ─────────────

#[test]
fn has_expected_tables() {
    let (program, _) = compile_osric_thief_skills();

    let mut table_names = Vec::new();
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node
            && sys.name == "OSRIC Thief Skills"
        {
            for decl in &sys.decls {
                if let DeclKind::Table(t) = &decl.node {
                    table_names.push(t.name.to_string());
                }
            }
        }
    }

    for expected in [
        "thief_skill_base",
        "assassin_skill_base",
        "dex_thief_adj",
        "ancestry_thief_adj",
    ] {
        assert!(
            table_names.iter().any(|n| n == expected),
            "missing table: {expected}, got: {table_names:?}"
        );
    }
}

#[test]
fn has_expected_derives() {
    let (program, _) = compile_osric_thief_skills();

    let mut derive_names = Vec::new();
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node
            && sys.name == "OSRIC Thief Skills"
        {
            for decl in &sys.decls {
                if let DeclKind::Derive(d) = &decl.node {
                    derive_names.push(d.name.to_string());
                }
            }
        }
    }

    for expected in [
        "skill_base_for_class",
        "effective_thief_skill",
        "character_thief_skill",
    ] {
        assert!(
            derive_names.iter().any(|n| n == expected),
            "missing derive: {expected}, got: {derive_names:?}"
        );
    }
}

#[test]
fn has_thief_skill_check_mechanic() {
    let (program, _) = compile_osric_thief_skills();

    let mut found = false;
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node
            && sys.name == "OSRIC Thief Skills"
        {
            for decl in &sys.decls {
                if let DeclKind::Mechanic(m) = &decl.node
                    && m.name == "thief_skill_check"
                {
                    found = true;
                }
            }
        }
    }
    assert!(found, "expected thief_skill_check mechanic");
}
