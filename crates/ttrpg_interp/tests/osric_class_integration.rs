//! OSRIC class definitions integration test — AST structure checks only.
//!
//! Runtime value checks (class_def fields for all 10 classes, xp_for_level
//! table lookups, check_level_up logic, cross-class property checks) have
//! been moved to osric/tests/osric_class.ttrpg-cli.
//! These tests verify AST structure that CLI scripts cannot inspect.

use ttrpg_ast::ast::{DeclKind, TopLevel};

mod osric_common;
use osric_common::*;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_class() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn osric_class_parses_and_typechecks() {
    let (program, _) = compile_osric_class();
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
}

// ── Declaration structure ──────────────────────────────────────

#[test]
fn osric_class_has_class_def_derive() {
    let (program, _) = compile_osric_class();

    let mut found = false;
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSRIC Classes" {
                for decl in &sys.decls {
                    if let DeclKind::Derive(f) = &decl.node {
                        if f.name == "class_def" {
                            assert_eq!(f.params.len(), 1);
                            found = true;
                        }
                    }
                }
            }
        }
    }
    assert!(found, "expected class_def derive");
}

#[test]
fn osric_class_has_xp_table() {
    let (program, _) = compile_osric_class();

    let mut found = false;
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSRIC Classes" {
                for decl in &sys.decls {
                    if let DeclKind::Table(t) = &decl.node {
                        if t.name == "xp_for_level" {
                            assert_eq!(t.params.len(), 2);
                            // 10 classes × varying levels = 186 entries
                            assert_eq!(
                                t.entries.len(),
                                186,
                                "expected 186 xp_for_level entries, got {}",
                                t.entries.len()
                            );
                            found = true;
                        }
                    }
                }
            }
        }
    }
    assert!(found, "expected xp_for_level table");
}

#[test]
fn osric_class_has_check_level_up_derive() {
    let (program, _) = compile_osric_class();

    let mut found = false;
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSRIC Classes" {
                for decl in &sys.decls {
                    if let DeclKind::Derive(f) = &decl.node {
                        if f.name == "check_level_up" {
                            assert_eq!(f.params.len(), 3);
                            found = true;
                        }
                    }
                }
            }
        }
    }
    assert!(found, "expected check_level_up derive");
}
