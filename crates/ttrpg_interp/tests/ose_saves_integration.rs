//! OSE saving throws integration test.
//!
//! Verifies that ose/ose_saves.ttrpg parses, lowers, and type-checks
//! through the full multi-file pipeline.
//!
//! Runtime table value tests have been moved to ose/tests/ose_saves.ttrpg-cli.

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_ast::diagnostic::Severity;

// ── Compile helpers ────────────────────────────────────────────

/// Compile both OSE files through the multi-file pipeline.
fn compile_ose_saves() -> ttrpg_ast::ast::Program {
    let core_source = include_str!("../../../ose/ose_core.ttrpg");
    let saves_source = include_str!("../../../ose/ose_saves.ttrpg");

    let sources = vec![
        ("ose/ose_core.ttrpg".to_string(), core_source.to_string()),
        ("ose/ose_saves.ttrpg".to_string(), saves_source.to_string()),
    ];

    let parse_result = ttrpg_parser::parse_multi(&sources);
    let parse_errors: Vec<_> = parse_result
        .diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .collect();
    assert!(
        parse_errors.is_empty(),
        "parse/lower errors: {:?}",
        parse_errors.iter().map(|d| &d.message).collect::<Vec<_>>()
    );

    let (program, module_map) = parse_result.ok().unwrap();
    let result = ttrpg_checker::check_with_modules(program, module_map);
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

    program.clone()
}

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn ose_saves_parses_and_typechecks() {
    let program = compile_ose_saves();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSE"));
    assert!(system_names.contains(&"OSE Saves"));
}

// ── Table declaration structure ────────────────────────────────

#[test]
fn ose_saves_has_table_and_mechanic() {
    let program = compile_ose_saves();

    let mut has_table = false;
    let mut has_mechanic = false;

    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSE Saves" {
                for decl in &sys.decls {
                    match &decl.node {
                        DeclKind::Table(t) if t.name == "saving_throws" => {
                            has_table = true;
                            assert_eq!(t.params.len(), 2);
                        }
                        DeclKind::Mechanic(f) if f.name == "saving_throw_check" => {
                            has_mechanic = true;
                            assert_eq!(f.params.len(), 2);
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    assert!(has_table, "expected saving_throws table");
    assert!(has_mechanic, "expected saving_throw_check mechanic");
}

// ── Table entry count ──────────────────────────────────────────

#[test]
fn ose_saves_table_has_all_entries() {
    let program = compile_ose_saves();

    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSE Saves" {
                for decl in &sys.decls {
                    if let DeclKind::Table(t) = &decl.node {
                        if t.name == "saving_throws" {
                            // 13 categories × varying tiers = 49 entries
                            assert_eq!(t.entries.len(), 49);
                            return;
                        }
                    }
                }
            }
        }
    }
    panic!("saving_throws table not found");
}

// ── Convenience derives count ──────────────────────────────────

#[test]
fn ose_saves_has_convenience_derives() {
    let program = compile_ose_saves();

    let derive_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) if sys.name == "OSE Saves" => Some(
                sys.decls
                    .iter()
                    .filter_map(|d| match &d.node {
                        DeclKind::Derive(f) => Some(f.name.as_str()),
                        _ => None,
                    })
                    .collect::<Vec<_>>(),
            ),
            _ => None,
        })
        .flatten()
        .collect();

    assert!(derive_names.contains(&"get_save_death"));
    assert!(derive_names.contains(&"get_save_wands"));
    assert!(derive_names.contains(&"get_save_paralysis"));
    assert!(derive_names.contains(&"get_save_breath"));
    assert!(derive_names.contains(&"get_save_spells"));
}
