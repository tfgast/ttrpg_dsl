//! OSE class definitions & XP tables integration test.
//!
//! Verifies that ose/ose_class.ttrpg parses, lowers, and type-checks
//! through the full multi-file pipeline.
//!
//! Runtime derive tests have been moved to ose/tests/ose_class.ttrpg-cli.

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_ast::diagnostic::Severity;

// ── Compile helpers ────────────────────────────────────────────

fn compile_ose_class() -> ttrpg_ast::ast::Program {
    let core_source = include_str!("../../../ose/ose_core.ttrpg");
    let class_source = include_str!("../../../ose/ose_class.ttrpg");

    let sources = vec![
        ("ose/ose_core.ttrpg".to_string(), core_source.to_string()),
        ("ose/ose_class.ttrpg".to_string(), class_source.to_string()),
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
fn ose_class_parses_and_typechecks() {
    let program = compile_ose_class();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSE"));
    assert!(system_names.contains(&"OSE Classes"));
}

// ── Declaration structure ──────────────────────────────────────

#[test]
fn ose_class_has_xp_group_enum() {
    let program = compile_ose_class();

    let mut found = false;
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node
            && sys.name == "OSE"
        {
            for decl in &sys.decls {
                if let DeclKind::Enum(e) = &decl.node
                    && e.name == "XpGroup"
                {
                    assert_eq!(e.variants.len(), 13);
                    found = true;
                }
            }
        }
    }
    assert!(found, "expected XpGroup enum with 13 variants");
}

#[test]
fn ose_class_has_table_and_derives() {
    let program = compile_ose_class();

    let mut has_table = false;
    let mut derive_names = Vec::new();

    for item in &program.items {
        if let TopLevel::System(sys) = &item.node
            && sys.name == "OSE Classes"
        {
            for decl in &sys.decls {
                match &decl.node {
                    DeclKind::Table(t) if t.name == "xp_table" => {
                        has_table = true;
                        assert_eq!(t.params.len(), 2);
                    }
                    DeclKind::Derive(f) => {
                        derive_names.push(f.name.as_str());
                    }
                    _ => {}
                }
            }
        }
    }

    assert!(has_table, "expected xp_table");
    assert!(derive_names.contains(&"class_def"));
    assert!(derive_names.contains(&"xp_group"));
    assert!(derive_names.contains(&"xp_for_level"));
    assert!(derive_names.contains(&"check_level_up"));
    assert!(derive_names.contains(&"prime_req_xp_modifier"));
    assert!(derive_names.contains(&"meets_requirements"));
    assert!(derive_names.contains(&"adjust_xp"));
}
