//! OSE starting equipment integration tests.
//!
//! Verifies that ose/ose_equipment.ttrpg parses, lowers, type-checks, and
//! has expected declarations.
//!
//! Runtime derive tests have been moved to ose/tests/ose_equipment.ttrpg-cli.

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_ast::diagnostic::Severity;

fn compile_ose_equipment() -> ttrpg_ast::ast::Program {
    let core_source = include_str!("../../../ose/ose_core.ttrpg");
    let class_source = include_str!("../../../ose/ose_class.ttrpg");
    let equipment_source = include_str!("../../../ose/ose_equipment.ttrpg");

    let sources = vec![
        ("ose/ose_core.ttrpg".to_string(), core_source.to_string()),
        ("ose/ose_class.ttrpg".to_string(), class_source.to_string()),
        (
            "ose/ose_equipment.ttrpg".to_string(),
            equipment_source.to_string(),
        ),
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

#[test]
fn ose_equipment_parses_and_typechecks() {
    let program = compile_ose_equipment();
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
    assert!(system_names.contains(&"OSE Equipment"));
}

#[test]
fn ose_equipment_has_expected_decls() {
    let program = compile_ose_equipment();
    let mut has_standard_gear = false;
    let mut has_default_armour = false;
    let mut has_equipment_package_table = false;
    let mut has_random_weapon_table = false;

    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSE Equipment" {
                for decl in &sys.decls {
                    match &decl.node {
                        DeclKind::Const(c) if c.name == "STANDARD_ADVENTURING_GEAR" => {
                            has_standard_gear = true;
                        }
                        DeclKind::Derive(d) if d.name == "default_starting_armour" => {
                            has_default_armour = true;
                        }
                        DeclKind::Table(t) if t.name == "equipment_package" => {
                            has_equipment_package_table = true;
                        }
                        DeclKind::Table(t) if t.name == "random_starting_weapon" => {
                            has_random_weapon_table = true;
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    assert!(
        has_standard_gear,
        "expected STANDARD_ADVENTURING_GEAR const"
    );
    assert!(has_default_armour, "expected default_starting_armour");
    assert!(
        has_equipment_package_table,
        "expected equipment_package table"
    );
    assert!(
        has_random_weapon_table,
        "expected random_starting_weapon table"
    );
}
