//! OSE character generation integration tests.
//!
//! Verifies that ose/ose_chargen.ttrpg parses, lowers, and type-checks
//! through the multi-file pipeline.
//!
//! Runtime derive/mechanic/table tests have been moved to
//! ose/tests/ose_chargen.ttrpg-cli.

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_ast::diagnostic::Severity;

fn compile_ose_chargen() -> ttrpg_ast::ast::Program {
    let core_source = include_str!("../../../ose/ose_core.ttrpg");
    let class_source = include_str!("../../../ose/ose_class.ttrpg");
    let chargen_source = include_str!("../../../ose/ose_chargen.ttrpg");

    let sources = vec![
        ("ose/ose_core.ttrpg".to_string(), core_source.to_string()),
        ("ose/ose_class.ttrpg".to_string(), class_source.to_string()),
        (
            "ose/ose_chargen.ttrpg".to_string(),
            chargen_source.to_string(),
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
fn ose_chargen_parses_and_typechecks() {
    let program = compile_ose_chargen();
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
    assert!(system_names.contains(&"OSE Chargen"));
}

#[test]
fn ose_chargen_has_expected_decls() {
    let program = compile_ose_chargen();
    let mut has_roll_ability = false;
    let mut has_roll_starting_hp = false;
    let mut has_thac0_table = false;
    let mut has_starting_spells_table = false;

    for item in &program.items {
        if let TopLevel::System(sys) = &item.node
            && sys.name == "OSE Chargen"
        {
            for decl in &sys.decls {
                match &decl.node {
                    DeclKind::Mechanic(m) if m.name == "roll_ability" => {
                        has_roll_ability = true;
                    }
                    DeclKind::Mechanic(m) if m.name == "roll_starting_hp" => {
                        has_roll_starting_hp = true;
                    }
                    DeclKind::Table(t) if t.name == "character_thac0" => has_thac0_table = true,
                    DeclKind::Table(t) if t.name == "available_starting_spells" => {
                        has_starting_spells_table = true;
                    }
                    _ => {}
                }
            }
        }
    }

    assert!(has_roll_ability, "expected roll_ability mechanic");
    assert!(has_roll_starting_hp, "expected roll_starting_hp mechanic");
    assert!(has_thac0_table, "expected character_thac0 table");
    assert!(
        has_starting_spells_table,
        "expected available_starting_spells table"
    );
}
