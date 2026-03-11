//! OSE spell metadata integration tests.
//!
//! Verifies that ose/ose_spells.ttrpg parses, lowers, and type-checks
//! through the multi-file pipeline.
//!
//! Runtime table lookup tests have been moved to ose/tests/ose_spells.ttrpg-cli.

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_ast::diagnostic::Severity;

fn compile_ose_spells() -> ttrpg_ast::ast::Program {
    let core_source = include_str!("../../../ose/ose_core.ttrpg");
    let spells_source = include_str!("../../../ose/ose_spells.ttrpg");

    let sources = vec![
        ("ose/ose_core.ttrpg".to_string(), core_source.to_string()),
        (
            "ose/ose_spells.ttrpg".to_string(),
            spells_source.to_string(),
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
fn ose_spells_parses_and_typechecks() {
    let program = compile_ose_spells();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSE"));
    assert!(system_names.contains(&"OSE Spells"));
}

#[test]
fn ose_spells_has_expected_decls() {
    let program = compile_ose_spells();

    let mut has_spell_save_enum = false;
    let mut has_spell_save_table = false;
    let mut has_spell_damage_table = false;

    for item in &program.items {
        if let TopLevel::System(sys) = &item.node
            && sys.name == "OSE Spells"
        {
            for decl in &sys.decls {
                match &decl.node {
                    DeclKind::Enum(e) if e.name == "SpellSaveType" => {
                        has_spell_save_enum = true;
                        assert_eq!(e.variants.len(), 6);
                    }
                    DeclKind::Table(t) if t.name == "spell_save_type" => {
                        has_spell_save_table = true;
                    }
                    DeclKind::Table(t) if t.name == "spell_damage_dice" => {
                        has_spell_damage_table = true;
                    }
                    _ => {}
                }
            }
        }
    }

    assert!(has_spell_save_enum, "expected SpellSaveType enum");
    assert!(has_spell_save_table, "expected spell_save_type table");
    assert!(has_spell_damage_table, "expected spell_damage_dice table");
}
