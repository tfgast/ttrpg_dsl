//! OSE magic & turn undead integration test.
//!
//! Verifies that ose/ose_magic.ttrpg (combined with ose/ose_core.ttrpg)
//! parses, lowers, and type-checks through the multi-file pipeline.
//!
//! Runtime table/derive/mechanic tests have been moved to
//! ose/tests/ose_magic.ttrpg-cli.

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_ast::diagnostic::Severity;

fn compile_ose_magic() -> ttrpg_ast::ast::Program {
    let core_source = include_str!("../../../ose/ose_core.ttrpg");
    let magic_source = include_str!("../../../ose/ose_magic.ttrpg");

    let sources = vec![
        ("ose/ose_core.ttrpg".to_string(), core_source.to_string()),
        ("ose/ose_magic.ttrpg".to_string(), magic_source.to_string()),
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
fn ose_magic_parses_and_typechecks() {
    let program = compile_ose_magic();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSE"));
    assert!(system_names.contains(&"OSE Magic"));
}

#[test]
fn ose_magic_has_expected_declarations() {
    let program = compile_ose_magic();

    let mut has_spell_slots_table = false;
    let mut has_can_cast = false;
    let mut has_total_spell_slots = false;
    let mut has_turn_undead_result = false;
    let mut has_undead_rank_from_hd = false;

    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSE Magic" {
                for decl in &sys.decls {
                    match &decl.node {
                        DeclKind::Table(t) if t.name == "spell_slots" => {
                            has_spell_slots_table = true;
                            assert_eq!(t.params.len(), 2);
                        }
                        DeclKind::Derive(f) if f.name == "can_cast" => {
                            has_can_cast = true;
                        }
                        DeclKind::Derive(f) if f.name == "total_spell_slots" => {
                            has_total_spell_slots = true;
                        }
                        DeclKind::Derive(f) if f.name == "turn_undead_result" => {
                            has_turn_undead_result = true;
                        }
                        DeclKind::Derive(f) if f.name == "undead_rank_from_hd" => {
                            has_undead_rank_from_hd = true;
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    assert!(has_spell_slots_table, "expected spell_slots table");
    assert!(has_can_cast, "expected can_cast derive");
    assert!(has_total_spell_slots, "expected total_spell_slots derive");
    assert!(has_turn_undead_result, "expected turn_undead_result derive");
    assert!(
        has_undead_rank_from_hd,
        "expected undead_rank_from_hd derive"
    );
}
