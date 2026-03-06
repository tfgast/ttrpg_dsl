//! OSE ability modifiers & encumbrance integration test.
//!
//! Verifies that ose/ose_ability.ttrpg parses, lowers, and type-checks
//! through the full multi-file pipeline.
//!
//! Runtime table value tests have been moved to ose/tests/ose_ability.ttrpg-cli.

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_ast::diagnostic::Severity;

// ── Compile helpers ────────────────────────────────────────────

/// Compile both OSE files through the multi-file pipeline.
fn compile_ose_ability() -> ttrpg_ast::ast::Program {
    let core_source = include_str!("../../../ose/ose_core.ttrpg");
    let ability_source = include_str!("../../../ose/ose_ability.ttrpg");

    let sources = vec![
        ("ose/ose_core.ttrpg".to_string(), core_source.to_string()),
        (
            "ose/ose_ability.ttrpg".to_string(),
            ability_source.to_string(),
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

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn ose_ability_parses_and_typechecks() {
    let program = compile_ose_ability();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSE"));
    assert!(system_names.contains(&"OSE Ability"));
}

// ── Declaration structure ──────────────────────────────────────

#[test]
fn ose_ability_has_all_tables() {
    let program = compile_ose_ability();

    let table_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) if sys.name == "OSE Ability" => Some(
                sys.decls
                    .iter()
                    .filter_map(|d| match &d.node {
                        DeclKind::Table(t) => Some(t.name.as_str()),
                        _ => None,
                    })
                    .collect::<Vec<_>>(),
            ),
            _ => None,
        })
        .flatten()
        .collect();

    let expected = [
        "str_melee_mod",
        "str_open_doors",
        "dex_mod",
        "dex_init_mod",
        "con_hp_mod",
        "int_extra_languages",
        "wis_magic_save_mod",
        "cha_reaction_mod",
        "cha_max_retainers",
        "cha_loyalty",
        "prime_req_xp_mod",
        "encumbrance_level",
        "movement_rate",
    ];

    for name in &expected {
        assert!(table_names.contains(name), "missing table: {name}");
    }

    assert_eq!(
        table_names.len(),
        expected.len(),
        "expected {} tables, got {}: {:?}",
        expected.len(),
        table_names.len(),
        table_names
    );
}
