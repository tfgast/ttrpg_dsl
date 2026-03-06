//! OSRIC ability modifier tables integration test.
//!
//! Verifies that osric/osric_ability.ttrpg parses, lowers, and type-checks
//! through the full multi-file pipeline. AST structure tests only — runtime
//! table/derive tests are in osric/tests/osric_ability.ttrpg-cli.

use ttrpg_ast::ast::{DeclKind, TopLevel};

mod osric_common;
use osric_common::*;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_ability() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn osric_ability_parses_and_typechecks() {
    let (program, _) = compile_osric_ability();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSRIC"));
    assert!(system_names.contains(&"OSRIC Ability"));
}

// ── Declaration structure ──────────────────────────────────────

#[test]
fn osric_ability_has_all_tables() {
    let (program, _) = compile_osric_ability();

    let table_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) if sys.name == "OSRIC Ability" => Some(
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
        // STR
        "str_to_hit",
        "str_damage",
        "str_encumbrance",
        "str_minor_test",
        "str_minor_extraordinary",
        "str_major_test",
        // Exceptional STR
        "exc_str_to_hit",
        "exc_str_damage",
        "exc_str_encumbrance",
        "exc_str_minor_test",
        "exc_str_minor_extraordinary",
        "exc_str_major_test",
        // DEX
        "dex_surprise",
        "dex_missile",
        "dex_ac_adj",
        "dex_init_missile",
        "dex_agility_save",
        // CON
        "con_hp_mod",
        "con_hp_mod_fighter",
        "con_resurrection",
        "con_system_shock",
        // INT
        "int_extra_languages",
        // WIS
        "wis_mental_save",
        // CHA
        "cha_max_henchmen",
        "cha_loyalty",
        "cha_reaction",
        // Stalwart
        "stalwart_save_bonus",
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
