//! OSRIC weapon specialisation integration test — AST structure verification.
//!
//! Runtime value tests (is_specialized_melee, melee_spec_hit_mod,
//! melee_spec_damage_mod, character_melee_attacks) have been moved to
//! `osric/tests/osric_weapon_spec.ttrpg-cli`.

use ttrpg_ast::ast::{DeclKind, TopLevel};

mod osric_common;
use osric_common::*;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_weapon_spec() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

fn get_weapon_spec_decls(program: &ttrpg_ast::ast::Program) -> &[ttrpg_ast::Spanned<DeclKind>] {
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSRIC Weapon Specialisation" {
                return &sys.decls;
            }
        }
    }
    panic!("no system block named 'OSRIC Weapon Specialisation' found");
}

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn osric_weapon_spec_parses_and_typechecks() {
    let (program, _) = compile_osric_weapon_spec();
    let has_system = program
        .items
        .iter()
        .any(|item| matches!(&item.node, TopLevel::System(sys) if sys.name == "OSRIC Weapon Specialisation"));
    assert!(
        has_system,
        "expected system named 'OSRIC Weapon Specialisation'"
    );
}

// ── Structure verification ─────────────────────────────────────

#[test]
fn osric_weapon_spec_has_group() {
    let (program, _) = compile_osric_weapon_spec();
    let decls = get_weapon_spec_decls(&program);
    let groups: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Group(g) => Some(&*g.name),
            _ => None,
        })
        .collect();
    assert!(
        groups.contains(&"WeaponSpecialization"),
        "missing WeaponSpecialization group"
    );
}

#[test]
fn osric_weapon_spec_has_derives() {
    let (program, _) = compile_osric_weapon_spec();
    let decls = get_weapon_spec_decls(&program);
    let derives: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Derive(d) => Some(&*d.name),
            _ => None,
        })
        .collect();
    let expected = [
        "can_specialize",
        "can_double_specialize_melee",
        "spec_hit_bonus",
        "spec_damage_bonus",
        "spec_melee_attacks",
        "spec_missile_rof",
        "is_pulled_bow",
        "is_specialized_melee",
        "is_specialized_missile",
        "melee_spec_hit_mod",
        "melee_spec_damage_mod",
        "missile_spec_hit_mod",
        "missile_spec_damage_mod",
        "character_melee_attacks",
        "character_missile_attacks",
    ];
    for name in &expected {
        assert!(derives.contains(name), "missing derive: {name}");
    }
}
