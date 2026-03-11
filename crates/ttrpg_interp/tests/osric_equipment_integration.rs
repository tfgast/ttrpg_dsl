//! OSRIC equipment integration test.
//!
//! AST structure tests that verify enum completeness and struct definitions.
//! Derive value checks and interpreter-level tests have been moved to the CLI
//! test script at `osric/tests/osric_equipment.ttrpg-cli`.

use ttrpg_ast::ast::{DeclKind, TopLevel};

mod osric_common;
use osric_common::*;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_equipment() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

/// Extract all DeclKind items from the "OSRIC Equipment" system block.
fn get_equipment_decls(program: &ttrpg_ast::ast::Program) -> &[ttrpg_ast::Spanned<DeclKind>] {
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node
            && sys.name == "OSRIC Equipment"
        {
            return &sys.decls;
        }
    }
    panic!("no system block named 'OSRIC Equipment' found");
}

/// Extract all DeclKind items from the "OSRIC" core system block.
fn get_core_decls(program: &ttrpg_ast::ast::Program) -> &[ttrpg_ast::Spanned<DeclKind>] {
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node
            && sys.name == "OSRIC"
        {
            return &sys.decls;
        }
    }
    panic!("no system block named 'OSRIC' found");
}

// ── Parse & typecheck ─────────────────────────────────────────

#[test]
fn osric_equipment_parses_and_typechecks() {
    let (program, _) = compile_osric_equipment();
    let has_system = program
        .items
        .iter()
        .any(|item| matches!(&item.node, TopLevel::System(sys) if sys.name == "OSRIC Equipment"));
    assert!(has_system, "expected system named 'OSRIC Equipment'");
}

// ── Enum completeness ──────────────────────────────────────────

#[test]
fn damage_type_enum_has_9_variants() {
    let (program, _) = compile_osric_equipment();
    let decls = get_core_decls(&program);
    let dt = decls
        .iter()
        .find_map(|d| match &d.node {
            DeclKind::Enum(e) if &*e.name == "DamageType" => Some(e),
            _ => None,
        })
        .expect("DamageType enum not found");

    let variants: Vec<_> = dt.variants.iter().map(|v| v.name.as_str()).collect();
    assert_eq!(
        variants,
        [
            "Slashing",
            "Piercing",
            "Blunt",
            "Fire",
            "Cold",
            "Lightning",
            "Acid",
            "Poison",
            "Corrosion"
        ]
    );
}

#[test]
fn melee_weapon_enum_has_27_variants() {
    let (program, _) = compile_osric_equipment();
    let decls = get_core_decls(&program);
    let mw = decls
        .iter()
        .find_map(|d| match &d.node {
            DeclKind::Enum(e) if &*e.name == "MeleeWeapon" => Some(e),
            _ => None,
        })
        .expect("MeleeWeapon enum not found");

    assert_eq!(mw.variants.len(), 27, "MeleeWeapon should have 27 variants");

    let expected = [
        "BattleAxe",
        "HandAxe",
        "Club",
        "Dagger",
        "FistOrKick",
        "FlailHeavy",
        "FlailLight",
        "Halberd",
        "Javelin",
        "Lance",
        "MaceHeavy",
        "MaceLight",
        "MorningStar",
        "PickHeavy",
        "PickLight",
        "PoleArm",
        "Spear",
        "Staff",
        "SwordBastard",
        "SwordBroad",
        "SwordLong",
        "SwordScimitar",
        "SwordShort",
        "SwordTwoHanded",
        "Trident",
        "WarhammerHeavy",
        "WarhammerLight",
    ];
    let actual: Vec<_> = mw.variants.iter().map(|v| v.name.as_str()).collect();
    for name in &expected {
        assert!(actual.contains(name), "MeleeWeapon missing variant: {name}");
    }
}

#[test]
fn missile_weapon_enum_has_15_variants() {
    let (program, _) = compile_osric_equipment();
    let decls = get_core_decls(&program);
    let mw = decls
        .iter()
        .find_map(|d| match &d.node {
            DeclKind::Enum(e) if &*e.name == "MissileWeapon" => Some(e),
            _ => None,
        })
        .expect("MissileWeapon enum not found");

    assert_eq!(
        mw.variants.len(),
        15,
        "MissileWeapon should have 15 variants"
    );

    let expected = [
        "BowLong",
        "BowShort",
        "CompositeBowLong",
        "CompositeBowShort",
        "CrossbowHeavy",
        "CrossbowLight",
        "DaggerThrown",
        "HandAxeThrown",
        "ClubThrown",
        "DartThrown",
        "JavelinThrown",
        "SpearThrown",
        "Sling",
        "SlingStone",
        "WarhammerThrown",
    ];
    let actual: Vec<_> = mw.variants.iter().map(|v| v.name.as_str()).collect();
    for name in &expected {
        assert!(
            actual.contains(name),
            "MissileWeapon missing variant: {name}"
        );
    }
}

#[test]
fn armour_type_enum_has_10_variants() {
    let (program, _) = compile_osric_equipment();
    let decls = get_core_decls(&program);
    let at = decls
        .iter()
        .find_map(|d| match &d.node {
            DeclKind::Enum(e) if &*e.name == "ArmourType" => Some(e),
            _ => None,
        })
        .expect("ArmourType enum not found");

    assert_eq!(at.variants.len(), 10, "ArmourType should have 10 variants");

    let expected = [
        "Banded",
        "ChainMail",
        "ElfinMail",
        "Leather",
        "Padded",
        "PlateMail",
        "RingMail",
        "ScaleLamellar",
        "Splint",
        "StuddedLeather",
    ];
    let actual: Vec<_> = at.variants.iter().map(|v| v.name.as_str()).collect();
    for name in &expected {
        assert!(actual.contains(name), "ArmourType missing variant: {name}");
    }
}

#[test]
fn shield_type_enum_has_3_variants() {
    let (program, _) = compile_osric_equipment();
    let decls = get_core_decls(&program);
    let st = decls
        .iter()
        .find_map(|d| match &d.node {
            DeclKind::Enum(e) if &*e.name == "ShieldType" => Some(e),
            _ => None,
        })
        .expect("ShieldType enum not found");

    let variants: Vec<_> = st.variants.iter().map(|v| v.name.as_str()).collect();
    assert_eq!(variants, ["SmallShield", "MediumShield", "LargeShield"]);
}

// ── Struct definitions ─────────────────────────────────────────

#[test]
fn equipment_structs_exist() {
    let (program, _) = compile_osric_equipment();
    let decls = get_equipment_decls(&program);
    let structs: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Struct(s) => Some((&*s.name, s.fields.len())),
            _ => None,
        })
        .collect();

    assert!(
        structs.contains(&("MeleeWeaponDef", 9)),
        "missing MeleeWeaponDef with 9 fields"
    );
    assert!(
        structs.contains(&("MissileWeaponDef", 9)),
        "missing MissileWeaponDef with 9 fields"
    );
    assert!(
        structs.contains(&("ArmourDef", 4)),
        "missing ArmourDef with 4 fields"
    );
    assert!(
        structs.contains(&("ShieldDef", 4)),
        "missing ShieldDef with 4 fields"
    );
}
