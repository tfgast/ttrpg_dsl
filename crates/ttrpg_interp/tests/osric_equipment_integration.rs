//! OSRIC equipment integration test.
//!
//! Verifies that osric/osric_equipment.ttrpg parses, lowers, and type-checks
//! through the full multi-file pipeline (core + class + equipment). Exercises
//! melee_weapon_def, missile_weapon_def, armour_def, shield_def derives,
//! equipment_package table, default_starting_armour derive, and enum
//! completeness for DamageType, MeleeWeapon, MissileWeapon, ArmourType,
//! ShieldType.

use std::collections::BTreeMap;

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_ast::diagnostic::Severity;
use ttrpg_ast::Name;
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

mod osric_common;
use osric_common::*;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_equipment() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    let core_source = include_str!("../../../osric/osric_core.ttrpg");
    let class_source = include_str!("../../../osric/osric_class.ttrpg");
    let equipment_source = include_str!("../../../osric/osric_equipment.ttrpg");

    let sources = vec![
        (
            "osric/osric_core.ttrpg".to_string(),
            core_source.to_string(),
        ),
        (
            "osric/osric_class.ttrpg".to_string(),
            class_source.to_string(),
        ),
        (
            "osric/osric_equipment.ttrpg".to_string(),
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

    (program.clone(), result)
}

/// Extract all DeclKind items from the "OSRIC Equipment" system block.
fn get_equipment_decls(program: &ttrpg_ast::ast::Program) -> &[ttrpg_ast::Spanned<DeclKind>] {
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSRIC Equipment" {
                return &sys.decls;
            }
        }
    }
    panic!("no system block named 'OSRIC Equipment' found");
}

/// Extract all DeclKind items from the "OSRIC" core system block.
fn get_core_decls(program: &ttrpg_ast::ast::Program) -> &[ttrpg_ast::Spanned<DeclKind>] {
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSRIC" {
                return &sys.decls;
            }
        }
    }
    panic!("no system block named 'OSRIC' found");
}

/// Call a derive and return struct fields as BTreeMap<String, Value>.
fn get_struct_fields(
    interp: &Interpreter,
    state: &GameState,
    handler: &mut NullHandler,
    derive_name: &str,
    args: Vec<Value>,
    expected_struct: &str,
) -> BTreeMap<String, Value> {
    let val = interp
        .evaluate_derive(state, handler, derive_name, args)
        .unwrap_or_else(|e| panic!("{derive_name} failed: {e}"));

    match val {
        Value::Struct { name, fields } => {
            assert_eq!(
                &*name, expected_struct,
                "expected {expected_struct}, got {name}"
            );
            fields
                .into_iter()
                .map(|(k, v)| (k.to_string(), v))
                .collect()
        }
        other => panic!("expected {expected_struct} struct, got: {other:?}"),
    }
}

fn get_damage_type(fields: &BTreeMap<String, Value>, key: &str) -> String {
    match fields.get(key) {
        Some(Value::EnumVariant { variant, .. }) => variant.to_string(),
        other => panic!("expected DamageType variant for '{key}', got: {other:?}"),
    }
}

/// Extract the int value from a Feet unit struct.
fn get_feet(fields: &BTreeMap<String, Value>, key: &str) -> i64 {
    match fields.get(key) {
        Some(Value::Struct { name, fields }) if &**name == "Feet" => {
            match fields.get(&Name::from("value")) {
                Some(Value::Int(n)) => *n,
                other => panic!("expected int inside Feet for '{key}', got: {other:?}"),
            }
        }
        other => panic!("expected Feet struct for '{key}', got: {other:?}"),
    }
}

/// Extract DiceExpr as (count, sides, modifier).
fn get_dice_expr(fields: &BTreeMap<String, Value>, key: &str) -> (u32, u32, i64) {
    match fields.get(key) {
        Some(Value::DiceExpr(expr)) => {
            assert_eq!(
                expr.groups.len(),
                1,
                "expected single dice group for '{key}'"
            );
            let g = &expr.groups[0];
            assert!(g.filter.is_none(), "unexpected filter on '{key}'");
            (g.count, g.sides, expr.modifier)
        }
        other => panic!("expected DiceExpr for '{key}', got: {other:?}"),
    }
}

fn get_string_list(val: Value) -> Vec<String> {
    match val {
        Value::List(items) => items
            .into_iter()
            .map(|v| match v {
                Value::Str(s) => s,
                other => panic!("expected string in list, got: {other:?}"),
            })
            .collect(),
        other => panic!("expected list, got: {other:?}"),
    }
}

// ── Parse + typecheck ──────────────────────────────────────────

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
fn damage_type_enum_has_3_variants() {
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
    assert_eq!(variants, ["Slashing", "Piercing", "Blunt"]);
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

// ── Melee weapon derives ───────────────────────────────────────

#[test]
fn melee_weapon_def_long_sword() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let fields = get_struct_fields(
        &interp,
        &state,
        &mut handler,
        "melee_weapon_def",
        vec![melee_variant("SwordLong")],
        "MeleeWeaponDef",
    );

    assert_eq!(get_int(&fields, "hands"), 1);
    assert_eq!(get_dice_expr(&fields, "damage_sm"), (1, 8, 0));
    assert_eq!(get_dice_expr(&fields, "damage_l"), (1, 12, 0));
    assert_eq!(get_int(&fields, "weight"), 7);
    assert_eq!(get_int(&fields, "cost_cp"), 1500);
    assert_eq!(get_int(&fields, "speed_factor"), 5);
    assert_eq!(get_damage_type(&fields, "damage_type"), "Slashing");
    assert_eq!(get_int(&fields, "one_hand_str"), 0);
}

#[test]
fn melee_weapon_def_dagger() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let fields = get_struct_fields(
        &interp,
        &state,
        &mut handler,
        "melee_weapon_def",
        vec![melee_variant("Dagger")],
        "MeleeWeaponDef",
    );

    assert_eq!(get_int(&fields, "hands"), 1);
    assert_eq!(get_dice_expr(&fields, "damage_sm"), (1, 4, 0));
    assert_eq!(get_dice_expr(&fields, "damage_l"), (1, 3, 0));
    assert_eq!(get_int(&fields, "weight"), 1);
    assert_eq!(get_int(&fields, "cost_cp"), 200);
    assert_eq!(get_int(&fields, "speed_factor"), 2);
    assert_eq!(get_damage_type(&fields, "damage_type"), "Piercing");
}

#[test]
fn melee_weapon_def_halberd() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let fields = get_struct_fields(
        &interp,
        &state,
        &mut handler,
        "melee_weapon_def",
        vec![melee_variant("Halberd")],
        "MeleeWeaponDef",
    );

    assert_eq!(get_int(&fields, "hands"), 2);
    assert_eq!(get_dice_expr(&fields, "damage_sm"), (1, 10, 0));
    assert_eq!(get_dice_expr(&fields, "damage_l"), (2, 6, 0));
    assert_eq!(get_int(&fields, "weight"), 18);
    assert_eq!(get_int(&fields, "cost_cp"), 900);
    assert_eq!(get_int(&fields, "speed_factor"), 9);
    assert_eq!(get_damage_type(&fields, "damage_type"), "Slashing");
}

#[test]
fn melee_weapon_def_fist_or_kick() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let fields = get_struct_fields(
        &interp,
        &state,
        &mut handler,
        "melee_weapon_def",
        vec![melee_variant("FistOrKick")],
        "MeleeWeaponDef",
    );

    assert_eq!(get_int(&fields, "hands"), 1);
    assert_eq!(get_dice_expr(&fields, "damage_sm"), (1, 2, 0));
    assert_eq!(get_dice_expr(&fields, "damage_l"), (1, 2, 0));
    assert_eq!(get_int(&fields, "weight"), 0);
    assert_eq!(get_int(&fields, "cost_cp"), 0);
    assert_eq!(get_int(&fields, "speed_factor"), 1);
    assert_eq!(get_damage_type(&fields, "damage_type"), "Blunt");
}

#[test]
fn melee_weapon_def_two_handed_sword() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let fields = get_struct_fields(
        &interp,
        &state,
        &mut handler,
        "melee_weapon_def",
        vec![melee_variant("SwordTwoHanded")],
        "MeleeWeaponDef",
    );

    assert_eq!(get_int(&fields, "hands"), 2);
    assert_eq!(get_dice_expr(&fields, "damage_sm"), (1, 10, 0));
    assert_eq!(get_dice_expr(&fields, "damage_l"), (3, 6, 0));
    assert_eq!(get_int(&fields, "weight"), 25);
    assert_eq!(get_int(&fields, "cost_cp"), 3000);
    assert_eq!(get_int(&fields, "speed_factor"), 10);
    assert_eq!(get_damage_type(&fields, "damage_type"), "Slashing");
}

#[test]
fn melee_weapon_def_flail_heavy_has_bonus_damage() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let fields = get_struct_fields(
        &interp,
        &state,
        &mut handler,
        "melee_weapon_def",
        vec![melee_variant("FlailHeavy")],
        "MeleeWeaponDef",
    );

    // Heavy flail has bonus damage: 1d6+1 vs S/M, 2d4 vs L+
    assert_eq!(get_dice_expr(&fields, "damage_sm"), (1, 6, 1));
    assert_eq!(get_dice_expr(&fields, "damage_l"), (2, 4, 0));
    assert_eq!(get_damage_type(&fields, "damage_type"), "Blunt");
}

#[test]
fn melee_weapon_def_lance() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let fields = get_struct_fields(
        &interp,
        &state,
        &mut handler,
        "melee_weapon_def",
        vec![melee_variant("Lance")],
        "MeleeWeaponDef",
    );

    assert_eq!(get_int(&fields, "hands"), 1);
    assert_eq!(get_dice_expr(&fields, "damage_sm"), (2, 4, 1));
    assert_eq!(get_dice_expr(&fields, "damage_l"), (3, 6, 0));
    assert_eq!(get_int(&fields, "speed_factor"), 8);
    assert_eq!(get_damage_type(&fields, "damage_type"), "Piercing");
}

// ── Missile weapon derives ─────────────────────────────────────

#[test]
fn missile_weapon_def_long_bow() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let fields = get_struct_fields(
        &interp,
        &state,
        &mut handler,
        "missile_weapon_def",
        vec![missile_variant("BowLong")],
        "MissileWeaponDef",
    );

    assert_eq!(get_int(&fields, "hands"), 2);
    assert!(!get_bool(&fields, "is_hurled"));
    assert_eq!(get_damage_type(&fields, "damage_type"), "Piercing");
    assert_eq!(get_feet(&fields, "range_increment"), 70);
    assert_eq!(get_int(&fields, "rate_of_fire"), 2);
    assert_eq!(get_dice_expr(&fields, "damage_sm"), (1, 6, 0));
    assert_eq!(get_dice_expr(&fields, "damage_l"), (1, 6, 0));
    assert_eq!(get_int(&fields, "weight"), 12);
    assert_eq!(get_int(&fields, "cost_cp"), 6000);
}

#[test]
fn missile_weapon_def_heavy_crossbow() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let fields = get_struct_fields(
        &interp,
        &state,
        &mut handler,
        "missile_weapon_def",
        vec![missile_variant("CrossbowHeavy")],
        "MissileWeaponDef",
    );

    assert_eq!(get_int(&fields, "hands"), 2);
    assert!(!get_bool(&fields, "is_hurled"));
    assert_eq!(get_feet(&fields, "range_increment"), 80);
    // Rate of fire 0 = every other round
    assert_eq!(get_int(&fields, "rate_of_fire"), 0);
    assert_eq!(get_dice_expr(&fields, "damage_sm"), (1, 6, 1));
    assert_eq!(get_dice_expr(&fields, "damage_l"), (1, 6, 1));
}

#[test]
fn missile_weapon_def_dagger_thrown_is_hurled() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let fields = get_struct_fields(
        &interp,
        &state,
        &mut handler,
        "missile_weapon_def",
        vec![missile_variant("DaggerThrown")],
        "MissileWeaponDef",
    );

    assert_eq!(get_int(&fields, "hands"), 1);
    assert!(get_bool(&fields, "is_hurled"));
    assert_eq!(get_damage_type(&fields, "damage_type"), "Piercing");
    assert_eq!(get_feet(&fields, "range_increment"), 10);
    assert_eq!(get_int(&fields, "rate_of_fire"), 2);
    assert_eq!(get_dice_expr(&fields, "damage_sm"), (1, 4, 0));
    assert_eq!(get_dice_expr(&fields, "damage_l"), (1, 3, 0));
}

#[test]
fn missile_weapon_def_sling() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let fields = get_struct_fields(
        &interp,
        &state,
        &mut handler,
        "missile_weapon_def",
        vec![missile_variant("Sling")],
        "MissileWeaponDef",
    );

    assert_eq!(get_int(&fields, "hands"), 1);
    // Sling is launched (not hurled)
    assert!(!get_bool(&fields, "is_hurled"));
    assert_eq!(get_damage_type(&fields, "damage_type"), "Blunt");
    assert_eq!(get_feet(&fields, "range_increment"), 35);
    assert_eq!(get_dice_expr(&fields, "damage_sm"), (1, 4, 1));
    assert_eq!(get_dice_expr(&fields, "damage_l"), (1, 6, 1));
}

#[test]
fn missile_weapon_def_dart_has_highest_rof() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let fields = get_struct_fields(
        &interp,
        &state,
        &mut handler,
        "missile_weapon_def",
        vec![missile_variant("DartThrown")],
        "MissileWeaponDef",
    );

    assert!(get_bool(&fields, "is_hurled"));
    assert_eq!(get_int(&fields, "rate_of_fire"), 3);
    assert_eq!(get_feet(&fields, "range_increment"), 15);
}

#[test]
fn missile_weapon_def_sling_stone_lower_damage() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let fields = get_struct_fields(
        &interp,
        &state,
        &mut handler,
        "missile_weapon_def",
        vec![missile_variant("SlingStone")],
        "MissileWeaponDef",
    );

    assert_eq!(get_int(&fields, "hands"), 1);
    assert!(!get_bool(&fields, "is_hurled"));
    assert_eq!(get_damage_type(&fields, "damage_type"), "Blunt");
    assert_eq!(get_feet(&fields, "range_increment"), 35);
    // Stone ammo: 1d4/1d4 (lower than bullet's 1d4+1/1d6+1)
    assert_eq!(get_dice_expr(&fields, "damage_sm"), (1, 4, 0));
    assert_eq!(get_dice_expr(&fields, "damage_l"), (1, 4, 0));
    assert_eq!(get_int(&fields, "cost_cp"), 50);
}

#[test]
fn missile_weapon_def_club_thrown_costs_2cp() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let fields = get_struct_fields(
        &interp,
        &state,
        &mut handler,
        "missile_weapon_def",
        vec![missile_variant("ClubThrown")],
        "MissileWeaponDef",
    );

    // Club costs 2 cp (was incorrectly 0 gp)
    assert_eq!(get_int(&fields, "cost_cp"), 2);
}

#[test]
fn missile_weapon_def_javelin_costs_50cp() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let fields = get_struct_fields(
        &interp,
        &state,
        &mut handler,
        "missile_weapon_def",
        vec![missile_variant("JavelinThrown")],
        "MissileWeaponDef",
    );

    // Javelin costs 5 sp = 50 cp (was incorrectly 0 gp)
    assert_eq!(get_int(&fields, "cost_cp"), 50);
}

// ── Handedness STR exceptions ─────────────────────────────────

#[test]
fn melee_weapon_battle_axe_one_hand_str_15() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let fields = get_struct_fields(
        &interp,
        &state,
        &mut handler,
        "melee_weapon_def",
        vec![melee_variant("BattleAxe")],
        "MeleeWeaponDef",
    );

    assert_eq!(get_int(&fields, "hands"), 2);
    assert_eq!(get_int(&fields, "one_hand_str"), 15);
}

#[test]
fn melee_weapon_sword_bastard_one_hand_str_15() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let fields = get_struct_fields(
        &interp,
        &state,
        &mut handler,
        "melee_weapon_def",
        vec![melee_variant("SwordBastard")],
        "MeleeWeaponDef",
    );

    assert_eq!(get_int(&fields, "hands"), 2);
    assert_eq!(get_int(&fields, "one_hand_str"), 15);
    assert_eq!(get_int(&fields, "cost_cp"), 2500);
}

#[test]
fn melee_weapon_sword_broad_one_hand_str_12() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let fields = get_struct_fields(
        &interp,
        &state,
        &mut handler,
        "melee_weapon_def",
        vec![melee_variant("SwordBroad")],
        "MeleeWeaponDef",
    );

    assert_eq!(get_int(&fields, "hands"), 2);
    assert_eq!(get_int(&fields, "one_hand_str"), 12);
}

#[test]
fn melee_weapon_club_costs_2cp() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let fields = get_struct_fields(
        &interp,
        &state,
        &mut handler,
        "melee_weapon_def",
        vec![melee_variant("Club")],
        "MeleeWeaponDef",
    );

    // Club costs 2 cp (was incorrectly 0 gp)
    assert_eq!(get_int(&fields, "cost_cp"), 2);
    assert_eq!(get_int(&fields, "one_hand_str"), 0);
}

#[test]
fn melee_weapon_javelin_costs_50cp() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let fields = get_struct_fields(
        &interp,
        &state,
        &mut handler,
        "melee_weapon_def",
        vec![melee_variant("Javelin")],
        "MeleeWeaponDef",
    );

    // Javelin costs 5 sp = 50 cp (was incorrectly 0 gp)
    assert_eq!(get_int(&fields, "cost_cp"), 50);
}

// ── Armour derives ─────────────────────────────────────────────

#[test]
fn armour_def_plate_mail() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let fields = get_struct_fields(
        &interp,
        &state,
        &mut handler,
        "armour_def",
        vec![armour_variant("PlateMail")],
        "ArmourDef",
    );

    assert_eq!(get_int(&fields, "ascending_ac"), 17);
    assert_eq!(get_int(&fields, "weight"), 45);
    assert_eq!(get_feet(&fields, "movement_cap"), 60);
    assert_eq!(get_int(&fields, "cost_gp"), 400);
}

#[test]
fn armour_def_chain_mail() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let fields = get_struct_fields(
        &interp,
        &state,
        &mut handler,
        "armour_def",
        vec![armour_variant("ChainMail")],
        "ArmourDef",
    );

    assert_eq!(get_int(&fields, "ascending_ac"), 15);
    assert_eq!(get_int(&fields, "weight"), 30);
    assert_eq!(get_feet(&fields, "movement_cap"), 90);
    assert_eq!(get_int(&fields, "cost_gp"), 75);
}

#[test]
fn armour_def_leather() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let fields = get_struct_fields(
        &interp,
        &state,
        &mut handler,
        "armour_def",
        vec![armour_variant("Leather")],
        "ArmourDef",
    );

    assert_eq!(get_int(&fields, "ascending_ac"), 12);
    assert_eq!(get_int(&fields, "weight"), 15);
    assert_eq!(get_feet(&fields, "movement_cap"), 120);
    assert_eq!(get_int(&fields, "cost_gp"), 5);
}

#[test]
fn armour_def_elfin_mail_is_lightweight() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let fields = get_struct_fields(
        &interp,
        &state,
        &mut handler,
        "armour_def",
        vec![armour_variant("ElfinMail")],
        "ArmourDef",
    );

    // Elfin mail: same AC as chain but half the weight, full movement, not purchasable
    assert_eq!(get_int(&fields, "ascending_ac"), 15);
    assert_eq!(get_int(&fields, "weight"), 15);
    assert_eq!(get_feet(&fields, "movement_cap"), 120);
    assert_eq!(get_int(&fields, "cost_gp"), 0);
}

#[test]
fn armour_def_banded_and_splint_same_ac() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let banded = get_struct_fields(
        &interp,
        &state,
        &mut handler,
        "armour_def",
        vec![armour_variant("Banded")],
        "ArmourDef",
    );
    let splint = get_struct_fields(
        &interp,
        &state,
        &mut handler,
        "armour_def",
        vec![armour_variant("Splint")],
        "ArmourDef",
    );

    assert_eq!(get_int(&banded, "ascending_ac"), 16);
    assert_eq!(get_int(&splint, "ascending_ac"), 16);
    // Banded is lighter
    assert!(get_int(&banded, "weight") < get_int(&splint, "weight"));
}

// ── Shield derives ─────────────────────────────────────────────

#[test]
fn shield_def_small() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let fields = get_struct_fields(
        &interp,
        &state,
        &mut handler,
        "shield_def",
        vec![shield_variant("SmallShield")],
        "ShieldDef",
    );

    assert_eq!(get_int(&fields, "ac_bonus"), 1);
    assert_eq!(get_int(&fields, "max_blocks"), 1);
    assert_eq!(get_int(&fields, "weight"), 5);
    assert_eq!(get_int(&fields, "cost_gp"), 10);
}

#[test]
fn shield_def_medium() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let fields = get_struct_fields(
        &interp,
        &state,
        &mut handler,
        "shield_def",
        vec![shield_variant("MediumShield")],
        "ShieldDef",
    );

    assert_eq!(get_int(&fields, "ac_bonus"), 1);
    assert_eq!(get_int(&fields, "max_blocks"), 2);
    assert_eq!(get_int(&fields, "weight"), 8);
    assert_eq!(get_int(&fields, "cost_gp"), 12);
}

#[test]
fn shield_def_large() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let fields = get_struct_fields(
        &interp,
        &state,
        &mut handler,
        "shield_def",
        vec![shield_variant("LargeShield")],
        "ShieldDef",
    );

    assert_eq!(get_int(&fields, "ac_bonus"), 1);
    assert_eq!(get_int(&fields, "max_blocks"), 3);
    assert_eq!(get_int(&fields, "weight"), 10);
    assert_eq!(get_int(&fields, "cost_gp"), 15);
}

#[test]
fn all_shields_have_ac_bonus_one() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    for variant in ["SmallShield", "MediumShield", "LargeShield"] {
        let fields = get_struct_fields(
            &interp,
            &state,
            &mut handler,
            "shield_def",
            vec![shield_variant(variant)],
            "ShieldDef",
        );
        assert_eq!(
            get_int(&fields, "ac_bonus"),
            1,
            "{variant} should have ac_bonus 1"
        );
    }
}

// ── Equipment package table ────────────────────────────────────

#[test]
fn equipment_package_fighter() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "equipment_package",
            vec![class_variant("Fighter")],
        )
        .expect("equipment_package(Fighter) failed");

    let items = get_string_list(val);
    assert!(items.contains(&"Sword, long".to_string()));
    assert!(items.contains(&"Shield".to_string()));
    assert!(items.contains(&"Chain mail".to_string()));
    assert!(items.contains(&"Backpack".to_string()));
}

#[test]
fn equipment_package_magic_user() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "equipment_package",
            vec![class_variant("MagicUser")],
        )
        .expect("equipment_package(MagicUser) failed");

    let items = get_string_list(val);
    assert!(items.contains(&"Dagger".to_string()));
    assert!(items.contains(&"Staff".to_string()));
    assert!(items.contains(&"Spell book (blank)".to_string()));
    // Magic-users should NOT have armour
    assert!(!items
        .iter()
        .any(|s| s.contains("mail") || s.contains("Leather")));
}

#[test]
fn equipment_package_thief() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "equipment_package",
            vec![class_variant("Thief")],
        )
        .expect("equipment_package(Thief) failed");

    let items = get_string_list(val);
    assert!(items.contains(&"Sword, short".to_string()));
    assert!(items.contains(&"Dagger".to_string()));
    assert!(items.contains(&"Leather".to_string()));
    assert!(items.contains(&"Thieves' tools".to_string()));
}

#[test]
fn equipment_package_druid() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "equipment_package",
            vec![class_variant("Druid")],
        )
        .expect("equipment_package(Druid) failed");

    let items = get_string_list(val);
    assert!(items.contains(&"Staff".to_string()));
    assert!(items.contains(&"Leather".to_string()));
    assert!(items.contains(&"Wooden shield".to_string()));
}

#[test]
fn equipment_package_all_classes_resolve() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let classes = [
        "Assassin",
        "Cleric",
        "Druid",
        "Fighter",
        "Illusionist",
        "MagicUser",
        "Monk",
        "Paladin",
        "Ranger",
        "Thief",
    ];

    for class in &classes {
        let val = interp
            .evaluate_derive(
                &state,
                &mut handler,
                "equipment_package",
                vec![class_variant(class)],
            )
            .unwrap_or_else(|e| panic!("equipment_package({class}) failed: {e}"));

        match &val {
            Value::List(items) => {
                assert!(
                    !items.is_empty(),
                    "equipment_package({class}) returned empty list"
                );
            }
            other => panic!("expected list for {class}, got: {other:?}"),
        }
    }
}

// ── Default starting armour ────────────────────────────────────

#[test]
fn default_starting_armour_fighter() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "default_starting_armour",
            vec![class_variant("Fighter")],
        )
        .expect("default_starting_armour(Fighter) failed");

    let items = get_string_list(val);
    assert_eq!(items, vec!["Chain mail", "Shield"]);
}

#[test]
fn default_starting_armour_thief() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "default_starting_armour",
            vec![class_variant("Thief")],
        )
        .expect("default_starting_armour(Thief) failed");

    let items = get_string_list(val);
    assert_eq!(items, vec!["Leather"]);
}

#[test]
fn default_starting_armour_magic_user_none() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "default_starting_armour",
            vec![class_variant("MagicUser")],
        )
        .expect("default_starting_armour(MagicUser) failed");

    let items = get_string_list(val);
    assert!(items.is_empty(), "MagicUser should have no starting armour");
}

#[test]
fn default_starting_armour_druid() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "default_starting_armour",
            vec![class_variant("Druid")],
        )
        .expect("default_starting_armour(Druid) failed");

    let items = get_string_list(val);
    assert_eq!(items, vec!["Leather", "Wooden shield"]);
}

// ── Class weapon restriction derives ──────────────────────────

fn get_enum_variant_list(val: Value) -> Vec<String> {
    match val {
        Value::List(items) => items
            .into_iter()
            .map(|v| match v {
                Value::EnumVariant { variant, .. } => variant.to_string(),
                other => panic!("expected enum variant in list, got: {other:?}"),
            })
            .collect(),
        other => panic!("expected list, got: {other:?}"),
    }
}

fn eval_bool(
    interp: &Interpreter,
    state: &GameState,
    handler: &mut NullHandler,
    name: &str,
    args: Vec<Value>,
) -> bool {
    match interp
        .evaluate_derive(state, handler, name, args)
        .unwrap_or_else(|e| panic!("{name} failed: {e}"))
    {
        Value::Bool(b) => b,
        other => panic!("expected bool from {name}, got: {other:?}"),
    }
}

#[test]
fn class_allowed_melee_cleric_is_blunt_only() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "class_allowed_melee",
            vec![class_variant("Cleric")],
        )
        .expect("class_allowed_melee(Cleric) failed");

    let weapons = get_enum_variant_list(val);
    // Clerics can only use blunt weapons
    assert!(weapons.contains(&"Club".to_string()));
    assert!(weapons.contains(&"MaceHeavy".to_string()));
    assert!(weapons.contains(&"Staff".to_string()));
    assert!(weapons.contains(&"FlailHeavy".to_string()));
    assert!(weapons.contains(&"WarhammerLight".to_string()));
    // Should NOT contain slashing/piercing weapons
    assert!(!weapons.contains(&"SwordLong".to_string()));
    assert!(!weapons.contains(&"Dagger".to_string()));
    assert!(!weapons.contains(&"Spear".to_string()));
}

#[test]
fn class_allowed_melee_magic_user_dagger_and_staff() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "class_allowed_melee",
            vec![class_variant("MagicUser")],
        )
        .expect("class_allowed_melee(MagicUser) failed");

    let weapons = get_enum_variant_list(val);
    assert_eq!(weapons.len(), 2);
    assert!(weapons.contains(&"Dagger".to_string()));
    assert!(weapons.contains(&"Staff".to_string()));
}

#[test]
fn class_allowed_melee_fighter_empty_means_any() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "class_allowed_melee",
            vec![class_variant("Fighter")],
        )
        .expect("class_allowed_melee(Fighter) failed");

    let weapons = get_enum_variant_list(val);
    // weapons_any classes return empty list (all weapons allowed)
    assert!(weapons.is_empty());
}

#[test]
fn class_allowed_missile_cleric_blunt_only() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "class_allowed_missile",
            vec![class_variant("Cleric")],
        )
        .expect("class_allowed_missile(Cleric) failed");

    let weapons = get_enum_variant_list(val);
    assert!(weapons.contains(&"Sling".to_string()));
    assert!(weapons.contains(&"ClubThrown".to_string()));
    assert!(weapons.contains(&"WarhammerThrown".to_string()));
    // Should NOT contain piercing/slashing missile weapons
    assert!(!weapons.contains(&"BowLong".to_string()));
    assert!(!weapons.contains(&"DaggerThrown".to_string()));
}

#[test]
fn class_allowed_missile_monk_has_crossbow() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "class_allowed_missile",
            vec![class_variant("Monk")],
        )
        .expect("class_allowed_missile(Monk) failed");

    let weapons = get_enum_variant_list(val);
    assert!(weapons.contains(&"CrossbowHeavy".to_string()));
    assert!(weapons.contains(&"CrossbowLight".to_string()));
    assert!(weapons.contains(&"DaggerThrown".to_string()));
    // Monks cannot use bows
    assert!(!weapons.contains(&"BowLong".to_string()));
}

#[test]
fn can_wield_melee_fighter_any_weapon() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Fighters can wield anything
    assert!(eval_bool(
        &interp,
        &state,
        &mut handler,
        "can_wield_melee",
        vec![class_variant("Fighter"), melee_variant("SwordTwoHanded")]
    ));
    assert!(eval_bool(
        &interp,
        &state,
        &mut handler,
        "can_wield_melee",
        vec![class_variant("Fighter"), melee_variant("Dagger")]
    ));
}

#[test]
fn can_wield_melee_cleric_blunt_yes_slashing_no() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Cleric CAN wield mace
    assert!(eval_bool(
        &interp,
        &state,
        &mut handler,
        "can_wield_melee",
        vec![class_variant("Cleric"), melee_variant("MaceHeavy")]
    ));
    // Cleric CANNOT wield longsword
    assert!(!eval_bool(
        &interp,
        &state,
        &mut handler,
        "can_wield_melee",
        vec![class_variant("Cleric"), melee_variant("SwordLong")]
    ));
}

#[test]
fn can_wield_melee_magic_user_dagger_yes_sword_no() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    assert!(eval_bool(
        &interp,
        &state,
        &mut handler,
        "can_wield_melee",
        vec![class_variant("MagicUser"), melee_variant("Dagger")]
    ));
    assert!(eval_bool(
        &interp,
        &state,
        &mut handler,
        "can_wield_melee",
        vec![class_variant("MagicUser"), melee_variant("Staff")]
    ));
    assert!(!eval_bool(
        &interp,
        &state,
        &mut handler,
        "can_wield_melee",
        vec![class_variant("MagicUser"), melee_variant("SwordLong")]
    ));
}

#[test]
fn can_wield_missile_cleric_sling_yes_bow_no() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    assert!(eval_bool(
        &interp,
        &state,
        &mut handler,
        "can_wield_missile",
        vec![class_variant("Cleric"), missile_variant("Sling")]
    ));
    assert!(!eval_bool(
        &interp,
        &state,
        &mut handler,
        "can_wield_missile",
        vec![class_variant("Cleric"), missile_variant("BowLong")]
    ));
}

#[test]
fn can_wield_all_restricted_classes_resolve() {
    let (program, result) = compile_osric_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Verify all 10 classes resolve without error for both melee and missile
    let classes = [
        "Assassin",
        "Cleric",
        "Druid",
        "Fighter",
        "Illusionist",
        "MagicUser",
        "Monk",
        "Paladin",
        "Ranger",
        "Thief",
    ];

    for class in &classes {
        // class_allowed_melee
        interp
            .evaluate_derive(
                &state,
                &mut handler,
                "class_allowed_melee",
                vec![class_variant(class)],
            )
            .unwrap_or_else(|e| panic!("class_allowed_melee({class}) failed: {e}"));

        // class_allowed_missile
        interp
            .evaluate_derive(
                &state,
                &mut handler,
                "class_allowed_missile",
                vec![class_variant(class)],
            )
            .unwrap_or_else(|e| panic!("class_allowed_missile({class}) failed: {e}"));

        // can_wield_melee with Dagger (should work for most)
        interp
            .evaluate_derive(
                &state,
                &mut handler,
                "can_wield_melee",
                vec![class_variant(class), melee_variant("Dagger")],
            )
            .unwrap_or_else(|e| panic!("can_wield_melee({class}, Dagger) failed: {e}"));
    }
}
