//! OSRIC weapon specialisation integration test.
//!
//! Verifies that osric/osric_weapon_spec.ttrpg parses, lowers, and type-checks
//! through the full multi-file pipeline. Exercises specialisation bonuses,
//! attack rate improvements, and missile rate-of-fire overrides.

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

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

// ── Character-level specialisation queries ─────────────────────

#[test]
fn is_specialized_melee_with_granted_group() {
    let (program, result) = compile_osric_weapon_spec();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    let fighter = make_character(
        &mut state,
        "Conan",
        "Fighter",
        5,
        &DEFAULT_ABILITIES,
        50,
        15,
        "Human",
    );
    grant_weapon_spec(
        &mut state,
        &fighter,
        "SpecMelee",
        "MeleeWeapon",
        "SwordLong",
        "Single",
    );

    // Specialized in SwordLong
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "is_specialized_melee",
            vec![
                Value::Entity(fighter),
                enum_variant("MeleeWeapon", "SwordLong"),
            ],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(true));

    // Not specialized in Dagger
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "is_specialized_melee",
            vec![
                Value::Entity(fighter),
                enum_variant("MeleeWeapon", "Dagger"),
            ],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(false));
}

#[test]
fn melee_spec_hit_mod_returns_bonus() {
    let (program, result) = compile_osric_weapon_spec();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    let fighter = make_character(
        &mut state,
        "Roland",
        "Fighter",
        7,
        &DEFAULT_ABILITIES,
        50,
        15,
        "Human",
    );
    grant_weapon_spec(
        &mut state,
        &fighter,
        "SpecMelee",
        "MeleeWeapon",
        "SwordLong",
        "Single",
    );

    // Hit bonus for specialized weapon: +1
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "melee_spec_hit_mod",
            vec![
                Value::Entity(fighter),
                enum_variant("MeleeWeapon", "SwordLong"),
            ],
        )
        .unwrap();
    assert_eq!(val, Value::Int(1));

    // Hit bonus for non-specialized weapon: 0
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "melee_spec_hit_mod",
            vec![
                Value::Entity(fighter),
                enum_variant("MeleeWeapon", "Dagger"),
            ],
        )
        .unwrap();
    assert_eq!(val, Value::Int(0));
}

#[test]
fn melee_spec_damage_mod_returns_bonus() {
    let (program, result) = compile_osric_weapon_spec();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    let fighter = make_character(
        &mut state,
        "Guts",
        "Fighter",
        7,
        &DEFAULT_ABILITIES,
        50,
        15,
        "Human",
    );
    grant_weapon_spec(
        &mut state,
        &fighter,
        "SpecMelee",
        "MeleeWeapon",
        "SwordLong",
        "Single",
    );

    // Damage bonus for specialized weapon: +2
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "melee_spec_damage_mod",
            vec![
                Value::Entity(fighter),
                enum_variant("MeleeWeapon", "SwordLong"),
            ],
        )
        .unwrap();
    assert_eq!(val, Value::Int(2));
}

#[test]
fn double_spec_bonuses() {
    let (program, result) = compile_osric_weapon_spec();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    let fighter = make_character(
        &mut state,
        "Drizzt",
        "Fighter",
        10,
        &DEFAULT_ABILITIES,
        60,
        15,
        "Human",
    );
    grant_weapon_spec(
        &mut state,
        &fighter,
        "SpecMelee",
        "MeleeWeapon",
        "SwordScimitar",
        "Double",
    );

    // Double spec: +3 hit, +3 damage
    let hit = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "melee_spec_hit_mod",
            vec![
                Value::Entity(fighter),
                enum_variant("MeleeWeapon", "SwordScimitar"),
            ],
        )
        .unwrap();
    assert_eq!(hit, Value::Int(3));

    let dmg = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "melee_spec_damage_mod",
            vec![
                Value::Entity(fighter),
                enum_variant("MeleeWeapon", "SwordScimitar"),
            ],
        )
        .unwrap();
    assert_eq!(dmg, Value::Int(3));
}

#[test]
fn no_spec_group_returns_zero_bonus() {
    let (program, result) = compile_osric_weapon_spec();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // Character without WeaponSpecialization group
    let fighter = make_character(
        &mut state,
        "Unspecialized",
        "Fighter",
        5,
        &DEFAULT_ABILITIES,
        30,
        15,
        "Human",
    );

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "melee_spec_hit_mod",
            vec![
                Value::Entity(fighter),
                enum_variant("MeleeWeapon", "SwordLong"),
            ],
        )
        .unwrap();
    assert_eq!(val, Value::Int(0));
}

// ── Character melee attacks integration ────────────────────────

#[test]
fn character_melee_attacks_specialist_vs_normal() {
    let (program, result) = compile_osric_weapon_spec();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // Level 5 specialist: 3/2 → alternating 2/1
    let specialist = make_character(
        &mut state,
        "Specialist",
        "Fighter",
        5,
        &DEFAULT_ABILITIES,
        40,
        15,
        "Human",
    );
    grant_weapon_spec(
        &mut state,
        &specialist,
        "SpecMelee",
        "MeleeWeapon",
        "SwordLong",
        "Single",
    );

    let round1 = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "character_melee_attacks",
            vec![
                Value::Entity(specialist),
                enum_variant("MeleeWeapon", "SwordLong"),
                Value::Int(1),
            ],
        )
        .unwrap();
    let round2 = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "character_melee_attacks",
            vec![
                Value::Entity(specialist),
                enum_variant("MeleeWeapon", "SwordLong"),
                Value::Int(2),
            ],
        )
        .unwrap();
    assert_eq!(round1, Value::Int(1), "specialist L5 odd: 1");
    assert_eq!(round2, Value::Int(2), "specialist L5 even: 2");

    // Same specialist using non-specialized weapon: normal 1 attack
    let normal = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "character_melee_attacks",
            vec![
                Value::Entity(specialist),
                enum_variant("MeleeWeapon", "Dagger"),
                Value::Int(1),
            ],
        )
        .unwrap();
    assert_eq!(normal, Value::Int(1), "non-spec weapon L5: 1 attack");
}

// ── Constants used by tests ────────────────────────────────────

const DEFAULT_ABILITIES: [(&str, i64); 6] = [
    ("STR", 16),
    ("DEX", 14),
    ("CON", 15),
    ("INT", 10),
    ("WIS", 10),
    ("CHA", 10),
];
