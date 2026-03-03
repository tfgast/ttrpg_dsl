//! OSRIC class definitions integration test.
//!
//! Verifies that osric/osric_class.ttrpg parses, lowers, and type-checks
//! through the full multi-file pipeline (core + class). Exercises the
//! class_def derive for all 10 classes, xp_for_level table lookups,
//! and check_level_up logic at XP thresholds.

use std::collections::BTreeMap;

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_ast::diagnostic::Severity;
use ttrpg_ast::Name;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_class() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    let core_source = include_str!("../../../osric/osric_core.ttrpg");
    let class_source = include_str!("../../../osric/osric_class.ttrpg");

    let sources = vec![
        ("osric/osric_core.ttrpg".to_string(), core_source.to_string()),
        (
            "osric/osric_class.ttrpg".to_string(),
            class_source.to_string(),
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

struct NullHandler;
impl EffectHandler for NullHandler {
    fn handle(&mut self, _effect: Effect) -> Response {
        Response::Acknowledged
    }
}

fn class_variant(variant: &str) -> Value {
    Value::EnumVariant {
        enum_name: Name::from("Class"),
        variant: Name::from(variant),
        fields: BTreeMap::new(),
    }
}

/// Call class_def and return the ClassDef struct fields as a BTreeMap.
fn get_class_def(
    interp: &Interpreter,
    state: &GameState,
    handler: &mut NullHandler,
    class: &str,
) -> BTreeMap<String, Value> {
    let val = interp
        .evaluate_derive(state, handler, "class_def", vec![class_variant(class)])
        .unwrap_or_else(|e| panic!("class_def({class}) failed: {e}"));

    match val {
        Value::Struct { name, fields } => {
            assert_eq!(&*name, "ClassDef");
            fields
                .into_iter()
                .map(|(k, v)| (k.to_string(), v))
                .collect()
        }
        other => panic!("expected ClassDef struct, got: {other:?}"),
    }
}

fn get_int(fields: &BTreeMap<String, Value>, key: &str) -> i64 {
    match fields.get(key) {
        Some(Value::Int(n)) => *n,
        other => panic!("expected int for {key}, got: {other:?}"),
    }
}

fn get_bool(fields: &BTreeMap<String, Value>, key: &str) -> bool {
    match fields.get(key) {
        Some(Value::Bool(b)) => *b,
        other => panic!("expected bool for {key}, got: {other:?}"),
    }
}

fn get_enum_variant<'a>(fields: &'a BTreeMap<String, Value>, key: &'a str) -> (&'a str, &'a str) {
    match fields.get(key) {
        Some(Value::EnumVariant {
            enum_name,
            variant,
            ..
        }) => (enum_name.as_str(), variant.as_str()),
        other => panic!("expected enum variant for {key}, got: {other:?}"),
    }
}

fn get_xp(
    interp: &Interpreter,
    state: &GameState,
    handler: &mut NullHandler,
    class: &str,
    level: i64,
) -> i64 {
    let val = interp
        .evaluate_derive(
            state,
            handler,
            "xp_for_level",
            vec![class_variant(class), Value::Int(level)],
        )
        .unwrap_or_else(|e| panic!("xp_for_level({class}, {level}) failed: {e}"));

    match val {
        Value::Int(n) => n,
        other => panic!("expected int, got: {other:?}"),
    }
}

fn check_level_up(
    interp: &Interpreter,
    state: &GameState,
    handler: &mut NullHandler,
    class: &str,
    current_level: i64,
    xp: i64,
) -> bool {
    let val = interp
        .evaluate_derive(
            state,
            handler,
            "check_level_up",
            vec![
                class_variant(class),
                Value::Int(current_level),
                Value::Int(xp),
            ],
        )
        .unwrap_or_else(|e| panic!("check_level_up({class}, {current_level}, {xp}) failed: {e}"));

    match val {
        Value::Bool(b) => b,
        other => panic!("expected bool, got: {other:?}"),
    }
}

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn osric_class_parses_and_typechecks() {
    let (program, _) = compile_osric_class();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSRIC"));
    assert!(system_names.contains(&"OSRIC Classes"));
}

// ── Declaration structure ──────────────────────────────────────

#[test]
fn osric_class_has_class_def_derive() {
    let (program, _) = compile_osric_class();

    let mut found = false;
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSRIC Classes" {
                for decl in &sys.decls {
                    if let DeclKind::Derive(f) = &decl.node {
                        if f.name == "class_def" {
                            assert_eq!(f.params.len(), 1);
                            found = true;
                        }
                    }
                }
            }
        }
    }
    assert!(found, "expected class_def derive");
}

#[test]
fn osric_class_has_xp_table() {
    let (program, _) = compile_osric_class();

    let mut found = false;
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSRIC Classes" {
                for decl in &sys.decls {
                    if let DeclKind::Table(t) = &decl.node {
                        if t.name == "xp_for_level" {
                            assert_eq!(t.params.len(), 2);
                            // 10 classes × varying levels = 186 entries
                            assert_eq!(
                                t.entries.len(),
                                186,
                                "expected 186 xp_for_level entries, got {}",
                                t.entries.len()
                            );
                            found = true;
                        }
                    }
                }
            }
        }
    }
    assert!(found, "expected xp_for_level table");
}

#[test]
fn osric_class_has_check_level_up_derive() {
    let (program, _) = compile_osric_class();

    let mut found = false;
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSRIC Classes" {
                for decl in &sys.decls {
                    if let DeclKind::Derive(f) = &decl.node {
                        if f.name == "check_level_up" {
                            assert_eq!(f.params.len(), 3);
                            found = true;
                        }
                    }
                }
            }
        }
    }
    assert!(found, "expected check_level_up derive");
}

// ── class_def: Fighter ─────────────────────────────────────────

#[test]
fn class_def_fighter() {
    let (program, result) = compile_osric_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let def = get_class_def(&interp, &state, &mut handler, "Fighter");
    assert_eq!(get_int(&def, "hit_die"), 10);
    assert_eq!(get_int(&def, "max_hit_dice"), 9);
    assert_eq!(get_int(&def, "hp_after_max"), 3);
    assert_eq!(get_int(&def, "non_prof_penalty"), -2);
    assert_eq!(
        get_enum_variant(&def, "combat_group"),
        ("CombatGroup", "FighterGroup")
    );
    assert_eq!(
        get_enum_variant(&def, "armour"),
        ("ArmourPermission", "any_armour")
    );
    assert_eq!(
        get_enum_variant(&def, "spell_progression"),
        ("SpellProgression", "NonCaster")
    );
    assert_eq!(get_bool(&def, "shield_allowed"), true);
    assert_eq!(get_bool(&def, "weapons_any"), true);
    assert_eq!(get_bool(&def, "weapon_specialization"), true);
    assert_eq!(get_bool(&def, "has_thief_skills"), false);
    assert_eq!(get_bool(&def, "can_backstab"), false);
    assert_eq!(get_bool(&def, "can_turn_undead"), false);
    assert_eq!(get_bool(&def, "has_exceptional_str"), true);
}

// ── class_def: Paladin ─────────────────────────────────────────

#[test]
fn class_def_paladin() {
    let (program, result) = compile_osric_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let def = get_class_def(&interp, &state, &mut handler, "Paladin");
    assert_eq!(get_int(&def, "hit_die"), 10);
    assert_eq!(get_int(&def, "max_hit_dice"), 9);
    assert_eq!(get_int(&def, "hp_after_max"), 3);
    assert_eq!(
        get_enum_variant(&def, "combat_group"),
        ("CombatGroup", "FighterGroup")
    );
    assert_eq!(
        get_enum_variant(&def, "spell_progression"),
        ("SpellProgression", "Paladin")
    );
    assert_eq!(get_bool(&def, "weapon_specialization"), true);
    assert_eq!(get_bool(&def, "can_turn_undead"), true);
    assert_eq!(get_bool(&def, "has_exceptional_str"), true);
}

// ── class_def: Ranger ──────────────────────────────────────────

#[test]
fn class_def_ranger() {
    let (program, result) = compile_osric_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let def = get_class_def(&interp, &state, &mut handler, "Ranger");
    assert_eq!(get_int(&def, "hit_die"), 8);
    assert_eq!(get_int(&def, "max_hit_dice"), 10);
    assert_eq!(get_int(&def, "hp_after_max"), 2);
    assert_eq!(
        get_enum_variant(&def, "combat_group"),
        ("CombatGroup", "FighterGroup")
    );
    assert_eq!(
        get_enum_variant(&def, "spell_progression"),
        ("SpellProgression", "Ranger")
    );
    assert_eq!(get_bool(&def, "weapon_specialization"), true);
    assert_eq!(get_bool(&def, "has_exceptional_str"), true);
}

// ── class_def: Cleric ──────────────────────────────────────────

#[test]
fn class_def_cleric() {
    let (program, result) = compile_osric_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let def = get_class_def(&interp, &state, &mut handler, "Cleric");
    assert_eq!(get_int(&def, "hit_die"), 8);
    assert_eq!(get_int(&def, "max_hit_dice"), 9);
    assert_eq!(get_int(&def, "hp_after_max"), 2);
    assert_eq!(
        get_enum_variant(&def, "combat_group"),
        ("CombatGroup", "ClericGroup")
    );
    assert_eq!(
        get_enum_variant(&def, "armour"),
        ("ArmourPermission", "any_armour")
    );
    assert_eq!(
        get_enum_variant(&def, "spell_progression"),
        ("SpellProgression", "Cleric")
    );
    assert_eq!(get_bool(&def, "shield_allowed"), true);
    assert_eq!(get_bool(&def, "weapons_any"), false);
    assert_eq!(get_bool(&def, "can_turn_undead"), true);
}

// ── class_def: Druid ───────────────────────────────────────────

#[test]
fn class_def_druid() {
    let (program, result) = compile_osric_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let def = get_class_def(&interp, &state, &mut handler, "Druid");
    assert_eq!(get_int(&def, "hit_die"), 8);
    assert_eq!(get_int(&def, "max_hit_dice"), 14);
    assert_eq!(get_int(&def, "hp_after_max"), 1);
    assert_eq!(
        get_enum_variant(&def, "combat_group"),
        ("CombatGroup", "ClericGroup")
    );
    assert_eq!(
        get_enum_variant(&def, "armour"),
        ("ArmourPermission", "leather_wooden")
    );
    assert_eq!(
        get_enum_variant(&def, "spell_progression"),
        ("SpellProgression", "Druid")
    );
    assert_eq!(get_int(&def, "non_prof_penalty"), -4);
}

// ── class_def: Thief ───────────────────────────────────────────

#[test]
fn class_def_thief() {
    let (program, result) = compile_osric_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let def = get_class_def(&interp, &state, &mut handler, "Thief");
    assert_eq!(get_int(&def, "hit_die"), 6);
    assert_eq!(get_int(&def, "max_hit_dice"), 10);
    assert_eq!(get_int(&def, "hp_after_max"), 2);
    assert_eq!(
        get_enum_variant(&def, "combat_group"),
        ("CombatGroup", "ThiefGroup")
    );
    assert_eq!(
        get_enum_variant(&def, "armour"),
        ("ArmourPermission", "leather_only")
    );
    assert_eq!(
        get_enum_variant(&def, "spell_progression"),
        ("SpellProgression", "NonCaster")
    );
    assert_eq!(get_bool(&def, "shield_allowed"), false);
    assert_eq!(get_bool(&def, "weapons_any"), true);
    assert_eq!(get_bool(&def, "has_thief_skills"), true);
    assert_eq!(get_bool(&def, "can_backstab"), true);
}

// ── class_def: Assassin ────────────────────────────────────────

#[test]
fn class_def_assassin() {
    let (program, result) = compile_osric_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let def = get_class_def(&interp, &state, &mut handler, "Assassin");
    assert_eq!(get_int(&def, "hit_die"), 6);
    assert_eq!(get_int(&def, "max_hit_dice"), 15);
    assert_eq!(get_int(&def, "hp_after_max"), 1);
    assert_eq!(
        get_enum_variant(&def, "combat_group"),
        ("CombatGroup", "ThiefGroup")
    );
    assert_eq!(
        get_enum_variant(&def, "armour"),
        ("ArmourPermission", "leather_shield")
    );
    assert_eq!(get_bool(&def, "shield_allowed"), true);
    assert_eq!(get_bool(&def, "has_thief_skills"), true);
    assert_eq!(get_bool(&def, "can_backstab"), true);
}

// ── class_def: Magic-User ──────────────────────────────────────

#[test]
fn class_def_magic_user() {
    let (program, result) = compile_osric_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let def = get_class_def(&interp, &state, &mut handler, "MagicUser");
    assert_eq!(get_int(&def, "hit_die"), 4);
    assert_eq!(get_int(&def, "max_hit_dice"), 11);
    assert_eq!(get_int(&def, "hp_after_max"), 1);
    assert_eq!(
        get_enum_variant(&def, "combat_group"),
        ("CombatGroup", "MagicUserGroup")
    );
    assert_eq!(
        get_enum_variant(&def, "armour"),
        ("ArmourPermission", "no_armour")
    );
    assert_eq!(
        get_enum_variant(&def, "spell_progression"),
        ("SpellProgression", "MagicUser")
    );
    assert_eq!(get_bool(&def, "shield_allowed"), false);
    assert_eq!(get_bool(&def, "weapons_any"), false);
    assert_eq!(get_int(&def, "non_prof_penalty"), -5);
}

// ── class_def: Illusionist ─────────────────────────────────────

#[test]
fn class_def_illusionist() {
    let (program, result) = compile_osric_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let def = get_class_def(&interp, &state, &mut handler, "Illusionist");
    assert_eq!(get_int(&def, "hit_die"), 4);
    assert_eq!(get_int(&def, "max_hit_dice"), 10);
    assert_eq!(
        get_enum_variant(&def, "combat_group"),
        ("CombatGroup", "MagicUserGroup")
    );
    assert_eq!(
        get_enum_variant(&def, "spell_progression"),
        ("SpellProgression", "Illusionist")
    );
    assert_eq!(get_int(&def, "non_prof_penalty"), -5);
}

// ── class_def: Monk ────────────────────────────────────────────

#[test]
fn class_def_monk() {
    let (program, result) = compile_osric_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let def = get_class_def(&interp, &state, &mut handler, "Monk");
    assert_eq!(get_int(&def, "hit_die"), 4);
    assert_eq!(get_int(&def, "max_hit_dice"), 18);
    assert_eq!(get_int(&def, "hp_after_max"), 0);
    assert_eq!(
        get_enum_variant(&def, "combat_group"),
        ("CombatGroup", "ClericGroup")
    );
    assert_eq!(
        get_enum_variant(&def, "armour"),
        ("ArmourPermission", "no_armour")
    );
    assert_eq!(
        get_enum_variant(&def, "spell_progression"),
        ("SpellProgression", "NonCaster")
    );
    assert_eq!(get_bool(&def, "shield_allowed"), false);
    assert_eq!(get_bool(&def, "weapons_any"), false);
    assert_eq!(get_bool(&def, "has_thief_skills"), true);
    assert_eq!(get_bool(&def, "can_backstab"), false);
}

// ── class_def: all classes return a class field matching input ──

#[test]
fn class_def_returns_matching_class_field() {
    let (program, result) = compile_osric_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let classes = [
        "Fighter",
        "Paladin",
        "Ranger",
        "Cleric",
        "Druid",
        "Thief",
        "Assassin",
        "MagicUser",
        "Illusionist",
        "Monk",
    ];
    for class in &classes {
        let def = get_class_def(&interp, &state, &mut handler, class);
        assert_eq!(
            def.get("class"),
            Some(&class_variant(class)),
            "class_def({class}).class should be {class}"
        );
    }
}

// ── XP table: all classes start at 0 XP for level 1 ───────────

#[test]
fn xp_for_level_1_is_zero_for_all_classes() {
    let (program, result) = compile_osric_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let classes = [
        "Fighter",
        "Paladin",
        "Ranger",
        "Cleric",
        "Druid",
        "Thief",
        "Assassin",
        "MagicUser",
        "Illusionist",
        "Monk",
    ];
    for class in &classes {
        assert_eq!(
            get_xp(&interp, &state, &mut handler, class, 1),
            0,
            "{class} should need 0 XP for level 1"
        );
    }
}

// ── XP table: spot checks ─────────────────────────────────────

#[test]
fn xp_for_level_fighter_spot_checks() {
    let (program, result) = compile_osric_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    assert_eq!(get_xp(&interp, &state, &mut handler, "Fighter", 2), 2000);
    assert_eq!(get_xp(&interp, &state, &mut handler, "Fighter", 5), 17000);
    assert_eq!(get_xp(&interp, &state, &mut handler, "Fighter", 9), 250000);
    assert_eq!(
        get_xp(&interp, &state, &mut handler, "Fighter", 20),
        3000000
    );
}

#[test]
fn xp_for_level_thief_spot_checks() {
    let (program, result) = compile_osric_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    assert_eq!(get_xp(&interp, &state, &mut handler, "Thief", 2), 1250);
    assert_eq!(get_xp(&interp, &state, &mut handler, "Thief", 8), 70000);
    assert_eq!(get_xp(&interp, &state, &mut handler, "Thief", 12), 440000);
}

#[test]
fn xp_for_level_magic_user_spot_checks() {
    let (program, result) = compile_osric_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    assert_eq!(get_xp(&interp, &state, &mut handler, "MagicUser", 2), 2400);
    assert_eq!(
        get_xp(&interp, &state, &mut handler, "MagicUser", 4),
        10250
    );
    assert_eq!(
        get_xp(&interp, &state, &mut handler, "MagicUser", 10),
        250000
    );
    assert_eq!(
        get_xp(&interp, &state, &mut handler, "MagicUser", 18),
        3000000
    );
}

#[test]
fn xp_for_level_cleric_spot_checks() {
    let (program, result) = compile_osric_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    assert_eq!(get_xp(&interp, &state, &mut handler, "Cleric", 2), 1500);
    assert_eq!(get_xp(&interp, &state, &mut handler, "Cleric", 7), 55000);
    assert_eq!(
        get_xp(&interp, &state, &mut handler, "Cleric", 20),
        2700000
    );
}

#[test]
fn xp_for_level_assassin_spot_checks() {
    let (program, result) = compile_osric_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    assert_eq!(get_xp(&interp, &state, &mut handler, "Assassin", 2), 1500);
    assert_eq!(get_xp(&interp, &state, &mut handler, "Assassin", 8), 100000);
    assert_eq!(
        get_xp(&interp, &state, &mut handler, "Assassin", 15),
        1500000
    );
}

#[test]
fn xp_for_level_monk_spot_checks() {
    let (program, result) = compile_osric_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    assert_eq!(get_xp(&interp, &state, &mut handler, "Monk", 3), 5000);
    assert_eq!(get_xp(&interp, &state, &mut handler, "Monk", 9), 350000);
    assert_eq!(
        get_xp(&interp, &state, &mut handler, "Monk", 17),
        3250000
    );
}

#[test]
fn xp_for_level_paladin_spot_checks() {
    let (program, result) = compile_osric_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    assert_eq!(get_xp(&interp, &state, &mut handler, "Paladin", 2), 2550);
    assert_eq!(get_xp(&interp, &state, &mut handler, "Paladin", 9), 325000);
    assert_eq!(
        get_xp(&interp, &state, &mut handler, "Paladin", 20),
        4150000
    );
}

#[test]
fn xp_for_level_ranger_spot_checks() {
    let (program, result) = compile_osric_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    assert_eq!(get_xp(&interp, &state, &mut handler, "Ranger", 2), 2250);
    assert_eq!(get_xp(&interp, &state, &mut handler, "Ranger", 8), 90000);
    assert_eq!(
        get_xp(&interp, &state, &mut handler, "Ranger", 20),
        3250000
    );
}

#[test]
fn xp_for_level_druid_spot_checks() {
    let (program, result) = compile_osric_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    assert_eq!(get_xp(&interp, &state, &mut handler, "Druid", 2), 2000);
    assert_eq!(get_xp(&interp, &state, &mut handler, "Druid", 9), 90000);
    assert_eq!(
        get_xp(&interp, &state, &mut handler, "Druid", 14),
        1500000
    );
}

#[test]
fn xp_for_level_illusionist_spot_checks() {
    let (program, result) = compile_osric_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    assert_eq!(
        get_xp(&interp, &state, &mut handler, "Illusionist", 2),
        2500
    );
    assert_eq!(
        get_xp(&interp, &state, &mut handler, "Illusionist", 7),
        60000
    );
    assert_eq!(
        get_xp(&interp, &state, &mut handler, "Illusionist", 20),
        2420000
    );
}

// ── XP increases monotonically ─────────────────────────────────

#[test]
fn xp_increases_monotonically_for_all_classes() {
    let (program, result) = compile_osric_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let class_max_levels = [
        ("Fighter", 20),
        ("Paladin", 20),
        ("Ranger", 20),
        ("Cleric", 20),
        ("Druid", 14),
        ("Thief", 20),
        ("Assassin", 15),
        ("MagicUser", 20),
        ("Illusionist", 20),
        ("Monk", 17),
    ];

    for (class, max_level) in &class_max_levels {
        let mut prev = 0;
        for level in 1..=*max_level {
            let xp = get_xp(&interp, &state, &mut handler, class, level);
            assert!(
                xp >= prev,
                "{class} XP should increase: level {level} ({xp}) < level {} ({prev})",
                level - 1
            );
            prev = xp;
        }
    }
}

// ── check_level_up: just below, at, and above thresholds ───────

#[test]
fn check_level_up_fighter_below_threshold() {
    let (program, result) = compile_osric_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Fighter level 2 requires 2000 XP. At 1999 XP, should NOT level up.
    assert!(!check_level_up(
        &interp, &state, &mut handler, "Fighter", 1, 1999
    ));
}

#[test]
fn check_level_up_fighter_at_threshold() {
    let (program, result) = compile_osric_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Fighter level 2 requires 2000 XP. At exactly 2000, should level up.
    assert!(check_level_up(
        &interp, &state, &mut handler, "Fighter", 1, 2000
    ));
}

#[test]
fn check_level_up_fighter_above_threshold() {
    let (program, result) = compile_osric_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Fighter level 2 requires 2000 XP. At 5000, should level up.
    assert!(check_level_up(
        &interp, &state, &mut handler, "Fighter", 1, 5000
    ));
}

#[test]
fn check_level_up_thief_below_threshold() {
    let (program, result) = compile_osric_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Thief level 5 requires 10000 XP. At 9999, should NOT level up from 4.
    assert!(!check_level_up(
        &interp, &state, &mut handler, "Thief", 4, 9999
    ));
}

#[test]
fn check_level_up_thief_at_threshold() {
    let (program, result) = compile_osric_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Thief level 5 requires 10000 XP.
    assert!(check_level_up(
        &interp, &state, &mut handler, "Thief", 4, 10000
    ));
}

#[test]
fn check_level_up_magic_user_mid_level() {
    let (program, result) = compile_osric_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // MagicUser level 10 requires 250000 XP. At 249999, should NOT level from 9.
    assert!(!check_level_up(
        &interp,
        &state,
        &mut handler,
        "MagicUser",
        9,
        249999
    ));
    assert!(check_level_up(
        &interp,
        &state,
        &mut handler,
        "MagicUser",
        9,
        250000
    ));
}

#[test]
fn check_level_up_cleric_high_level() {
    let (program, result) = compile_osric_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Cleric level 20 requires 2700000 XP. At 2699999, should NOT level from 19.
    assert!(!check_level_up(
        &interp,
        &state,
        &mut handler,
        "Cleric",
        19,
        2699999
    ));
    assert!(check_level_up(
        &interp,
        &state,
        &mut handler,
        "Cleric",
        19,
        2700000
    ));
}

// ── Fighter group shares combat_group ──────────────────────────

#[test]
fn fighter_group_shares_combat_group() {
    let (program, result) = compile_osric_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    for class in &["Fighter", "Paladin", "Ranger"] {
        let def = get_class_def(&interp, &state, &mut handler, class);
        assert_eq!(
            get_enum_variant(&def, "combat_group"),
            ("CombatGroup", "FighterGroup"),
            "{class} should be in FighterGroup"
        );
    }
}

// ── Thief group: backstab + thief skills ───────────────────────

#[test]
fn thief_group_has_thief_skills_and_backstab() {
    let (program, result) = compile_osric_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    for class in &["Thief", "Assassin"] {
        let def = get_class_def(&interp, &state, &mut handler, class);
        assert_eq!(
            get_bool(&def, "has_thief_skills"),
            true,
            "{class} should have thief skills"
        );
        assert_eq!(
            get_bool(&def, "can_backstab"),
            true,
            "{class} should be able to backstab"
        );
    }
}

// ── Caster classes have spell progressions ─────────────────────

#[test]
fn caster_classes_have_spell_progression() {
    let (program, result) = compile_osric_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let expected = [
        ("Cleric", "Cleric"),
        ("Druid", "Druid"),
        ("MagicUser", "MagicUser"),
        ("Illusionist", "Illusionist"),
        ("Paladin", "Paladin"),
        ("Ranger", "Ranger"),
    ];
    for (class, progression) in &expected {
        let def = get_class_def(&interp, &state, &mut handler, class);
        assert_eq!(
            get_enum_variant(&def, "spell_progression"),
            ("SpellProgression", *progression),
            "{class} should have {progression} spell progression"
        );
    }
}

#[test]
fn non_caster_classes_have_non_caster_progression() {
    let (program, result) = compile_osric_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    for class in &["Fighter", "Thief", "Assassin", "Monk"] {
        let def = get_class_def(&interp, &state, &mut handler, class);
        assert_eq!(
            get_enum_variant(&def, "spell_progression"),
            ("SpellProgression", "NonCaster"),
            "{class} should be NonCaster"
        );
    }
}

// ── Exceptional strength: only fighter-type classes ─────────────

#[test]
fn exceptional_str_only_fighter_types() {
    let (program, result) = compile_osric_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let with_exc_str = ["Fighter", "Paladin", "Ranger"];
    let without = [
        "Cleric",
        "Druid",
        "Thief",
        "Assassin",
        "MagicUser",
        "Illusionist",
        "Monk",
    ];

    for class in &with_exc_str {
        let def = get_class_def(&interp, &state, &mut handler, class);
        assert_eq!(
            get_bool(&def, "has_exceptional_str"),
            true,
            "{class} should have exceptional strength"
        );
    }
    for class in &without {
        let def = get_class_def(&interp, &state, &mut handler, class);
        assert_eq!(
            get_bool(&def, "has_exceptional_str"),
            false,
            "{class} should NOT have exceptional strength"
        );
    }
}
