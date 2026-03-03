//! OSRIC combat integration test.
//!
//! Verifies that osric/osric_combat.ttrpg parses, lowers, and type-checks
//! through the full multi-file pipeline (core + ability + class + equipment +
//! combat). Exercises BTHB tables for all 4 combat groups, fighter_attacks,
//! missile_range_penalty, attack_roll_aac, damage_roll,
//! resolve_melee_attack, resolve_missile_attack, resolve_monster_attack,
//! Damaged/CreatureSlain events, and MeleeAttack/MissileAttack/Charge actions.

use std::collections::{BTreeMap, VecDeque};

use rustc_hash::FxHashMap;
use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_ast::diagnostic::Severity;
use ttrpg_ast::Name;
use ttrpg_interp::adapter::StateAdapter;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::{EntityRef, StateProvider};
use ttrpg_interp::value::{DiceExpr, RollResult, Value};
use ttrpg_interp::Interpreter;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_combat() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    let core_source = include_str!("../../../osric/osric_core.ttrpg");
    let ability_source = include_str!("../../../osric/osric_ability.ttrpg");
    let class_source = include_str!("../../../osric/osric_class.ttrpg");
    let equipment_source = include_str!("../../../osric/osric_equipment.ttrpg");
    let combat_source = include_str!("../../../osric/osric_combat.ttrpg");

    let sources = vec![
        ("osric/osric_core.ttrpg".to_string(), core_source.to_string()),
        (
            "osric/osric_ability.ttrpg".to_string(),
            ability_source.to_string(),
        ),
        (
            "osric/osric_class.ttrpg".to_string(),
            class_source.to_string(),
        ),
        (
            "osric/osric_equipment.ttrpg".to_string(),
            equipment_source.to_string(),
        ),
        (
            "osric/osric_combat.ttrpg".to_string(),
            combat_source.to_string(),
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

/// Extract all DeclKind items from the "OSRIC Combat" system block.
fn get_combat_decls(program: &ttrpg_ast::ast::Program) -> &[ttrpg_ast::Spanned<DeclKind>] {
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSRIC Combat" {
                return &sys.decls;
            }
        }
    }
    panic!("no system block named 'OSRIC Combat' found");
}

// ── Value helpers ──────────────────────────────────────────────

fn enum_variant(enum_name: &str, variant: &str) -> Value {
    Value::EnumVariant {
        enum_name: Name::from(enum_name),
        variant: Name::from(variant),
        fields: BTreeMap::new(),
    }
}

fn class_variant(variant: &str) -> Value {
    enum_variant("Class", variant)
}

fn ability(variant: &str) -> Value {
    enum_variant("Ability", variant)
}

fn feet(value: i64) -> Value {
    Value::Struct {
        name: Name::from("Feet"),
        fields: {
            let mut f = BTreeMap::new();
            f.insert(Name::from("value"), Value::Int(value));
            f
        },
    }
}

fn monster_attack(name: &str, count: u32, sides: u32, bonus: i64) -> Value {
    Value::Struct {
        name: Name::from("MonsterAttack"),
        fields: {
            let mut f = BTreeMap::new();
            f.insert(Name::from("name"), Value::Str(name.to_string()));
            f.insert(
                Name::from("damage"),
                Value::DiceExpr(DiceExpr::single(count, sides, None, bonus)),
            );
            f
        },
    }
}

// ── Effect handler ─────────────────────────────────────────────

struct NullHandler;
impl EffectHandler for NullHandler {
    fn handle(&mut self, _effect: Effect) -> Response {
        Response::Acknowledged
    }
}

struct ScriptedHandler {
    script: VecDeque<Response>,
    log: Vec<Effect>,
}

impl ScriptedHandler {
    fn with_responses(responses: Vec<Response>) -> Self {
        ScriptedHandler {
            script: responses.into(),
            log: Vec::new(),
        }
    }
}

impl EffectHandler for ScriptedHandler {
    fn handle(&mut self, effect: Effect) -> Response {
        self.log.push(effect);
        self.script.pop_front().unwrap_or(Response::Acknowledged)
    }
}

fn scripted_roll(
    count: u32,
    sides: u32,
    modifier: i64,
    dice_vals: Vec<i64>,
    kept_vals: Vec<i64>,
    total: i64,
    unmodified: i64,
) -> Response {
    Response::Rolled(RollResult {
        expr: DiceExpr::single(count, sides, None, modifier),
        dice: dice_vals,
        kept: kept_vals,
        modifier,
        total,
        unmodified,
    })
}

// ── Entity builders ────────────────────────────────────────────

/// Build a Character entity with customizable fields.
fn make_character(
    state: &mut GameState,
    name: &str,
    class: &str,
    level: i64,
    abilities: &[(&str, i64)],
    max_hp: i64,
    ac: i64,
    ancestry: &str,
) -> EntityRef {
    let mut ability_map = BTreeMap::new();
    for &(ab, score) in abilities {
        ability_map.insert(ability(ab), Value::Int(score));
    }

    let mut fields = FxHashMap::default();
    fields.insert(Name::from("name"), Value::Str(name.to_string()));
    fields.insert(Name::from("class"), class_variant(class));
    fields.insert(Name::from("ancestry"), enum_variant("Ancestry", ancestry));
    fields.insert(Name::from("level"), Value::Int(level));
    fields.insert(
        Name::from("alignment"),
        enum_variant("Alignment", "TrueNeutral"),
    );
    fields.insert(Name::from("abilities"), Value::Map(ability_map));
    fields.insert(Name::from("max_hp"), Value::Int(max_hp));
    fields.insert(Name::from("hp"), Value::Int(max_hp));
    fields.insert(Name::from("armor_ac"), Value::Int(ac));
    fields.insert(Name::from("shield_ac_bonus"), Value::Int(0));
    fields.insert(Name::from("xp"), Value::Int(0));
    fields.insert(Name::from("base_movement"), feet(120));
    fields.insert(Name::from("gold"), Value::Int(0));
    fields.insert(Name::from("saving_throws"), Value::Option(None));

    state.add_entity("Character", fields)
}

/// Build a Monster entity.
fn make_monster(
    state: &mut GameState,
    name: &str,
    hit_dice: i64,
    max_hp: i64,
    ac: i64,
    attacks: Vec<Value>,
) -> EntityRef {
    let mut fields = FxHashMap::default();
    fields.insert(Name::from("name"), Value::Str(name.to_string()));
    fields.insert(Name::from("hit_dice"), Value::Int(hit_dice));
    fields.insert(Name::from("max_hp"), Value::Int(max_hp));
    fields.insert(Name::from("hp"), Value::Int(max_hp));
    fields.insert(Name::from("ac"), Value::Int(ac));
    fields.insert(Name::from("morale"), Value::Int(7));
    fields.insert(Name::from("xp_value"), Value::Int(0));
    fields.insert(Name::from("attacks"), Value::List(attacks));
    fields.insert(
        Name::from("size"),
        enum_variant("Size", "Medium"),
    );
    fields.insert(Name::from("special"), Value::List(vec![]));

    state.add_entity("Monster", fields)
}

/// Standard abilities: all 12s (no modifiers).
fn standard_abilities() -> Vec<(&'static str, i64)> {
    vec![
        ("STR", 12),
        ("DEX", 12),
        ("CON", 12),
        ("INT", 12),
        ("WIS", 12),
        ("CHA", 12),
    ]
}

/// Turn budget for OSRIC combat: just `attack` token.
fn combat_turn_budget() -> BTreeMap<Name, Value> {
    let mut b = BTreeMap::new();
    b.insert("attack".into(), Value::Int(1));
    b
}

fn get_int(fields: &BTreeMap<String, Value>, key: &str) -> i64 {
    match fields.get(key) {
        Some(Value::Int(n)) => *n,
        other => panic!("expected int for '{key}', got: {other:?}"),
    }
}

#[allow(dead_code)]
fn get_struct_fields(
    interp: &Interpreter,
    state: &GameState,
    handler: &mut dyn EffectHandler,
    name: &str,
    args: Vec<Value>,
    expected_struct: &str,
) -> BTreeMap<String, Value> {
    let val = interp
        .evaluate_derive(state, handler, name, args)
        .unwrap_or_else(|e| panic!("{name} failed: {e}"));

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

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn osric_combat_parses_and_typechecks() {
    let (program, _) = compile_osric_combat();
    let has_system = program.items.iter().any(
        |item| matches!(&item.node, TopLevel::System(sys) if sys.name == "OSRIC Combat"),
    );
    assert!(has_system, "expected system named 'OSRIC Combat'");
}

// ── Structure verification ─────────────────────────────────────

#[test]
fn osric_combat_has_enums() {
    let (program, _) = compile_osric_combat();
    let decls = get_combat_decls(&program);
    let enums: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Enum(e) => Some((&*e.name, e.variants.len())),
            _ => None,
        })
        .collect();
    assert!(enums.contains(&("AttackOutcome", 2)));
    assert!(enums.contains(&("Duration", 3)));
    assert!(enums.contains(&("SurpriseState", 4)));
}

#[test]
fn osric_combat_has_structs() {
    let (program, _) = compile_osric_combat();
    let decls = get_combat_decls(&program);
    let structs: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Struct(s) => Some((&*s.name, s.fields.len())),
            _ => None,
        })
        .collect();
    assert!(
        structs.contains(&("AttackResult", 3)),
        "missing AttackResult with 3 fields"
    );
    assert!(
        structs.contains(&("TurnBudget", 1)),
        "missing TurnBudget with 1 field"
    );
    assert!(
        structs.contains(&("EncounterStart", 4)),
        "missing EncounterStart with 4 fields"
    );
}

#[test]
fn osric_combat_has_tables() {
    let (program, _) = compile_osric_combat();
    let decls = get_combat_decls(&program);
    let tables: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Table(t) => Some(&*t.name),
            _ => None,
        })
        .collect();
    assert!(tables.contains(&"cleric_group_bthb"));
    assert!(tables.contains(&"thief_group_bthb"));
    assert!(tables.contains(&"magic_user_group_bthb"));
    assert!(tables.contains(&"monster_bthb"));
}

#[test]
fn osric_combat_has_derives() {
    let (program, _) = compile_osric_combat();
    let decls = get_combat_decls(&program);
    let derives: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Derive(d) => Some(&*d.name),
            _ => None,
        })
        .collect();
    assert!(derives.contains(&"fighter_group_bthb"));
    assert!(derives.contains(&"bthb"));
    assert!(derives.contains(&"fighter_attacks"));
    assert!(derives.contains(&"missile_range_penalty"));
}

#[test]
fn osric_combat_has_mechanics() {
    let (program, _) = compile_osric_combat();
    let decls = get_combat_decls(&program);
    let mechanics: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Mechanic(m) => Some(&*m.name),
            _ => None,
        })
        .collect();
    assert!(mechanics.contains(&"attack_roll_aac"));
    assert!(mechanics.contains(&"damage_roll"));
    assert!(mechanics.contains(&"resolve_melee_attack"));
    assert!(mechanics.contains(&"resolve_missile_attack"));
    assert!(mechanics.contains(&"resolve_monster_attack"));
    assert!(mechanics.contains(&"surprise_roll"));
    assert!(mechanics.contains(&"encounter_distance"));
    assert!(mechanics.contains(&"group_initiative"));
    assert!(mechanics.contains(&"encounter_sequence"));
}

#[test]
fn osric_combat_has_events() {
    let (program, _) = compile_osric_combat();
    let decls = get_combat_decls(&program);
    let events: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Event(e) => Some(&*e.name),
            _ => None,
        })
        .collect();
    assert!(events.contains(&"Damaged"));
    assert!(events.contains(&"CreatureSlain"));
}

#[test]
fn osric_combat_has_actions() {
    let (program, _) = compile_osric_combat();
    let decls = get_combat_decls(&program);
    let actions: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Action(a) => Some(&*a.name),
            _ => None,
        })
        .collect();
    assert!(actions.contains(&"MeleeAttack"));
    assert!(actions.contains(&"MissileAttack"));
    assert!(actions.contains(&"Charge"));
}

// ── BTHB tables ────────────────────────────────────────────────

#[test]
fn fighter_group_bthb_is_linear() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Fighter BTHB = level - 1
    let cases = vec![
        (1, 0),
        (5, 4),
        (7, 6),
        (10, 9),
        (13, 12),
        (20, 19),
    ];

    for (level, expected) in cases {
        let val = interp
            .evaluate_derive(
                &state,
                &mut handler,
                "fighter_group_bthb",
                vec![Value::Int(level)],
            )
            .unwrap();
        assert_eq!(
            val,
            Value::Int(expected),
            "fighter_group_bthb({level}) should be {expected}"
        );
    }
}

#[test]
fn cleric_group_bthb_step_function() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Cleric BTHB: 1-3=0, 4-6=2, 7-10=4, 11-12=6, 13-15=8, 16-18=10, 19+=11
    let cases = vec![
        (1, 0),
        (3, 0),
        (4, 2),
        (6, 2),
        (7, 4),
        (10, 4),
        (11, 6),
        (12, 6),
        (13, 8),
        (15, 8),
        (16, 10),
        (18, 10),
        (19, 11),
        (25, 11),
    ];

    for (level, expected) in cases {
        let val = interp
            .evaluate_derive(
                &state,
                &mut NullHandler,
                "cleric_group_bthb",
                vec![Value::Int(level)],
            )
            .unwrap();
        assert_eq!(
            val,
            Value::Int(expected),
            "cleric_group_bthb({level}) should be {expected}"
        );
    }
}

#[test]
fn thief_group_bthb_step_function() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Thief BTHB: 1-4=-1, 5-8=1, 9-12=4, 13-17=6, 18+=8
    let cases = vec![
        (1, -1),
        (4, -1),
        (5, 1),
        (8, 1),
        (9, 4),
        (12, 4),
        (13, 6),
        (17, 6),
        (18, 8),
        (25, 8),
    ];

    for (level, expected) in cases {
        let val = interp
            .evaluate_derive(
                &state,
                &mut NullHandler,
                "thief_group_bthb",
                vec![Value::Int(level)],
            )
            .unwrap();
        assert_eq!(
            val,
            Value::Int(expected),
            "thief_group_bthb({level}) should be {expected}"
        );
    }
}

#[test]
fn magic_user_group_bthb_step_function() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // MU BTHB: 1-5=-1, 6-10=1, 11-15=3, 16+=5
    let cases = vec![
        (1, -1),
        (5, -1),
        (6, 1),
        (10, 1),
        (11, 3),
        (15, 3),
        (16, 5),
        (25, 5),
    ];

    for (level, expected) in cases {
        let val = interp
            .evaluate_derive(
                &state,
                &mut NullHandler,
                "magic_user_group_bthb",
                vec![Value::Int(level)],
            )
            .unwrap();
        assert_eq!(
            val,
            Value::Int(expected),
            "magic_user_group_bthb({level}) should be {expected}"
        );
    }
}

#[test]
fn bthb_dispatches_by_combat_group() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Fighter level 5 → fighter_group_bthb(5) = 4
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "bthb",
            vec![class_variant("Fighter"), Value::Int(5)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(4));

    // Cleric level 7 → cleric_group_bthb(7) = 4
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "bthb",
            vec![class_variant("Cleric"), Value::Int(7)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(4));

    // Thief level 5 → thief_group_bthb(5) = 1
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "bthb",
            vec![class_variant("Thief"), Value::Int(5)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(1));

    // MagicUser level 1 → magic_user_group_bthb(1) = -1
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "bthb",
            vec![class_variant("MagicUser"), Value::Int(1)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(-1));
}

#[test]
fn bthb_all_classes_resolve() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Fighter group: Fighter, Paladin, Ranger → level-1
    for class in ["Fighter", "Paladin", "Ranger"] {
        let val = interp
            .evaluate_derive(
                &state,
                &mut handler,
                "bthb",
                vec![class_variant(class), Value::Int(10)],
            )
            .unwrap();
        assert_eq!(
            val,
            Value::Int(9),
            "{class} level 10 should have BTHB 9"
        );
    }

    // Cleric group: Cleric, Druid, Monk → 7-10=4
    for class in ["Cleric", "Druid", "Monk"] {
        let val = interp
            .evaluate_derive(
                &state,
                &mut handler,
                "bthb",
                vec![class_variant(class), Value::Int(10)],
            )
            .unwrap();
        assert_eq!(
            val,
            Value::Int(4),
            "{class} level 10 should have BTHB 4"
        );
    }

    // Thief group: Thief, Assassin → 5-8=1
    for class in ["Thief", "Assassin"] {
        let val = interp
            .evaluate_derive(
                &state,
                &mut handler,
                "bthb",
                vec![class_variant(class), Value::Int(5)],
            )
            .unwrap();
        assert_eq!(
            val,
            Value::Int(1),
            "{class} level 5 should have BTHB 1"
        );
    }

    // MU group: MagicUser, Illusionist → 6-10=1
    for class in ["MagicUser", "Illusionist"] {
        let val = interp
            .evaluate_derive(
                &state,
                &mut handler,
                "bthb",
                vec![class_variant(class), Value::Int(6)],
            )
            .unwrap();
        assert_eq!(
            val,
            Value::Int(1),
            "{class} level 6 should have BTHB 1"
        );
    }
}

#[test]
fn monster_bthb_all_tiers() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // monster_bthb: HD 0=-1, 1=1, 2-3=4, 4-5=5, 6-7=7, 8-9=8, 10-11=10,
    // 12-13=11, 14-15=12, 16+=13
    let cases = vec![
        (0, -1),
        (1, 1),
        (2, 4),
        (3, 4),
        (4, 5),
        (5, 5),
        (6, 7),
        (7, 7),
        (8, 8),
        (9, 8),
        (10, 10),
        (11, 10),
        (12, 11),
        (13, 11),
        (14, 12),
        (15, 12),
        (16, 13),
        (25, 13),
    ];

    for (hd, expected) in cases {
        let val = interp
            .evaluate_derive(
                &state,
                &mut NullHandler,
                "monster_bthb",
                vec![Value::Int(hd)],
            )
            .unwrap();
        assert_eq!(
            val,
            Value::Int(expected),
            "monster_bthb({hd}) should be {expected}"
        );
    }
}

// ── Fighter multiple attacks ───────────────────────────────────

#[test]
fn fighter_attacks_single_at_low_level() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Level 1-6: always 1 attack
    for level in 1..=6 {
        for round in 1..=4 {
            let val = interp
                .evaluate_derive(
                    &state,
                    &mut handler,
                    "fighter_attacks",
                    vec![Value::Int(level), Value::Int(round)],
                )
                .unwrap();
            assert_eq!(
                val,
                Value::Int(1),
                "level {level} round {round} should have 1 attack"
            );
        }
    }
}

#[test]
fn fighter_attacks_three_halves_at_mid_level() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Level 7-12: 3/2 attacks → alternates 1 and 2 based on round parity
    // even round = 2, odd round = 1
    for level in [7, 10, 12] {
        let r1 = interp
            .evaluate_derive(
                &state,
                &mut handler,
                "fighter_attacks",
                vec![Value::Int(level), Value::Int(1)],
            )
            .unwrap();
        assert_eq!(r1, Value::Int(1), "level {level} odd round: 1 attack");

        let r2 = interp
            .evaluate_derive(
                &state,
                &mut handler,
                "fighter_attacks",
                vec![Value::Int(level), Value::Int(2)],
            )
            .unwrap();
        assert_eq!(r2, Value::Int(2), "level {level} even round: 2 attacks");

        let r3 = interp
            .evaluate_derive(
                &state,
                &mut handler,
                "fighter_attacks",
                vec![Value::Int(level), Value::Int(3)],
            )
            .unwrap();
        assert_eq!(r3, Value::Int(1), "level {level} odd round: 1 attack");
    }
}

#[test]
fn fighter_attacks_two_at_high_level() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Level 13+: always 2 attacks
    for level in [13, 15, 20] {
        for round in 1..=4 {
            let val = interp
                .evaluate_derive(
                    &state,
                    &mut handler,
                    "fighter_attacks",
                    vec![Value::Int(level), Value::Int(round)],
                )
                .unwrap();
            assert_eq!(
                val,
                Value::Int(2),
                "level {level} round {round} should have 2 attacks"
            );
        }
    }
}

// ── Missile range penalty ──────────────────────────────────────

#[test]
fn missile_range_penalty_first_increment() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Distance within first range increment: 0 increments beyond = 0 penalty
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "missile_range_penalty",
            vec![feet(50), feet(70)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(0));
}

#[test]
fn missile_range_penalty_second_increment() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Distance 100ft, increment 70ft → floor(100/70) = 1 beyond → -2
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "missile_range_penalty",
            vec![feet(100), feet(70)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(-2));
}

#[test]
fn missile_range_penalty_third_increment() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Distance 150ft, increment 70ft → floor(150/70) = 2 beyond → -4
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "missile_range_penalty",
            vec![feet(150), feet(70)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(-4));
}

#[test]
fn missile_range_penalty_zero_distance() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Distance 0 → 0 increments beyond → 0 penalty
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "missile_range_penalty",
            vec![feet(0), feet(70)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(0));
}

#[test]
fn missile_range_penalty_errors_on_zero_increment() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let err = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "missile_range_penalty",
            vec![feet(50), feet(0)],
        )
        .unwrap_err();
    assert!(
        err.message.contains("range_increment must be positive"),
        "unexpected error: {}",
        err.message
    );
}

// ── attack_roll_aac mechanic ───────────────────────────────────

#[test]
fn attack_roll_aac_natural_1_always_misses() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Natural 1 → always miss, even with huge bonuses
    let roll = scripted_roll(1, 20, 0, vec![1], vec![1], 1, 1);
    let mut handler = ScriptedHandler::with_responses(vec![roll]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "attack_roll_aac",
            vec![Value::Int(20), Value::Int(5), Value::Int(10)],
        )
        .unwrap();
    assert_eq!(val, enum_variant("AttackOutcome", "Miss"));
}

#[test]
fn attack_roll_aac_natural_20_gets_bonus() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Natural 20 gets +5 bonus → 20+0+0+5 = 25, hits AC 25
    let roll = scripted_roll(1, 20, 0, vec![20], vec![20], 20, 20);
    let mut handler = ScriptedHandler::with_responses(vec![roll]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "attack_roll_aac",
            vec![Value::Int(0), Value::Int(25)],
        )
        .unwrap();
    assert_eq!(val, enum_variant("AttackOutcome", "Hit"));
}

#[test]
fn attack_roll_aac_standard_hit() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // attack_bonus=4, target_ac=15, roll 11 → 11+4 = 15 >= 15 → Hit
    let roll = scripted_roll(1, 20, 0, vec![11], vec![11], 11, 11);
    let mut handler = ScriptedHandler::with_responses(vec![roll]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "attack_roll_aac",
            vec![Value::Int(4), Value::Int(15)],
        )
        .unwrap();
    assert_eq!(val, enum_variant("AttackOutcome", "Hit"));
}

#[test]
fn attack_roll_aac_standard_miss() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // attack_bonus=4, target_ac=15, roll 10 → 10+4 = 14 < 15 → Miss
    let roll = scripted_roll(1, 20, 0, vec![10], vec![10], 10, 10);
    let mut handler = ScriptedHandler::with_responses(vec![roll]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "attack_roll_aac",
            vec![Value::Int(4), Value::Int(15)],
        )
        .unwrap();
    assert_eq!(val, enum_variant("AttackOutcome", "Miss"));
}

#[test]
fn attack_roll_aac_with_attack_mod() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // attack_bonus=2, target_ac=15, attack_mod=3, roll 10 → 10+2+3 = 15 → Hit
    let roll = scripted_roll(1, 20, 0, vec![10], vec![10], 10, 10);
    let mut handler = ScriptedHandler::with_responses(vec![roll]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "attack_roll_aac",
            vec![Value::Int(2), Value::Int(15), Value::Int(3)],
        )
        .unwrap();
    assert_eq!(val, enum_variant("AttackOutcome", "Hit"));
}

// ── damage_roll mechanic ──────────────────────────────────────

#[test]
fn damage_roll_normal_roll() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // 1d8, damage_mod=0, roll 5 → max(1, 5+0) = 5
    let roll = scripted_roll(1, 8, 0, vec![5], vec![5], 5, 5);
    let mut handler = ScriptedHandler::with_responses(vec![roll]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "damage_roll",
            vec![Value::DiceExpr(DiceExpr::single(1, 8, None, 0))],
        )
        .unwrap();
    assert_eq!(val, Value::Int(5));
}

#[test]
fn damage_roll_with_bonus_and_mod() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // 1d6+1, damage_mod=2, roll 3 → total=3+1=4, max(1, 4+2) = 6
    let roll = scripted_roll(1, 6, 1, vec![3], vec![3], 4, 3);
    let mut handler = ScriptedHandler::with_responses(vec![roll]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "damage_roll",
            vec![
                Value::DiceExpr(DiceExpr::single(1, 6, None, 1)),
                Value::Int(2),
            ],
        )
        .unwrap();
    assert_eq!(val, Value::Int(6));
}

#[test]
fn damage_roll_minimum_is_one() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // 1d4, damage_mod=-10, roll 1 → max(1, 1+(-10)) = max(1, -9) = 1
    let roll = scripted_roll(1, 4, 0, vec![1], vec![1], 1, 1);
    let mut handler = ScriptedHandler::with_responses(vec![roll]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "damage_roll",
            vec![
                Value::DiceExpr(DiceExpr::single(1, 4, None, 0)),
                Value::Int(-10),
            ],
        )
        .unwrap();
    assert_eq!(val, Value::Int(1));
}

// ── resolve_melee_attack mechanic ──────────────────────────────

#[test]
fn resolve_melee_attack_hit_deals_damage() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    // Fighter level 5 (BTHB=4), STR 12 (str_to_hit=0, str_damage=0)
    // Target AC 14, Human (Medium)
    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities(),
        30,
        15,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        14,
        "Human",
    );

    // attack_roll_aac: roll 15 → 15+4+0+0 = 19 >= 14 → Hit
    let atk_roll = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    // damage_roll: SwordLong damage_sm = 1d8, roll 6
    let dmg_roll = scripted_roll(1, 8, 0, vec![6], vec![6], 6, 6);
    let mut handler = ScriptedHandler::with_responses(vec![atk_roll, dmg_roll]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "resolve_melee_attack",
            vec![
                Value::Entity(attacker),
                Value::Entity(target),
                enum_variant("MeleeWeapon", "SwordLong"),
            ],
        )
        .unwrap();

    match val {
        Value::Struct { name, fields } => {
            assert_eq!(&*name, "AttackResult");
            let fields: BTreeMap<String, Value> =
                fields.into_iter().map(|(k, v)| (k.to_string(), v)).collect();
            assert_eq!(
                fields.get("outcome").unwrap(),
                &enum_variant("AttackOutcome", "Hit")
            );
            assert_eq!(get_int(&fields, "damage"), 6);
            assert_eq!(get_int(&fields, "total_mod"), 4); // BTHB=4, str_hit=0
        }
        other => panic!("expected AttackResult struct, got: {other:?}"),
    }
}

#[test]
fn resolve_melee_attack_miss_deals_zero() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        10,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        18,
        "Human",
    );

    // Roll 5 → 5+0+0 = 5 < 18 → Miss
    let atk_roll = scripted_roll(1, 20, 0, vec![5], vec![5], 5, 5);
    let mut handler = ScriptedHandler::with_responses(vec![atk_roll]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "resolve_melee_attack",
            vec![
                Value::Entity(attacker),
                Value::Entity(target),
                enum_variant("MeleeWeapon", "Dagger"),
            ],
        )
        .unwrap();

    match val {
        Value::Struct { name, fields } => {
            assert_eq!(&*name, "AttackResult");
            let fields: BTreeMap<String, Value> =
                fields.into_iter().map(|(k, v)| (k.to_string(), v)).collect();
            assert_eq!(
                fields.get("outcome").unwrap(),
                &enum_variant("AttackOutcome", "Miss")
            );
            assert_eq!(get_int(&fields, "damage"), 0);
        }
        other => panic!("expected AttackResult struct, got: {other:?}"),
    }
}

// ── resolve_missile_attack mechanic ────────────────────────────

#[test]
fn resolve_missile_attack_hit() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    // Fighter level 3 (BTHB=2), DEX 12 (dex_missile=0)
    let attacker = make_character(
        &mut state,
        "Archer",
        "Fighter",
        3,
        &standard_abilities(),
        20,
        14,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        12,
        "Human",
    );

    // BowLong: range_increment=70ft, not hurled
    // Distance 60ft → missile_range_penalty = floor(60/70)*-2 = 0
    // Roll 12 → 12+2+0+0 = 14 >= 12 → Hit
    let atk_roll = scripted_roll(1, 20, 0, vec![12], vec![12], 12, 12);
    // BowLong damage_sm: 1d6, roll 4
    let dmg_roll = scripted_roll(1, 6, 0, vec![4], vec![4], 4, 4);
    let mut handler = ScriptedHandler::with_responses(vec![atk_roll, dmg_roll]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "resolve_missile_attack",
            vec![
                Value::Entity(attacker),
                Value::Entity(target),
                enum_variant("MissileWeapon", "BowLong"),
                feet(60),
            ],
        )
        .unwrap();

    match val {
        Value::Struct { name, fields } => {
            assert_eq!(&*name, "AttackResult");
            let fields: BTreeMap<String, Value> =
                fields.into_iter().map(|(k, v)| (k.to_string(), v)).collect();
            assert_eq!(
                fields.get("outcome").unwrap(),
                &enum_variant("AttackOutcome", "Hit")
            );
            assert_eq!(get_int(&fields, "damage"), 4);
        }
        other => panic!("expected AttackResult struct, got: {other:?}"),
    }
}

#[test]
fn resolve_missile_attack_range_penalty_causes_miss() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Archer",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        10,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        12,
        "Human",
    );

    // BowLong: range_increment=70ft
    // Distance 150ft → floor(150/70)=2 → penalty -4
    // BTHB=0, dex_missile=0, range=-4, roll 15 → 15+0+0+(-4) = 11 < 12 → Miss
    let atk_roll = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    let mut handler = ScriptedHandler::with_responses(vec![atk_roll]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "resolve_missile_attack",
            vec![
                Value::Entity(attacker),
                Value::Entity(target),
                enum_variant("MissileWeapon", "BowLong"),
                feet(150),
            ],
        )
        .unwrap();

    match val {
        Value::Struct { fields, .. } => {
            let fields: BTreeMap<String, Value> =
                fields.into_iter().map(|(k, v)| (k.to_string(), v)).collect();
            assert_eq!(
                fields.get("outcome").unwrap(),
                &enum_variant("AttackOutcome", "Miss")
            );
            assert_eq!(get_int(&fields, "damage"), 0);
        }
        other => panic!("expected AttackResult struct, got: {other:?}"),
    }
}

// ── resolve_monster_attack mechanic ────────────────────────────

#[test]
fn resolve_monster_attack_hit() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    // Ogre: 4 HD → monster_bthb(4) = 5
    let monster = make_monster(
        &mut state,
        "Ogre",
        4,
        26,
        15,
        vec![monster_attack("Club", 1, 10, 0)],
    );
    let target = make_character(
        &mut state,
        "Victim",
        "Fighter",
        1,
        &standard_abilities(),
        8,
        14,
        "Human",
    );

    // Roll 12 → 12+5 = 17 >= 14 → Hit
    let atk_roll = scripted_roll(1, 20, 0, vec![12], vec![12], 12, 12);
    // damage: 1d10, roll 7
    let dmg_roll = scripted_roll(1, 10, 0, vec![7], vec![7], 7, 7);
    let mut handler = ScriptedHandler::with_responses(vec![atk_roll, dmg_roll]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "resolve_monster_attack",
            vec![
                Value::Entity(monster),
                Value::Entity(target),
                monster_attack("Club", 1, 10, 0),
            ],
        )
        .unwrap();

    match val {
        Value::Struct { name, fields } => {
            assert_eq!(&*name, "AttackResult");
            let fields: BTreeMap<String, Value> =
                fields.into_iter().map(|(k, v)| (k.to_string(), v)).collect();
            assert_eq!(
                fields.get("outcome").unwrap(),
                &enum_variant("AttackOutcome", "Hit")
            );
            assert_eq!(get_int(&fields, "damage"), 7);
            assert_eq!(get_int(&fields, "total_mod"), 5); // monster_bthb(4)=5
        }
        other => panic!("expected AttackResult struct, got: {other:?}"),
    }
}

#[test]
fn resolve_monster_attack_miss() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    // Rat: 0 HD → monster_bthb(0) = -1
    let monster = make_monster(
        &mut state,
        "Rat",
        0,
        1,
        10,
        vec![monster_attack("Bite", 1, 2, 0)],
    );
    let target = make_character(
        &mut state,
        "Warrior",
        "Fighter",
        5,
        &standard_abilities(),
        30,
        17,
        "Human",
    );

    // Roll 10 → 10+(-1) = 9 < 17 → Miss
    let atk_roll = scripted_roll(1, 20, 0, vec![10], vec![10], 10, 10);
    let mut handler = ScriptedHandler::with_responses(vec![atk_roll]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "resolve_monster_attack",
            vec![
                Value::Entity(monster),
                Value::Entity(target),
                monster_attack("Bite", 1, 2, 0),
            ],
        )
        .unwrap();

    match val {
        Value::Struct { fields, .. } => {
            let fields: BTreeMap<String, Value> =
                fields.into_iter().map(|(k, v)| (k.to_string(), v)).collect();
            assert_eq!(
                fields.get("outcome").unwrap(),
                &enum_variant("AttackOutcome", "Miss")
            );
            assert_eq!(get_int(&fields, "damage"), 0);
        }
        other => panic!("expected AttackResult struct, got: {other:?}"),
    }
}

// ── Surprise & initiative mechanics ────────────────────────────

#[test]
fn surprise_roll_returns_die_value() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let roll = scripted_roll(1, 6, 0, vec![3], vec![3], 3, 3);
    let mut handler = ScriptedHandler::with_responses(vec![roll]);

    let val = interp
        .evaluate_mechanic(&state, &mut handler, "surprise_roll", vec![])
        .unwrap();
    assert_eq!(val, Value::Int(3));
}

#[test]
fn group_initiative_returns_die_value() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let roll = scripted_roll(1, 6, 0, vec![5], vec![5], 5, 5);
    let mut handler = ScriptedHandler::with_responses(vec![roll]);

    let val = interp
        .evaluate_mechanic(&state, &mut handler, "group_initiative", vec![])
        .unwrap();
    assert_eq!(val, Value::Int(5));
}

#[test]
fn encounter_distance_normal() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Normal: (1d4+4)*10. Roll d4=3 → (3+4)*10 = 70ft
    let roll = scripted_roll(1, 4, 0, vec![3], vec![3], 3, 3);
    let mut handler = ScriptedHandler::with_responses(vec![roll]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "encounter_distance",
            vec![Value::Bool(false)],
        )
        .unwrap();
    assert_eq!(val, feet(70));
}

#[test]
fn encounter_distance_surprised() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Surprised: 1d3*10. Roll d3=2 → 2*10 = 20ft
    let roll = scripted_roll(1, 3, 0, vec![2], vec![2], 2, 2);
    let mut handler = ScriptedHandler::with_responses(vec![roll]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "encounter_distance",
            vec![Value::Bool(true)],
        )
        .unwrap();
    assert_eq!(val, feet(20));
}

#[test]
fn encounter_sequence_no_surprise() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Party rolls 4 (not surprised), Monster rolls 5 (not surprised)
    // → NoSurprise. Distance: normal (1d4+4)*10, roll d4=2 → 60ft
    let party_surp = scripted_roll(1, 6, 0, vec![4], vec![4], 4, 4);
    let monster_surp = scripted_roll(1, 6, 0, vec![5], vec![5], 5, 5);
    let dist = scripted_roll(1, 4, 0, vec![2], vec![2], 2, 2);
    let mut handler = ScriptedHandler::with_responses(vec![party_surp, monster_surp, dist]);

    let val = interp
        .evaluate_mechanic(&state, &mut handler, "encounter_sequence", vec![])
        .unwrap();

    let fields = match val {
        Value::Struct { name, fields } => {
            assert_eq!(&*name, "EncounterStart");
            fields
                .into_iter()
                .map(|(k, v)| (k.to_string(), v))
                .collect::<BTreeMap<String, Value>>()
        }
        other => panic!("expected EncounterStart, got {other:?}"),
    };

    assert_eq!(get_int(&fields, "party_roll"), 4);
    assert_eq!(get_int(&fields, "monster_roll"), 5);
    assert_eq!(
        fields.get("surprise").unwrap(),
        &enum_variant("SurpriseState", "NoSurprise")
    );
    assert_eq!(fields.get("distance").unwrap(), &feet(60));
}

#[test]
fn encounter_sequence_party_surprises_monsters() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Party rolls 4 (no), Monster rolls 1 (surprised)
    // → PartySurprises. Distance: surprised (1d3)*10, roll d3=1 → 10ft
    let party_surp = scripted_roll(1, 6, 0, vec![4], vec![4], 4, 4);
    let monster_surp = scripted_roll(1, 6, 0, vec![1], vec![1], 1, 1);
    let dist = scripted_roll(1, 3, 0, vec![1], vec![1], 1, 1);
    let mut handler = ScriptedHandler::with_responses(vec![party_surp, monster_surp, dist]);

    let val = interp
        .evaluate_mechanic(&state, &mut handler, "encounter_sequence", vec![])
        .unwrap();

    let fields = match val {
        Value::Struct { name, fields } => {
            assert_eq!(&*name, "EncounterStart");
            fields
                .into_iter()
                .map(|(k, v)| (k.to_string(), v))
                .collect::<BTreeMap<String, Value>>()
        }
        other => panic!("expected EncounterStart, got {other:?}"),
    };

    assert_eq!(
        fields.get("surprise").unwrap(),
        &enum_variant("SurpriseState", "PartySurprises")
    );
    assert_eq!(fields.get("distance").unwrap(), &feet(10));
}

// ── MeleeAttack action ────────────────────────────────────────

#[test]
fn melee_attack_action_hits_and_damages() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities(),
        30,
        15,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        14,
        "Human",
    );
    state.set_turn_budget(&attacker, combat_turn_budget());

    // Action pipeline: ActionStarted → DeductCost → resolve body → ActionCompleted
    let atk_roll = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    let dmg_roll = scripted_roll(1, 8, 0, vec![6], vec![6], 6, 6);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, Response::Acknowledged, atk_roll, dmg_roll,
    ]);

    let adapter = StateAdapter::new(state);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "MeleeAttack",
                attacker,
                vec![
                    Value::Entity(target),
                    enum_variant("MeleeWeapon", "SwordLong"),
                ],
            )
            .unwrap();
    });

    // Verify HP was reduced
    let final_state = adapter.into_inner();
    let hp = final_state.read_field(&target, "hp").unwrap();
    assert_eq!(hp, Value::Int(4), "target HP should be 10 - 6 = 4");
}

#[test]
fn melee_attack_action_miss_preserves_hp() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        10,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        18,
        "Human",
    );
    state.set_turn_budget(&attacker, combat_turn_budget());

    // Roll 5 → miss (5+0 = 5 < 18)
    let atk_roll = scripted_roll(1, 20, 0, vec![5], vec![5], 5, 5);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, Response::Acknowledged, atk_roll,
    ]);

    let adapter = StateAdapter::new(state);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "MeleeAttack",
                attacker,
                vec![
                    Value::Entity(target),
                    enum_variant("MeleeWeapon", "Dagger"),
                ],
            )
            .unwrap();
    });

    let final_state = adapter.into_inner();
    let hp = final_state.read_field(&target, "hp").unwrap();
    assert_eq!(hp, Value::Int(10), "target HP should be unchanged on miss");
}

// ── MissileAttack action ──────────────────────────────────────

#[test]
fn missile_attack_action_hits() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Archer",
        "Fighter",
        3,
        &standard_abilities(),
        20,
        14,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        12,
        "Human",
    );
    state.set_turn_budget(&attacker, combat_turn_budget());

    // Roll 14 → 14+2+0+0 = 16 >= 12 → Hit; damage 1d6 roll 3
    let atk_roll = scripted_roll(1, 20, 0, vec![14], vec![14], 14, 14);
    let dmg_roll = scripted_roll(1, 6, 0, vec![3], vec![3], 3, 3);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, Response::Acknowledged, atk_roll, dmg_roll,
    ]);

    let adapter = StateAdapter::new(state);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "MissileAttack",
                attacker,
                vec![
                    Value::Entity(target),
                    enum_variant("MissileWeapon", "BowLong"),
                    feet(60),
                ],
            )
            .unwrap();
    });

    let final_state = adapter.into_inner();
    let hp = final_state.read_field(&target, "hp").unwrap();
    assert_eq!(hp, Value::Int(7), "target HP should be 10 - 3 = 7");
}

// ── Charge action ─────────────────────────────────────────────

#[test]
fn charge_action_adds_attack_mod() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    // Fighter level 1 (BTHB=0), STR 12 (no mod)
    // Target AC 14
    // Charge gives attack_mod=2 to resolve_melee_attack
    let attacker = make_character(
        &mut state,
        "Charger",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        10,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        14,
        "Human",
    );
    state.set_turn_budget(&attacker, combat_turn_budget());

    // Roll 12 → 12+0+0+2 = 14 >= 14 → Hit (only hits because of +2 charge bonus)
    let atk_roll = scripted_roll(1, 20, 0, vec![12], vec![12], 12, 12);
    // damage: SwordLong 1d8, roll 5
    let dmg_roll = scripted_roll(1, 8, 0, vec![5], vec![5], 5, 5);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, Response::Acknowledged, atk_roll, dmg_roll,
    ]);

    let adapter = StateAdapter::new(state);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "Charge",
                attacker,
                vec![
                    Value::Entity(target),
                    enum_variant("MeleeWeapon", "SwordLong"),
                ],
            )
            .unwrap();
    });

    let final_state = adapter.into_inner();
    let hp = final_state.read_field(&target, "hp").unwrap();
    assert_eq!(hp, Value::Int(5), "target HP should be 10 - 5 = 5");
}

#[test]
fn charge_would_miss_without_bonus() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    // Same setup but test a regular MeleeAttack with the same roll would miss
    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        10,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        14,
        "Human",
    );
    state.set_turn_budget(&attacker, combat_turn_budget());

    // Roll 12 → 12+0+0 = 12 < 14 → Miss (no charge bonus)
    let atk_roll = scripted_roll(1, 20, 0, vec![12], vec![12], 12, 12);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, Response::Acknowledged, atk_roll,
    ]);

    let adapter = StateAdapter::new(state);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "MeleeAttack",
                attacker,
                vec![
                    Value::Entity(target),
                    enum_variant("MeleeWeapon", "SwordLong"),
                ],
            )
            .unwrap();
    });

    let final_state = adapter.into_inner();
    let hp = final_state.read_field(&target, "hp").unwrap();
    assert_eq!(hp, Value::Int(10), "regular attack should miss");
}

// ── Creature slain event ──────────────────────────────────────

#[test]
fn melee_attack_emits_creature_slain_on_kill() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities(),
        30,
        15,
        "Human",
    );
    // Target with only 3 HP — will die from any hit
    let target = make_character(
        &mut state,
        "Victim",
        "Fighter",
        1,
        &standard_abilities(),
        3,
        10,
        "Human",
    );
    state.set_turn_budget(&attacker, combat_turn_budget());

    // Roll 18 → hit; damage 1d8 roll 5 → 5 damage kills target (3 HP)
    let atk_roll = scripted_roll(1, 20, 0, vec![18], vec![18], 18, 18);
    let dmg_roll = scripted_roll(1, 8, 0, vec![5], vec![5], 5, 5);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, Response::Acknowledged, atk_roll, dmg_roll,
    ]);

    let adapter = StateAdapter::new(state);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "MeleeAttack",
                attacker,
                vec![
                    Value::Entity(target),
                    enum_variant("MeleeWeapon", "SwordLong"),
                ],
            )
            .unwrap();
    });

    let final_state = adapter.into_inner();
    let hp = final_state.read_field(&target, "hp").unwrap();
    assert_eq!(hp, Value::Int(0), "target HP should be clamped to 0");
}
