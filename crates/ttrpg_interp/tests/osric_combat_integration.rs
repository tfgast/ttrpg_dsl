//! OSRIC combat integration test.
//!
//! Verifies that osric/osric_combat.ttrpg parses, lowers, and type-checks
//! through the full multi-file pipeline (core + ability + class + equipment +
//! combat). Exercises BTHB tables for all 4 combat groups, fighter_attacks,
//! missile_range_penalty, attack_roll_aac, damage_roll,
//! resolve_melee_attack, resolve_missile_attack, resolve_monster_attack,
//! Damaged/CreatureSlain events, and MeleeAttack/MissileAttack/Charge actions.

use std::collections::BTreeMap;

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_interp::adapter::StateAdapter;
use ttrpg_interp::effect::{EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::StateProvider;
use ttrpg_interp::value::{DiceExpr, Value};
use ttrpg_interp::Interpreter;

mod osric_common;
use osric_common::*;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_combat() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
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

// ── File-specific helpers ──────────────────────────────────────

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
    let has_system = program
        .items
        .iter()
        .any(|item| matches!(&item.node, TopLevel::System(sys) if sys.name == "OSRIC Combat"));
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
    assert!(enums.contains(&("Duration", 7)));
    assert!(enums.contains(&("SurpriseState", 4)));
    assert!(enums.contains(&("AssassinationOutcome", 3)));
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
    assert!(
        structs.contains(&("AssassinationResult", 4)),
        "missing AssassinationResult with 4 fields"
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
    assert!(derives.contains(&"monster_bthb"));
    assert!(derives.contains(&"fighter_attacks"));
    assert!(derives.contains(&"missile_range_penalty"));
    assert!(derives.contains(&"deal_damage"));
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
    assert!(actions.contains(&"TakeDamage"));
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
    let cases = vec![(1, 0), (5, 4), (7, 6), (10, 9), (13, 12), (20, 19)];

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
        assert_eq!(val, Value::Int(9), "{class} level 10 should have BTHB 9");
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
        assert_eq!(val, Value::Int(4), "{class} level 10 should have BTHB 4");
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
        assert_eq!(val, Value::Int(1), "{class} level 5 should have BTHB 1");
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
        assert_eq!(val, Value::Int(1), "{class} level 6 should have BTHB 1");
    }
}

#[test]
fn monster_bthb_all_tiers() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Helper: build a DiceExpr value from (count, sides, modifier).
    let hd = |count: u32, sides: u32, modifier: i64| -> Value {
        Value::DiceExpr(DiceExpr::single(count, sides, None, modifier))
    };

    // OSRIC Table 2.1.2A: all 16 monster HD tiers.
    // (dice_count, dice_sides, modifier) → expected BTHB
    let cases: Vec<(Value, i64, &str)> = vec![
        (hd(0, 0, 0), -1, "<1-1 (0 dice)"),
        (hd(1, 4, 0), -1, "<1-1 (1d4)"),
        (hd(1, 8, -2), -1, "<1-1 (1d8-2)"),
        (hd(1, 8, -1), 0, "1-1"),
        (hd(1, 8, 0), 1, "1"),
        (hd(1, 8, 1), 2, "1+"),
        (hd(1, 8, 2), 2, "1+2"),
        (hd(2, 8, 0), 4, "2"),
        (hd(3, 8, 3), 4, "3+3"),
        (hd(4, 8, 1), 5, "4+1"),
        (hd(5, 8, 0), 5, "5"),
        (hd(6, 8, 0), 7, "6"),
        (hd(7, 8, 1), 7, "7+1"),
        (hd(8, 8, 0), 8, "8"),
        (hd(9, 8, 2), 8, "9+2"),
        (hd(10, 8, 0), 10, "10"),
        (hd(11, 8, 0), 10, "11"),
        (hd(12, 8, 0), 11, "12"),
        (hd(13, 8, 0), 11, "13"),
        (hd(14, 8, 0), 12, "14"),
        (hd(15, 8, 0), 12, "15"),
        (hd(16, 8, 0), 13, "16"),
        (hd(17, 8, 0), 13, "17"),
        (hd(18, 8, 0), 15, "18"),
        (hd(19, 8, 0), 15, "19"),
        (hd(20, 8, 0), 16, "20"),
        (hd(21, 8, 0), 16, "21"),
        (hd(22, 8, 0), 17, "22"),
        (hd(23, 8, 0), 17, "23"),
        (hd(24, 8, 0), 18, "24"),
        (hd(30, 8, 0), 18, "30"),
    ];

    for (dice, expected, label) in cases {
        let val = interp
            .evaluate_derive(&state, &mut NullHandler, "monster_bthb", vec![dice])
            .unwrap();
        assert_eq!(
            val,
            Value::Int(expected),
            "monster_bthb({label}) should be {expected}"
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
fn missile_range_penalty_at_exact_boundary() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Distance exactly equal to increment: still first band, no penalty
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "missile_range_penalty",
            vec![feet(70), feet(70)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(0));
}

#[test]
fn missile_range_penalty_just_past_boundary() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Distance 1ft past first increment: second band, -2 penalty
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "missile_range_penalty",
            vec![feet(71), feet(70)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(-2));
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
        &standard_abilities_12(),
        30,
        15,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities_12(),
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
            let fields: BTreeMap<String, Value> = fields
                .into_iter()
                .map(|(k, v)| (k.to_string(), v))
                .collect();
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
        &standard_abilities_12(),
        10,
        10,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities_12(),
        10,
        17,
        "Human",
    );

    // Roll 5 → 5+0+0 = 5 < 17 → Miss
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
            let fields: BTreeMap<String, Value> = fields
                .into_iter()
                .map(|(k, v)| (k.to_string(), v))
                .collect();
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
        &standard_abilities_12(),
        20,
        14,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities_12(),
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
            let fields: BTreeMap<String, Value> = fields
                .into_iter()
                .map(|(k, v)| (k.to_string(), v))
                .collect();
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
        &standard_abilities_12(),
        10,
        10,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities_12(),
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
            let fields: BTreeMap<String, Value> = fields
                .into_iter()
                .map(|(k, v)| (k.to_string(), v))
                .collect();
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

    // Ogre: 4d8+1 HD → monster_bthb = 5 (4-5+ tier)
    let monster = make_monster(
        &mut state,
        "Ogre",
        (4, 8, 1),
        26,
        15,
        vec![monster_attack("Club", 1, 10, 0)],
    );
    let target = make_character(
        &mut state,
        "Victim",
        "Fighter",
        1,
        &standard_abilities_12(),
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
            let fields: BTreeMap<String, Value> = fields
                .into_iter()
                .map(|(k, v)| (k.to_string(), v))
                .collect();
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

    // Rat: <1-1 HD (1d4, no modifier, sub-1-die creature) → BTHB -1
    let monster = make_monster(
        &mut state,
        "Rat",
        (0, 0, 0),
        1,
        10,
        vec![monster_attack("Bite", 1, 2, 0)],
    );
    let target = make_character(
        &mut state,
        "Warrior",
        "Fighter",
        5,
        &standard_abilities_12(),
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
            let fields: BTreeMap<String, Value> = fields
                .into_iter()
                .map(|(k, v)| (k.to_string(), v))
                .collect();
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
        &standard_abilities_12(),
        30,
        15,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities_12(),
        10,
        14,
        "Human",
    );
    state.set_turn_budget(&attacker, combat_turn_budget());
    // Equip a longsword on the attacker
    set_field(
        &mut state,
        &attacker,
        "wielded_main",
        wielded_melee_item("SwordLong"),
    );

    // Action pipeline: ActionStarted → RequiresCheck → DeductCost → resolve body → ActionCompleted
    let atk_roll = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    let dmg_roll = scripted_roll(1, 8, 0, vec![6], vec![6], 6, 6);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged,
        Response::Acknowledged, // RequiresCheck (wielded_melee is_some → pass)
        Response::Acknowledged,
        atk_roll,
        dmg_roll,
    ]);

    let adapter = StateAdapter::new(state);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "MeleeAttack",
                attacker,
                vec![Value::Entity(target)],
            )
            .unwrap();
    });

    // Verify HP was reduced
    let final_state = adapter.into_inner();
    let hp = read_group_field(&final_state, &target, "HitPoints", "hp").unwrap();
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
        &standard_abilities_12(),
        10,
        10,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities_12(),
        10,
        17,
        "Human",
    );
    state.set_turn_budget(&attacker, combat_turn_budget());
    // Equip a dagger on the attacker
    set_field(
        &mut state,
        &attacker,
        "wielded_main",
        wielded_melee_item("Dagger"),
    );

    // Roll 5 → miss (5+0 = 5 < 17)
    let atk_roll = scripted_roll(1, 20, 0, vec![5], vec![5], 5, 5);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged,
        Response::Acknowledged, // RequiresCheck
        Response::Acknowledged,
        atk_roll,
    ]);

    let adapter = StateAdapter::new(state);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "MeleeAttack",
                attacker,
                vec![Value::Entity(target)],
            )
            .unwrap();
    });

    let final_state = adapter.into_inner();
    let hp = read_group_field(&final_state, &target, "HitPoints", "hp").unwrap();
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
        &standard_abilities_12(),
        20,
        14,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities_12(),
        10,
        12,
        "Human",
    );
    state.set_turn_budget(&attacker, combat_turn_budget());
    // Equip a longbow on the attacker
    set_field(
        &mut state,
        &attacker,
        "wielded_main",
        wielded_missile_item("BowLong"),
    );

    // Roll 14 → 14+2+0+0 = 16 >= 12 → Hit; damage 1d6 roll 3
    let atk_roll = scripted_roll(1, 20, 0, vec![14], vec![14], 14, 14);
    let dmg_roll = scripted_roll(1, 6, 0, vec![3], vec![3], 3, 3);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged,
        Response::Acknowledged, // RequiresCheck
        Response::Acknowledged,
        atk_roll,
        dmg_roll,
    ]);

    let adapter = StateAdapter::new(state);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "MissileAttack",
                attacker,
                vec![Value::Entity(target), feet(60)],
            )
            .unwrap();
    });

    let final_state = adapter.into_inner();
    let hp = read_group_field(&final_state, &target, "HitPoints", "hp").unwrap();
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
        &standard_abilities_12(),
        10,
        10,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities_12(),
        10,
        14,
        "Human",
    );
    state.set_turn_budget(&attacker, combat_turn_budget());
    // Equip a longsword on the charger
    set_field(
        &mut state,
        &attacker,
        "wielded_main",
        wielded_melee_item("SwordLong"),
    );

    // Roll 12 → 12+0+0+2 = 14 >= 14 → Hit (only hits because of +2 charge bonus)
    let atk_roll = scripted_roll(1, 20, 0, vec![12], vec![12], 12, 12);
    // damage: SwordLong 1d8, roll 5
    let dmg_roll = scripted_roll(1, 8, 0, vec![5], vec![5], 5, 5);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, // ActionStarted
        Response::Acknowledged, // RequiresCheck (wielded + no ChargeRecovery → pass)
        Response::Acknowledged, // DeductCost(attack)
        Response::Acknowledged, // ConditionApplyGate (ChargeRecovery)
        atk_roll,
        dmg_roll,
    ]);

    let adapter = StateAdapter::new(state);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "Charge",
                attacker,
                vec![Value::Entity(target)],
            )
            .unwrap();
    });

    let final_state = adapter.into_inner();
    let hp = read_group_field(&final_state, &target, "HitPoints", "hp").unwrap();
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
        &standard_abilities_12(),
        10,
        10,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities_12(),
        10,
        14,
        "Human",
    );
    state.set_turn_budget(&attacker, combat_turn_budget());
    set_field(
        &mut state,
        &attacker,
        "wielded_main",
        wielded_melee_item("SwordLong"),
    );

    // Roll 12 → 12+0+0 = 12 < 14 → Miss (no charge bonus)
    let atk_roll = scripted_roll(1, 20, 0, vec![12], vec![12], 12, 12);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged,
        Response::Acknowledged, // RequiresCheck
        Response::Acknowledged,
        atk_roll,
    ]);

    let adapter = StateAdapter::new(state);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "MeleeAttack",
                attacker,
                vec![Value::Entity(target)],
            )
            .unwrap();
    });

    let final_state = adapter.into_inner();
    let hp = read_group_field(&final_state, &target, "HitPoints", "hp").unwrap();
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
        &standard_abilities_12(),
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
        &standard_abilities_12(),
        3,
        10,
        "Human",
    );
    state.set_turn_budget(&attacker, combat_turn_budget());
    set_field(
        &mut state,
        &attacker,
        "wielded_main",
        wielded_melee_item("SwordLong"),
    );

    // Roll 18 → hit; damage 1d8 roll 5 → 5 damage to 3 HP target → HP -2
    // Under OSRIC §1.6.6, at 0 HP the character is unconscious (not dead).
    // Death occurs at -10 HP.
    let atk_roll = scripted_roll(1, 20, 0, vec![18], vec![18], 18, 18);
    let dmg_roll = scripted_roll(1, 8, 0, vec![5], vec![5], 5, 5);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged,
        Response::Acknowledged, // RequiresCheck
        Response::Acknowledged,
        atk_roll,
        dmg_roll,
    ]);

    let adapter = StateAdapter::new(state);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "MeleeAttack",
                attacker,
                vec![Value::Entity(target)],
            )
            .unwrap();
    });

    let final_state = adapter.into_inner();
    let hp = read_group_field(&final_state, &target, "HitPoints", "hp").unwrap();
    assert_eq!(
        hp,
        Value::Int(-2),
        "target HP should be -2 (unconscious, not dead)"
    );
}

// ── deal_damage derive ────────────────────────────────────────

#[test]
fn deal_damage_returns_raw_damage() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities_12(),
        30,
        15,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities_12(),
        10,
        14,
        "Human",
    );
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "deal_damage",
            vec![
                Value::Entity(target),
                Value::Entity(attacker),
                Value::Int(7),
                enum_variant("DamageType", "Slashing"),
            ],
        )
        .unwrap();
    assert_eq!(
        val,
        Value::Int(7),
        "deal_damage should pass through raw_damage"
    );
}

#[test]
fn deal_damage_with_default_damage_type() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        1,
        &standard_abilities_12(),
        10,
        10,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities_12(),
        10,
        10,
        "Human",
    );
    let mut handler = NullHandler;

    // Call with only 3 args — damage_type defaults to Blunt
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "deal_damage",
            vec![
                Value::Entity(target),
                Value::Entity(attacker),
                Value::Int(3),
            ],
        )
        .unwrap();
    assert_eq!(
        val,
        Value::Int(3),
        "deal_damage with default type should still pass through"
    );
}

// ── TakeDamage action ─────────────────────────────────────────

#[test]
fn take_damage_action_reduces_hp() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities_12(),
        30,
        15,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities_12(),
        10,
        14,
        "Human",
    );
    state.set_turn_budget(&target, combat_turn_budget());

    // TakeDamage pipeline: ActionStarted, DeductCost, resolve (deal_damage + hp mutation + emit)
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, // ActionStarted
        Response::Acknowledged, // DeductCost
    ]);

    let adapter = StateAdapter::new(state);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "TakeDamage",
                target,
                vec![
                    Value::Entity(attacker),
                    Value::Int(6),
                    enum_variant("DamageType", "Slashing"),
                ],
            )
            .unwrap();
    });

    let final_state = adapter.into_inner();
    let hp = read_group_field(&final_state, &target, "HitPoints", "hp").unwrap();
    assert_eq!(hp, Value::Int(4), "target HP should be 10 - 6 = 4");
}

#[test]
fn take_damage_action_emits_creature_slain_on_kill() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities_12(),
        30,
        15,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Victim",
        "Fighter",
        1,
        &standard_abilities_12(),
        3,
        10,
        "Human",
    );
    state.set_turn_budget(&target, combat_turn_budget());

    let mut handler =
        ScriptedHandler::with_responses(vec![Response::Acknowledged, Response::Acknowledged]);

    let adapter = StateAdapter::new(state);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "TakeDamage",
                target,
                vec![
                    Value::Entity(attacker),
                    Value::Int(5),
                    enum_variant("DamageType", "Blunt"),
                ],
            )
            .unwrap();
    });

    let final_state = adapter.into_inner();
    let hp = read_group_field(&final_state, &target, "HitPoints", "hp").unwrap();
    assert_eq!(
        hp,
        Value::Int(-2),
        "target HP should be -2 (unconscious, not dead)"
    );
}

// ── Monster TakeDamage ───────────────────────────────────────

#[test]
fn monster_take_damage_reduces_hp() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities_12(),
        30,
        15,
        "Human",
    );
    let orc = make_monster(&mut state, "Orc", (1, 8, 0), 8, 14, vec![]);

    let mut handler =
        ScriptedHandler::with_responses(vec![Response::Acknowledged, Response::Acknowledged]);

    let adapter = StateAdapter::new(state);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "TakeDamage",
                orc,
                vec![
                    Value::Entity(attacker),
                    Value::Int(3),
                    enum_variant("DamageType", "Slashing"),
                ],
            )
            .unwrap();
    });

    let final_state = adapter.into_inner();
    let hp = final_state.read_field(&orc, "hp").unwrap();
    assert_eq!(hp, Value::Int(5), "monster HP should be 8 - 3 = 5");
}

#[test]
fn monster_take_damage_kills_at_zero() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities_12(),
        30,
        15,
        "Human",
    );
    let goblin = make_monster(&mut state, "Goblin", (1, 8, -1), 3, 14, vec![]);

    let mut handler =
        ScriptedHandler::with_responses(vec![Response::Acknowledged, Response::Acknowledged]);

    let adapter = StateAdapter::new(state);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "TakeDamage",
                goblin,
                vec![
                    Value::Entity(attacker),
                    Value::Int(10),
                    enum_variant("DamageType", "Blunt"),
                ],
            )
            .unwrap();
    });

    let final_state = adapter.into_inner();
    let hp = final_state.read_field(&goblin, "hp").unwrap();
    assert!(
        matches!(hp, Value::Int(n) if n <= 0),
        "goblin should be at or below 0 HP"
    );

    // Monster should have Dead condition
    let conditions = final_state.read_conditions(&goblin).unwrap_or_default();
    assert!(
        conditions.iter().any(|c| c.name.as_str() == "Dead"),
        "goblin should have Dead condition after lethal damage"
    );
}

// ── Backstab ──────────────────────────────────────────────────

// The Backstab action should be present in the combat system.
#[test]
fn osric_combat_has_backstab_action() {
    let (program, _) = compile_osric_combat();
    let decls = get_combat_decls(&program);
    let actions: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Action(a) => Some(&*a.name),
            _ => None,
        })
        .collect();
    assert!(actions.contains(&"Backstab"), "missing Backstab action");
}

// Thief backstab multiplier: x2 at L1-4, x3 at L5-8, x4 at L9-12, x5 at L13-16, x6 at L17+.
#[test]
fn thief_backstab_multiplier_table() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let cases = vec![
        (1, 2),
        (4, 2), // L1-4 → x2
        (5, 3),
        (8, 3), // L5-8 → x3
        (9, 4),
        (12, 4), // L9-12 → x4
        (13, 5),
        (16, 5), // L13-16 → x5
        (17, 6),
        (20, 6), // L17+ → x6
    ];

    for (level, expected_mult) in cases {
        let val = interp
            .evaluate_derive(
                &state,
                &mut handler,
                "thief_backstab_multiplier",
                vec![Value::Int(level)],
            )
            .unwrap_or_else(|e| panic!("thief_backstab_multiplier({level}) failed: {e}"));
        assert_eq!(
            expect_int(val, &format!("thief_backstab_multiplier({level})")),
            expected_mult,
            "thief_backstab_multiplier({level})"
        );
    }
}

// Assassin backstab multiplier: x2 at L1-4, x3 at L5-8, x4 at L9-12, x5 at L13+.
#[test]
fn assassin_backstab_multiplier_table() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let cases = vec![
        (1, 2),
        (4, 2), // L1-4 → x2
        (5, 3),
        (8, 3), // L5-8 → x3
        (9, 4),
        (12, 4), // L9-12 → x4
        (13, 5),
        (15, 5), // L13+ → x5 (caps at x5)
    ];

    for (level, expected_mult) in cases {
        let val = interp
            .evaluate_derive(
                &state,
                &mut handler,
                "assassin_backstab_multiplier",
                vec![Value::Int(level)],
            )
            .unwrap_or_else(|e| panic!("assassin_backstab_multiplier({level}) failed: {e}"));
        assert_eq!(
            expect_int(val, &format!("assassin_backstab_multiplier({level})")),
            expected_mult,
            "assassin_backstab_multiplier({level})"
        );
    }
}

// backstab_multiplier dispatches to thief or assassin table based on class.
#[test]
fn backstab_multiplier_dispatch() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Thief L17 → x6 (thief table)
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "backstab_multiplier",
            vec![class_variant("Thief"), Value::Int(17)],
        )
        .unwrap();
    assert_eq!(expect_int(val, "backstab_multiplier(Thief, 17)"), 6);

    // Assassin L17 → x5 (assassin table caps at x5)
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "backstab_multiplier",
            vec![class_variant("Assassin"), Value::Int(17)],
        )
        .unwrap();
    assert_eq!(expect_int(val, "backstab_multiplier(Assassin, 17)"), 5);
}

// backstab_attack_bonus returns 4.
#[test]
fn backstab_attack_bonus_is_4() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "backstab_attack_bonus", vec![])
        .unwrap();
    assert_eq!(expect_int(val, "backstab_attack_bonus"), 4);
}

// character_can_backstab: true for Thief and Assassin, false for others.
#[test]
fn character_can_backstab_thief() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let thief = make_character(
        &mut state,
        "Thief",
        "Thief",
        5,
        &standard_abilities_12(),
        20,
        12,
        "Human",
    );
    let fighter = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities_12(),
        30,
        17,
        "Human",
    );
    let assassin = make_character(
        &mut state,
        "Assassin",
        "Assassin",
        5,
        &standard_abilities_12(),
        20,
        12,
        "Human",
    );

    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "character_can_backstab",
            vec![Value::Entity(thief)],
        )
        .unwrap();
    assert!(expect_bool(val, "character_can_backstab(Thief)"));

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "character_can_backstab",
            vec![Value::Entity(assassin)],
        )
        .unwrap();
    assert!(expect_bool(val, "character_can_backstab(Assassin)"));

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "character_can_backstab",
            vec![Value::Entity(fighter)],
        )
        .unwrap();
    assert!(!expect_bool(val, "character_can_backstab(Fighter)"));
}

// resolve_melee_attack with damage_mult > 1 multiplies dice before adding bonuses.
#[test]
fn resolve_melee_attack_with_damage_mult() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    // STR 12 → +0 to hit, +0 damage (no STR modifiers at 12)
    let attacker = make_character(
        &mut state,
        "Attacker",
        "Thief",
        5,
        &standard_abilities_12(),
        20,
        10,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities_12(),
        20,
        10,
        "Human",
    );

    // Equip attacker with a dagger
    set_field(
        &mut state,
        &attacker,
        "wielded_main",
        wielded_melee_item("Dagger"),
    );

    // Script rolls: d20=18 (hit), damage d4=3
    let responses = vec![
        scripted_roll(1, 20, 0, vec![18], vec![18], 18, 18), // d20 attack roll
        scripted_roll(1, 4, 0, vec![3], vec![3], 3, 3),      // d4 damage roll (raw dice)
    ];
    let mut handler = ScriptedHandler::with_responses(responses);

    // Call resolve_melee_attack with damage_mult=3 (L5-8 thief backstab)
    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "resolve_melee_attack",
            vec![
                Value::Entity(attacker),
                Value::Entity(target),
                melee_variant("Dagger"),
                Value::Int(0),                      // attack_mod
                enum_variant("RollMode", "Normal"), // roll_mode
                Value::Bool(false),                 // max_damage
                Value::Int(3),                      // damage_mult (x3)
            ],
        )
        .unwrap();

    // With damage_mult=3: raw=3, damage = max(1, 3*3 + 0) = 9
    match val {
        Value::Struct { fields, .. } => {
            let damage = fields.get::<ttrpg_ast::Name>(&"damage".into()).unwrap();
            assert_eq!(*damage, Value::Int(9), "backstab damage should be 3*3=9");
        }
        other => panic!("expected AttackResult struct, got: {other:?}"),
    }
}

// ── Assassination ────────────────────────────────────────────

#[test]
fn osric_combat_has_assassination_enum_and_struct() {
    let (program, _) = compile_osric_combat();
    let decls = get_combat_decls(&program);

    let enums: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Enum(e) => Some((&*e.name, e.variants.len())),
            _ => None,
        })
        .collect();
    assert!(
        enums.contains(&("AssassinationOutcome", 3)),
        "missing AssassinationOutcome enum with 3 variants"
    );

    let structs: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Struct(s) => Some((&*s.name, s.fields.len())),
            _ => None,
        })
        .collect();
    assert!(
        structs.contains(&("AssassinationResult", 4)),
        "missing AssassinationResult struct with 4 fields"
    );
}

#[test]
fn osric_combat_has_assassination_mechanic() {
    let (program, _) = compile_osric_combat();
    let decls = get_combat_decls(&program);
    let mechanics: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Mechanic(m) => Some(&*m.name),
            _ => None,
        })
        .collect();
    assert!(mechanics.contains(&"resolve_assassination"));
}

#[test]
fn osric_combat_has_assassinate_action() {
    let (program, _) = compile_osric_combat();
    let decls = get_combat_decls(&program);
    let actions: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Action(a) => Some(&*a.name),
            _ => None,
        })
        .collect();
    assert!(actions.contains(&"Assassinate"));
}

/// assassination_chance: 50 + level*5 - floor(hd/2)*5
/// L8 assassin vs 8 HD target: 50 + 40 - 20 = 70
#[test]
fn assassination_chance_level_8_vs_8hd() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "assassination_chance",
            vec![Value::Int(8), Value::Int(8)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(70), "L8 vs 8HD should be 70%");
}

/// L1 assassin vs 0 HD target: 50 + 5 - 0 = 55
#[test]
fn assassination_chance_level_1_vs_0hd() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "assassination_chance",
            vec![Value::Int(1), Value::Int(0)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(55), "L1 vs 0HD should be 55%");
}

/// L1 assassin vs 21 HD target: 50 + 5 - 50 = 5 (but minimum is 1)
#[test]
fn assassination_chance_clamps_to_minimum_1() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "assassination_chance",
            vec![Value::Int(1), Value::Int(21)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(5), "L1 vs 21HD = 50+5-50 = 5");
}

/// Odd HD: L4 vs 7 HD: 50 + 20 - floor(7/2)*5 = 70 - 15 = 55
#[test]
fn assassination_chance_odd_hd_rounds_down() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "assassination_chance",
            vec![Value::Int(4), Value::Int(7)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(55), "L4 vs 7HD: 50+20-15 = 55");
}

/// resolve_assassination with a successful d100 roll → Kill outcome
#[test]
fn resolve_assassination_success_kills() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    // L8 assassin (Assassin class, level 8)
    let attacker = make_character(
        &mut state,
        "Shadowblade",
        "Assassin",
        8,
        &standard_abilities_12(),
        30,
        12,
        "Human",
    );
    // Target with AC 14
    let target = make_character(
        &mut state,
        "Guard",
        "Fighter",
        4,
        &standard_abilities_12(),
        30,
        14,
        "Human",
    );
    // Equip attacker with dagger
    set_field(
        &mut state,
        &attacker,
        "wielded_main",
        wielded_melee_item("Dagger"),
    );

    // L8 vs 8 HD: chance = 70%. Script d100 = 50 (success, 50 <= 70)
    let responses = vec![
        scripted_roll(1, 100, 0, vec![50], vec![50], 50, 50), // d100 assassination roll
    ];
    let mut handler = ScriptedHandler::with_responses(responses);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "resolve_assassination",
            vec![
                Value::Entity(attacker),
                Value::Entity(target),
                melee_variant("Dagger"),
                Value::Int(8), // target_hd
            ],
        )
        .unwrap();

    match val {
        Value::Struct { name, fields } => {
            assert_eq!(&*name, "AssassinationResult");
            let outcome = fields.get::<ttrpg_ast::Name>(&"outcome".into()).unwrap();
            assert_eq!(
                *outcome,
                enum_variant("AssassinationOutcome", "Kill"),
                "d100=50 vs 70% chance should be a kill"
            );
            let chance = fields.get::<ttrpg_ast::Name>(&"chance".into()).unwrap();
            assert_eq!(*chance, Value::Int(70));
        }
        other => panic!("expected AssassinationResult struct, got: {other:?}"),
    }
}

/// resolve_assassination with a failed d100 roll → normal weapon attack
#[test]
fn resolve_assassination_failure_does_normal_attack() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    // L4 assassin
    let attacker = make_character(
        &mut state,
        "Shadowblade",
        "Assassin",
        4,
        &standard_abilities_12(),
        30,
        12,
        "Human",
    );
    // Target
    let target = make_character(
        &mut state,
        "Guard",
        "Fighter",
        4,
        &standard_abilities_12(),
        30,
        12,
        "Human",
    );
    // Equip attacker with dagger
    set_field(
        &mut state,
        &attacker,
        "wielded_main",
        wielded_melee_item("Dagger"),
    );

    // L4 vs 6 HD: chance = 50+20-15 = 55%. Script d100 = 80 (fail, 80 > 55)
    // Then normal attack: d20=18 (hit), d4=3 (damage)
    let responses = vec![
        scripted_roll(1, 100, 0, vec![80], vec![80], 80, 80), // d100 assassination roll (fail)
        scripted_roll(1, 20, 0, vec![18], vec![18], 18, 18),  // d20 attack roll
        scripted_roll(1, 4, 0, vec![3], vec![3], 3, 3),       // d4 damage roll
    ];
    let mut handler = ScriptedHandler::with_responses(responses);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "resolve_assassination",
            vec![
                Value::Entity(attacker),
                Value::Entity(target),
                melee_variant("Dagger"),
                Value::Int(6), // target_hd
            ],
        )
        .unwrap();

    match val {
        Value::Struct { name, fields } => {
            assert_eq!(&*name, "AssassinationResult");
            let outcome = fields.get::<ttrpg_ast::Name>(&"outcome".into()).unwrap();
            assert_eq!(
                *outcome,
                enum_variant("AssassinationOutcome", "WeaponHit"),
                "failed assassination with hit should give WeaponHit"
            );
            let damage = fields.get::<ttrpg_ast::Name>(&"damage".into()).unwrap();
            assert_eq!(*damage, Value::Int(3), "normal attack damage should be 3");
        }
        other => panic!("expected AssassinationResult struct, got: {other:?}"),
    }
}

// ── PARRYING (§1.6.2.9) ──────────────────────────────────────

#[test]
fn parry_bonus_with_str_only() {
    // STR 17 → +1 to hit. No weapon spec. Parry bonus = 1.
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let abilities = vec![
        ("STR", 17),
        ("DEX", 12),
        ("CON", 12),
        ("INT", 12),
        ("WIS", 12),
        ("CHA", 12),
    ];
    let parrier = make_character(
        &mut state, "Parrier", "Fighter", 5, &abilities, 30, 15, "Human",
    );
    set_field(
        &mut state,
        &parrier,
        "wielded_main",
        wielded_melee_item("SwordLong"),
    );

    let mut handler = ScriptedHandler::with_responses(vec![]);
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "parry_bonus",
            vec![Value::Entity(parrier)],
        )
        .unwrap();
    assert_eq!(
        val,
        Value::Int(1),
        "STR 17 gives +1 to hit → parry_bonus = 1"
    );
}

#[test]
fn parry_bonus_with_str_and_spec() {
    // STR 17 → +1 to hit. Single spec → +1 to hit. Parry bonus = 2.
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let abilities = vec![
        ("STR", 17),
        ("DEX", 12),
        ("CON", 12),
        ("INT", 12),
        ("WIS", 12),
        ("CHA", 12),
    ];
    let parrier = make_character(
        &mut state, "Parrier", "Fighter", 5, &abilities, 30, 15, "Human",
    );
    set_field(
        &mut state,
        &parrier,
        "wielded_main",
        wielded_melee_item("SwordLong"),
    );
    grant_weapon_spec(
        &mut state,
        &parrier,
        "SpecMelee",
        "MeleeWeapon",
        "SwordLong",
        "Single",
    );

    let mut handler = ScriptedHandler::with_responses(vec![]);
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "parry_bonus",
            vec![Value::Entity(parrier)],
        )
        .unwrap();
    assert_eq!(
        val,
        Value::Int(2),
        "STR 17 (+1) + Single spec (+1) → parry_bonus = 2"
    );
}

#[test]
fn parry_bonus_zero_with_no_str_bonus() {
    // STR 12 → +0 to hit. No weapon spec. Parry bonus = 0.
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let parrier = make_character(
        &mut state,
        "Parrier",
        "Fighter",
        5,
        &standard_abilities_12(),
        30,
        15,
        "Human",
    );
    set_field(
        &mut state,
        &parrier,
        "wielded_main",
        wielded_melee_item("SwordLong"),
    );

    let mut handler = ScriptedHandler::with_responses(vec![]);
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "parry_bonus",
            vec![Value::Entity(parrier)],
        )
        .unwrap();
    assert_eq!(
        val,
        Value::Int(0),
        "STR 12 gives +0 to hit → parry_bonus = 0"
    );
}

#[test]
fn parry_action_applies_condition_and_penalises_attacker() {
    // Parrier: STR 17 (+1 to-hit), single spec longsword (+1) → parry_bonus = 2.
    // Attacker: Fighter L1, STR 12, no spec.
    // Attacker rolls 14 → 14+0(BTHB)+0(STR)+0(spec) = 14, but parry subtracts 2 → effective 12 < 14 AC → miss.
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let parrier_abilities = vec![
        ("STR", 17),
        ("DEX", 12),
        ("CON", 12),
        ("INT", 12),
        ("WIS", 12),
        ("CHA", 12),
    ];
    let parrier = make_character(
        &mut state,
        "Parrier",
        "Fighter",
        5,
        &parrier_abilities,
        30,
        14,
        "Human",
    );
    set_field(
        &mut state,
        &parrier,
        "wielded_main",
        wielded_melee_item("SwordLong"),
    );
    grant_weapon_spec(
        &mut state,
        &parrier,
        "SpecMelee",
        "MeleeWeapon",
        "SwordLong",
        "Single",
    );

    let attacker = make_character(
        &mut state,
        "Attacker",
        "Fighter",
        1,
        &standard_abilities_12(),
        10,
        10,
        "Human",
    );
    set_field(
        &mut state,
        &attacker,
        "wielded_main",
        wielded_melee_item("SwordLong"),
    );

    // Execute Parry action on the parrier
    state.set_turn_budget(&parrier, combat_turn_budget());
    let mut parry_handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, // ActionStarted
        Response::Acknowledged, // RequiresCheck (wielded → pass)
        Response::Acknowledged, // DeductCost(attack)
        Response::Acknowledged, // ConditionApplyGate (Parrying)
    ]);

    let adapter = StateAdapter::new(state);
    adapter.run(&mut parry_handler, |state, eff_handler| {
        interp
            .execute_action(state, eff_handler, "Parry", parrier, vec![])
            .unwrap();
    });
    let mut state = adapter.into_inner();

    // Now attacker makes a melee attack on the parrier.
    // Roll 14 → 14+0(BTHB)+0(STR)+0(spec) = 14, but Parrying subtracts 2 → 12 < 14 AC → miss.
    state.set_turn_budget(&attacker, combat_turn_budget());
    let atk_roll = scripted_roll(1, 20, 0, vec![14], vec![14], 14, 14);
    let mut attack_handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, // ActionStarted
        Response::Acknowledged, // RequiresCheck
        Response::Acknowledged, // DeductCost
        Response::Acknowledged, // ModifyApplied (Parrying condition)
        atk_roll,
    ]);

    let adapter = StateAdapter::new(state);
    adapter.run(&mut attack_handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "MeleeAttack",
                attacker,
                vec![Value::Entity(parrier)],
            )
            .unwrap();
    });

    let final_state = adapter.into_inner();
    let hp = read_group_field(&final_state, &parrier, "HitPoints", "hp").unwrap();
    assert_eq!(
        hp,
        Value::Int(30),
        "parrier HP should remain 30 — attack missed due to parry penalty"
    );
}

#[test]
fn parry_action_without_parry_same_roll_would_hit() {
    // Same setup as above but without parrying. Roll 14 → 14 >= 14 → hit.
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let parrier = make_character(
        &mut state,
        "Target",
        "Fighter",
        5,
        &standard_abilities_12(),
        30,
        14,
        "Human",
    );
    set_field(
        &mut state,
        &parrier,
        "wielded_main",
        wielded_melee_item("SwordLong"),
    );

    let attacker = make_character(
        &mut state,
        "Attacker",
        "Fighter",
        1,
        &standard_abilities_12(),
        10,
        10,
        "Human",
    );
    set_field(
        &mut state,
        &attacker,
        "wielded_main",
        wielded_melee_item("SwordLong"),
    );

    // No Parry action — directly attack. Roll 14 → 14+0+0 = 14 >= 14 → hit.
    state.set_turn_budget(&attacker, combat_turn_budget());
    let atk_roll = scripted_roll(1, 20, 0, vec![14], vec![14], 14, 14);
    let dmg_roll = scripted_roll(1, 8, 0, vec![5], vec![5], 5, 5);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged,
        Response::Acknowledged,
        Response::Acknowledged,
        atk_roll,
        dmg_roll,
    ]);

    let adapter = StateAdapter::new(state);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "MeleeAttack",
                attacker,
                vec![Value::Entity(parrier)],
            )
            .unwrap();
    });

    let final_state = adapter.into_inner();
    let hp = read_group_field(&final_state, &parrier, "HitPoints", "hp").unwrap();
    assert_eq!(
        hp,
        Value::Int(25),
        "target HP should be 30 - 5 = 25 (hit without parry)"
    );
}

// ── Two-Weapon Fighting (§1.6.3.4) ────────────────────────────

#[test]
fn two_weapon_valid_offhand_dagger() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = ScriptedHandler::with_responses(vec![]);
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "is_valid_offhand_weapon",
            vec![enum_variant("MeleeWeapon", "Dagger")],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(true));
}

#[test]
fn two_weapon_valid_offhand_hand_axe() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = ScriptedHandler::with_responses(vec![]);
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "is_valid_offhand_weapon",
            vec![enum_variant("MeleeWeapon", "HandAxe")],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(true));
}

#[test]
fn two_weapon_invalid_offhand_longsword() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = ScriptedHandler::with_responses(vec![]);
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "is_valid_offhand_weapon",
            vec![enum_variant("MeleeWeapon", "SwordLong")],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(false));
}

#[test]
fn two_weapon_primary_penalty_dex_12() {
    // DEX 12 → dex_missile = 0. Primary penalty = max(-1, -2 + 0) = -2.
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = ScriptedHandler::with_responses(vec![]);
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "two_weapon_primary_penalty",
            vec![Value::Int(12)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(-2), "DEX 12: primary penalty = -2");
}

#[test]
fn two_weapon_offhand_penalty_dex_12() {
    // DEX 12 → dex_missile = 0. Off-hand penalty = max(-1, -4 + 0) = -4.
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = ScriptedHandler::with_responses(vec![]);
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "two_weapon_offhand_penalty",
            vec![Value::Int(12)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(-4), "DEX 12: off-hand penalty = -4");
}

#[test]
fn two_weapon_primary_penalty_dex_18() {
    // DEX 18 → dex_missile = +3. Primary penalty = min(-1, -2 + 3) = min(-1, 1) = -1.
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = ScriptedHandler::with_responses(vec![]);
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "two_weapon_primary_penalty",
            vec![Value::Int(18)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(-1), "DEX 18: primary penalty capped at -1");
}

#[test]
fn two_weapon_offhand_penalty_dex_18() {
    // DEX 18 → dex_missile = +3. Off-hand penalty = min(-1, -4 + 3) = min(-1, -1) = -1.
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = ScriptedHandler::with_responses(vec![]);
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "two_weapon_offhand_penalty",
            vec![Value::Int(18)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(-1), "DEX 18: off-hand penalty capped at -1");
}

#[test]
fn two_weapon_offhand_penalty_dex_3() {
    // DEX 3 → dex_missile = -3. Off-hand penalty = min(-1, -4 + (-3)) = -7.
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = ScriptedHandler::with_responses(vec![]);
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "two_weapon_offhand_penalty",
            vec![Value::Int(3)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(-7), "DEX 3: off-hand penalty = -7");
}

#[test]
fn two_weapon_attack_both_hit() {
    // Fighter L1, STR 12, DEX 12 → primary -2, off-hand -4.
    // Main: SwordLong, Off: Dagger.
    // Target: AC 10, 30 HP.
    // Primary roll 20 (natural 20 → +5 bonus, auto-hit). Damage: 1d8 → 5.
    // Off-hand roll 20 (natural 20 → auto-hit). Damage: 1d4 → 3.
    // Target HP: 30 - 5 - 3 = 22.
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "DualWielder",
        "Fighter",
        1,
        &standard_abilities_12(),
        10,
        10,
        "Human",
    );
    set_field(
        &mut state,
        &attacker,
        "wielded_main",
        wielded_melee_item("SwordLong"),
    );
    set_field(
        &mut state,
        &attacker,
        "wielded_off",
        wielded_melee_item("Dagger"),
    );

    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities_12(),
        30,
        10,
        "Human",
    );

    state.set_turn_budget(&attacker, combat_turn_budget());

    // Primary attack: roll 20, damage 1d8 → 5
    let primary_atk = scripted_roll(1, 20, 0, vec![20], vec![20], 20, 20);
    let primary_dmg = scripted_roll(1, 8, 0, vec![5], vec![5], 5, 5);
    // Off-hand attack: roll 20, damage 1d4 → 3
    let offhand_atk = scripted_roll(1, 20, 0, vec![20], vec![20], 20, 20);
    let offhand_dmg = scripted_roll(1, 4, 0, vec![3], vec![3], 3, 3);

    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, // ActionStarted
        Response::Acknowledged, // RequiresCheck
        Response::Acknowledged, // DeductCost(attack)
        primary_atk,            // Primary attack roll
        primary_dmg,            // Primary damage roll
        Response::Acknowledged, // TakeDamage ActionStarted
        Response::Acknowledged, // DeductCost (free)
        Response::Acknowledged, // Damaged event
        Response::Acknowledged, // TakeDamage ActionCompleted
        offhand_atk,            // Off-hand attack roll
        offhand_dmg,            // Off-hand damage roll
        Response::Acknowledged, // TakeDamage ActionStarted
        Response::Acknowledged, // DeductCost (free)
        Response::Acknowledged, // Damaged event
        Response::Acknowledged, // TakeDamage ActionCompleted
        Response::Acknowledged, // ActionCompleted
    ]);

    let adapter = StateAdapter::new(state);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "TwoWeaponAttack",
                attacker,
                vec![Value::Entity(target)],
            )
            .unwrap();
    });

    let final_state = adapter.into_inner();
    let hp = read_group_field(&final_state, &target, "HitPoints", "hp").unwrap();
    assert_eq!(hp, Value::Int(22), "target HP should be 30 - 5 - 3 = 22");
}

// ── effective_target_ac for Monster targets ───────────────────

#[test]
fn effective_target_ac_monster_returns_flat_ac() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let orc = make_monster(&mut state, "Orc", (1, 8, 0), 8, 14, vec![]);

    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "effective_target_ac",
            vec![Value::Entity(orc)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(14), "monster effective AC should equal its ac field");
}

#[test]
fn effective_target_ac_monster_with_ac_mod() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let dragon = make_monster(&mut state, "Dragon", (10, 8, 0), 50, 18, vec![]);

    // include_dex=true, include_shield=true, ac_mod=-2
    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "effective_target_ac",
            vec![
                Value::Entity(dragon),
                Value::Bool(true),
                Value::Bool(true),
                Value::Int(-2),
            ],
        )
        .unwrap();
    assert_eq!(val, Value::Int(16), "monster effective AC with ac_mod=-2: 18 + (-2) = 16");
}

// ── Monster MeleeAttack action ────────────────────────────────

#[test]
fn monster_melee_attack_hits_and_damages_character() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    // Ogre: 4d8+1 HD → monster_bthb = 5
    let ogre = make_monster(
        &mut state,
        "Ogre",
        (4, 8, 1),
        26,
        15,
        vec![monster_attack("Club", 1, 10, 0)],
    );
    let target = make_character(
        &mut state,
        "Victim",
        "Fighter",
        1,
        &standard_abilities_12(),
        10,
        14,
        "Human",
    );
    state.set_turn_budget(&ogre, combat_turn_budget());

    // Roll 15 → 15+5 = 20 >= 14 → Hit
    let atk_roll = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    // damage: 1d10, roll 6
    let dmg_roll = scripted_roll(1, 10, 0, vec![6], vec![6], 6, 6);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, // ActionStarted
        Response::Acknowledged, // DeductCost
        atk_roll,               // attack roll
        dmg_roll,               // damage roll
        Response::Acknowledged, // TakeDamage ActionStarted
        Response::Acknowledged, // DeductCost (free)
        Response::Acknowledged, // Damaged event
        Response::Acknowledged, // TakeDamage ActionCompleted
        Response::Acknowledged, // ActionCompleted
    ]);

    let adapter = StateAdapter::new(state);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "MeleeAttack",
                ogre,
                vec![
                    Value::Entity(target),
                    monster_attack("Club", 1, 10, 0),
                ],
            )
            .unwrap();
    });

    let final_state = adapter.into_inner();
    let hp = read_group_field(&final_state, &target, "HitPoints", "hp").unwrap();
    assert_eq!(hp, Value::Int(4), "target HP should be 10 - 6 = 4");
}

#[test]
fn monster_melee_attack_miss_preserves_hp() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    // Rat: sub-1 HD → BTHB -1
    let rat = make_monster(
        &mut state,
        "Rat",
        (0, 0, 0),
        1,
        10,
        vec![monster_attack("Bite", 1, 2, 0)],
    );
    let target = make_character(
        &mut state,
        "Warrior",
        "Fighter",
        5,
        &standard_abilities_12(),
        30,
        17,
        "Human",
    );
    state.set_turn_budget(&rat, combat_turn_budget());

    // Roll 10 → 10+(-1) = 9 < 17 → Miss
    let atk_roll = scripted_roll(1, 20, 0, vec![10], vec![10], 10, 10);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, // ActionStarted
        Response::Acknowledged, // DeductCost
        atk_roll,               // attack roll (miss, no damage roll)
        Response::Acknowledged, // ActionCompleted
    ]);

    let adapter = StateAdapter::new(state);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "MeleeAttack",
                rat,
                vec![
                    Value::Entity(target),
                    monster_attack("Bite", 1, 2, 0),
                ],
            )
            .unwrap();
    });

    let final_state = adapter.into_inner();
    let hp = read_group_field(&final_state, &target, "HitPoints", "hp").unwrap();
    assert_eq!(hp, Value::Int(30), "target HP should remain 30 on miss");
}

#[test]
fn monster_melee_attack_against_monster() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    // Ogre attacks a Goblin
    let ogre = make_monster(
        &mut state,
        "Ogre",
        (4, 8, 1),
        26,
        15,
        vec![monster_attack("Club", 1, 10, 0)],
    );
    let goblin = make_monster(
        &mut state,
        "Goblin",
        (1, 8, -1),
        5,
        14,
        vec![monster_attack("Sword", 1, 6, 0)],
    );
    state.set_turn_budget(&ogre, combat_turn_budget());

    // Roll 12 → 12+5 = 17 >= 14 → Hit
    let atk_roll = scripted_roll(1, 20, 0, vec![12], vec![12], 12, 12);
    // damage: 1d10, roll 4
    let dmg_roll = scripted_roll(1, 10, 0, vec![4], vec![4], 4, 4);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, // ActionStarted
        Response::Acknowledged, // DeductCost
        atk_roll,               // attack roll
        dmg_roll,               // damage roll
        Response::Acknowledged, // TakeDamage ActionStarted
        Response::Acknowledged, // DeductCost (free)
        Response::Acknowledged, // Damaged event
        Response::Acknowledged, // TakeDamage ActionCompleted
        Response::Acknowledged, // ActionCompleted
    ]);

    let adapter = StateAdapter::new(state);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "MeleeAttack",
                ogre,
                vec![
                    Value::Entity(goblin),
                    monster_attack("Club", 1, 10, 0),
                ],
            )
            .unwrap();
    });

    let final_state = adapter.into_inner();
    let hp = final_state.read_field(&goblin, "hp").unwrap();
    assert_eq!(hp, Value::Int(1), "goblin HP should be 5 - 4 = 1");
}

// ── resolve_monster_attack vs Monster target ──────────────────

#[test]
fn resolve_monster_attack_against_monster_target() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    // Ogre (4 HD, BTHB=5) attacks a Goblin (AC 14)
    let ogre = make_monster(
        &mut state,
        "Ogre",
        (4, 8, 1),
        26,
        15,
        vec![monster_attack("Club", 1, 10, 0)],
    );
    let goblin = make_monster(
        &mut state,
        "Goblin",
        (1, 8, -1),
        5,
        14,
        vec![],
    );

    // Roll 12 → 12+5 = 17 >= 14 → Hit
    let atk_roll = scripted_roll(1, 20, 0, vec![12], vec![12], 12, 12);
    let dmg_roll = scripted_roll(1, 10, 0, vec![7], vec![7], 7, 7);
    let mut handler = ScriptedHandler::with_responses(vec![atk_roll, dmg_roll]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "resolve_monster_attack",
            vec![
                Value::Entity(ogre),
                Value::Entity(goblin),
                monster_attack("Club", 1, 10, 0),
            ],
        )
        .unwrap();

    match val {
        Value::Struct { name, fields } => {
            assert_eq!(&*name, "AttackResult");
            let fields: BTreeMap<String, Value> = fields
                .into_iter()
                .map(|(k, v)| (k.to_string(), v))
                .collect();
            assert_eq!(
                fields.get("outcome").unwrap(),
                &enum_variant("AttackOutcome", "Hit")
            );
            assert_eq!(get_int(&fields, "damage"), 7);
            assert_eq!(get_int(&fields, "total_mod"), 5);
        }
        other => panic!("expected AttackResult struct, got: {other:?}"),
    }
}
