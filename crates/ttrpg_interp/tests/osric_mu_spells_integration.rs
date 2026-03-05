//! OSRIC magic-user spell effects integration tests.
//!
//! Tests Magic Missile, Fireball resolve functions and SpellDef derives.

use std::collections::VecDeque;

use ttrpg_interp::adapter::StateAdapter;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

mod osric_common;
use osric_common::*;

// ── Helpers ─────────────────────────────────────────────────

fn compile_all() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

/// Handler that returns scripted Rolled responses for RollDice effects
/// and Acknowledged for everything else, avoiding position-dependent ordering issues.
struct RollHandler {
    rolls: VecDeque<Response>,
}

impl RollHandler {
    fn new(rolls: Vec<Response>) -> Self {
        RollHandler {
            rolls: rolls.into(),
        }
    }
}

impl EffectHandler for RollHandler {
    fn handle(&mut self, effect: Effect) -> Response {
        match effect {
            Effect::RollDice { .. } => self
                .rolls
                .pop_front()
                .expect("RollHandler: ran out of scripted rolls"),
            _ => Response::Acknowledged,
        }
    }
}

fn run_function_with_rolls(
    interp: &Interpreter,
    state: GameState,
    rolls: Vec<Response>,
    func: &str,
    args: Vec<Value>,
) -> GameState {
    let mut handler = RollHandler::new(rolls);
    let adapter = StateAdapter::new(state);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .evaluate_function(state, eff_handler, func, args)
            .unwrap();
    });
    adapter.into_inner()
}

fn read_hp(state: &GameState, entity: &ttrpg_interp::state::EntityRef) -> i64 {
    let val = read_group_field(state, entity, "HitPoints", "hp")
        .expect("entity should have HitPoints.hp");
    match val {
        Value::Int(n) => n,
        other => panic!("expected int for hp, got {other:?}"),
    }
}

/// Scripted 1d4 roll returning the given value.
fn roll_1d4(val: i64) -> Response {
    scripted_roll(1, 4, 0, vec![val], vec![val], val, val)
}

// ── Parse + typecheck ──────────────────────────────────────

#[test]
fn osric_mu_spells_parses_and_typechecks() {
    let (program, _) = compile_all();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            ttrpg_ast::ast::TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSRIC MU Spells"));
}

// ── magic_missile_count derive ─────────────────────────────

#[test]
fn magic_missile_count_scales_correctly() {
    let (program, result) = compile_all();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let cases = [
        (1, 1),
        (2, 1),
        (3, 2),
        (4, 2),
        (5, 3),
        (7, 4),
        (9, 5),
        (11, 6),
    ];

    for (level, expected) in &cases {
        let val = interp
            .evaluate_derive(
                &state,
                &mut handler,
                "magic_missile_count",
                vec![Value::Int(*level)],
            )
            .unwrap();
        assert_eq!(
            expect_int(val, "magic_missile_count"),
            *expected,
            "magic_missile_count({level})"
        );
    }
}

// ── Magic Missile resolve ──────────────────────────────────

#[test]
fn magic_missile_deals_damage_single_target() {
    let (program, result) = compile_all();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let caster = make_caster_with_slots(
        &mut state,
        "Merlin",
        "MagicUser",
        1,
        &standard_abilities_12(),
        4,
        10,
        "Human",
        &[(1, 1)],
    );

    let target = make_character(
        &mut state,
        "Orc",
        "Fighter",
        1,
        &standard_abilities_12(),
        8,
        14,
        "Human",
    );

    // Level 1 MU = 1 missile. Roll 3 on 1d4, +1 = 4 damage.
    let state = run_function_with_rolls(
        &interp,
        state,
        vec![roll_1d4(3)],
        "resolve_magic_missile",
        vec![
            Value::Entity(caster),
            Value::List(vec![Value::Entity(target)]),
        ],
    );

    assert_eq!(
        read_hp(&state, &target),
        4,
        "target should take 4 damage (8 - 4 = 4)"
    );
}

#[test]
fn magic_missile_multiple_missiles_same_target() {
    let (program, result) = compile_all();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let caster = make_caster_with_slots(
        &mut state,
        "Merlin",
        "MagicUser",
        5,
        &standard_abilities_12(),
        10,
        10,
        "Human",
        &[(1, 4), (2, 2), (3, 1)],
    );

    let target = make_character(
        &mut state,
        "Orc",
        "Fighter",
        1,
        &standard_abilities_12(),
        30,
        14,
        "Human",
    );

    // Level 5 MU = 3 missiles. Roll 2, 4, 1 on 1d4 => damage 3, 5, 2 = 10 total.
    let state = run_function_with_rolls(
        &interp,
        state,
        vec![roll_1d4(2), roll_1d4(4), roll_1d4(1)],
        "resolve_magic_missile",
        vec![
            Value::Entity(caster),
            Value::List(vec![
                Value::Entity(target),
                Value::Entity(target),
                Value::Entity(target),
            ]),
        ],
    );

    assert_eq!(
        read_hp(&state, &target),
        20,
        "target should take 10 total damage (30 - 10 = 20)"
    );
}

#[test]
fn magic_missile_split_across_targets() {
    let (program, result) = compile_all();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let caster = make_caster_with_slots(
        &mut state,
        "Merlin",
        "MagicUser",
        3,
        &standard_abilities_12(),
        10,
        10,
        "Human",
        &[(1, 2), (2, 1)],
    );

    let target_a = make_character(
        &mut state,
        "Orc A",
        "Fighter",
        1,
        &standard_abilities_12(),
        10,
        14,
        "Human",
    );

    let target_b = make_character(
        &mut state,
        "Orc B",
        "Fighter",
        1,
        &standard_abilities_12(),
        10,
        14,
        "Human",
    );

    // Level 3 MU = 2 missiles. Roll 3, 2 on 1d4 => damage 4, 3. One per target.
    let state = run_function_with_rolls(
        &interp,
        state,
        vec![roll_1d4(3), roll_1d4(2)],
        "resolve_magic_missile",
        vec![
            Value::Entity(caster),
            Value::List(vec![Value::Entity(target_a), Value::Entity(target_b)]),
        ],
    );

    assert_eq!(
        read_hp(&state, &target_a),
        6,
        "target A should take 4 damage (10 - 4 = 6)"
    );
    assert_eq!(
        read_hp(&state, &target_b),
        7,
        "target B should take 3 damage (10 - 3 = 7)"
    );
}

// ── Fireball resolve ─────────────────────────────────────

fn roll_save(val: i64) -> Response {
    scripted_roll(1, 20, 0, vec![val], vec![val], val, val)
}

#[test]
fn fireball_full_damage_on_failed_save() {
    let (program, result) = compile_all();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let caster = make_caster_with_slots(
        &mut state,
        "Merlin",
        "MagicUser",
        5,
        &standard_abilities_12(),
        10,
        10,
        "Human",
        &[(1, 4), (2, 2), (3, 1)],
    );

    let target = make_character(
        &mut state,
        "Orc",
        "Fighter",
        1,
        &standard_abilities_12(),
        40,
        14,
        "Human",
    );

    // Level 5 MU: 5d6 damage. Script total=18. Save roll=1 (always fails).
    let damage_roll = scripted_roll(5, 6, 0, vec![3, 4, 2, 5, 4], vec![3, 4, 2, 5, 4], 18, 18);
    let state = run_function_with_rolls(
        &interp,
        state,
        vec![damage_roll, roll_save(1)],
        "resolve_fireball",
        vec![
            Value::Entity(caster),
            Value::List(vec![Value::Entity(target)]),
        ],
    );

    assert_eq!(
        read_hp(&state, &target),
        22,
        "target should take 18 full damage (40 - 18 = 22)"
    );
}

#[test]
fn fireball_half_damage_on_successful_save() {
    let (program, result) = compile_all();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let caster = make_caster_with_slots(
        &mut state,
        "Merlin",
        "MagicUser",
        5,
        &standard_abilities_12(),
        10,
        10,
        "Human",
        &[(1, 4), (2, 2), (3, 1)],
    );

    let target = make_character(
        &mut state,
        "Orc",
        "Fighter",
        1,
        &standard_abilities_12(),
        40,
        14,
        "Human",
    );

    // Level 5 MU: 5d6 damage. Script total=18. Save roll=20 (always succeeds).
    // Half of 18 = floor(9) = 9 damage.
    let damage_roll = scripted_roll(5, 6, 0, vec![3, 4, 2, 5, 4], vec![3, 4, 2, 5, 4], 18, 18);
    let state = run_function_with_rolls(
        &interp,
        state,
        vec![damage_roll, roll_save(20)],
        "resolve_fireball",
        vec![
            Value::Entity(caster),
            Value::List(vec![Value::Entity(target)]),
        ],
    );

    assert_eq!(
        read_hp(&state, &target),
        31,
        "target should take 9 half damage (40 - 9 = 31)"
    );
}

#[test]
fn fireball_multiple_targets_mixed_saves() {
    let (program, result) = compile_all();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let caster = make_caster_with_slots(
        &mut state,
        "Merlin",
        "MagicUser",
        3,
        &standard_abilities_12(),
        10,
        10,
        "Human",
        &[(1, 2), (2, 1)],
    );

    let target_a = make_character(
        &mut state,
        "Orc A",
        "Fighter",
        1,
        &standard_abilities_12(),
        20,
        14,
        "Human",
    );

    let target_b = make_character(
        &mut state,
        "Orc B",
        "Fighter",
        1,
        &standard_abilities_12(),
        20,
        14,
        "Human",
    );

    // Level 3 MU: 3d6 damage = 10. Target A fails save (roll 1), Target B saves (roll 20).
    let damage_roll = scripted_roll(3, 6, 0, vec![3, 4, 3], vec![3, 4, 3], 10, 10);
    let state = run_function_with_rolls(
        &interp,
        state,
        vec![damage_roll, roll_save(1), roll_save(20)],
        "resolve_fireball",
        vec![
            Value::Entity(caster),
            Value::List(vec![Value::Entity(target_a), Value::Entity(target_b)]),
        ],
    );

    assert_eq!(
        read_hp(&state, &target_a),
        10,
        "target A should take full 10 damage (20 - 10 = 10)"
    );
    assert_eq!(
        read_hp(&state, &target_b),
        15,
        "target B should take half 5 damage (20 - 5 = 15)"
    );
}

// ── SpellDef ───────────────────────────────────────────────

#[test]
fn fireball_def_has_correct_fields() {
    let (program, result) = compile_all();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "fireball_def", vec![])
        .unwrap();

    let (level, school) = match &val {
        Value::Struct { fields, .. } => (
            expect_int(
                fields
                    .get::<ttrpg_ast::Name>(&"level".into())
                    .cloned()
                    .unwrap(),
                "level",
            ),
            fields
                .get::<ttrpg_ast::Name>(&"school".into())
                .cloned()
                .unwrap(),
        ),
        other => panic!("expected Struct for SpellDef, got {other:?}"),
    };
    assert_eq!(level, 3);
    match school {
        Value::EnumVariant { variant, .. } => assert_eq!(variant.as_str(), "Evocation"),
        other => panic!("expected Evocation variant, got {other:?}"),
    }
}

#[test]
fn magic_missile_def_has_correct_fields() {
    let (program, result) = compile_all();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "magic_missile_def", vec![])
        .unwrap();

    let (level, reversible) = match &val {
        Value::Struct { fields, .. } => (
            expect_int(
                fields
                    .get::<ttrpg_ast::Name>(&"level".into())
                    .cloned()
                    .unwrap(),
                "level",
            ),
            expect_bool(
                fields
                    .get::<ttrpg_ast::Name>(&"reversible".into())
                    .cloned()
                    .unwrap(),
                "reversible",
            ),
        ),
        other => panic!("expected Struct for SpellDef, got {other:?}"),
    };
    assert_eq!(level, 1);
    assert!(!reversible);
}
