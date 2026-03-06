//! OSRIC cleric spell effects integration tests.
//!
//! Tests caster_level derive, SpellDef derives, and resolve functions
//! for Cure Light Wounds and Cause Light Wounds.

use ttrpg_interp::effect::Response;
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::StateProvider;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

mod osric_common;
use osric_common::*;

// ── Compile helper ──────────────────────────────────────────

fn compile_all() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

/// Scripted 1d8 roll returning the given value.
fn roll_1d8(val: i64) -> Response {
    scripted_roll(1, 8, 0, vec![val], vec![val], val, val)
}

// ── Parse + typecheck ──────────────────────────────────────

#[test]
fn osric_cleric_spells_parses_and_typechecks() {
    let (program, _) = compile_all();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            ttrpg_ast::ast::TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSRIC Cleric Spells"));
}

// ── caster_level derive ────────────────────────────────────

#[test]
fn caster_level_for_single_class_cleric() {
    let (program, result) = compile_all();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    let caster = make_caster_with_slots(
        &mut state,
        "Alaric",
        "Cleric",
        5,
        &standard_abilities_12(),
        20,
        10,
        "Human",
        &[(1, 3), (2, 3), (3, 1)],
    );

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "caster_level",
            vec![
                Value::Entity(caster),
                enum_variant("SpellClassType", "Divine"),
            ],
        )
        .unwrap();
    assert_eq!(expect_int(val, "caster_level"), 5);
}

#[test]
fn caster_level_for_magic_user() {
    let (program, result) = compile_all();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    let caster = make_caster_with_slots(
        &mut state,
        "Merlin",
        "MagicUser",
        7,
        &standard_abilities_12(),
        15,
        10,
        "Human",
        &[(1, 4), (2, 3), (3, 2), (4, 1)],
    );

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "caster_level",
            vec![
                Value::Entity(caster),
                enum_variant("SpellClassType", "Arcane"),
            ],
        )
        .unwrap();
    assert_eq!(expect_int(val, "caster_level"), 7);
}

#[test]
fn caster_level_returns_zero_for_non_caster() {
    let (program, result) = compile_all();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    let fighter = make_character(
        &mut state,
        "Borin",
        "Fighter",
        5,
        &standard_abilities_12(),
        40,
        17,
        "Human",
    );

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "caster_level",
            vec![
                Value::Entity(fighter),
                enum_variant("SpellClassType", "Arcane"),
            ],
        )
        .unwrap();
    assert_eq!(expect_int(val, "caster_level"), 0);
}

// ── Cure Light Wounds ──────────────────────────────────────

#[test]
fn clw_heals_conscious_target() {
    let (program, result) = compile_all();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let caster = make_caster_with_slots(
        &mut state,
        "Alaric",
        "Cleric",
        3,
        &standard_abilities_12(),
        20,
        10,
        "Human",
        &[(1, 2)],
    );

    let target = make_character(
        &mut state,
        "Borin",
        "Fighter",
        5,
        &standard_abilities_12(),
        30,
        17,
        "Human",
    );

    // Wound target: 30 -> 10 HP
    let mut handler = ScriptedHandler::with_responses(vec![]);
    let state = run_action(
        &interp,
        state,
        &mut handler,
        "TakeDamage",
        target,
        vec![Value::Entity(caster), Value::Int(20)],
    );
    assert_eq!(read_hp(&state, &target), 10);

    // Cast CLW with scripted roll of 5
    let mut handler = ScriptedHandler::with_responses(vec![roll_1d8(5)]);
    let state = run_function(
        &interp,
        state,
        &mut handler,
        "resolve_cure_light_wounds",
        vec![Value::Entity(caster), Value::Entity(target)],
    );

    assert_eq!(read_hp(&state, &target), 15, "should heal 5 HP (10+5=15)");
}

#[test]
fn clw_does_not_exceed_max_hp() {
    let (program, result) = compile_all();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let caster = make_caster_with_slots(
        &mut state,
        "Alaric",
        "Cleric",
        3,
        &standard_abilities_12(),
        20,
        10,
        "Human",
        &[(1, 2)],
    );

    let target = make_character(
        &mut state,
        "Borin",
        "Fighter",
        5,
        &standard_abilities_12(),
        30,
        17,
        "Human",
    );

    // Wound target: 30 -> 28
    let mut handler = ScriptedHandler::with_responses(vec![]);
    let state = run_action(
        &interp,
        state,
        &mut handler,
        "TakeDamage",
        target,
        vec![Value::Entity(caster), Value::Int(2)],
    );
    assert_eq!(read_hp(&state, &target), 28);

    // Roll 8 for healing — should cap at 30
    let mut handler = ScriptedHandler::with_responses(vec![roll_1d8(8)]);
    let state = run_function(
        &interp,
        state,
        &mut handler,
        "resolve_cure_light_wounds",
        vec![Value::Entity(caster), Value::Entity(target)],
    );

    assert_eq!(read_hp(&state, &target), 30, "HP should cap at max_hp (30)");
}

// ── Cause Light Wounds ─────────────────────────────────────

#[test]
fn cause_light_wounds_deals_damage() {
    let (program, result) = compile_all();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let caster = make_caster_with_slots(
        &mut state,
        "Alaric",
        "Cleric",
        3,
        &standard_abilities_12(),
        20,
        10,
        "Human",
        &[(1, 2)],
    );

    let target = make_character(
        &mut state,
        "Borin",
        "Fighter",
        5,
        &standard_abilities_12(),
        30,
        17,
        "Human",
    );

    // Roll 6 for damage. TakeDamage also needs a deal_damage roll which is identity (returns raw_damage).
    let mut handler = ScriptedHandler::with_responses(vec![roll_1d8(6)]);
    let state = run_function(
        &interp,
        state,
        &mut handler,
        "resolve_cause_light_wounds",
        vec![Value::Entity(caster), Value::Entity(target)],
    );

    assert_eq!(
        read_hp(&state, &target),
        24,
        "should take 6 damage (30-6=24)"
    );
}

#[test]
fn cause_light_wounds_can_knock_unconscious() {
    let (program, result) = compile_all();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let caster = make_caster_with_slots(
        &mut state,
        "Alaric",
        "Cleric",
        3,
        &standard_abilities_12(),
        20,
        10,
        "Human",
        &[(1, 2)],
    );

    let target = make_character(
        &mut state,
        "Borin",
        "Fighter",
        5,
        &standard_abilities_12(),
        30,
        17,
        "Human",
    );

    // Wound target to 3 HP first
    let mut handler = ScriptedHandler::with_responses(vec![]);
    let state = run_action(
        &interp,
        state,
        &mut handler,
        "TakeDamage",
        target,
        vec![Value::Entity(caster), Value::Int(27)],
    );
    assert_eq!(read_hp(&state, &target), 3);

    // Roll 8 damage via Cause Light Wounds — takes target to -5 HP
    let mut handler = ScriptedHandler::with_responses(vec![roll_1d8(8)]);
    let state = run_function(
        &interp,
        state,
        &mut handler,
        "resolve_cause_light_wounds",
        vec![Value::Entity(caster), Value::Entity(target)],
    );

    assert_eq!(read_hp(&state, &target), -5);
    let conditions = state.read_conditions(&target).unwrap_or_default();
    assert!(
        conditions.iter().any(|c| &*c.name == "Unconscious"),
        "target should be unconscious at -5 HP"
    );
    assert!(
        conditions.iter().any(|c| &*c.name == "Bleeding"),
        "target should be bleeding at -5 HP"
    );
}

// ── Bless ──────────────────────────────────────────────────

#[test]
fn bless_applies_blessed_condition() {
    let (program, result) = compile_all();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let caster = make_caster_with_slots(
        &mut state,
        "Alaric",
        "Cleric",
        3,
        &standard_abilities_12(),
        20,
        10,
        "Human",
        &[(1, 2)],
    );

    let target = make_character(
        &mut state,
        "Borin",
        "Fighter",
        5,
        &standard_abilities_12(),
        30,
        17,
        "Human",
    );

    let mut handler = ScriptedHandler::with_responses(vec![]);
    let state = run_function(
        &interp,
        state,
        &mut handler,
        "resolve_bless",
        vec![
            Value::Entity(caster),
            Value::List(vec![Value::Entity(target)]),
        ],
    );

    let conditions = state.read_conditions(&target).unwrap_or_default();
    assert!(
        conditions.iter().any(|c| &*c.name == "Blessed"),
        "target should have Blessed condition, got: {:?}",
        conditions.iter().map(|c| &c.name).collect::<Vec<_>>()
    );
}

#[test]
fn bless_def_has_correct_fields() {
    let (program, result) = compile_all();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "bless_def", vec![])
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
    assert!(reversible);
}

// ── Curse ──────────────────────────────────────────────────

#[test]
fn curse_applies_cursed_on_failed_save() {
    let (program, result) = compile_all();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let caster = make_caster_with_slots(
        &mut state,
        "Alaric",
        "Cleric",
        3,
        &standard_abilities_12(),
        20,
        10,
        "Human",
        &[(1, 2)],
    );

    let target = make_character(
        &mut state,
        "Borin",
        "Fighter",
        5,
        &standard_abilities_12(),
        30,
        17,
        "Human",
    );

    // Script a failed save: roll 1 on d20 (natural 1 always fails)
    let save_roll = scripted_roll(1, 20, 0, vec![1], vec![1], 1, 1);
    let state = run_function_with_rolls(
        &interp,
        state,
        vec![save_roll],
        "resolve_curse",
        vec![
            Value::Entity(caster),
            Value::List(vec![Value::Entity(target)]),
        ],
    );

    let conditions = state.read_conditions(&target).unwrap_or_default();
    assert!(
        conditions.iter().any(|c| &*c.name == "Cursed"),
        "target should have Cursed condition on failed save"
    );
}

#[test]
fn curse_does_not_apply_on_successful_save() {
    let (program, result) = compile_all();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let caster = make_caster_with_slots(
        &mut state,
        "Alaric",
        "Cleric",
        3,
        &standard_abilities_12(),
        20,
        10,
        "Human",
        &[(1, 2)],
    );

    let target = make_character(
        &mut state,
        "Borin",
        "Fighter",
        5,
        &standard_abilities_12(),
        30,
        17,
        "Human",
    );

    // Script a successful save: roll 20 on d20 (natural 20 always succeeds)
    let save_roll = scripted_roll(1, 20, 0, vec![20], vec![20], 20, 20);
    let state = run_function_with_rolls(
        &interp,
        state,
        vec![save_roll],
        "resolve_curse",
        vec![
            Value::Entity(caster),
            Value::List(vec![Value::Entity(target)]),
        ],
    );

    let conditions = state.read_conditions(&target).unwrap_or_default();
    assert!(
        !conditions.iter().any(|c| &*c.name == "Cursed"),
        "target should NOT have Cursed condition on successful save"
    );
}

// ── SpellDef derives ───────────────────────────────────────

#[test]
fn cure_light_wounds_def_has_correct_level() {
    let (program, result) = compile_all();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "cure_light_wounds_def", vec![])
        .unwrap();

    let level = match &val {
        Value::Struct { fields, .. } => fields
            .get::<ttrpg_ast::Name>(&"level".into())
            .cloned()
            .unwrap(),
        other => panic!("expected Struct for SpellDef, got {other:?}"),
    };
    assert_eq!(expect_int(level, "level"), 1);
}

#[test]
fn cause_light_wounds_def_is_reversible() {
    let (program, result) = compile_all();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "cause_light_wounds_def", vec![])
        .unwrap();

    let reversible = match &val {
        Value::Struct { fields, .. } => fields
            .get::<ttrpg_ast::Name>(&"reversible".into())
            .cloned()
            .unwrap(),
        other => panic!("expected Struct for SpellDef, got {other:?}"),
    };
    assert!(expect_bool(reversible, "reversible"));
}

// ── Hold Person ──────────────────────────────────────────

#[test]
fn hold_person_save_bonus_scaling() {
    let (program, result) = compile_all();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let cases = [(1, -2), (2, 0), (3, 2)];
    for (count, expected) in &cases {
        let val = interp
            .evaluate_derive(
                &state,
                &mut handler,
                "hold_person_save_bonus",
                vec![Value::Int(*count)],
            )
            .unwrap();
        assert_eq!(
            expect_int(val, "hold_person_save_bonus"),
            *expected,
            "hold_person_save_bonus({count})"
        );
    }
}

#[test]
fn hold_person_paralyzes_on_failed_save() {
    let (program, result) = compile_all();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let caster = make_caster_with_slots(
        &mut state,
        "Alaric",
        "Cleric",
        5,
        &standard_abilities_12(),
        20,
        10,
        "Human",
        &[(1, 3), (2, 2)],
    );

    let target = make_character(
        &mut state,
        "Bandit",
        "Fighter",
        3,
        &standard_abilities_12(),
        20,
        14,
        "Human",
    );

    // Single target: save at -2. Roll 1 (always fails).
    let state = run_function_with_rolls(
        &interp,
        state,
        vec![roll_save(1)],
        "resolve_hold_person",
        vec![
            Value::Entity(caster),
            Value::List(vec![Value::Entity(target)]),
        ],
    );

    let conditions = state.read_conditions(&target).unwrap_or_default();
    assert!(
        conditions.iter().any(|c| &*c.name == "Paralyzed"),
        "target should be Paralyzed on failed save"
    );
}

#[test]
fn hold_person_no_effect_on_successful_save() {
    let (program, result) = compile_all();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let caster = make_caster_with_slots(
        &mut state,
        "Alaric",
        "Cleric",
        5,
        &standard_abilities_12(),
        20,
        10,
        "Human",
        &[(1, 3), (2, 2)],
    );

    let target = make_character(
        &mut state,
        "Bandit",
        "Fighter",
        3,
        &standard_abilities_12(),
        20,
        14,
        "Human",
    );

    // Single target: save at -2. Roll 20 (always succeeds).
    let state = run_function_with_rolls(
        &interp,
        state,
        vec![roll_save(20)],
        "resolve_hold_person",
        vec![
            Value::Entity(caster),
            Value::List(vec![Value::Entity(target)]),
        ],
    );

    let conditions = state.read_conditions(&target).unwrap_or_default();
    assert!(
        !conditions.iter().any(|c| &*c.name == "Paralyzed"),
        "target should NOT be Paralyzed on successful save"
    );
}

#[test]
fn hold_person_multiple_targets_mixed_saves() {
    let (program, result) = compile_all();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let caster = make_caster_with_slots(
        &mut state,
        "Alaric",
        "Cleric",
        3,
        &standard_abilities_12(),
        20,
        10,
        "Human",
        &[(1, 2), (2, 1)],
    );

    let target_a = make_character(
        &mut state,
        "Bandit A",
        "Fighter",
        3,
        &standard_abilities_12(),
        20,
        14,
        "Human",
    );

    let target_b = make_character(
        &mut state,
        "Bandit B",
        "Fighter",
        3,
        &standard_abilities_12(),
        20,
        14,
        "Human",
    );

    // Two targets: save at 0. Target A fails (roll 1), Target B saves (roll 20).
    let state = run_function_with_rolls(
        &interp,
        state,
        vec![roll_save(1), roll_save(20)],
        "resolve_hold_person",
        vec![
            Value::Entity(caster),
            Value::List(vec![Value::Entity(target_a), Value::Entity(target_b)]),
        ],
    );

    let conds_a = state.read_conditions(&target_a).unwrap_or_default();
    assert!(
        conds_a.iter().any(|c| &*c.name == "Paralyzed"),
        "target A should be Paralyzed"
    );

    let conds_b = state.read_conditions(&target_b).unwrap_or_default();
    assert!(
        !conds_b.iter().any(|c| &*c.name == "Paralyzed"),
        "target B should NOT be Paralyzed"
    );
}

#[test]
fn hold_person_def_has_correct_fields() {
    let (program, result) = compile_all();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "hold_person_def", vec![])
        .unwrap();

    let level = match &val {
        Value::Struct { fields, .. } => fields
            .get::<ttrpg_ast::Name>(&"level".into())
            .cloned()
            .unwrap(),
        other => panic!("expected Struct for SpellDef, got {other:?}"),
    };
    assert_eq!(expect_int(level, "level"), 2);
}
