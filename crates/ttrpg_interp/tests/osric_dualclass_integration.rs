//! OSRIC dual-classing integration tests.
//!
//! Verifies the dual-class rules from osric/osric_dualclass.ttrpg:
//! prime requisite lookups, eligibility checks, HP gain logic,
//! old ability usage, and XP forfeit rules.

use ttrpg_ast::ast::TopLevel;
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

mod osric_common;
use osric_common::*;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_dualclass() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn osric_dualclass_parses_and_typechecks() {
    let (program, _) = compile_osric_dualclass();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSRIC Dualclass"));
}

// ── prime_requisites ──────────────────────────────────────────

#[test]
fn prime_requisites_fighter_is_str() {
    let (program, result) = compile_osric_dualclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "prime_requisites", vec![class_variant("Fighter")])
        .unwrap();
    assert_eq!(val, Value::List(vec![ability("STR")]));
}

#[test]
fn prime_requisites_ranger_is_str_int_wis() {
    let (program, result) = compile_osric_dualclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "prime_requisites", vec![class_variant("Ranger")])
        .unwrap();
    assert_eq!(
        val,
        Value::List(vec![ability("STR"), ability("INT"), ability("WIS")])
    );
}

#[test]
fn prime_requisites_assassin_is_empty() {
    let (program, result) = compile_osric_dualclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "prime_requisites", vec![class_variant("Assassin")])
        .unwrap();
    assert_eq!(val, Value::List(vec![]));
}

// ── meets_dual_class_from_reqs ────────────────────────────────

fn abilities_map(scores: &[(&str, i64)]) -> Value {
    use std::collections::BTreeMap;
    let mut m = BTreeMap::new();
    for &(ab, score) in scores {
        m.insert(ability(ab), Value::Int(score));
    }
    Value::Map(m)
}

#[test]
fn meets_from_reqs_fighter_str_15_passes() {
    let (program, result) = compile_osric_dualclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let abs = abilities_map(&[
        ("STR", 15), ("DEX", 10), ("CON", 10), ("INT", 10), ("WIS", 10), ("CHA", 10),
    ]);
    let val = interp
        .evaluate_derive(&state, &mut handler, "meets_dual_class_from_reqs", vec![class_variant("Fighter"), abs])
        .unwrap();
    assert_eq!(expect_bool(val, "fighter from 15"), true);
}

#[test]
fn meets_from_reqs_fighter_str_14_fails() {
    let (program, result) = compile_osric_dualclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let abs = abilities_map(&[
        ("STR", 14), ("DEX", 10), ("CON", 10), ("INT", 10), ("WIS", 10), ("CHA", 10),
    ]);
    let val = interp
        .evaluate_derive(&state, &mut handler, "meets_dual_class_from_reqs", vec![class_variant("Fighter"), abs])
        .unwrap();
    assert_eq!(expect_bool(val, "fighter from 14"), false);
}

#[test]
fn meets_from_reqs_assassin_always_passes() {
    let (program, result) = compile_osric_dualclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Assassin has no prime requisites — vacuously true
    let abs = abilities_map(&[
        ("STR", 3), ("DEX", 3), ("CON", 3), ("INT", 3), ("WIS", 3), ("CHA", 3),
    ]);
    let val = interp
        .evaluate_derive(&state, &mut handler, "meets_dual_class_from_reqs", vec![class_variant("Assassin"), abs])
        .unwrap();
    assert_eq!(expect_bool(val, "assassin from any"), true);
}

// ── meets_dual_class_to_reqs ──────────────────────────────────

#[test]
fn meets_to_reqs_ranger_all_17_passes() {
    let (program, result) = compile_osric_dualclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let abs = abilities_map(&[
        ("STR", 17), ("DEX", 10), ("CON", 10), ("INT", 17), ("WIS", 17), ("CHA", 10),
    ]);
    let val = interp
        .evaluate_derive(&state, &mut handler, "meets_dual_class_to_reqs", vec![class_variant("Ranger"), abs])
        .unwrap();
    assert_eq!(expect_bool(val, "ranger to 17s"), true);
}

#[test]
fn meets_to_reqs_ranger_one_16_fails() {
    let (program, result) = compile_osric_dualclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // INT only 16 — fails
    let abs = abilities_map(&[
        ("STR", 17), ("DEX", 10), ("CON", 10), ("INT", 16), ("WIS", 17), ("CHA", 10),
    ]);
    let val = interp
        .evaluate_derive(&state, &mut handler, "meets_dual_class_to_reqs", vec![class_variant("Ranger"), abs])
        .unwrap();
    assert_eq!(expect_bool(val, "ranger to 16 int"), false);
}

// ── can_dual_class ────────────────────────────────────────────

#[test]
fn can_dual_class_paladin_to_ranger_example() {
    let (program, result) = compile_osric_dualclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // PG p.69 example: paladin → ranger needs 17 STR, 17 INT, 17 WIS
    // Paladin prime reqs (STR, WIS) need 15+
    let abs = abilities_map(&[
        ("STR", 17), ("DEX", 10), ("CON", 10), ("INT", 17), ("WIS", 17), ("CHA", 17),
    ]);
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "can_dual_class",
            vec![ancestry("Human"), class_variant("Paladin"), class_variant("Ranger"), abs],
        )
        .unwrap();
    assert_eq!(expect_bool(val, "paladin->ranger"), true);
}

#[test]
fn can_dual_class_non_human_fails() {
    let (program, result) = compile_osric_dualclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let abs = abilities_map(&[
        ("STR", 18), ("DEX", 18), ("CON", 18), ("INT", 18), ("WIS", 18), ("CHA", 18),
    ]);
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "can_dual_class",
            vec![ancestry("Elf"), class_variant("Fighter"), class_variant("Thief"), abs],
        )
        .unwrap();
    assert_eq!(expect_bool(val, "elf dual-class"), false);
}

#[test]
fn can_dual_class_same_class_fails() {
    let (program, result) = compile_osric_dualclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let abs = abilities_map(&[
        ("STR", 18), ("DEX", 18), ("CON", 18), ("INT", 18), ("WIS", 18), ("CHA", 18),
    ]);
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "can_dual_class",
            vec![ancestry("Human"), class_variant("Fighter"), class_variant("Fighter"), abs],
        )
        .unwrap();
    assert_eq!(expect_bool(val, "same class"), false);
}

#[test]
fn can_dual_class_fighter_to_thief_borderline() {
    let (program, result) = compile_osric_dualclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Fighter from: STR >= 15 (exactly 15). Thief to: DEX >= 17 (exactly 17).
    let abs = abilities_map(&[
        ("STR", 15), ("DEX", 17), ("CON", 10), ("INT", 10), ("WIS", 10), ("CHA", 10),
    ]);
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "can_dual_class",
            vec![ancestry("Human"), class_variant("Fighter"), class_variant("Thief"), abs],
        )
        .unwrap();
    assert_eq!(expect_bool(val, "fighter->thief borderline"), true);
}

#[test]
fn can_dual_class_fighter_to_thief_str_too_low() {
    let (program, result) = compile_osric_dualclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Fighter from: STR 14 (too low). Thief to: DEX 17 (ok).
    let abs = abilities_map(&[
        ("STR", 14), ("DEX", 17), ("CON", 10), ("INT", 10), ("WIS", 10), ("CHA", 10),
    ]);
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "can_dual_class",
            vec![ancestry("Human"), class_variant("Fighter"), class_variant("Thief"), abs],
        )
        .unwrap();
    assert_eq!(expect_bool(val, "fighter->thief str low"), false);
}

// ── dual_class_new_exceeds_old ────────────────────────────────

fn high_abilities() -> Vec<(&'static str, i64)> {
    vec![
        ("STR", 17), ("DEX", 17), ("CON", 14), ("INT", 17), ("WIS", 17), ("CHA", 17),
    ]
}

#[test]
fn dual_class_new_exceeds_old_false_when_equal() {
    let (program, result) = compile_osric_dualclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // Fighter 5 → Thief 5: new == old, not exceeded
    let char_ref = make_dualclass_character(
        &mut state, "Equal", "Fighter", 5, "Thief", 5, &high_abilities(),
    );
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "dual_class_new_exceeds_old",
            vec![Value::Entity(char_ref)],
        )
        .unwrap();
    assert_eq!(expect_bool(val, "5==5"), false);
}

#[test]
fn dual_class_new_exceeds_old_false_when_lower() {
    let (program, result) = compile_osric_dualclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // Fighter 7 → Thief 3: new < old
    let char_ref = make_dualclass_character(
        &mut state, "Lower", "Fighter", 7, "Thief", 3, &high_abilities(),
    );
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "dual_class_new_exceeds_old",
            vec![Value::Entity(char_ref)],
        )
        .unwrap();
    assert_eq!(expect_bool(val, "3<7"), false);
}

#[test]
fn dual_class_new_exceeds_old_true_when_higher() {
    let (program, result) = compile_osric_dualclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // Fighter 5 → Thief 6: new > old
    let char_ref = make_dualclass_character(
        &mut state, "Higher", "Fighter", 5, "Thief", 6, &high_abilities(),
    );
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "dual_class_new_exceeds_old",
            vec![Value::Entity(char_ref)],
        )
        .unwrap();
    assert_eq!(expect_bool(val, "6>5"), true);
}

// ── dual_class_hp_gain ────────────────────────────────────────

#[test]
fn dual_class_hp_gain_zero_when_not_exceeded() {
    let (program, result) = compile_osric_dualclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // die_roll=6, con_mod=+1, new_exceeds_old=false → 0
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "dual_class_hp_gain",
            vec![Value::Int(6), Value::Int(1), Value::Bool(false)],
        )
        .unwrap();
    assert_eq!(expect_int(val, "no hp gain"), 0);
}

#[test]
fn dual_class_hp_gain_full_when_exceeded() {
    let (program, result) = compile_osric_dualclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // die_roll=6, con_mod=+1, new_exceeds_old=true → 7
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "dual_class_hp_gain",
            vec![Value::Int(6), Value::Int(1), Value::Bool(true)],
        )
        .unwrap();
    assert_eq!(expect_int(val, "hp gain 6+1"), 7);
}

#[test]
fn dual_class_hp_gain_minimum_one() {
    let (program, result) = compile_osric_dualclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // die_roll=1, con_mod=-3, new_exceeds_old=true → min 1
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "dual_class_hp_gain",
            vec![Value::Int(1), Value::Int(-3), Value::Bool(true)],
        )
        .unwrap();
    assert_eq!(expect_int(val, "hp gain min 1"), 1);
}

// ── dual_class_can_use_old_abilities ──────────────────────────

#[test]
fn old_abilities_locked_when_new_lower() {
    let (program, result) = compile_osric_dualclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    let char_ref = make_dualclass_character(
        &mut state, "Locked", "Fighter", 5, "MagicUser", 3, &high_abilities(),
    );
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "dual_class_can_use_old_abilities",
            vec![Value::Entity(char_ref)],
        )
        .unwrap();
    assert_eq!(expect_bool(val, "locked"), false);
}

#[test]
fn old_abilities_unlocked_when_new_higher() {
    let (program, result) = compile_osric_dualclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    let char_ref = make_dualclass_character(
        &mut state, "Unlocked", "Fighter", 5, "MagicUser", 6, &high_abilities(),
    );
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "dual_class_can_use_old_abilities",
            vec![Value::Entity(char_ref)],
        )
        .unwrap();
    assert_eq!(expect_bool(val, "unlocked"), true);
}

// ── dual_class_xp_forfeit ─────────────────────────────────────

#[test]
fn xp_forfeit_no_penalty_when_exceeded() {
    let (program, result) = compile_osric_dualclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // New > old: using old abilities is fine
    let char_ref = make_dualclass_character(
        &mut state, "Free", "Fighter", 5, "Thief", 6, &high_abilities(),
    );
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "dual_class_xp_forfeit",
            vec![Value::Entity(char_ref), Value::Bool(true)],
        )
        .unwrap();
    assert_eq!(expect_bool(val, "no forfeit"), false);
}

#[test]
fn xp_forfeit_penalty_when_not_exceeded_and_used() {
    let (program, result) = compile_osric_dualclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // New < old: used old abilities → forfeit
    let char_ref = make_dualclass_character(
        &mut state, "Forfeit", "Fighter", 5, "Thief", 3, &high_abilities(),
    );
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "dual_class_xp_forfeit",
            vec![Value::Entity(char_ref), Value::Bool(true)],
        )
        .unwrap();
    assert_eq!(expect_bool(val, "forfeit"), true);
}

#[test]
fn xp_forfeit_no_penalty_when_not_exceeded_but_not_used() {
    let (program, result) = compile_osric_dualclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // New < old: did NOT use old abilities → no forfeit
    let char_ref = make_dualclass_character(
        &mut state, "Safe", "Fighter", 5, "Thief", 3, &high_abilities(),
    );
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "dual_class_xp_forfeit",
            vec![Value::Entity(char_ref), Value::Bool(false)],
        )
        .unwrap();
    assert_eq!(expect_bool(val, "no forfeit"), false);
}

// ── dual_class_can_read_languages ─────────────────────────────

#[test]
fn read_languages_available_when_old_class_thief() {
    let (program, result) = compile_osric_dualclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // Thief → Fighter: Read Languages always available
    let char_ref = make_dualclass_character(
        &mut state, "ExThief", "Thief", 5, "Fighter", 2, &high_abilities(),
    );
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "dual_class_can_read_languages",
            vec![Value::Entity(char_ref)],
        )
        .unwrap();
    assert_eq!(expect_bool(val, "read languages"), true);
}

#[test]
fn read_languages_unavailable_when_old_class_not_thief() {
    let (program, result) = compile_osric_dualclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // Fighter → Thief: no Read Languages exception (old class wasn't Thief)
    let char_ref = make_dualclass_character(
        &mut state, "ExFighter", "Fighter", 5, "Thief", 2, &high_abilities(),
    );
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "dual_class_can_read_languages",
            vec![Value::Entity(char_ref)],
        )
        .unwrap();
    assert_eq!(expect_bool(val, "no read languages"), false);
}
