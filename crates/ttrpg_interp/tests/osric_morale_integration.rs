//! OSRIC morale integration test.
//!
//! Verifies that osric/osric_morale.ttrpg parses, lowers, and type-checks
//! through the full multi-file pipeline. Exercises base_morale derive,
//! check_morale function (pass, retreat, surrender outcomes), fanatical
//! auto-pass after 2 checks, and reset_morale function.
//!
//! Reference: OSRIC 3.0 Player Guide, §1.6.8 (p.100)

use ttrpg_ast::Name;
use ttrpg_interp::adapter::StateAdapter;
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::{EntityRef, StateProvider};
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

mod osric_common;
use osric_common::*;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_morale() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

// ── Helper: extract MoraleResult fields ────────────────────────

fn extract_morale_result(val: Value) -> (String, i64, i64, i64, i64) {
    match val {
        Value::Struct { fields, .. } => {
            let outcome = match fields.get::<Name>(&"outcome".into()) {
                Some(Value::EnumVariant { variant, .. }) => variant.to_string(),
                other => panic!("expected outcome enum, got {other:?}"),
            };
            let base_morale = expect_int(
                fields.get::<Name>(&"base_morale".into()).unwrap().clone(),
                "base_morale",
            );
            let roll = expect_int(fields.get::<Name>(&"roll".into()).unwrap().clone(), "roll");
            let modified_roll = expect_int(
                fields.get::<Name>(&"modified_roll".into()).unwrap().clone(),
                "modified_roll",
            );
            let margin = expect_int(
                fields.get::<Name>(&"margin".into()).unwrap().clone(),
                "margin",
            );
            (outcome, base_morale, roll, modified_roll, margin)
        }
        other => panic!("expected MoraleResult struct, got {other:?}"),
    }
}

/// Helper: call check_morale via StateAdapter.run pattern.
fn run_check_morale(
    interp: &Interpreter,
    adapter: &StateAdapter<GameState>,
    handler: &mut ScriptedHandler,
    monster: EntityRef,
    modifier: i64,
) -> Value {
    adapter
        .run(handler, |s, h| {
            interp.evaluate_function(
                s,
                h,
                "check_morale",
                vec![Value::Entity(monster), Value::Int(modifier)],
            )
        })
        .unwrap()
}

/// Helper: call reset_morale via StateAdapter.run pattern.
fn run_reset_morale(
    interp: &Interpreter,
    adapter: &StateAdapter<GameState>,
    handler: &mut NullHandler,
    monster: EntityRef,
) {
    adapter
        .run(handler, |s, h| {
            interp.evaluate_function(s, h, "reset_morale", vec![Value::Entity(monster)])
        })
        .unwrap();
}

// ── Tests ──────────────────────────────────────────────────────

/// base_morale: 50 + 5 * dice_count(hit_dice).
#[test]
fn base_morale_from_hit_dice() {
    let (program, result) = compile_osric_morale();
    let mut state = GameState::new();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut handler = NullHandler;

    // 1 HD: 50 + 5 = 55
    let m1 = make_monster(
        &mut state,
        "Goblin",
        (1, 8, 0),
        4,
        14,
        vec![monster_attack("Club", 1, 6, 0)],
    );
    let val = interp
        .evaluate_derive(&state, &mut handler, "base_morale", vec![Value::Entity(m1)])
        .unwrap();
    assert_eq!(val, Value::Int(55), "1 HD -> base morale 55");

    // 8+1 HD: 50 + 40 = 90
    let m8 = make_monster(
        &mut state,
        "Hill Giant",
        (8, 8, 1),
        36,
        16,
        vec![monster_attack("Fist", 2, 6, 0)],
    );
    let val = interp
        .evaluate_derive(&state, &mut handler, "base_morale", vec![Value::Entity(m8)])
        .unwrap();
    assert_eq!(val, Value::Int(90), "8+1 HD -> base morale 90");

    // 4 HD: 50 + 20 = 70
    let m4 = make_monster(
        &mut state,
        "Ogre",
        (4, 8, 0),
        18,
        15,
        vec![monster_attack("Club", 1, 10, 0)],
    );
    let val = interp
        .evaluate_derive(&state, &mut handler, "base_morale", vec![Value::Entity(m4)])
        .unwrap();
    assert_eq!(val, Value::Int(70), "4 HD -> base morale 70");
}

/// check_morale: roll d100 <= base_morale -> Pass.
#[test]
fn morale_check_pass() {
    let (program, result) = compile_osric_morale();
    let mut state = GameState::new();
    let interp = Interpreter::new(&program, &result.env).unwrap();

    let m = make_monster(
        &mut state,
        "Ogre",
        (4, 8, 0),
        18,
        15,
        vec![monster_attack("Club", 1, 10, 0)],
    );

    let adapter = StateAdapter::new(state);

    // Script a d100 roll of 40 (under base morale 70 -> pass)
    let mut handler =
        ScriptedHandler::with_responses(vec![scripted_roll(1, 100, 0, vec![40], vec![40], 40, 40)]);

    let val = run_check_morale(&interp, &adapter, &mut handler, m, 0);
    let (outcome, base_morale, roll, modified_roll, margin) = extract_morale_result(val);
    assert_eq!(outcome, "Pass");
    assert_eq!(base_morale, 70);
    assert_eq!(roll, 40);
    assert_eq!(modified_roll, 40);
    assert_eq!(margin, 0);

    // morale_checks_made should be 1
    let state = adapter.into_inner();
    let checks = state.read_field(&m, "morale_checks_made").unwrap();
    assert_eq!(checks, Value::Int(1));
}

/// check_morale: roll d100 > base_morale by 1-50 -> Retreat.
#[test]
fn morale_check_retreat() {
    let (program, result) = compile_osric_morale();
    let mut state = GameState::new();
    let interp = Interpreter::new(&program, &result.env).unwrap();

    let m = make_monster(
        &mut state,
        "Ogre",
        (4, 8, 0),
        18,
        15,
        vec![monster_attack("Club", 1, 10, 0)],
    );

    let adapter = StateAdapter::new(state);

    // Roll 85 vs base 70 -> fail by 15 -> retreat
    let mut handler =
        ScriptedHandler::with_responses(vec![scripted_roll(1, 100, 0, vec![85], vec![85], 85, 85)]);

    let val = run_check_morale(&interp, &adapter, &mut handler, m, 0);
    let (outcome, base_morale, _, _, margin) = extract_morale_result(val);
    assert_eq!(outcome, "Retreat");
    assert_eq!(base_morale, 70);
    assert_eq!(margin, 15);
}

/// check_morale: roll d100 > base_morale by 51+ -> Surrender.
#[test]
fn morale_check_surrender() {
    let (program, result) = compile_osric_morale();
    let mut state = GameState::new();
    let interp = Interpreter::new(&program, &result.env).unwrap();

    let m = make_monster(
        &mut state,
        "Goblin",
        (1, 8, 0),
        4,
        14,
        vec![monster_attack("Club", 1, 6, 0)],
    );

    let adapter = StateAdapter::new(state);

    // Roll 50, modifier +60 -> modified 110 vs base 55 -> margin 55 -> surrender
    let mut handler =
        ScriptedHandler::with_responses(vec![scripted_roll(1, 100, 0, vec![50], vec![50], 50, 50)]);

    let val = run_check_morale(&interp, &adapter, &mut handler, m, 60);
    let (outcome, base_morale, roll, modified_roll, margin) = extract_morale_result(val);
    assert_eq!(outcome, "Surrender");
    assert_eq!(base_morale, 55);
    assert_eq!(roll, 50);
    assert_eq!(modified_roll, 110);
    assert_eq!(margin, 55);
}

/// Negative modifier helps pass a borderline check.
#[test]
fn morale_check_modifier_helps_pass() {
    let (program, result) = compile_osric_morale();
    let mut state = GameState::new();
    let interp = Interpreter::new(&program, &result.env).unwrap();

    let m = make_monster(
        &mut state,
        "Ogre",
        (4, 8, 0),
        18,
        15,
        vec![monster_attack("Club", 1, 10, 0)],
    );

    let adapter = StateAdapter::new(state);

    // Roll 75, modifier -10 -> modified 65 vs base 70 -> pass
    let mut handler =
        ScriptedHandler::with_responses(vec![scripted_roll(1, 100, 0, vec![75], vec![75], 75, 75)]);

    let val = run_check_morale(&interp, &adapter, &mut handler, m, -10);
    let (outcome, _, _, modified_roll, _) = extract_morale_result(val);
    assert_eq!(outcome, "Pass");
    assert_eq!(modified_roll, 65);
}

/// After 2 passed checks, monster is fanatical and auto-passes.
#[test]
fn morale_fanatical_after_two_checks() {
    let (program, result) = compile_osric_morale();
    let mut state = GameState::new();
    let interp = Interpreter::new(&program, &result.env).unwrap();

    let m = make_monster(
        &mut state,
        "Ogre",
        (4, 8, 0),
        18,
        15,
        vec![monster_attack("Club", 1, 10, 0)],
    );

    let adapter = StateAdapter::new(state);

    // First check: roll 40 -> pass
    let mut handler =
        ScriptedHandler::with_responses(vec![scripted_roll(1, 100, 0, vec![40], vec![40], 40, 40)]);
    let _ = run_check_morale(&interp, &adapter, &mut handler, m, 0);

    // Second check: roll 50 -> pass
    let mut handler =
        ScriptedHandler::with_responses(vec![scripted_roll(1, 100, 0, vec![50], vec![50], 50, 50)]);
    let _ = run_check_morale(&interp, &adapter, &mut handler, m, 0);

    // Third check: auto-pass (fanatical), no dice roll needed
    let mut handler = ScriptedHandler::with_responses(vec![]);
    let val = run_check_morale(&interp, &adapter, &mut handler, m, 0);
    let (outcome, base_morale, roll, modified_roll, margin) = extract_morale_result(val);
    assert_eq!(outcome, "Pass", "fanatical auto-pass");
    assert_eq!(base_morale, 70);
    assert_eq!(roll, 0);
    assert_eq!(modified_roll, 0);
    assert_eq!(margin, 0);

    // Counter should still be 2 (no increment for fanatical)
    let state = adapter.into_inner();
    let checks = state.read_field(&m, "morale_checks_made").unwrap();
    assert_eq!(checks, Value::Int(2));
}

/// reset_morale clears the check counter.
#[test]
fn reset_morale_clears_counter() {
    let (program, result) = compile_osric_morale();
    let mut state = GameState::new();
    let interp = Interpreter::new(&program, &result.env).unwrap();

    let m = make_monster(
        &mut state,
        "Ogre",
        (4, 8, 0),
        18,
        15,
        vec![monster_attack("Club", 1, 10, 0)],
    );

    let adapter = StateAdapter::new(state);

    // Make one check
    let mut handler =
        ScriptedHandler::with_responses(vec![scripted_roll(1, 100, 0, vec![40], vec![40], 40, 40)]);
    let _ = run_check_morale(&interp, &adapter, &mut handler, m, 0);

    // Reset
    let mut handler = NullHandler;
    run_reset_morale(&interp, &adapter, &mut handler, m);

    let state = adapter.into_inner();
    let checks = state.read_field(&m, "morale_checks_made").unwrap();
    assert_eq!(checks, Value::Int(0));
}

/// Boundary: margin exactly 50 -> Retreat, margin 51 -> Surrender.
#[test]
fn morale_retreat_surrender_boundary() {
    let (program, result) = compile_osric_morale();
    let mut state = GameState::new();
    let interp = Interpreter::new(&program, &result.env).unwrap();

    // 1 HD, base morale = 55

    // Margin 50: roll 5, modifier +100 -> modified 105 vs 55 -> margin 50 -> Retreat
    let m1 = make_monster(
        &mut state,
        "Goblin A",
        (1, 8, 0),
        4,
        14,
        vec![monster_attack("Club", 1, 6, 0)],
    );

    // Margin 51: roll 6, modifier +100 -> modified 106 vs 55 -> margin 51 -> Surrender
    let m2 = make_monster(
        &mut state,
        "Goblin B",
        (1, 8, 0),
        4,
        14,
        vec![monster_attack("Club", 1, 6, 0)],
    );

    let adapter = StateAdapter::new(state);

    let mut handler =
        ScriptedHandler::with_responses(vec![scripted_roll(1, 100, 0, vec![5], vec![5], 5, 5)]);
    let val = run_check_morale(&interp, &adapter, &mut handler, m1, 100);
    let (outcome, _, _, _, margin) = extract_morale_result(val);
    assert_eq!(outcome, "Retreat");
    assert_eq!(margin, 50);

    let mut handler =
        ScriptedHandler::with_responses(vec![scripted_roll(1, 100, 0, vec![6], vec![6], 6, 6)]);
    let val = run_check_morale(&interp, &adapter, &mut handler, m2, 100);
    let (outcome, _, _, _, margin) = extract_morale_result(val);
    assert_eq!(outcome, "Surrender");
    assert_eq!(margin, 51);
}
