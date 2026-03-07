//! OSRIC falling damage integration tests (§1.5.5).
//!
//! Tests the mechanics from osric_falling.ttrpg:
//! - Falling damage dice lookup by distance
//! - Full falling damage application with optional saving throw

use std::collections::BTreeMap;

use ttrpg_ast::ast::TopLevel;
use ttrpg_ast::Name;
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::{DiceExpr, Value};
use ttrpg_interp::Interpreter;

mod osric_common;
#[allow(unused_imports)]
use osric_common::*;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_falling() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn osric_falling_parses_and_typechecks() {
    let (program, _) = compile_osric_falling();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSRIC Falling"));
}

// ── Helper: build SavingThrows value ───────────────────────────

fn saving_throws_struct(aimed: i64, breath: i64, death: i64, petrify: i64, spells: i64) -> Value {
    Value::Struct {
        name: Name::from("SavingThrows"),
        fields: {
            let mut f = BTreeMap::new();
            f.insert(Name::from("aimed_magic"), Value::Int(aimed));
            f.insert(Name::from("breath"), Value::Int(breath));
            f.insert(Name::from("death_paralysis_poison"), Value::Int(death));
            f.insert(Name::from("petrification_polymorph"), Value::Int(petrify));
            f.insert(Name::from("spells"), Value::Int(spells));
            f
        },
    }
}

// ── DERIVE TESTS: falling_damage_dice ──────────────────────────

#[test]
fn falling_less_than_10ft_no_damage() {
    let (program, result) = compile_osric_falling();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "falling_damage_dice",
            vec![Value::Int(5)],
        )
        .unwrap();

    assert_eq!(val, Value::DiceExpr(DiceExpr::single(0, 6, None, 0)));
}

#[test]
fn falling_10ft_is_1d6() {
    let (program, result) = compile_osric_falling();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "falling_damage_dice",
            vec![Value::Int(10)],
        )
        .unwrap();

    assert_eq!(val, Value::DiceExpr(DiceExpr::single(1, 6, None, 0)));
}

#[test]
fn falling_20ft_is_3d6() {
    let (program, result) = compile_osric_falling();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "falling_damage_dice",
            vec![Value::Int(20)],
        )
        .unwrap();

    assert_eq!(val, Value::DiceExpr(DiceExpr::single(3, 6, None, 0)));
}

#[test]
fn falling_30ft_is_6d6() {
    let (program, result) = compile_osric_falling();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "falling_damage_dice",
            vec![Value::Int(30)],
        )
        .unwrap();

    assert_eq!(val, Value::DiceExpr(DiceExpr::single(6, 6, None, 0)));
}

#[test]
fn falling_40ft_is_10d6() {
    let (program, result) = compile_osric_falling();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "falling_damage_dice",
            vec![Value::Int(40)],
        )
        .unwrap();

    assert_eq!(val, Value::DiceExpr(DiceExpr::single(10, 6, None, 0)));
}

#[test]
fn falling_50ft_is_15d6() {
    let (program, result) = compile_osric_falling();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "falling_damage_dice",
            vec![Value::Int(50)],
        )
        .unwrap();

    assert_eq!(val, Value::DiceExpr(DiceExpr::single(15, 6, None, 0)));
}

#[test]
fn falling_over_50ft_is_20d6() {
    let (program, result) = compile_osric_falling();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "falling_damage_dice",
            vec![Value::Int(100)],
        )
        .unwrap();

    assert_eq!(val, Value::DiceExpr(DiceExpr::single(20, 6, None, 0)));
}

// ── MECHANIC TESTS: apply_falling_damage ───────────────────────

#[test]
fn falling_no_save_full_damage() {
    let (program, result) = compile_osric_falling();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // 20ft fall = 3d6. Script rolls: 3+4+5 = 12
    let mut handler = ScriptedHandler::with_responses(vec![scripted_roll(
        3,
        6,
        0,
        vec![3, 4, 5],
        vec![3, 4, 5],
        12,
        12,
    )]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "apply_falling_damage",
            vec![
                Value::Int(20),                           // distance_ft
                saving_throws_struct(13, 13, 11, 12, 14), // saves (unused)
                Value::Bool(false),                       // allow_save
                Value::Int(0),                            // save_bonus
            ],
        )
        .unwrap();

    match val {
        Value::Struct { name, fields } => {
            assert_eq!(&*name, "FallingResult");
            assert_eq!(
                *fields.get::<Name>(&"distance_ft".into()).unwrap(),
                Value::Int(20)
            );
            assert_eq!(
                *fields.get::<Name>(&"base_damage".into()).unwrap(),
                Value::Int(12)
            );
            assert_eq!(
                *fields.get::<Name>(&"saved".into()).unwrap(),
                Value::Bool(false)
            );
            assert_eq!(
                *fields.get::<Name>(&"damage_taken".into()).unwrap(),
                Value::Int(12)
            );
        }
        other => panic!("expected FallingResult struct, got {other:?}"),
    }
}

#[test]
fn falling_save_succeeds_halves_damage() {
    let (program, result) = compile_osric_falling();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // 30ft fall = 6d6. Script rolls: 2+3+4+1+2+6 = 18. Save roll: 15 vs 11 = pass.
    // Halved: floor(18/2) = 9.
    let mut handler = ScriptedHandler::with_responses(vec![
        scripted_roll(
            6,
            6,
            0,
            vec![2, 3, 4, 1, 2, 6],
            vec![2, 3, 4, 1, 2, 6],
            18,
            18,
        ),
        scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15),
    ]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "apply_falling_damage",
            vec![
                Value::Int(30),                           // distance_ft
                saving_throws_struct(13, 13, 11, 12, 14), // saves: death save = 11
                Value::Bool(true),                        // allow_save
                Value::Int(0),                            // save_bonus
            ],
        )
        .unwrap();

    match val {
        Value::Struct { name, fields } => {
            assert_eq!(&*name, "FallingResult");
            assert_eq!(
                *fields.get::<Name>(&"base_damage".into()).unwrap(),
                Value::Int(18)
            );
            assert_eq!(
                *fields.get::<Name>(&"saved".into()).unwrap(),
                Value::Bool(true)
            );
            assert_eq!(
                *fields.get::<Name>(&"damage_taken".into()).unwrap(),
                Value::Int(9)
            );
        }
        other => panic!("expected FallingResult struct, got {other:?}"),
    }
}

#[test]
fn falling_save_fails_full_damage() {
    let (program, result) = compile_osric_falling();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // 30ft fall = 6d6. Script rolls: 3+3+3+3+3+3 = 18. Save roll: 5 vs 11 = fail.
    let mut handler = ScriptedHandler::with_responses(vec![
        scripted_roll(
            6,
            6,
            0,
            vec![3, 3, 3, 3, 3, 3],
            vec![3, 3, 3, 3, 3, 3],
            18,
            18,
        ),
        scripted_roll(1, 20, 0, vec![5], vec![5], 5, 5),
    ]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "apply_falling_damage",
            vec![
                Value::Int(30),
                saving_throws_struct(13, 13, 11, 12, 14),
                Value::Bool(true),
                Value::Int(0),
            ],
        )
        .unwrap();

    match val {
        Value::Struct { name, fields } => {
            assert_eq!(&*name, "FallingResult");
            assert_eq!(
                *fields.get::<Name>(&"base_damage".into()).unwrap(),
                Value::Int(18)
            );
            assert_eq!(
                *fields.get::<Name>(&"saved".into()).unwrap(),
                Value::Bool(false)
            );
            assert_eq!(
                *fields.get::<Name>(&"damage_taken".into()).unwrap(),
                Value::Int(18)
            );
        }
        other => panic!("expected FallingResult struct, got {other:?}"),
    }
}

#[test]
fn falling_less_than_10ft_zero_damage_no_save_attempted() {
    let (program, result) = compile_osric_falling();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // <10ft = 0d6. Roll result should be 0. Even with allow_save=true,
    // base==0 means no save is attempted.
    let mut handler =
        ScriptedHandler::with_responses(vec![scripted_roll(0, 6, 0, vec![], vec![], 0, 0)]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "apply_falling_damage",
            vec![
                Value::Int(5),
                saving_throws_struct(13, 13, 11, 12, 14),
                Value::Bool(true),
                Value::Int(0),
            ],
        )
        .unwrap();

    match val {
        Value::Struct { name, fields } => {
            assert_eq!(&*name, "FallingResult");
            assert_eq!(
                *fields.get::<Name>(&"damage_taken".into()).unwrap(),
                Value::Int(0)
            );
            assert_eq!(
                *fields.get::<Name>(&"saved".into()).unwrap(),
                Value::Bool(false)
            );
        }
        other => panic!("expected FallingResult struct, got {other:?}"),
    }
}
