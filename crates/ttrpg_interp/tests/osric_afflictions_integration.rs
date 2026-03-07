//! OSRIC poison, disease & insanity integration tests.
//!
//! Tests the mechanics from osric_afflictions.ttrpg:
//! - Poison: lethal and damage-only with saving throws
//! - Disease: contraction check, parameter rolling, fatality detection
//! - Insanity: table rolling, ability decline, phobia generation

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

fn compile_osric_afflictions() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn osric_afflictions_parses_and_typechecks() {
    let (program, _) = compile_osric_afflictions();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSRIC Afflictions"));
}

// ── Helper: build SavingThrows value ───────────────────────────

fn saving_throws_struct(
    aimed: i64,
    breath: i64,
    death: i64,
    petrify: i64,
    spells: i64,
) -> Value {
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

// ── Helper: build PoisonType enum values ───────────────────────

fn poison_type_lethal() -> Value {
    enum_variant("PoisonType", "Lethal")
}

fn poison_type_damage(dice_count: u32, die_size: u32, modifier: i64) -> Value {
    let mut fields = BTreeMap::new();
    fields.insert(
        Name::from("damage"),
        Value::DiceExpr(DiceExpr::single(dice_count, die_size, None, modifier)),
    );
    enum_variant_with("PoisonType", "DamageOnly", fields)
}

// ── POISON TESTS ───────────────────────────────────────────────

#[test]
fn lethal_poison_save_succeeds() {
    let (program, result) = compile_osric_afflictions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Fighter level 5: death_paralysis_poison save = 11
    // Roll 15 on d20 → 15 >= 11, saves
    let mut handler = ScriptedHandler::with_responses(vec![
        scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15),
    ]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "apply_poison",
            vec![
                saving_throws_struct(13, 13, 11, 12, 14), // fighter level 5
                poison_type_lethal(),
                Value::Int(0), // no modifier
            ],
        )
        .unwrap();

    match val {
        Value::Struct { name, fields } => {
            assert_eq!(&*name, "PoisonResult");
            assert_eq!(*fields.get::<Name>(&"saved".into()).unwrap(), Value::Bool(true));
            assert_eq!(*fields.get::<Name>(&"died".into()).unwrap(), Value::Bool(false));
            assert_eq!(
                *fields.get::<Name>(&"damage_taken".into()).unwrap(),
                Value::Int(0)
            );
        }
        other => panic!("expected PoisonResult struct, got {other:?}"),
    }
}

#[test]
fn lethal_poison_save_fails_kills() {
    let (program, result) = compile_osric_afflictions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // death_paralysis_poison save = 11. Roll 5 → fails.
    let mut handler = ScriptedHandler::with_responses(vec![
        scripted_roll(1, 20, 0, vec![5], vec![5], 5, 5),
    ]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "apply_poison",
            vec![
                saving_throws_struct(13, 13, 11, 12, 14),
                poison_type_lethal(),
                Value::Int(0),
            ],
        )
        .unwrap();

    match val {
        Value::Struct { name, fields } => {
            assert_eq!(&*name, "PoisonResult");
            assert_eq!(*fields.get::<Name>(&"saved".into()).unwrap(), Value::Bool(false));
            assert_eq!(*fields.get::<Name>(&"died".into()).unwrap(), Value::Bool(true));
        }
        other => panic!("expected PoisonResult struct, got {other:?}"),
    }
}

#[test]
fn damage_poison_save_halves_damage() {
    let (program, result) = compile_osric_afflictions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Save succeeds (roll 15 >= 11), then 2d6 damage = 8, half = 4
    let mut handler = ScriptedHandler::with_responses(vec![
        scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15), // save
        scripted_roll(2, 6, 0, vec![5, 3], vec![5, 3], 8, 8), // 2d6 = 8
    ]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "apply_poison",
            vec![
                saving_throws_struct(13, 13, 11, 12, 14),
                poison_type_damage(2, 6, 0),
                Value::Int(0),
            ],
        )
        .unwrap();

    match val {
        Value::Struct { name, fields } => {
            assert_eq!(&*name, "PoisonResult");
            assert_eq!(*fields.get::<Name>(&"saved".into()).unwrap(), Value::Bool(true));
            assert_eq!(*fields.get::<Name>(&"died".into()).unwrap(), Value::Bool(false));
            assert_eq!(
                *fields.get::<Name>(&"damage_taken".into()).unwrap(),
                Value::Int(4) // floor(8/2) = 4
            );
        }
        other => panic!("expected PoisonResult struct, got {other:?}"),
    }
}

#[test]
fn damage_poison_save_fails_full_damage() {
    let (program, result) = compile_osric_afflictions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Save fails (roll 5 < 11), then 2d6 = 10
    let mut handler = ScriptedHandler::with_responses(vec![
        scripted_roll(1, 20, 0, vec![5], vec![5], 5, 5),       // save
        scripted_roll(2, 6, 0, vec![4, 6], vec![4, 6], 10, 10), // 2d6 = 10
    ]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "apply_poison",
            vec![
                saving_throws_struct(13, 13, 11, 12, 14),
                poison_type_damage(2, 6, 0),
                Value::Int(0),
            ],
        )
        .unwrap();

    match val {
        Value::Struct { name, fields } => {
            assert_eq!(&*name, "PoisonResult");
            assert_eq!(*fields.get::<Name>(&"saved".into()).unwrap(), Value::Bool(false));
            assert_eq!(
                *fields.get::<Name>(&"damage_taken".into()).unwrap(),
                Value::Int(10)
            );
        }
        other => panic!("expected PoisonResult struct, got {other:?}"),
    }
}

#[test]
fn lethal_poison_natural_1_always_fails() {
    let (program, result) = compile_osric_afflictions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Natural 1 always fails, even with a very low target (save = 2)
    let mut handler = ScriptedHandler::with_responses(vec![
        scripted_roll(1, 20, 0, vec![1], vec![1], 1, 1),
    ]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "apply_poison",
            vec![
                saving_throws_struct(4, 3, 2, 3, 5), // very good saves
                poison_type_lethal(),
                Value::Int(0),
            ],
        )
        .unwrap();

    match val {
        Value::Struct { fields, .. } => {
            assert_eq!(*fields.get::<Name>(&"saved".into()).unwrap(), Value::Bool(false));
            assert_eq!(*fields.get::<Name>(&"died".into()).unwrap(), Value::Bool(true));
        }
        other => panic!("expected PoisonResult, got {other:?}"),
    }
}

// ── DISEASE TESTS ──────────────────────────────────────────────

#[test]
fn disease_contraction_save_succeeds() {
    let (program, result) = compile_osric_afflictions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Save succeeds (roll 15 >= 11)
    let mut handler = ScriptedHandler::with_responses(vec![
        scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15),
    ]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "check_disease_contraction",
            vec![
                saving_throws_struct(13, 13, 11, 12, 14),
                enum_variant("DiseaseSource", "Plague"),
                Value::Int(0),
            ],
        )
        .unwrap();

    match val {
        Value::Struct { name, fields } => {
            assert_eq!(&*name, "DiseaseCheckResult");
            assert_eq!(
                *fields.get::<Name>(&"contracted".into()).unwrap(),
                Value::Bool(false)
            );
            let params_val = fields.get::<Name>(&"params".into()).unwrap();
            assert!(
                matches!(params_val, Value::Void),
                "expected Option(None), got {params_val:?}"
            );
        }
        other => panic!("expected DiseaseCheckResult, got {other:?}"),
    }
}

#[test]
fn disease_contraction_fails_rolls_params() {
    let (program, result) = compile_osric_afflictions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Save fails (roll 5 < 11), then disease params:
    // inc_d1=3, inc_d2=5 (incubation=8), dur_d1=4, dur_d2=6 (duration=10),
    // stat_pen=4, roll_pen=3, no 8s → not fatal
    let mut handler = ScriptedHandler::with_responses(vec![
        scripted_roll(1, 20, 0, vec![5], vec![5], 5, 5), // save
        scripted_roll(1, 8, 0, vec![3], vec![3], 3, 3),  // inc_d1
        scripted_roll(1, 8, 0, vec![5], vec![5], 5, 5),  // inc_d2
        scripted_roll(1, 8, 0, vec![4], vec![4], 4, 4),  // dur_d1
        scripted_roll(1, 8, 0, vec![6], vec![6], 6, 6),  // dur_d2
        scripted_roll(1, 6, 0, vec![4], vec![4], 4, 4),  // stat_pen
        scripted_roll(1, 6, 0, vec![3], vec![3], 3, 3),  // roll_pen
    ]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "check_disease_contraction",
            vec![
                saving_throws_struct(13, 13, 11, 12, 14),
                enum_variant("DiseaseSource", "Plague"),
                Value::Int(0),
            ],
        )
        .unwrap();

    match val {
        Value::Struct { name, fields } => {
            assert_eq!(&*name, "DiseaseCheckResult");
            assert_eq!(
                *fields.get::<Name>(&"contracted".into()).unwrap(),
                Value::Bool(true)
            );
            match fields.get::<Name>(&"params".into()).unwrap() {
                Value::Option(Some(boxed)) => match boxed.as_ref() {
                    Value::Struct { name, fields } => {
                        assert_eq!(&**name, "DiseaseParams");
                        assert_eq!(
                            *fields.get::<Name>(&"incubation_days".into()).unwrap(),
                            Value::Int(8)
                        );
                        assert_eq!(
                            *fields.get::<Name>(&"duration_days".into()).unwrap(),
                            Value::Int(10)
                        );
                        assert_eq!(
                            *fields.get::<Name>(&"stat_penalty".into()).unwrap(),
                            Value::Int(4)
                        );
                        assert_eq!(
                            *fields.get::<Name>(&"roll_penalty".into()).unwrap(),
                            Value::Int(3)
                        );
                        assert_eq!(
                            *fields.get::<Name>(&"is_fatal".into()).unwrap(),
                            Value::Bool(false)
                        );
                    }
                    other => panic!("expected DiseaseParams struct, got {other:?}"),
                },
                other => panic!("expected Some(DiseaseParams), got {other:?}"),
            }
        }
        other => panic!("expected DiseaseCheckResult, got {other:?}"),
    }
}

#[test]
fn disease_fatal_when_d8_shows_eight() {
    let (program, result) = compile_osric_afflictions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Save fails, inc_d2 = 8 → fatal
    let mut handler = ScriptedHandler::with_responses(vec![
        scripted_roll(1, 20, 0, vec![3], vec![3], 3, 3),  // save fails
        scripted_roll(1, 8, 0, vec![4], vec![4], 4, 4),   // inc_d1
        scripted_roll(1, 8, 0, vec![8], vec![8], 8, 8),   // inc_d2 = 8!
        scripted_roll(1, 8, 0, vec![3], vec![3], 3, 3),   // dur_d1
        scripted_roll(1, 8, 0, vec![5], vec![5], 5, 5),   // dur_d2
        scripted_roll(1, 6, 0, vec![2], vec![2], 2, 2),   // stat_pen
        scripted_roll(1, 6, 0, vec![1], vec![1], 1, 1),   // roll_pen
    ]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "check_disease_contraction",
            vec![
                saving_throws_struct(13, 13, 11, 12, 14),
                enum_variant("DiseaseSource", "Infection"),
                Value::Int(0),
            ],
        )
        .unwrap();

    match val {
        Value::Struct { fields, .. } => {
            assert_eq!(
                *fields.get::<Name>(&"contracted".into()).unwrap(),
                Value::Bool(true)
            );
            match fields.get::<Name>(&"params".into()).unwrap() {
                Value::Option(Some(boxed)) => match boxed.as_ref() {
                    Value::Struct { fields, .. } => {
                        assert_eq!(
                            *fields.get::<Name>(&"is_fatal".into()).unwrap(),
                            Value::Bool(true)
                        );
                        assert_eq!(
                            *fields.get::<Name>(&"incubation_days".into()).unwrap(),
                            Value::Int(12) // 4 + 8
                        );
                    }
                    other => panic!("expected DiseaseParams, got {other:?}"),
                },
                other => panic!("expected Some, got {other:?}"),
            }
        }
        other => panic!("expected DiseaseCheckResult, got {other:?}"),
    }
}

// ── DISEASE RECOVERY TESTS ─────────────────────────────────────

#[test]
fn disease_recovery_reduces_penalty() {
    let (program, result) = compile_osric_afflictions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = ScriptedHandler::with_responses(vec![]);

    let val = interp
        .evaluate_derive(&state, &mut handler, "disease_recovery_one_day", vec![Value::Int(4)])
        .unwrap();
    assert_eq!(val, Value::Int(3));
}

#[test]
fn disease_recovery_floors_at_zero() {
    let (program, result) = compile_osric_afflictions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = ScriptedHandler::with_responses(vec![]);

    let val = interp
        .evaluate_derive(&state, &mut handler, "disease_recovery_one_day", vec![Value::Int(0)])
        .unwrap();
    assert_eq!(val, Value::Int(0));
}

// ── INSANITY TESTS ─────────────────────────────────────────────

#[test]
fn roll_insanity_type_returns_correct_variant() {
    let (program, result) = compile_osric_afflictions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Roll 1 → AbilityDecline
    let mut handler = ScriptedHandler::with_responses(vec![
        scripted_roll(1, 6, 0, vec![1], vec![1], 1, 1),
    ]);

    let val = interp
        .evaluate_mechanic(&state, &mut handler, "roll_insanity_type", vec![])
        .unwrap();

    assert_eq!(val, enum_variant("InsanityType", "AbilityDecline"));
}

#[test]
fn roll_insanity_phobia_type() {
    let (program, result) = compile_osric_afflictions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Roll 6 → Phobia
    let mut handler = ScriptedHandler::with_responses(vec![
        scripted_roll(1, 6, 0, vec![6], vec![6], 6, 6),
    ]);

    let val = interp
        .evaluate_mechanic(&state, &mut handler, "roll_insanity_type", vec![])
        .unwrap();

    assert_eq!(val, enum_variant("InsanityType", "Phobia"));
}

#[test]
fn roll_insanity_full_ability_decline() {
    let (program, result) = compile_osric_afflictions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // roll_insanity_type → 1 (AbilityDecline)
    // roll_ability_decline → INT 3, WIS 5, CHA 2
    let mut handler = ScriptedHandler::with_responses(vec![
        scripted_roll(1, 6, 0, vec![1], vec![1], 1, 1), // type = AbilityDecline
        scripted_roll(1, 6, 0, vec![3], vec![3], 3, 3), // int_loss
        scripted_roll(1, 6, 0, vec![5], vec![5], 5, 5), // wis_loss
        scripted_roll(1, 6, 0, vec![2], vec![2], 2, 2), // cha_loss
    ]);

    let val = interp
        .evaluate_mechanic(&state, &mut handler, "roll_insanity", vec![])
        .unwrap();

    match val {
        Value::Struct { name, fields } => {
            assert_eq!(&*name, "InsanityResult");
            assert_eq!(
                *fields.get::<Name>(&"insanity_type".into()).unwrap(),
                enum_variant("InsanityType", "AbilityDecline")
            );
            match fields.get::<Name>(&"ability_decline".into()).unwrap() {
                Value::Option(Some(boxed)) => match boxed.as_ref() {
                    Value::Struct { name, fields } => {
                        assert_eq!(&**name, "AbilityDeclineResult");
                        assert_eq!(
                            *fields.get::<Name>(&"int_loss".into()).unwrap(),
                            Value::Int(3)
                        );
                        assert_eq!(
                            *fields.get::<Name>(&"wis_loss".into()).unwrap(),
                            Value::Int(5)
                        );
                        assert_eq!(
                            *fields.get::<Name>(&"cha_loss".into()).unwrap(),
                            Value::Int(2)
                        );
                    }
                    other => panic!("expected AbilityDeclineResult, got {other:?}"),
                },
                other => panic!("expected Some, got {other:?}"),
            }
            assert!(matches!(
                fields.get::<Name>(&"phobia_object".into()).unwrap(),
                Value::Void
            ));
        }
        other => panic!("expected InsanityResult, got {other:?}"),
    }
}

#[test]
fn roll_insanity_full_phobia() {
    let (program, result) = compile_osric_afflictions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // roll_insanity_type → 6 (Phobia)
    // roll_phobia_object → 7 (Crowds)
    let mut handler = ScriptedHandler::with_responses(vec![
        scripted_roll(1, 6, 0, vec![6], vec![6], 6, 6),   // type = Phobia
        scripted_roll(1, 10, 0, vec![7], vec![7], 7, 7),  // phobia = Crowds
    ]);

    let val = interp
        .evaluate_mechanic(&state, &mut handler, "roll_insanity", vec![])
        .unwrap();

    match val {
        Value::Struct { name, fields } => {
            assert_eq!(&*name, "InsanityResult");
            assert_eq!(
                *fields.get::<Name>(&"insanity_type".into()).unwrap(),
                enum_variant("InsanityType", "Phobia")
            );
            assert!(matches!(
                fields.get::<Name>(&"ability_decline".into()).unwrap(),
                Value::Void
            ));
            match fields.get::<Name>(&"phobia_object".into()).unwrap() {
                Value::Option(Some(boxed)) => {
                    assert_eq!(**boxed, enum_variant("PhobiaObject", "Crowds"));
                }
                other => panic!("expected Some(Crowds), got {other:?}"),
            }
        }
        other => panic!("expected InsanityResult, got {other:?}"),
    }
}

#[test]
fn roll_insanity_marker_type_no_extras() {
    let (program, result) = compile_osric_afflictions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // roll_insanity_type → 5 (PathologicalLiar) — no extra rolls
    let mut handler = ScriptedHandler::with_responses(vec![
        scripted_roll(1, 6, 0, vec![5], vec![5], 5, 5),
    ]);

    let val = interp
        .evaluate_mechanic(&state, &mut handler, "roll_insanity", vec![])
        .unwrap();

    match val {
        Value::Struct { name, fields } => {
            assert_eq!(&*name, "InsanityResult");
            assert_eq!(
                *fields.get::<Name>(&"insanity_type".into()).unwrap(),
                enum_variant("InsanityType", "PathologicalLiar")
            );
            assert!(matches!(
                fields.get::<Name>(&"ability_decline".into()).unwrap(),
                Value::Void
            ));
            assert!(matches!(
                fields.get::<Name>(&"phobia_object".into()).unwrap(),
                Value::Void
            ));
        }
        other => panic!("expected InsanityResult, got {other:?}"),
    }
}

// ── DISEASE STAT LOSS DERIVE ───────────────────────────────────

#[test]
fn disease_stat_loss_returns_all_six_abilities() {
    let (program, result) = compile_osric_afflictions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = ScriptedHandler::with_responses(vec![]);

    let val = interp
        .evaluate_derive(&state, &mut handler, "disease_stat_loss", vec![Value::Int(3)])
        .unwrap();

    match val {
        Value::Map(map) => {
            assert_eq!(map.len(), 6);
            for (_k, v) in map.iter() {
                assert_eq!(*v, Value::Int(3));
            }
        }
        other => panic!("expected Map, got {other:?}"),
    }
}
