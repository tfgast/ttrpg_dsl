//! OSRIC level drain & restoration integration tests.
//!
//! Verifies the level drain rules from osric/osric_level_drain.ttrpg:
//! drain candidate selection, XP reset, death check, drain history,
//! and restoration with time-window eligibility.

use std::collections::BTreeMap;

use ttrpg_ast::ast::TopLevel;
use ttrpg_ast::Name;
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

mod osric_common;
use osric_common::*;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_level_drain() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn osric_level_drain_parses_and_typechecks() {
    let (program, _) = compile_osric_level_drain();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSRIC Level Drain"));
}

// ── Helper: build a character with specific class levels and XP ──

fn make_drain_character(
    state: &mut GameState,
    name: &str,
    classes: &[(&str, i64, i64)], // (class, level, xp)
    mode: &str,
) -> ttrpg_interp::state::EntityRef {
    let mut ability_map = BTreeMap::new();
    for &(ab, score) in &standard_abilities_14() {
        ability_map.insert(ability(ab), Value::Int(score));
    }

    let class_levels: Vec<Value> = classes
        .iter()
        .map(|(c, l, xp)| class_level_struct(c, *l, *xp))
        .collect();

    let mut fields = rustc_hash::FxHashMap::default();
    fields.insert(Name::from("name"), Value::Str(name.to_string()));
    fields.insert(Name::from("classes"), Value::List(class_levels));
    fields.insert(Name::from("classing_mode"), classing_mode(mode));
    fields.insert(Name::from("ancestry"), enum_variant("Ancestry", "Human"));
    fields.insert(
        Name::from("alignment"),
        enum_variant("Alignment", "TrueNeutral"),
    );
    fields.insert(Name::from("abilities"), Value::Map(ability_map));
    fields.insert(Name::from("HitPoints"), hit_points_group(30));
    fields.insert(Name::from("base_movement"), feet(120));
    fields.insert(Name::from("gold"), Value::Int(0));
    fields.insert(Name::from("drain_history"), Value::List(vec![]));
    fields.insert(Name::from("saving_throws"), Value::Option(None));
    fields.insert(
        Name::from("EquipmentSlots"),
        equipment_slots_group(Value::Option(None), Value::Option(None)),
    );

    state.add_entity("Character", fields)
}

// ── highest_class_level ────────────────────────────────────────

#[test]
fn highest_class_level_single() {
    let (program, result) = compile_osric_level_drain();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    let char_ref = make_drain_character(&mut state, "Fighter5", &[("Fighter", 5, 17000)], "Single");

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "highest_class_level",
            vec![Value::Entity(char_ref)],
        )
        .unwrap();
    assert_eq!(expect_int(val, "highest_class_level"), 5);
}

#[test]
fn highest_class_level_multiclass() {
    let (program, result) = compile_osric_level_drain();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    let char_ref = make_drain_character(
        &mut state,
        "FT",
        &[("Fighter", 5, 17000), ("Thief", 7, 40000)],
        "Multi",
    );

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "highest_class_level",
            vec![Value::Entity(char_ref)],
        )
        .unwrap();
    assert_eq!(expect_int(val, "highest_class_level multiclass"), 7);
}

// ── drain_candidate_classes ────────────────────────────────────

#[test]
fn drain_candidates_single_class() {
    let (program, result) = compile_osric_level_drain();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    let char_ref = make_drain_character(&mut state, "Fighter5", &[("Fighter", 5, 17000)], "Single");

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "drain_candidate_classes",
            vec![Value::Entity(char_ref)],
        )
        .unwrap();
    match val {
        Value::List(items) => {
            assert_eq!(items.len(), 1);
            assert_eq!(items[0], class_variant("Fighter"));
        }
        other => panic!("expected list, got {other:?}"),
    }
}

#[test]
fn drain_candidates_tied_multiclass() {
    let (program, result) = compile_osric_level_drain();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // Both at level 5 — tied
    let char_ref = make_drain_character(
        &mut state,
        "FT",
        &[("Fighter", 5, 17000), ("Thief", 5, 10000)],
        "Multi",
    );

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "drain_candidate_classes",
            vec![Value::Entity(char_ref)],
        )
        .unwrap();
    match val {
        Value::List(items) => {
            assert_eq!(items.len(), 2, "should have 2 tied candidates");
        }
        other => panic!("expected list, got {other:?}"),
    }
}

// ── xp_after_drain ─────────────────────────────────────────────

#[test]
fn xp_after_drain_fighter_5() {
    let (program, result) = compile_osric_level_drain();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Fighter level 5 → drained to level 4 → XP = xp_for_level(Fighter, 4) = 8000
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "xp_after_drain",
            vec![class_variant("Fighter"), Value::Int(5)],
        )
        .unwrap();
    assert_eq!(expect_int(val, "xp_after_drain(Fighter,5)"), 8000);
}

#[test]
fn xp_after_drain_to_zero() {
    let (program, result) = compile_osric_level_drain();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Fighter level 1 → drained below 1 → XP = 0
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "xp_after_drain",
            vec![class_variant("Fighter"), Value::Int(1)],
        )
        .unwrap();
    assert_eq!(expect_int(val, "xp_after_drain(Fighter,1)"), 0);
}

// ── is_killed_by_drain ─────────────────────────────────────────

#[test]
fn killed_by_drain_at_level_1() {
    let (program, result) = compile_osric_level_drain();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "is_killed_by_drain",
            vec![Value::Int(1)],
        )
        .unwrap();
    assert!(expect_bool(val, "killed at level 1"));

    let val2 = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "is_killed_by_drain",
            vec![Value::Int(2)],
        )
        .unwrap();
    assert!(!expect_bool(val2, "not killed at level 2"));
}

// ── apply_drain_to_classes ─────────────────────────────────────

#[test]
fn apply_drain_decrements_level_and_sets_xp() {
    let (program, result) = compile_osric_level_drain();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let classes = Value::List(vec![
        class_level_struct("Fighter", 5, 20000),
        class_level_struct("Thief", 3, 3000),
    ]);

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "apply_drain_to_classes",
            vec![classes, class_variant("Fighter")],
        )
        .unwrap();

    match val {
        Value::List(items) => {
            assert_eq!(items.len(), 2);
            // Fighter should be level 4 with XP 8000
            match &items[0] {
                Value::Struct { fields, .. } => {
                    let level = fields.get::<Name>(&"level".into()).unwrap();
                    let xp = fields.get::<Name>(&"xp".into()).unwrap();
                    assert_eq!(*level, Value::Int(4), "Fighter drained to level 4");
                    assert_eq!(*xp, Value::Int(8000), "Fighter XP set to start of level 4");
                }
                other => panic!("expected struct, got {other:?}"),
            }
            // Thief should be unchanged
            match &items[1] {
                Value::Struct { fields, .. } => {
                    let level = fields.get::<Name>(&"level".into()).unwrap();
                    assert_eq!(*level, Value::Int(3), "Thief unchanged");
                }
                other => panic!("expected struct, got {other:?}"),
            }
        }
        other => panic!("expected list, got {other:?}"),
    }
}

// ── apply_level_drain (function — full drain with dice) ────────

#[test]
fn apply_level_drain_single_class() {
    let (program, result) = compile_osric_level_drain();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let char_ref = make_drain_character(
        &mut state,
        "Fighter5",
        &[("Fighter", 5, 20000)],
        "Single",
    );

    // No dice needed — single class, no tie-breaking
    let mut handler = NullHandler;

    let adapter = ttrpg_interp::adapter::StateAdapter::new(state);
    let result_val = adapter.run(&mut handler, |s, h| {
        interp.evaluate_function(
            s,
            h,
            "apply_level_drain",
            vec![Value::Entity(char_ref), Value::Int(1000)], // current_time = 1000 segments
        )
    });

    let val = result_val.unwrap();
    match val {
        Value::Struct { name, fields } => {
            assert_eq!(&*name, "DrainResult");
            // killed should be false (was level 5)
            let killed = fields.get::<Name>(&"killed".into()).unwrap();
            assert_eq!(*killed, Value::Bool(false));
            // drained_class should be Fighter
            let drained = fields.get::<Name>(&"drained_class".into()).unwrap();
            assert_eq!(*drained, class_variant("Fighter"));
            // classes should have Fighter at level 4
            let classes = fields.get::<Name>(&"classes".into()).unwrap();
            match classes {
                Value::List(items) => {
                    match &items[0] {
                        Value::Struct { fields, .. } => {
                            assert_eq!(
                                *fields.get::<Name>(&"level".into()).unwrap(),
                                Value::Int(4)
                            );
                        }
                        other => panic!("expected struct, got {other:?}"),
                    }
                }
                other => panic!("expected list, got {other:?}"),
            }
            // drain_history should have 1 entry
            let history = fields.get::<Name>(&"drain_history".into()).unwrap();
            match history {
                Value::List(items) => {
                    assert_eq!(items.len(), 1, "one drain event recorded");
                }
                other => panic!("expected list, got {other:?}"),
            }
        }
        other => panic!("expected DrainResult struct, got {other:?}"),
    }
}

// ── restoration_eligible ───────────────────────────────────────

#[test]
fn restoration_eligible_within_window() {
    let (program, result) = compile_osric_level_drain();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // segments_per_day = 14400
    // caster is level 7 cleric → window = 7 * 14400 = 100800 segments
    let drain = Value::Struct {
        name: Name::from("DrainEvent"),
        fields: {
            let mut f = BTreeMap::new();
            f.insert(Name::from("class"), class_variant("Fighter"));
            f.insert(Name::from("original_level"), Value::Int(5));
            f.insert(Name::from("timestamp"), Value::Int(1000));
            f
        },
    };

    // Within window: 1000 + 50000 = 51000, window = 100800
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "restoration_eligible",
            vec![drain.clone(), Value::Int(51000), Value::Int(7)],
        )
        .unwrap();
    assert!(expect_bool(val, "within window"));

    // Outside window: 1000 + 200000 = 201000, window = 100800
    let val2 = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "restoration_eligible",
            vec![drain, Value::Int(201000), Value::Int(7)],
        )
        .unwrap();
    assert!(!expect_bool(val2, "outside window"));
}

// ── apply_restoration ──────────────────────────────────────────

#[test]
fn restoration_restores_oldest_eligible() {
    let (program, result) = compile_osric_level_drain();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // Character was drained twice:
    // 1st drain: Fighter 5→4 at time 1000
    // 2nd drain: Fighter 4→3 at time 2000
    // Current classes: Fighter level 3
    let drain_history = Value::List(vec![
        Value::Struct {
            name: Name::from("DrainEvent"),
            fields: {
                let mut f = BTreeMap::new();
                f.insert(Name::from("class"), class_variant("Fighter"));
                f.insert(Name::from("original_level"), Value::Int(5));
                f.insert(Name::from("timestamp"), Value::Int(1000));
                f
            },
        },
        Value::Struct {
            name: Name::from("DrainEvent"),
            fields: {
                let mut f = BTreeMap::new();
                f.insert(Name::from("class"), class_variant("Fighter"));
                f.insert(Name::from("original_level"), Value::Int(4));
                f.insert(Name::from("timestamp"), Value::Int(2000));
                f
            },
        },
    ]);

    let char_ref = make_drain_character(
        &mut state,
        "Fighter3",
        &[("Fighter", 3, 4000)],
        "Single",
    );
    set_field(&mut state, &char_ref, "drain_history", drain_history);

    // Restore at time 10000, caster cleric level 7 (window = 100800)
    // Both drains are within window — should restore oldest (level 5)
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "apply_restoration",
            vec![Value::Entity(char_ref), Value::Int(10000), Value::Int(7)],
        )
        .unwrap();

    match val {
        Value::Option(Some(boxed)) => match *boxed {
            Value::Struct { name, fields } => {
                assert_eq!(&*name, "RestoreResult");
                let restored_level = fields.get::<Name>(&"restored_level".into()).unwrap();
                assert_eq!(*restored_level, Value::Int(5), "restores to original level 5");
                // drain_history should have 1 remaining entry
                let history = fields.get::<Name>(&"drain_history".into()).unwrap();
                match history {
                    Value::List(items) => {
                        assert_eq!(items.len(), 1, "one drain event remains");
                    }
                    other => panic!("expected list, got {other:?}"),
                }
            }
            other => panic!("expected RestoreResult struct, got {other:?}"),
        },
        // DSL some() wraps in Value::Option(Some(..)), but check both none representations
        Value::Option(None) | Value::None => panic!("expected Some(RestoreResult), got None"),
        other => panic!("expected Option, got {other:?}"),
    }
}

#[test]
fn restoration_returns_none_when_expired() {
    let (program, result) = compile_osric_level_drain();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // Drain at time 1000, restore at time 500000 with caster level 7
    // window = 7 * 14400 = 100800. 500000 - 1000 = 499000 > 100800 → expired
    let drain_history = Value::List(vec![Value::Struct {
        name: Name::from("DrainEvent"),
        fields: {
            let mut f = BTreeMap::new();
            f.insert(Name::from("class"), class_variant("Fighter"));
            f.insert(Name::from("original_level"), Value::Int(5));
            f.insert(Name::from("timestamp"), Value::Int(1000));
            f
        },
    }]);

    let char_ref = make_drain_character(
        &mut state,
        "Fighter4",
        &[("Fighter", 4, 8000)],
        "Single",
    );
    set_field(&mut state, &char_ref, "drain_history", drain_history);

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "apply_restoration",
            vec![Value::Entity(char_ref), Value::Int(500000), Value::Int(7)],
        )
        .unwrap();

    assert!(
        matches!(val, Value::None),
        "expected None (expired), got {:?}",
        val
    );
}
