//! OSRIC level drain & restoration integration tests — AST + detailed assertions.
//!
//! Most runtime tests (highest_class_level, drain_candidate_classes,
//! apply_drain_to_classes, apply_level_drain, restoration expired) have been
//! moved to `osric/tests/osric_level_drain.ttrpg-cli`.
//!
//! This file retains:
//! - Parse+typecheck test
//! - Detailed restoration field assertions (CLI can't access fields on Option values)

use std::collections::BTreeMap;

use ttrpg_ast::ast::TopLevel;
use ttrpg_ast::Name;
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

mod osric_common;
#[allow(unused_imports)]
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

    fields.insert(Name::from("drain_history"), Value::List(vec![]));
    fields.insert(Name::from("hp_rolls"), Value::List(vec![]));
    fields.insert(Name::from("saving_throws"), Value::Option(None));
    fields.insert(
        Name::from("EquipmentSlots"),
        equipment_slots_group(Value::Option(None), Value::Option(None)),
    );

    state.add_entity("Character", fields)
}

// ── Helper: build an HpRoll struct value ───────────────────────

fn hp_roll_struct(class: &str, level: i64, amount: i64) -> Value {
    Value::Struct {
        name: Name::from("HpRoll"),
        fields: {
            let mut f = BTreeMap::new();
            f.insert(Name::from("class"), class_variant(class));
            f.insert(Name::from("level"), Value::Int(level));
            f.insert(Name::from("amount"), Value::Int(amount));
            f
        },
    }
}

// ── apply_restoration ──────────────────────────────────────────

#[test]
fn restoration_restores_oldest_eligible() {
    let (program, result) = compile_osric_level_drain();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

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

    let char_ref = make_drain_character(&mut state, "Fighter3", &[("Fighter", 3, 4000)], "Single");
    set_field(&mut state, &char_ref, "drain_history", drain_history);
    // hp_rolls for remaining levels 1-3
    let hp_rolls = Value::List(
        (1..=3)
            .map(|lvl| hp_roll_struct("Fighter", lvl, 6))
            .collect(),
    );
    set_field(&mut state, &char_ref, "hp_rolls", hp_rolls);

    // Scripted: restoration re-rolls 1d10 for the restored level → roll 8
    // Fighter hit_die=10, CON 14 → con_hp_mod=0, single class
    // HP gained = max(1, 8+0) = 8
    let mut handler = ScriptedHandler::with_responses(vec![
        scripted_roll(1, 10, 0, vec![8], vec![8], 8, 8), // roll_hp_for_level → 1d10 = 8
    ]);

    // Restore at time 10000, caster cleric level 7 (window = 100800)
    // Both drains are within window — should restore oldest (level 5)
    let val = interp
        .evaluate_mechanic(
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
                assert_eq!(
                    *restored_level,
                    Value::Int(5),
                    "restores to original level 5"
                );
                // drain_history should have 1 remaining entry
                let history = fields.get::<Name>(&"drain_history".into()).unwrap();
                match history {
                    Value::List(items) => {
                        assert_eq!(items.len(), 1, "one drain event remains");
                    }
                    other => panic!("expected list, got {other:?}"),
                }
                // hp_change should be 8 (re-rolled)
                let hp_change = fields.get::<Name>(&"hp_change".into()).unwrap();
                assert_eq!(*hp_change, Value::Int(8), "HP gained from restoration");
                // hp_rolls should have 4 entries (3 original + 1 restored)
                let rolls = fields.get::<Name>(&"hp_rolls".into()).unwrap();
                match rolls {
                    Value::List(items) => {
                        assert_eq!(items.len(), 4, "restored level 5 roll added");
                    }
                    other => panic!("expected list, got {other:?}"),
                }
            }
            other => panic!("expected RestoreResult struct, got {other:?}"),
        },
        Value::Option(None) | Value::Void => panic!("expected Some(RestoreResult), got None"),
        other => panic!("expected Option, got {other:?}"),
    }
}
