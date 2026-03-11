//! Integration tests for optional groups.
//!
//! Script-suitable lifecycle, alias, and derive/runtime coverage has moved to
//! `tests/optional_groups.ttrpg-cli`.
//! These Rust tests keep only pipeline construction and raw effect payload
//! coverage that still belongs next to the interpreter.

use std::collections::{BTreeMap, VecDeque};

use rustc_hash::FxHashMap;
use ttrpg_ast::FileId;
use ttrpg_ast::diagnostic::Severity;
use ttrpg_interp::Interpreter;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::{EntityRef, WritableState};
use ttrpg_interp::value::Value;

const PROGRAM_SOURCE: &str = r#"
system "OptionalGroupsTest" {
    entity Character {
        name: string
        level: int = 1
        HP: int

        optional Spellcasting {
            spell_slots: int
            spell_dc: int = 10
            spellcasting_ability: string = "INT"
        }

        optional KiPowers {
            ki_points: int
            ki_dc: int = 8
        }
    }

    derive effective_spell_dc(caster: Character) -> int {
        if caster has Spellcasting {
            caster.Spellcasting.spell_dc
        } else {
            0
        }
    }

    derive total_resources(c: Character) -> int {
        let spells = if c has Spellcasting { c.Spellcasting.spell_slots } else { 0 }
        let ki = if c has KiPowers { c.KiPowers.ki_points } else { 0 }
        spells + ki
    }

    action AwakeMagic on gm: Character (target: Character, slots: int, dc: int) {
        resolve {
            grant target.Spellcasting { spell_slots: slots, spell_dc: dc }
        }
    }

    action SealMagic on gm: Character (target: Character) {
        resolve {
            revoke target.Spellcasting
        }
    }

    action UnlockKi on gm: Character (target: Character, points: int) {
        resolve {
            grant target.KiPowers { ki_points: points }
        }
    }

    action CastSpell on caster: Character with Spellcasting (cost: int) {
        resolve {
            caster.Spellcasting.spell_slots -= cost
        }
    }

    derive spell_save_dc(caster: Character) -> int {
        if caster has Spellcasting {
            caster.Spellcasting.spell_dc + caster.level
        } else {
            0
        }
    }
}
"#;

fn setup() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    let (program, parse_errors) = ttrpg_parser::parse(PROGRAM_SOURCE, FileId::SYNTH);
    assert!(
        parse_errors.is_empty(),
        "parse errors: {:?}",
        parse_errors.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    let mut lower_diags = Vec::new();
    let program = ttrpg_parser::lower_moves(program, &mut lower_diags);
    assert!(
        lower_diags.is_empty(),
        "lowering errors: {:?}",
        lower_diags.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    let result = ttrpg_checker::check(&program);
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
    (program, result)
}

struct ScriptedHandler {
    script: VecDeque<Response>,
    log: Vec<Effect>,
}

impl ScriptedHandler {
    fn with_responses(responses: Vec<Response>) -> Self {
        Self {
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

fn add_character(state: &mut GameState, name: &str, level: i64, hp: i64) -> EntityRef {
    let mut fields = FxHashMap::default();
    fields.insert("name".into(), Value::Str(name.to_string()));
    fields.insert("level".into(), Value::Int(level));
    fields.insert("HP".into(), Value::Int(hp));
    state.add_entity("Character", fields)
}

fn standard_turn_budget() -> BTreeMap<ttrpg_ast::Name, Value> {
    let mut budget = BTreeMap::new();
    budget.insert("actions".into(), Value::Int(1));
    budget.insert("bonus_actions".into(), Value::Int(1));
    budget.insert("reactions".into(), Value::Int(1));
    budget.insert("movement".into(), Value::Int(30));
    budget.insert("free_interactions".into(), Value::Int(1));
    budget
}

#[test]
fn pipeline_parses_checks_and_builds_interpreter() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env);
    assert!(
        interp.is_ok(),
        "interpreter creation failed: {:?}",
        interp.err()
    );
}

#[test]
fn grant_action_emits_correct_effect() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let gm = add_character(&mut state, "GM", 1, 999);
    let wizard = add_character(&mut state, "Wizard", 5, 30);
    state.set_turn_budget(&gm, standard_turn_budget());

    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged,
        Response::Acknowledged,
        Response::Acknowledged,
    ]);

    interp
        .execute_action(
            &state,
            &mut handler,
            "AwakeMagic",
            gm,
            vec![Value::Entity(wizard), Value::Int(4), Value::Int(15)],
        )
        .unwrap();

    let grant_effect = handler
        .log
        .iter()
        .find(|e| matches!(e, Effect::GrantGroup { .. }))
        .expect("should emit GrantGroup effect");

    match grant_effect {
        Effect::GrantGroup {
            entity,
            group_name,
            fields,
        } => {
            assert_eq!(*entity, wizard);
            assert_eq!(group_name, "Spellcasting");
            match fields {
                Value::Struct { name, fields } => {
                    assert_eq!(name, "Spellcasting");
                    assert_eq!(fields.get("spell_slots"), Some(&Value::Int(4)));
                    assert_eq!(fields.get("spell_dc"), Some(&Value::Int(15)));
                    assert_eq!(
                        fields.get("spellcasting_ability"),
                        Some(&Value::Str("INT".into()))
                    );
                }
                _ => panic!("expected Struct, got {fields:?}"),
            }
        }
        _ => unreachable!(),
    }
}

#[test]
fn revoke_action_emits_correct_effect() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let gm = add_character(&mut state, "GM", 1, 999);
    let wizard = add_character(&mut state, "Wizard", 5, 30);
    state.set_turn_budget(&gm, standard_turn_budget());

    let group_val = Value::Struct {
        name: "Spellcasting".into(),
        fields: {
            let mut fields = BTreeMap::new();
            fields.insert("spell_slots".into(), Value::Int(4));
            fields.insert("spell_dc".into(), Value::Int(15));
            fields.insert("spellcasting_ability".into(), Value::Str("INT".into()));
            fields
        },
    };
    state.write_field(
        &wizard,
        &[ttrpg_interp::effect::FieldPathSegment::Field(
            "Spellcasting".into(),
        )],
        group_val,
    );

    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged,
        Response::Acknowledged,
        Response::Acknowledged,
    ]);

    interp
        .execute_action(
            &state,
            &mut handler,
            "SealMagic",
            gm,
            vec![Value::Entity(wizard)],
        )
        .unwrap();

    let revoke_effect = handler
        .log
        .iter()
        .find(|e| matches!(e, Effect::RevokeGroup { .. }))
        .expect("should emit RevokeGroup effect");

    match revoke_effect {
        Effect::RevokeGroup { entity, group_name } => {
            assert_eq!(*entity, wizard);
            assert_eq!(group_name, "Spellcasting");
        }
        _ => unreachable!(),
    }
}
