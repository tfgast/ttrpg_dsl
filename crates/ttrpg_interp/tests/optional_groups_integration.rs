//! End-to-end integration tests for optional groups.
//!
//! Runs a self-contained DSL program through the full pipeline
//! (parse → lower → check → interpret), exercising:
//! - Entity declarations with optional groups
//! - `has` expressions for group presence checks
//! - `grant` and `revoke` statements in actions
//! - `with` constraints on action receivers and parameters
//! - Namespaced field reads (entity.Group.field)
//! - Guards in derives (`if entity has Group`)
//! - StateAdapter grant/revoke lifecycle

use std::collections::{BTreeMap, HashMap, VecDeque};

use ttrpg_ast::diagnostic::Severity;
use ttrpg_ast::FileId;
use ttrpg_interp::adapter::StateAdapter;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::{EntityRef, StateProvider, WritableState};
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

// ── DSL program source ───────────────────────────────────────

/// A 5e-inspired program with optional Spellcasting and KiPowers groups.
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

    // Pure derive: returns spell DC if entity has Spellcasting, else 0
    derive effective_spell_dc(caster: Character) -> int {
        if caster has Spellcasting {
            caster.Spellcasting.spell_dc
        } else {
            0
        }
    }

    // Pure derive: total resource count from optional groups
    derive total_resources(c: Character) -> int {
        let spells = if c has Spellcasting { c.Spellcasting.spell_slots } else { 0 }
        let ki = if c has KiPowers { c.KiPowers.ki_points } else { 0 }
        spells + ki
    }

    // Action: grant Spellcasting to a character
    action AwakeMagic on gm: Character (target: Character, slots: int, dc: int) {
        resolve {
            grant target.Spellcasting { spell_slots: slots, spell_dc: dc }
        }
    }

    // Action: revoke Spellcasting from a character
    action SealMagic on gm: Character (target: Character) {
        resolve {
            revoke target.Spellcasting
        }
    }

    // Action: grant KiPowers
    action UnlockKi on gm: Character (target: Character, points: int) {
        resolve {
            grant target.KiPowers { ki_points: points }
        }
    }

    // Action with `with` constraint: only works on entities with Spellcasting
    action CastSpell on caster: Character with Spellcasting (cost: int) {
        resolve {
            caster.Spellcasting.spell_slots -= cost
        }
    }

    // Derive: reads Spellcasting.spell_dc through namespaced access with has-guard
    derive spell_save_dc(caster: Character) -> int {
        if caster has Spellcasting {
            caster.Spellcasting.spell_dc + caster.level
        } else {
            0
        }
    }
}
"#;

/// Program using top-level groups with external entity attachment syntax.
const EXTERNAL_GROUP_PROGRAM_SOURCE: &str = r#"
system "ExternalGroupsTest" {
    group Spellcasting {
        spell_slots: int
        spell_dc: int = 11
    }

    entity Character {
        name: string
        HP: int
        optional Spellcasting
    }

    action GrantSpellcasting on gm: Character (target: Character, slots: int) {
        resolve {
            grant target.Spellcasting { spell_slots: slots }
        }
    }

    derive spell_dc(c: Character) -> int {
        if c has Spellcasting {
            c.Spellcasting.spell_dc
        } else {
            0
        }
    }
}
"#;

// ── Setup ────────────────────────────────────────────────────

fn setup_from_source(source: &str) -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    let (program, parse_errors) = ttrpg_parser::parse(source, FileId::SYNTH);
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

fn setup() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    setup_from_source(PROGRAM_SOURCE)
}

// ── ScriptedHandler ──────────────────────────────────────────

struct ScriptedHandler {
    script: VecDeque<Response>,
    log: Vec<Effect>,
}

impl ScriptedHandler {
    fn new() -> Self {
        ScriptedHandler {
            script: VecDeque::new(),
            log: Vec::new(),
        }
    }

    fn with_responses(responses: Vec<Response>) -> Self {
        ScriptedHandler {
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

// ── Entity helpers ───────────────────────────────────────────

fn add_character(state: &mut GameState, name: &str, level: i64, hp: i64) -> EntityRef {
    let mut fields = HashMap::new();
    fields.insert("name".into(), Value::Str(name.to_string()));
    fields.insert("level".into(), Value::Int(level));
    fields.insert("HP".into(), Value::Int(hp));
    state.add_entity("Character", fields)
}

fn standard_turn_budget() -> BTreeMap<ttrpg_ast::Name, Value> {
    let mut b = BTreeMap::new();
    b.insert("actions".into(), Value::Int(1));
    b.insert("bonus_actions".into(), Value::Int(1));
    b.insert("reactions".into(), Value::Int(1));
    b.insert("movement".into(), Value::Int(30));
    b.insert("free_interactions".into(), Value::Int(1));
    b
}

// ════════════════════════════════════════════════════════════════
// Group 1: Pipeline Validation
// ════════════════════════════════════════════════════════════════

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
fn external_group_attachment_grant_uses_group_defaults() {
    let (program, result) = setup_from_source(EXTERNAL_GROUP_PROGRAM_SOURCE);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut gm_fields = HashMap::new();
    gm_fields.insert("name".into(), Value::Str("GM".into()));
    gm_fields.insert("HP".into(), Value::Int(999));
    let gm = state.add_entity("Character", gm_fields);

    let mut wizard_fields = HashMap::new();
    wizard_fields.insert("name".into(), Value::Str("Wizard".into()));
    wizard_fields.insert("HP".into(), Value::Int(12));
    let wizard = state.add_entity("Character", wizard_fields);

    state.set_turn_budget(&gm, standard_turn_budget());
    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::with_responses(vec![Response::Acknowledged]);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "GrantSpellcasting",
                gm,
                vec![Value::Entity(wizard), Value::Int(3)],
            )
            .unwrap();
    });

    let state = adapter.into_inner();
    let group = state.read_field(&wizard, "Spellcasting").unwrap();
    match group {
        Value::Struct { fields, .. } => {
            assert_eq!(fields.get("spell_slots"), Some(&Value::Int(3)));
            assert_eq!(fields.get("spell_dc"), Some(&Value::Int(11)));
        }
        other => panic!("expected Struct, got {:?}", other),
    }

    let mut handler = ScriptedHandler::new();
    let dc = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "spell_dc",
            vec![Value::Entity(wizard)],
        )
        .unwrap();
    assert_eq!(dc, Value::Int(11));
}

// ════════════════════════════════════════════════════════════════
// Group 2: Has Expression
// ════════════════════════════════════════════════════════════════

#[test]
fn has_returns_false_when_no_group_granted() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let wizard = add_character(&mut state, "Wizard", 5, 30);

    // effective_spell_dc should return 0 when no Spellcasting granted
    let mut handler = ScriptedHandler::new();
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "effective_spell_dc",
            vec![Value::Entity(wizard)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(0));
}

#[test]
fn has_returns_true_when_group_is_granted() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let wizard = add_character(&mut state, "Wizard", 5, 30);

    // Manually grant Spellcasting by writing the group struct to state
    let group_val = Value::Struct {
        name: "Spellcasting".into(),
        fields: {
            let mut f = BTreeMap::new();
            f.insert("spell_slots".into(), Value::Int(4));
            f.insert("spell_dc".into(), Value::Int(15));
            f.insert("spellcasting_ability".into(), Value::Str("INT".into()));
            f
        },
    };
    state.write_field(
        &wizard,
        &[ttrpg_interp::effect::FieldPathSegment::Field(
            "Spellcasting".into(),
        )],
        group_val,
    );

    // effective_spell_dc should return the spell_dc value
    let mut handler = ScriptedHandler::new();
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "effective_spell_dc",
            vec![Value::Entity(wizard)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(15));
}

// ════════════════════════════════════════════════════════════════
// Group 3: Grant via Action (through StateAdapter)
// ════════════════════════════════════════════════════════════════

#[test]
fn grant_action_adds_group_fields_to_state() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let gm = add_character(&mut state, "GM", 1, 999);
    let wizard = add_character(&mut state, "Wizard", 5, 30);
    state.set_turn_budget(&gm, standard_turn_budget());

    let adapter = StateAdapter::new(state);

    // AwakeMagic: grant wizard.Spellcasting { spell_slots: 4, spell_dc: 15 }
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, // ActionStarted
    ]);

    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "AwakeMagic",
                gm,
                vec![Value::Entity(wizard), Value::Int(4), Value::Int(15)],
            )
            .unwrap();
    });

    // Verify Spellcasting group was granted in final state
    let final_state = adapter.into_inner();
    let group = final_state.read_field(&wizard, "Spellcasting");
    assert!(group.is_some(), "Spellcasting should be granted");

    match group.unwrap() {
        Value::Struct { name, fields } => {
            assert_eq!(name, "Spellcasting");
            assert_eq!(fields.get("spell_slots"), Some(&Value::Int(4)));
            assert_eq!(fields.get("spell_dc"), Some(&Value::Int(15)));
            assert_eq!(
                fields.get("spellcasting_ability"),
                Some(&Value::Str("INT".into())),
                "default should be filled"
            );
        }
        other => panic!("expected Struct, got {:?}", other),
    }
}

#[test]
fn grant_fills_defaults_from_declaration() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let gm = add_character(&mut state, "GM", 1, 999);
    let monk = add_character(&mut state, "Monk", 3, 25);
    state.set_turn_budget(&gm, standard_turn_budget());

    let adapter = StateAdapter::new(state);

    // UnlockKi: grant monk.KiPowers { ki_points: 3 }
    // ki_dc has default=8, so should be filled in
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, // ActionStarted
    ]);

    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "UnlockKi",
                gm,
                vec![Value::Entity(monk), Value::Int(3)],
            )
            .unwrap();
    });

    let final_state = adapter.into_inner();
    let group = final_state.read_field(&monk, "KiPowers").unwrap();
    match group {
        Value::Struct { fields, .. } => {
            assert_eq!(fields.get("ki_points"), Some(&Value::Int(3)));
            assert_eq!(
                fields.get("ki_dc"),
                Some(&Value::Int(8)),
                "ki_dc should default to 8"
            );
        }
        other => panic!("expected Struct, got {:?}", other),
    }
}

// ════════════════════════════════════════════════════════════════
// Group 4: Revoke via Action
// ════════════════════════════════════════════════════════════════

#[test]
fn revoke_action_removes_group_from_state() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let gm = add_character(&mut state, "GM", 1, 999);
    let wizard = add_character(&mut state, "Wizard", 5, 30);
    state.set_turn_budget(&gm, standard_turn_budget());

    // Pre-grant Spellcasting
    let group_val = Value::Struct {
        name: "Spellcasting".into(),
        fields: {
            let mut f = BTreeMap::new();
            f.insert("spell_slots".into(), Value::Int(4));
            f.insert("spell_dc".into(), Value::Int(15));
            f.insert("spellcasting_ability".into(), Value::Str("INT".into()));
            f
        },
    };
    state.write_field(
        &wizard,
        &[ttrpg_interp::effect::FieldPathSegment::Field(
            "Spellcasting".into(),
        )],
        group_val,
    );

    // Verify it's there
    assert!(state.read_field(&wizard, "Spellcasting").is_some());

    let adapter = StateAdapter::new(state);

    // SealMagic: revoke wizard.Spellcasting
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, // ActionStarted
    ]);

    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "SealMagic",
                gm,
                vec![Value::Entity(wizard)],
            )
            .unwrap();
    });

    // Verify Spellcasting was removed
    let final_state = adapter.into_inner();
    assert!(
        final_state.read_field(&wizard, "Spellcasting").is_none(),
        "Spellcasting should be revoked"
    );
}

// ════════════════════════════════════════════════════════════════
// Group 5: Full Grant/Revoke Lifecycle
// ════════════════════════════════════════════════════════════════

#[test]
fn full_grant_use_revoke_lifecycle() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let gm = add_character(&mut state, "GM", 1, 999);
    let wizard = add_character(&mut state, "Wizard", 5, 30);
    state.set_turn_budget(&gm, standard_turn_budget());
    state.set_turn_budget(&wizard, standard_turn_budget());

    // Step 1: Verify no groups — total_resources should be 0
    let mut handler = ScriptedHandler::new();
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "total_resources",
            vec![Value::Entity(wizard)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(0), "no groups means 0 resources");

    // Step 2: Grant Spellcasting via action
    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::with_responses(vec![Response::Acknowledged]);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "AwakeMagic",
                gm,
                vec![Value::Entity(wizard), Value::Int(4), Value::Int(15)],
            )
            .unwrap();
    });
    let mut state = adapter.into_inner();
    state.set_turn_budget(&gm, standard_turn_budget());
    state.set_turn_budget(&wizard, standard_turn_budget());

    // Step 3: Verify has expression + derive reads group fields
    let mut handler = ScriptedHandler::new();
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "effective_spell_dc",
            vec![Value::Entity(wizard)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(15), "spell_dc should be 15");

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "total_resources",
            vec![Value::Entity(wizard)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(4), "only Spellcasting with 4 slots");

    // Step 4: Grant KiPowers via action
    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::with_responses(vec![Response::Acknowledged]);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "UnlockKi",
                gm,
                vec![Value::Entity(wizard), Value::Int(3)],
            )
            .unwrap();
    });
    let mut state = adapter.into_inner();
    state.set_turn_budget(&gm, standard_turn_budget());
    state.set_turn_budget(&wizard, standard_turn_budget());

    // Step 5: Both groups active — total_resources = 4 + 3 = 7
    let mut handler = ScriptedHandler::new();
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "total_resources",
            vec![Value::Entity(wizard)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(7), "4 spell slots + 3 ki points");

    // Step 6: Revoke Spellcasting
    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::with_responses(vec![Response::Acknowledged]);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "SealMagic",
                gm,
                vec![Value::Entity(wizard)],
            )
            .unwrap();
    });
    let state = adapter.into_inner();

    // Step 7: Verify Spellcasting gone, KiPowers remains
    assert!(state.read_field(&wizard, "Spellcasting").is_none());
    assert!(state.read_field(&wizard, "KiPowers").is_some());

    let mut handler = ScriptedHandler::new();
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "total_resources",
            vec![Value::Entity(wizard)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(3), "only ki points remain");

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "effective_spell_dc",
            vec![Value::Entity(wizard)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(0), "no Spellcasting means dc=0");
}

// ════════════════════════════════════════════════════════════════
// Group 6: With-Constrained Action
// ════════════════════════════════════════════════════════════════

#[test]
fn with_constrained_action_succeeds_when_group_granted() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let wizard = add_character(&mut state, "Wizard", 5, 30);
    state.set_turn_budget(&wizard, standard_turn_budget());

    // Grant Spellcasting with 4 slots
    let group_val = Value::Struct {
        name: "Spellcasting".into(),
        fields: {
            let mut f = BTreeMap::new();
            f.insert("spell_slots".into(), Value::Int(4));
            f.insert("spell_dc".into(), Value::Int(15));
            f.insert("spellcasting_ability".into(), Value::Str("INT".into()));
            f
        },
    };
    state.write_field(
        &wizard,
        &[ttrpg_interp::effect::FieldPathSegment::Field(
            "Spellcasting".into(),
        )],
        group_val,
    );

    // CastSpell: costs 1 spell slot
    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::with_responses(vec![Response::Acknowledged]);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(state, eff_handler, "CastSpell", wizard, vec![Value::Int(1)])
            .unwrap();
    });

    // spell_slots should go from 4 to 3
    let final_state = adapter.into_inner();
    let group = final_state.read_field(&wizard, "Spellcasting").unwrap();
    match group {
        Value::Struct { fields, .. } => {
            assert_eq!(fields.get("spell_slots"), Some(&Value::Int(3)));
        }
        other => panic!("expected Struct, got {:?}", other),
    }
}

// ════════════════════════════════════════════════════════════════
// Group 7: Derive with Has Guard + Level
// ════════════════════════════════════════════════════════════════

#[test]
fn spell_save_dc_uses_level_and_group() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let wizard = add_character(&mut state, "Wizard", 5, 30);

    // Without Spellcasting: dc should be 0
    let mut handler = ScriptedHandler::new();
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "spell_save_dc",
            vec![Value::Entity(wizard)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(0));

    // Grant Spellcasting with dc=12
    let group_val = Value::Struct {
        name: "Spellcasting".into(),
        fields: {
            let mut f = BTreeMap::new();
            f.insert("spell_slots".into(), Value::Int(3));
            f.insert("spell_dc".into(), Value::Int(12));
            f.insert("spellcasting_ability".into(), Value::Str("WIS".into()));
            f
        },
    };
    state.write_field(
        &wizard,
        &[ttrpg_interp::effect::FieldPathSegment::Field(
            "Spellcasting".into(),
        )],
        group_val,
    );

    // With Spellcasting: dc should be spell_dc + level = 12 + 5 = 17
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "spell_save_dc",
            vec![Value::Entity(wizard)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(17));
}

// ════════════════════════════════════════════════════════════════
// Group 8: Multiple Entities, Independent Groups
// ════════════════════════════════════════════════════════════════

#[test]
fn groups_are_per_entity_independent() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let gm = add_character(&mut state, "GM", 1, 999);
    let wizard = add_character(&mut state, "Wizard", 5, 30);
    let monk = add_character(&mut state, "Monk", 4, 25);
    state.set_turn_budget(&gm, standard_turn_budget());

    // Grant Spellcasting to wizard
    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::with_responses(vec![Response::Acknowledged]);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "AwakeMagic",
                gm,
                vec![Value::Entity(wizard), Value::Int(4), Value::Int(15)],
            )
            .unwrap();
    });
    let mut state = adapter.into_inner();
    state.set_turn_budget(&gm, standard_turn_budget());

    // Grant KiPowers to monk
    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::with_responses(vec![Response::Acknowledged]);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "UnlockKi",
                gm,
                vec![Value::Entity(monk), Value::Int(5)],
            )
            .unwrap();
    });
    let state = adapter.into_inner();

    // Wizard has Spellcasting but not KiPowers
    let mut handler = ScriptedHandler::new();
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "total_resources",
            vec![Value::Entity(wizard)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(4), "wizard: 4 spell slots, 0 ki");

    // Monk has KiPowers but not Spellcasting
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "total_resources",
            vec![Value::Entity(monk)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(5), "monk: 0 spell slots, 5 ki");
}

// ════════════════════════════════════════════════════════════════
// Group 9: Grant Effect Contents
// ════════════════════════════════════════════════════════════════

#[test]
fn grant_action_emits_correct_effect() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let gm = add_character(&mut state, "GM", 1, 999);
    let wizard = add_character(&mut state, "Wizard", 5, 30);
    state.set_turn_budget(&gm, standard_turn_budget());

    // Use plain handler (no adapter) to inspect raw effects
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, // ActionStarted
        Response::Acknowledged, // GrantGroup
        Response::Acknowledged, // ActionCompleted
    ]);

    let _ = interp.execute_action(
        &state,
        &mut handler,
        "AwakeMagic",
        gm,
        vec![Value::Entity(wizard), Value::Int(4), Value::Int(15)],
    );

    // Find the GrantGroup effect
    let grant_effect = handler
        .log
        .iter()
        .find(|e| matches!(e, Effect::GrantGroup { .. }));
    assert!(grant_effect.is_some(), "should emit GrantGroup effect");

    match grant_effect.unwrap() {
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
                    // Default should be filled
                    assert_eq!(
                        fields.get("spellcasting_ability"),
                        Some(&Value::Str("INT".into()))
                    );
                }
                _ => panic!("expected Struct, got {:?}", fields),
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

    // Pre-grant Spellcasting
    let group_val = Value::Struct {
        name: "Spellcasting".into(),
        fields: {
            let mut f = BTreeMap::new();
            f.insert("spell_slots".into(), Value::Int(4));
            f.insert("spell_dc".into(), Value::Int(15));
            f.insert("spellcasting_ability".into(), Value::Str("INT".into()));
            f
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
        Response::Acknowledged, // ActionStarted
        Response::Acknowledged, // RevokeGroup
        Response::Acknowledged, // ActionCompleted
    ]);

    let _ = interp.execute_action(
        &state,
        &mut handler,
        "SealMagic",
        gm,
        vec![Value::Entity(wizard)],
    );

    let revoke_effect = handler
        .log
        .iter()
        .find(|e| matches!(e, Effect::RevokeGroup { .. }));
    assert!(revoke_effect.is_some(), "should emit RevokeGroup effect");

    match revoke_effect.unwrap() {
        Effect::RevokeGroup { entity, group_name } => {
            assert_eq!(*entity, wizard);
            assert_eq!(group_name, "Spellcasting");
        }
        _ => unreachable!(),
    }
}
