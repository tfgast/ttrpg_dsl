//! Integration tests for resource-valued maps: `map<K, resource(min..max)>`.
//!
//! Tests the full pipeline: parse → lower → check → interpret, verifying
//! that resource bounds are properly resolved and clamped for map entries.

use std::collections::{BTreeMap, HashMap, VecDeque};

use ttrpg_ast::diagnostic::Severity;
use ttrpg_interp::adapter::StateAdapter;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::StateProvider;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

// ── Setup ──────────────────────────────────────────────────────

fn compile(source: &str) -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    let (program, parse_errors) = ttrpg_parser::parse(source);
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

fn standard_turn_budget() -> BTreeMap<String, Value> {
    let mut b = BTreeMap::new();
    b.insert("actions".into(), Value::Int(1));
    b.insert("bonus_actions".into(), Value::Int(1));
    b.insert("reactions".into(), Value::Int(1));
    b.insert("movement".into(), Value::Int(30));
    b.insert("free_interactions".into(), Value::Int(1));
    b
}

// ── Scripted handler (returns Acknowledged, records effects) ──

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

// ── Test systems ───────────────────────────────────────────────

const RESOURCE_MAP_SYSTEM: &str = r#"
system "test" {
    entity Character {
        spell_slots: map<int, resource(0..9)>
    }
    action CastSpell on actor: Character (level: int) {
        cost { action }
        resolve {
            actor.spell_slots[level] -= 1
        }
    }
    action GainSlot on actor: Character (level: int) {
        cost { action }
        resolve {
            actor.spell_slots[level] += 1
        }
    }
    action SetSlot on actor: Character (level: int, count: int) {
        cost { action }
        resolve {
            actor.spell_slots[level] = count
        }
    }
}
"#;

// ── Tests ──────────────────────────────────────────────────────

#[test]
fn resource_map_mutation_carries_bounds() {
    let (program, result) = compile(RESOURCE_MAP_SYSTEM);
    let interp = Interpreter::new(&program, &result.env).unwrap();

    let mut state = GameState::new();
    let mut slots = BTreeMap::new();
    slots.insert(Value::Int(1), Value::Int(4));
    let mut fields = HashMap::new();
    fields.insert("spell_slots".into(), Value::Map(slots));
    let hero = state.add_entity("Character", fields);
    state.set_turn_budget(&hero, standard_turn_budget());

    // Execute CastSpell — record the raw effects (no adapter)
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, // ActionStarted
    ]);
    let _ = interp.execute_action(&state, &mut handler, "CastSpell", hero, vec![Value::Int(1)]);

    // Find the MutateField effect and verify it carries bounds
    let mutate = handler
        .log
        .iter()
        .find(|e| matches!(e, Effect::MutateField { .. }));
    assert!(mutate.is_some(), "expected MutateField effect");
    if let Effect::MutateField { bounds, .. } = mutate.unwrap() {
        assert_eq!(
            *bounds,
            Some((Value::Int(0), Value::Int(9))),
            "resource bounds should be (0, 9)"
        );
    }
}

#[test]
fn resource_map_clamping_prevents_underflow() {
    let (program, result) = compile(RESOURCE_MAP_SYSTEM);
    let interp = Interpreter::new(&program, &result.env).unwrap();

    let mut state = GameState::new();
    let mut slots = BTreeMap::new();
    slots.insert(Value::Int(1), Value::Int(0)); // already at min
    let mut fields = HashMap::new();
    fields.insert("spell_slots".into(), Value::Map(slots));
    let hero = state.add_entity("Character", fields);
    state.set_turn_budget(&hero, standard_turn_budget());

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, // ActionStarted
    ]);
    adapter.run(&mut handler, |s, h| {
        interp
            .execute_action(s, h, "CastSpell", hero, vec![Value::Int(1)])
            .unwrap();
    });

    // Value should be clamped at 0, not -1
    let slot_val = adapter.read_field(&hero, "spell_slots");
    let map = match slot_val {
        Some(Value::Map(m)) => m,
        other => panic!("expected Map, got {:?}", other),
    };
    assert_eq!(map.get(&Value::Int(1)), Some(&Value::Int(0)));
}

#[test]
fn resource_map_clamping_prevents_overflow() {
    let (program, result) = compile(RESOURCE_MAP_SYSTEM);
    let interp = Interpreter::new(&program, &result.env).unwrap();

    let mut state = GameState::new();
    let mut slots = BTreeMap::new();
    slots.insert(Value::Int(1), Value::Int(9)); // already at max
    let mut fields = HashMap::new();
    fields.insert("spell_slots".into(), Value::Map(slots));
    let hero = state.add_entity("Character", fields);
    state.set_turn_budget(&hero, standard_turn_budget());

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, // ActionStarted
    ]);
    adapter.run(&mut handler, |s, h| {
        interp
            .execute_action(s, h, "GainSlot", hero, vec![Value::Int(1)])
            .unwrap();
    });

    // Value should be clamped at 9, not 10
    let slot_val = adapter.read_field(&hero, "spell_slots");
    let map = match slot_val {
        Some(Value::Map(m)) => m,
        other => panic!("expected Map, got {:?}", other),
    };
    assert_eq!(map.get(&Value::Int(1)), Some(&Value::Int(9)));
}

#[test]
fn resource_map_set_is_clamped() {
    let (program, result) = compile(RESOURCE_MAP_SYSTEM);
    let interp = Interpreter::new(&program, &result.env).unwrap();

    let mut state = GameState::new();
    let mut slots = BTreeMap::new();
    slots.insert(Value::Int(1), Value::Int(5));
    let mut fields = HashMap::new();
    fields.insert("spell_slots".into(), Value::Map(slots));
    let hero = state.add_entity("Character", fields);
    state.set_turn_budget(&hero, standard_turn_budget());

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, // ActionStarted
    ]);
    adapter.run(&mut handler, |s, h| {
        interp
            .execute_action(s, h, "SetSlot", hero, vec![Value::Int(1), Value::Int(20)])
            .unwrap();
    });

    // Value should be clamped at 9, not 20
    let slot_val = adapter.read_field(&hero, "spell_slots");
    let map = match slot_val {
        Some(Value::Map(m)) => m,
        other => panic!("expected Map, got {:?}", other),
    };
    assert_eq!(map.get(&Value::Int(1)), Some(&Value::Int(9)));
}

#[test]
fn resource_map_write_to_missing_key_auto_initializes() {
    let (program, result) = compile(RESOURCE_MAP_SYSTEM);
    let interp = Interpreter::new(&program, &result.env).unwrap();

    let mut state = GameState::new();
    let mut fields = HashMap::new();
    fields.insert("spell_slots".into(), Value::Map(BTreeMap::new())); // empty map
    let hero = state.add_entity("Character", fields);
    state.set_turn_budget(&hero, standard_turn_budget());

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, // ActionStarted
    ]);
    // GainSlot on missing key 5: current defaults to 0, 0+1=1, within bounds
    adapter.run(&mut handler, |s, h| {
        interp
            .execute_action(s, h, "GainSlot", hero, vec![Value::Int(5)])
            .unwrap();
    });

    let slot_val = adapter.read_field(&hero, "spell_slots");
    let map = match slot_val {
        Some(Value::Map(m)) => m,
        other => panic!("expected Map, got {:?}", other),
    };
    assert_eq!(
        map.get(&Value::Int(5)),
        Some(&Value::Int(1)),
        "missing key should auto-init to 0 then apply += 1"
    );
}

// ── Dynamic bounds from entity field ───────────────────────────

const DYNAMIC_BOUNDS_SYSTEM: &str = r#"
system "test" {
    entity Character {
        max_slots: int = 4
        spell_slots: map<int, resource(0..max_slots)>
    }
    action GainSlot on actor: Character (level: int) {
        cost { action }
        resolve {
            actor.spell_slots[level] += 1
        }
    }
}
"#;

#[test]
fn resource_map_dynamic_bounds_from_entity_field() {
    let (program, result) = compile(DYNAMIC_BOUNDS_SYSTEM);
    let interp = Interpreter::new(&program, &result.env).unwrap();

    let mut state = GameState::new();
    let mut slots = BTreeMap::new();
    slots.insert(Value::Int(1), Value::Int(4)); // at max_slots
    let mut fields = HashMap::new();
    fields.insert("max_slots".into(), Value::Int(4));
    fields.insert("spell_slots".into(), Value::Map(slots));
    let hero = state.add_entity("Character", fields);
    state.set_turn_budget(&hero, standard_turn_budget());

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, // ActionStarted
    ]);
    adapter.run(&mut handler, |s, h| {
        interp
            .execute_action(s, h, "GainSlot", hero, vec![Value::Int(1)])
            .unwrap();
    });

    // Should be clamped at max_slots=4, not 5
    let slot_val = adapter.read_field(&hero, "spell_slots");
    let map = match slot_val {
        Some(Value::Map(m)) => m,
        other => panic!("expected Map, got {:?}", other),
    };
    assert_eq!(map.get(&Value::Int(1)), Some(&Value::Int(4)));
}

// ── Resource map inside optional group ─────────────────────────

const GROUP_RESOURCE_MAP_SYSTEM: &str = r#"
system "test" {
    entity Character {
        optional Spellcasting {
            spell_slots: map<int, resource(0..9)>
        }
    }
    action CastSpell on actor: Character with Spellcasting (level: int) {
        cost { action }
        resolve {
            actor.Spellcasting.spell_slots[level] -= 1
        }
    }
}
"#;

#[test]
fn resource_map_in_optional_group_is_clamped() {
    let (program, result) = compile(GROUP_RESOURCE_MAP_SYSTEM);
    let interp = Interpreter::new(&program, &result.env).unwrap();

    let mut state = GameState::new();
    let mut slots = BTreeMap::new();
    slots.insert(Value::Int(1), Value::Int(0)); // at min
    let group_struct = Value::Struct {
        name: "Spellcasting".to_string(),
        fields: {
            let mut f = BTreeMap::new();
            f.insert("spell_slots".to_string(), Value::Map(slots));
            f
        },
    };
    let mut fields = HashMap::new();
    fields.insert("Spellcasting".into(), group_struct);
    let hero = state.add_entity("Character", fields);
    state.set_turn_budget(&hero, standard_turn_budget());

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, // ActionStarted
    ]);
    adapter.run(&mut handler, |s, h| {
        interp
            .execute_action(s, h, "CastSpell", hero, vec![Value::Int(1)])
            .unwrap();
    });

    // Should be clamped at 0, not go to -1
    let group_val = adapter.read_field(&hero, "Spellcasting");
    let spell_slots = match group_val {
        Some(Value::Struct { fields, .. }) => fields.get("spell_slots").cloned().unwrap(),
        other => panic!("expected Struct, got {:?}", other),
    };
    let map = match spell_slots {
        Value::Map(m) => m,
        other => panic!("expected Map, got {:?}", other),
    };
    assert_eq!(map.get(&Value::Int(1)), Some(&Value::Int(0)));
}

// ── Direct resource field (not map) also gets bounds ───────────

const DIRECT_RESOURCE_SYSTEM: &str = r#"
system "test" {
    entity Character {
        max_HP: int = 100
        HP: resource(0..max_HP)
    }
    action Damage on target: Character (amount: int) {
        cost { action }
        resolve {
            target.HP -= amount
        }
    }
}
"#;

#[test]
fn direct_resource_field_is_clamped() {
    let (program, result) = compile(DIRECT_RESOURCE_SYSTEM);
    let interp = Interpreter::new(&program, &result.env).unwrap();

    let mut state = GameState::new();
    let mut fields = HashMap::new();
    fields.insert("max_HP".into(), Value::Int(100));
    fields.insert("HP".into(), Value::Int(10));
    let hero = state.add_entity("Character", fields);
    state.set_turn_budget(&hero, standard_turn_budget());

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, // ActionStarted
    ]);
    adapter.run(&mut handler, |s, h| {
        interp
            .execute_action(s, h, "Damage", hero, vec![Value::Int(50)])
            .unwrap();
    });

    // HP should be clamped at 0, not -40
    let hp = adapter.read_field(&hero, "HP");
    assert_eq!(hp, Some(Value::Int(0)), "HP should be clamped at 0");
}
