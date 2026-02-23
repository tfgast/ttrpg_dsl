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

// ── Non-zero min bounds ────────────────────────────────────────

const NONZERO_MIN_SYSTEM: &str = r#"
system "test" {
    entity Character {
        abilities: map<int, resource(1..20)>
    }
    action Buff on actor: Character (stat: int) {
        cost { action }
        resolve {
            actor.abilities[stat] += 1
        }
    }
    action Drain on actor: Character (stat: int) {
        cost { action }
        resolve {
            actor.abilities[stat] -= 1
        }
    }
    action SetStat on actor: Character (stat: int, val: int) {
        cost { action }
        resolve {
            actor.abilities[stat] = val
        }
    }
}
"#;

#[test]
fn resource_map_nonzero_min_prevents_underflow() {
    let (program, result) = compile(NONZERO_MIN_SYSTEM);
    let interp = Interpreter::new(&program, &result.env).unwrap();

    let mut state = GameState::new();
    let mut abilities = BTreeMap::new();
    abilities.insert(Value::Int(1), Value::Int(1)); // STR at min
    let mut fields = HashMap::new();
    fields.insert("abilities".into(), Value::Map(abilities));
    let hero = state.add_entity("Character", fields);
    state.set_turn_budget(&hero, standard_turn_budget());

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, // ActionStarted
    ]);
    adapter.run(&mut handler, |s, h| {
        interp
            .execute_action(s, h, "Drain", hero, vec![Value::Int(1)])
            .unwrap();
    });

    // Should be clamped at 1 (the min), not 0
    let val = adapter.read_field(&hero, "abilities");
    let map = match val {
        Some(Value::Map(m)) => m,
        other => panic!("expected Map, got {:?}", other),
    };
    assert_eq!(map.get(&Value::Int(1)), Some(&Value::Int(1)));
}

#[test]
fn resource_map_nonzero_min_set_below_clamps_up() {
    let (program, result) = compile(NONZERO_MIN_SYSTEM);
    let interp = Interpreter::new(&program, &result.env).unwrap();

    let mut state = GameState::new();
    let mut abilities = BTreeMap::new();
    abilities.insert(Value::Int(1), Value::Int(10));
    let mut fields = HashMap::new();
    fields.insert("abilities".into(), Value::Map(abilities));
    let hero = state.add_entity("Character", fields);
    state.set_turn_budget(&hero, standard_turn_budget());

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, // ActionStarted
    ]);
    adapter.run(&mut handler, |s, h| {
        interp
            .execute_action(s, h, "SetStat", hero, vec![Value::Int(1), Value::Int(-5)])
            .unwrap();
    });

    // Setting to -5 should clamp up to 1 (the min)
    let val = adapter.read_field(&hero, "abilities");
    let map = match val {
        Some(Value::Map(m)) => m,
        other => panic!("expected Map, got {:?}", other),
    };
    assert_eq!(map.get(&Value::Int(1)), Some(&Value::Int(1)));
}

#[test]
fn resource_map_nonzero_min_auto_init_missing_key() {
    let (program, result) = compile(NONZERO_MIN_SYSTEM);
    let interp = Interpreter::new(&program, &result.env).unwrap();

    let mut state = GameState::new();
    let mut fields = HashMap::new();
    fields.insert("abilities".into(), Value::Map(BTreeMap::new())); // empty map
    let hero = state.add_entity("Character", fields);
    state.set_turn_budget(&hero, standard_turn_budget());

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, // ActionStarted
    ]);
    // Buff on missing key 1: current defaults to 0, 0+1=1, clamped to [1..20] → 1
    adapter.run(&mut handler, |s, h| {
        interp
            .execute_action(s, h, "Buff", hero, vec![Value::Int(1)])
            .unwrap();
    });

    let val = adapter.read_field(&hero, "abilities");
    let map = match val {
        Some(Value::Map(m)) => m,
        other => panic!("expected Map, got {:?}", other),
    };
    assert_eq!(
        map.get(&Value::Int(1)),
        Some(&Value::Int(1)),
        "missing key: 0+1=1, within [1..20]"
    );
}

// ── Multiple mutations in one action ──────────────────────────

const MULTI_MUTATE_SYSTEM: &str = r#"
system "test" {
    entity Character {
        spell_slots: map<int, resource(0..9)>
    }
    action MultiCast on actor: Character (level1: int, level2: int) {
        cost { action }
        resolve {
            actor.spell_slots[level1] -= 1
            actor.spell_slots[level2] -= 1
        }
    }
}
"#;

#[test]
fn resource_map_multiple_keys_mutated_in_one_action() {
    let (program, result) = compile(MULTI_MUTATE_SYSTEM);
    let interp = Interpreter::new(&program, &result.env).unwrap();

    let mut state = GameState::new();
    let mut slots = BTreeMap::new();
    slots.insert(Value::Int(1), Value::Int(4));
    slots.insert(Value::Int(3), Value::Int(2));
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
            .execute_action(s, h, "MultiCast", hero, vec![Value::Int(1), Value::Int(3)])
            .unwrap();
    });

    let slot_val = adapter.read_field(&hero, "spell_slots");
    let map = match slot_val {
        Some(Value::Map(m)) => m,
        other => panic!("expected Map, got {:?}", other),
    };
    assert_eq!(map.get(&Value::Int(1)), Some(&Value::Int(3)), "level 1: 4-1=3");
    assert_eq!(map.get(&Value::Int(3)), Some(&Value::Int(1)), "level 3: 2-1=1");
}

// ── Derive reads from resource map ─────────────────────────────

const DERIVE_READS_MAP_SYSTEM: &str = r#"
system "test" {
    entity Character {
        spell_slots: map<int, resource(0..9)>
    }
    derive slots_at(actor: Character, level: int) -> int {
        actor.spell_slots[level]
    }
    derive total_low_slots(actor: Character) -> int {
        actor.spell_slots[1] + actor.spell_slots[2] + actor.spell_slots[3]
    }
}
"#;

#[test]
fn resource_map_derive_reads_present_key() {
    let (program, result) = compile(DERIVE_READS_MAP_SYSTEM);
    let interp = Interpreter::new(&program, &result.env).unwrap();

    let mut state = GameState::new();
    let mut slots = BTreeMap::new();
    slots.insert(Value::Int(1), Value::Int(4));
    slots.insert(Value::Int(2), Value::Int(3));
    slots.insert(Value::Int(3), Value::Int(2));
    let mut fields = HashMap::new();
    fields.insert("spell_slots".into(), Value::Map(slots));
    let hero = state.add_entity("Character", fields);

    let mut handler = ScriptedHandler::new();
    let result_val = interp
        .evaluate_derive(&state, &mut handler, "slots_at", vec![Value::Entity(hero), Value::Int(2)])
        .unwrap();
    assert_eq!(result_val, Value::Int(3));
}

#[test]
fn resource_map_derive_sums_multiple_keys() {
    let (program, result) = compile(DERIVE_READS_MAP_SYSTEM);
    let interp = Interpreter::new(&program, &result.env).unwrap();

    let mut state = GameState::new();
    let mut slots = BTreeMap::new();
    slots.insert(Value::Int(1), Value::Int(4));
    slots.insert(Value::Int(2), Value::Int(3));
    slots.insert(Value::Int(3), Value::Int(2));
    let mut fields = HashMap::new();
    fields.insert("spell_slots".into(), Value::Map(slots));
    let hero = state.add_entity("Character", fields);

    let mut handler = ScriptedHandler::new();
    let result_val = interp
        .evaluate_derive(&state, &mut handler, "total_low_slots", vec![Value::Entity(hero)])
        .unwrap();
    assert_eq!(result_val, Value::Int(9), "4+3+2=9");
}

// ── Enum-keyed resource map ────────────────────────────────────

const ENUM_KEY_SYSTEM: &str = r#"
system "test" {
    enum Ability { STR, DEX, CON, INT, WIS, CHA }
    entity Character {
        abilities: map<Ability, resource(1..20)>
    }
    action Buff on actor: Character (stat: Ability) {
        cost { action }
        resolve {
            actor.abilities[stat] += 1
        }
    }
    derive get_stat(actor: Character, stat: Ability) -> int {
        actor.abilities[stat]
    }
}
"#;

fn ability_variant(variant: &str) -> Value {
    Value::EnumVariant {
        enum_name: "Ability".to_string(),
        variant: variant.to_string(),
        fields: BTreeMap::new(),
    }
}

#[test]
fn resource_map_enum_key_read_and_mutate() {
    let (program, result) = compile(ENUM_KEY_SYSTEM);
    let interp = Interpreter::new(&program, &result.env).unwrap();

    let mut state = GameState::new();
    let mut abilities = BTreeMap::new();
    abilities.insert(ability_variant("STR"), Value::Int(18));
    abilities.insert(ability_variant("DEX"), Value::Int(14));
    let mut fields = HashMap::new();
    fields.insert("abilities".into(), Value::Map(abilities));
    let hero = state.add_entity("Character", fields);
    state.set_turn_budget(&hero, standard_turn_budget());

    // Read via derive
    let mut handler = ScriptedHandler::new();
    let str_val = interp
        .evaluate_derive(&state, &mut handler, "get_stat", vec![Value::Entity(hero), ability_variant("STR")])
        .unwrap();
    assert_eq!(str_val, Value::Int(18));

    // Buff STR (18 → 19)
    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, // ActionStarted
    ]);
    adapter.run(&mut handler, |s, h| {
        interp
            .execute_action(s, h, "Buff", hero, vec![ability_variant("STR")])
            .unwrap();
    });

    let val = adapter.read_field(&hero, "abilities");
    let map = match val {
        Some(Value::Map(m)) => m,
        other => panic!("expected Map, got {:?}", other),
    };
    assert_eq!(map.get(&ability_variant("STR")), Some(&Value::Int(19)));
    assert_eq!(map.get(&ability_variant("DEX")), Some(&Value::Int(14)), "DEX unchanged");
}

#[test]
fn resource_map_enum_key_clamped_at_max() {
    let (program, result) = compile(ENUM_KEY_SYSTEM);
    let interp = Interpreter::new(&program, &result.env).unwrap();

    let mut state = GameState::new();
    let mut abilities = BTreeMap::new();
    abilities.insert(ability_variant("STR"), Value::Int(20)); // at max
    let mut fields = HashMap::new();
    fields.insert("abilities".into(), Value::Map(abilities));
    let hero = state.add_entity("Character", fields);
    state.set_turn_budget(&hero, standard_turn_budget());

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, // ActionStarted
    ]);
    adapter.run(&mut handler, |s, h| {
        interp
            .execute_action(s, h, "Buff", hero, vec![ability_variant("STR")])
            .unwrap();
    });

    let val = adapter.read_field(&hero, "abilities");
    let map = match val {
        Some(Value::Map(m)) => m,
        other => panic!("expected Map, got {:?}", other),
    };
    assert_eq!(
        map.get(&ability_variant("STR")),
        Some(&Value::Int(20)),
        "should be clamped at max 20"
    );
}

// ── Local-to-entity path preserves bounds (trigger payload) ────

const LOCAL_TO_ENTITY_SYSTEM: &str = r#"
system "test" {
    entity Character {
        spell_slots: map<int, resource(0..9)>
    }
    event spell_cast(caster: Character, level: int) {}
    reaction CounterSpell on reactor: Character (trigger: spell_cast(reactor)) {
        cost { reaction }
        resolve {
            trigger.caster.spell_slots[trigger.level] -= 1
        }
    }
}
"#;

#[test]
fn local_to_entity_mutation_carries_bounds() {
    let (program, result) = compile(LOCAL_TO_ENTITY_SYSTEM);
    let interp = Interpreter::new(&program, &result.env).unwrap();

    let mut state = GameState::new();
    // The caster entity (trigger.caster)
    let mut caster_slots = BTreeMap::new();
    caster_slots.insert(Value::Int(1), Value::Int(0)); // at min
    let mut caster_fields = HashMap::new();
    caster_fields.insert("spell_slots".into(), Value::Map(caster_slots));
    let caster = state.add_entity("Character", caster_fields);

    // The reactor entity
    let mut reactor_fields = HashMap::new();
    reactor_fields.insert("spell_slots".into(), Value::Map(BTreeMap::new()));
    let reactor = state.add_entity("Character", reactor_fields);
    state.set_turn_budget(&reactor, standard_turn_budget());

    // Build event payload struct: { caster: Entity, level: Int }
    let payload = Value::Struct {
        name: "__event_spell_cast".to_string(),
        fields: {
            let mut f = BTreeMap::new();
            f.insert("caster".to_string(), Value::Entity(caster));
            f.insert("level".to_string(), Value::Int(1));
            f
        },
    };

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, // ActionStarted
    ]);
    adapter.run(&mut handler, |s, h| {
        interp
            .execute_reaction(s, h, "CounterSpell", reactor, payload.clone())
            .unwrap();
    });

    // Should clamp at 0, not go to -1
    let slot_val = adapter.read_field(&caster, "spell_slots");
    let map = match slot_val {
        Some(Value::Map(m)) => m,
        other => panic!("expected Map, got {:?}", other),
    };
    assert_eq!(
        map.get(&Value::Int(1)),
        Some(&Value::Int(0)),
        "local-to-entity mutation via trigger should respect resource bounds"
    );
}

#[test]
fn local_to_entity_mutation_effect_has_bounds() {
    let (program, result) = compile(LOCAL_TO_ENTITY_SYSTEM);
    let interp = Interpreter::new(&program, &result.env).unwrap();

    let mut state = GameState::new();
    let mut caster_slots = BTreeMap::new();
    caster_slots.insert(Value::Int(1), Value::Int(4));
    let mut caster_fields = HashMap::new();
    caster_fields.insert("spell_slots".into(), Value::Map(caster_slots));
    let caster = state.add_entity("Character", caster_fields);

    let mut reactor_fields = HashMap::new();
    reactor_fields.insert("spell_slots".into(), Value::Map(BTreeMap::new()));
    let reactor = state.add_entity("Character", reactor_fields);
    state.set_turn_budget(&reactor, standard_turn_budget());

    let payload = Value::Struct {
        name: "__event_spell_cast".to_string(),
        fields: {
            let mut f = BTreeMap::new();
            f.insert("caster".to_string(), Value::Entity(caster));
            f.insert("level".to_string(), Value::Int(1));
            f
        },
    };

    // Record raw effects (no adapter)
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, // ActionStarted
    ]);
    let _ = interp.execute_reaction(&state, &mut handler, "CounterSpell", reactor, payload);

    let mutate = handler
        .log
        .iter()
        .find(|e| matches!(e, Effect::MutateField { .. }));
    assert!(mutate.is_some(), "expected MutateField effect");
    if let Effect::MutateField { bounds, .. } = mutate.unwrap() {
        assert_eq!(
            *bounds,
            Some((Value::Int(0), Value::Int(9))),
            "local-to-entity MutateField via trigger should carry resource bounds"
        );
    }
}

// ── Complex bound expressions ──────────────────────────────────

const COMPLEX_BOUNDS_SYSTEM: &str = r#"
system "test" {
    entity Character {
        max_slots: int = 4
        spell_slots: map<int, resource(0..max_slots + 1)>
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
fn complex_bound_expression_is_evaluated() {
    let (program, result) = compile(COMPLEX_BOUNDS_SYSTEM);
    let interp = Interpreter::new(&program, &result.env).unwrap();

    let mut state = GameState::new();
    let mut slots = BTreeMap::new();
    slots.insert(Value::Int(1), Value::Int(5)); // max_slots + 1 = 5, so at max
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

    // max_slots=4, so max bound is 4+1=5. Already at 5, should stay clamped.
    let slot_val = adapter.read_field(&hero, "spell_slots");
    let map = match slot_val {
        Some(Value::Map(m)) => m,
        other => panic!("expected Map, got {:?}", other),
    };
    assert_eq!(
        map.get(&Value::Int(1)),
        Some(&Value::Int(5)),
        "complex bound (max_slots + 1 = 5) should clamp at 5"
    );
}

#[test]
fn complex_bound_expression_effect_has_bounds() {
    let (program, result) = compile(COMPLEX_BOUNDS_SYSTEM);
    let interp = Interpreter::new(&program, &result.env).unwrap();

    let mut state = GameState::new();
    let mut slots = BTreeMap::new();
    slots.insert(Value::Int(1), Value::Int(3));
    let mut fields = HashMap::new();
    fields.insert("max_slots".into(), Value::Int(4));
    fields.insert("spell_slots".into(), Value::Map(slots));
    let hero = state.add_entity("Character", fields);
    state.set_turn_budget(&hero, standard_turn_budget());

    // Record raw effects
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, // ActionStarted
    ]);
    let _ = interp.execute_action(&state, &mut handler, "GainSlot", hero, vec![Value::Int(1)]);

    let mutate = handler
        .log
        .iter()
        .find(|e| matches!(e, Effect::MutateField { .. }));
    assert!(mutate.is_some(), "expected MutateField effect");
    if let Effect::MutateField { bounds, .. } = mutate.unwrap() {
        assert_eq!(
            *bounds,
            Some((Value::Int(0), Value::Int(5))),
            "complex bound expression should resolve to (0, max_slots+1=5)"
        );
    }
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
