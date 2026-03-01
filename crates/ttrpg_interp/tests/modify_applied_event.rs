//! Integration tests for the built-in `modify_applied` event.
//!
//! Tests the full pipeline (parse → lower → check → interpret) verifying that
//! when a condition's modify clause fires, matching `modify_applied` hooks
//! execute automatically.

use std::collections::{HashMap, VecDeque};

use ttrpg_ast::diagnostic::Severity;
use ttrpg_ast::FileId;
use ttrpg_interp::adapter::StateAdapter;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::StateProvider;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

// ── Setup ──────────────────────────────────────────────────────

fn setup(source: &str) -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
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

fn setup_expect_errors(source: &str) -> Vec<String> {
    let (program, parse_errors) = ttrpg_parser::parse(source, FileId::SYNTH);
    if !parse_errors.is_empty() {
        return parse_errors.iter().map(|d| d.message.clone()).collect();
    }
    let mut lower_diags = Vec::new();
    let program = ttrpg_parser::lower_moves(program, &mut lower_diags);
    let result = ttrpg_checker::check(&program);
    result
        .diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .map(|d| d.message.clone())
        .collect()
}

// ── ScriptedHandler ────────────────────────────────────────────

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
}

impl EffectHandler for ScriptedHandler {
    fn handle(&mut self, effect: Effect) -> Response {
        self.log.push(effect);
        self.script.pop_front().unwrap_or(Response::Acknowledged)
    }
}

// ── Tests ──────────────────────────────────────────────────────

#[test]
fn modify_applied_event_registered_as_builtin() {
    // The modify_applied event should be available even without user-defined events
    let source = r#"
system "test" {
    entity Character { HP: int }
}
"#;
    let (_program, result) = setup(source);
    assert!(
        result.env.events.contains_key("modify_applied"),
        "modify_applied should be registered as a built-in event"
    );
    let event_info = &result.env.events["modify_applied"];
    assert_eq!(event_info.params.len(), 2);
    assert_eq!(event_info.params[0].name, "bearer");
    assert_eq!(event_info.params[1].name, "condition");
    assert_eq!(event_info.fields.len(), 1);
    assert_eq!(event_info.fields[0].0, "target_fn");
}

#[test]
fn modify_applied_hook_type_checks() {
    // A hook on modify_applied should type-check successfully
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Blessed on bearer: Character {
        modify attack_roll(attacker: bearer) {
            modifier = modifier + 4
        }
    }
    derive attack_roll(attacker: Character, modifier: int) -> int {
        modifier
    }
    hook TrackModify on c: Character (trigger: modify_applied(bearer: c)) {
        c.HP += 1
    }
}
"#;
    let errors = setup_expect_errors(source);
    assert!(
        errors.is_empty(),
        "hook on modify_applied should type-check without errors, got: {:?}",
        errors
    );
}

#[test]
fn modify_applied_hook_fires_when_modifier_activates() {
    // When a condition's modify clause fires, the modify_applied hook should execute
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Blessed on bearer: Character {
        modify attack_roll(attacker: bearer) {
            modifier = modifier + 4
        }
    }
    derive attack_roll(attacker: Character, modifier: int) -> int {
        modifier
    }
    hook TrackModify on c: Character (trigger: modify_applied(bearer: c)) {
        c.HP += 1
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(10));
    let entity = state.add_entity("Character", fields);

    // Grant Blessed condition
    state.apply_condition(
        &entity,
        "Blessed",
        std::collections::BTreeMap::new(),
        Value::None,
        None,
    );

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();

    let val = adapter.run(&mut handler, |state, eff_handler| {
        interp.evaluate_derive(
            state,
            eff_handler,
            "attack_roll",
            vec![Value::Entity(entity), Value::Int(0)],
        )
    });

    // The derive result should be 4 (0 + 4 from Blessed modifier)
    assert_eq!(val.unwrap(), Value::Int(4));

    let state = adapter.into_inner();
    // Hook should have incremented HP from 10 to 11
    assert_eq!(
        state.read_field(&entity, "HP"),
        Some(Value::Int(11)),
        "modify_applied hook should have fired and incremented HP"
    );
}

#[test]
fn modify_applied_hook_accesses_trigger_fields() {
    // Hook should be able to access trigger.condition and trigger.target_fn
    let source = r#"
system "test" {
    entity Character { HP: int, last_modified_fn: string }
    condition Blessed on bearer: Character {
        modify attack_roll(attacker: bearer) {
            modifier = modifier + 4
        }
    }
    derive attack_roll(attacker: Character, modifier: int) -> int {
        modifier
    }
    hook RecordModify on c: Character (trigger: modify_applied(bearer: c)) {
        c.last_modified_fn = trigger.target_fn
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(10));
    fields.insert("last_modified_fn".into(), Value::Str("none".into()));
    let entity = state.add_entity("Character", fields);

    state.apply_condition(
        &entity,
        "Blessed",
        std::collections::BTreeMap::new(),
        Value::None,
        None,
    );

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();

    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .evaluate_derive(
                state,
                eff_handler,
                "attack_roll",
                vec![Value::Entity(entity), Value::Int(0)],
            )
            .unwrap();
    });

    let state = adapter.into_inner();
    // Hook should have recorded the target function name
    assert_eq!(
        state.read_field(&entity, "last_modified_fn"),
        Some(Value::Str("attack_roll".into())),
        "hook should have access to trigger.target_fn"
    );
}

#[test]
fn modify_applied_hook_can_remove_condition() {
    // The "until next use" pattern: hook removes the condition after its modifier fires
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition OneTimeBoost on bearer: Character {
        modify attack_roll(attacker: bearer) {
            modifier = modifier + 10
        }
    }
    derive attack_roll(attacker: Character, modifier: int) -> int {
        modifier
    }
    hook ConsumeOnUse on c: Character (trigger: modify_applied(bearer: c)) {
        if trigger.condition.name == "OneTimeBoost" {
            remove_condition(c, trigger.condition)
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(10));
    let entity = state.add_entity("Character", fields);

    state.apply_condition(
        &entity,
        "OneTimeBoost",
        std::collections::BTreeMap::new(),
        Value::None,
        None,
    );

    // Verify condition exists before
    assert_eq!(state.read_conditions(&entity).unwrap().len(), 1);

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();

    // First call: modifier fires, hook removes condition
    let val = adapter.run(&mut handler, |state, eff_handler| {
        interp.evaluate_derive(
            state,
            eff_handler,
            "attack_roll",
            vec![Value::Entity(entity), Value::Int(0)],
        )
    });
    assert_eq!(val.unwrap(), Value::Int(10), "first call should get the +10 boost");

    let state = adapter.into_inner();
    // Condition should have been removed by the hook
    assert_eq!(
        state.read_conditions(&entity).unwrap().len(),
        0,
        "hook should have removed OneTimeBoost condition"
    );
}

#[test]
fn modify_applied_not_emitted_when_no_hooks() {
    // When no hooks listen for modify_applied, the fast path should skip event emission
    // (verified by checking that no extra ActionStarted effects are emitted for hooks)
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Blessed on bearer: Character {
        modify attack_roll(attacker: bearer) {
            modifier = modifier + 4
        }
    }
    derive attack_roll(attacker: Character, modifier: int) -> int {
        modifier
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(10));
    let entity = state.add_entity("Character", fields);

    state.apply_condition(
        &entity,
        "Blessed",
        std::collections::BTreeMap::new(),
        Value::None,
        None,
    );

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();

    let val = adapter.run(&mut handler, |state, eff_handler| {
        interp.evaluate_derive(
            state,
            eff_handler,
            "attack_roll",
            vec![Value::Entity(entity), Value::Int(0)],
        )
    });
    assert_eq!(val.unwrap(), Value::Int(4));

    // Should have ModifyApplied effect (from the pipeline) but no ActionStarted for hooks
    let hook_effects: Vec<_> = handler
        .log
        .iter()
        .filter(|e| matches!(e, Effect::ActionStarted { kind: ttrpg_interp::effect::ActionKind::Hook { .. }, .. }))
        .collect();
    assert!(
        hook_effects.is_empty(),
        "no hook ActionStarted should be emitted when no hooks listen for modify_applied"
    );
}

#[test]
fn modify_applied_deduplicates_by_condition_id() {
    // A condition with multiple modify clauses that all fire should emit only one
    // modify_applied event (deduplicated by condition_id)
    let source = r#"
system "test" {
    entity Character { HP: int, counter: int }
    condition DoubleModify on bearer: Character {
        modify compute(target: bearer) {
            a = a + 1
        }
        modify compute(target: bearer) {
            b = b + 1
        }
    }
    derive compute(target: Character, a: int, b: int) -> int {
        a + b
    }
    hook CountModifyApplied on c: Character (trigger: modify_applied(bearer: c)) {
        c.counter += 1
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(10));
    fields.insert("counter".into(), Value::Int(0));
    let entity = state.add_entity("Character", fields);

    state.apply_condition(
        &entity,
        "DoubleModify",
        std::collections::BTreeMap::new(),
        Value::None,
        None,
    );

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();

    let val = adapter.run(&mut handler, |state, eff_handler| {
        interp.evaluate_derive(
            state,
            eff_handler,
            "compute",
            vec![Value::Entity(entity), Value::Int(0), Value::Int(0)],
        )
    });
    // a=0+1=1, b=0+1=1, result=2
    assert_eq!(val.unwrap(), Value::Int(2));

    let state = adapter.into_inner();
    // Hook should fire only once despite two modify clauses from the same condition
    assert_eq!(
        state.read_field(&entity, "counter"),
        Some(Value::Int(1)),
        "modify_applied should deduplicate by condition id — hook fires once"
    );
}
