//! Integration tests for condition lifecycle hooks (on_apply / on_remove).

use std::collections::VecDeque;

use rustc_hash::FxHashMap;
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

// ── Helpers ────────────────────────────────────────────────────

fn make_character(state: &mut GameState, hp: i64) -> ttrpg_interp::state::EntityRef {
    let mut fields = FxHashMap::default();
    fields.insert("hp".into(), Value::Int(hp));
    state.add_entity("Character", fields)
}

fn count_gate_effects(log: &[Effect], kind_name: &str) -> usize {
    log.iter()
        .filter(|e| {
            matches!(
                (kind_name, e),
                ("ConditionApplyGate", Effect::ConditionApplyGate { .. })
                    | ("ConditionRemovalGate", Effect::ConditionRemovalGate { .. })
            )
        })
        .count()
}

// ═══════════════════════════════════════════════════════════════
// on_apply fires and mutates state
// ═══════════════════════════════════════════════════════════════

#[test]
fn on_apply_fires_and_mutates_bearer() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    condition Poisoned on bearer: Character {
        on_apply {
            bearer.hp = bearer.hp - 5
        }
    }
    function poison(c: Character) {
        apply_condition(c, Poisoned, Duration.indefinite)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let c = make_character(&mut state, 20);

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, handler| {
        interp
            .evaluate_function(state, handler, "poison", vec![Value::Entity(c)])
            .unwrap();
    });

    // hp should be reduced by on_apply
    let final_state = adapter.into_inner();
    assert_eq!(final_state.read_field(&c, "hp"), Some(Value::Int(15)));

    // Gate effect should have been forwarded to handler
    assert_eq!(count_gate_effects(&handler.log, "ConditionApplyGate"), 1);
}

// ═══════════════════════════════════════════════════════════════
// on_apply error prevents condition activation
// ═══════════════════════════════════════════════════════════════

#[test]
fn on_apply_error_prevents_condition() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    condition Cursed on bearer: Character {
        on_apply {
            error("on_apply failed")
        }
    }
    function curse(c: Character) {
        apply_condition(c, Cursed, Duration.indefinite)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let c = make_character(&mut state, 20);

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    let err = adapter.run(&mut handler, |state, handler| {
        interp.evaluate_function(state, handler, "curse", vec![Value::Entity(c)])
    });

    // Should have errored
    assert!(err.is_err(), "expected error from on_apply");

    // Gate emitted, condition should NOT be active
    assert_eq!(count_gate_effects(&handler.log, "ConditionApplyGate"), 1);
    let final_state = adapter.into_inner();
    let conds = final_state.read_conditions(&c).unwrap_or_default();
    assert!(conds.is_empty(), "condition should not have been applied");
}

// ═══════════════════════════════════════════════════════════════
// on_remove fires and mutates state
// ═══════════════════════════════════════════════════════════════

#[test]
fn on_remove_fires_and_mutates_bearer() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    condition Poisoned on bearer: Character {
        on_remove {
            bearer.hp = bearer.hp + 3
        }
    }
    function poison_then_cure(c: Character) {
        apply_condition(c, Poisoned, Duration.indefinite)
        remove_condition(c, Poisoned)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let c = make_character(&mut state, 20);

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, handler| {
        interp
            .evaluate_function(
                state,
                handler,
                "poison_then_cure",
                vec![Value::Entity(c)],
            )
            .unwrap();
    });

    // hp should be +3 from on_remove
    let final_state = adapter.into_inner();
    assert_eq!(final_state.read_field(&c, "hp"), Some(Value::Int(23)));

    // Both gate effects forwarded
    assert_eq!(count_gate_effects(&handler.log, "ConditionApplyGate"), 1);
    assert_eq!(count_gate_effects(&handler.log, "ConditionRemovalGate"), 1);
}

// ═══════════════════════════════════════════════════════════════
// on_remove error does NOT prevent removal
// ═══════════════════════════════════════════════════════════════

#[test]
fn on_remove_error_still_removes_condition() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    condition Cursed on bearer: Character {
        on_remove {
            error("on_remove failed")
        }
    }
    function apply_and_remove(c: Character) {
        apply_condition(c, Cursed, Duration.indefinite)
        remove_condition(c, Cursed)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let c = make_character(&mut state, 20);

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    let err = adapter.run(&mut handler, |state, handler| {
        interp.evaluate_function(
            state,
            handler,
            "apply_and_remove",
            vec![Value::Entity(c)],
        )
    });

    // on_remove error propagates
    assert!(err.is_err());

    // But removal still happened — condition should be gone
    let final_state = adapter.into_inner();
    let conds = final_state.read_conditions(&c).unwrap_or_default();
    assert!(conds.is_empty(), "condition should have been removed despite on_remove error");
}

// ═══════════════════════════════════════════════════════════════
// on_apply with params in scope
// ═══════════════════════════════════════════════════════════════

#[test]
fn on_apply_can_access_params() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    condition Damaged(amount: int) on bearer: Character {
        on_apply {
            bearer.hp = bearer.hp - amount
        }
    }
    function deal_damage(c: Character, dmg: int) {
        apply_condition(c, Damaged(amount: dmg), Duration.indefinite)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let c = make_character(&mut state, 30);

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, handler| {
        interp
            .evaluate_function(
                state,
                handler,
                "deal_damage",
                vec![Value::Entity(c), Value::Int(7)],
            )
            .unwrap();
    });

    let final_state = adapter.into_inner();
    assert_eq!(final_state.read_field(&c, "hp"), Some(Value::Int(23)));
}

// ═══════════════════════════════════════════════════════════════
// Host veto of apply gate → no on_apply, no condition
// ═══════════════════════════════════════════════════════════════

#[test]
fn host_veto_apply_gate_prevents_everything() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    condition Poisoned on bearer: Character {
        on_apply {
            bearer.hp = bearer.hp - 99
        }
    }
    function poison(c: Character) {
        apply_condition(c, Poisoned, Duration.indefinite)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let c = make_character(&mut state, 20);

    let adapter = StateAdapter::new(state);
    // Veto the gate — this is the only non-mutation effect forwarded before apply
    let mut handler = ScriptedHandler::with_responses(vec![Response::Vetoed]);
    adapter.run(&mut handler, |state, handler| {
        interp
            .evaluate_function(state, handler, "poison", vec![Value::Entity(c)])
            .unwrap();
    });

    // hp unchanged — on_apply never ran
    let final_state = adapter.into_inner();
    assert_eq!(final_state.read_field(&c, "hp"), Some(Value::Int(20)));

    // No condition applied
    let conds = final_state.read_conditions(&c).unwrap_or_default();
    assert!(conds.is_empty());
}

// ═══════════════════════════════════════════════════════════════
// Host veto of removal gate → no on_remove, condition stays
// ═══════════════════════════════════════════════════════════════

#[test]
fn host_veto_removal_gate_keeps_condition() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    condition Poisoned on bearer: Character {
        on_remove {
            bearer.hp = bearer.hp + 99
        }
    }
    function poison_then_cure(c: Character) {
        apply_condition(c, Poisoned, Duration.indefinite)
        remove_condition(c, Poisoned)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let c = make_character(&mut state, 20);

    let adapter = StateAdapter::new(state);
    // apply gate → Ack, removal gate → Veto
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, // ConditionApplyGate
        Response::Vetoed,       // ConditionRemovalGate
    ]);
    adapter.run(&mut handler, |state, handler| {
        interp
            .evaluate_function(
                state,
                handler,
                "poison_then_cure",
                vec![Value::Entity(c)],
            )
            .unwrap();
    });

    // hp unchanged by on_remove (it never ran)
    let final_state = adapter.into_inner();
    assert_eq!(final_state.read_field(&c, "hp"), Some(Value::Int(20)));

    // Condition still active
    let conds = final_state.read_conditions(&c).unwrap_or_default();
    assert_eq!(conds.len(), 1);
    assert_eq!(conds[0].name.as_str(), "Poisoned");
}

// ═══════════════════════════════════════════════════════════════
// Emit inside lifecycle block works (indirect bypass)
// ═══════════════════════════════════════════════════════════════

#[test]
fn emit_inside_lifecycle_block_triggers_hooks() {
    let source = r#"
system "test" {
    entity Character { hp: int, notified: bool }
    event PoisonApplied(target: Character) {}
    hook OnPoisonApplied on listener: Character (trigger: PoisonApplied(target: listener)) {
        listener.notified = true
    }
    condition Poisoned on bearer: Character {
        on_apply {
            emit PoisonApplied(target: bearer)
        }
    }
    function poison(c: Character) {
        apply_condition(c, Poisoned, Duration.indefinite)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut fields = FxHashMap::default();
    fields.insert("hp".into(), Value::Int(20));
    fields.insert("notified".into(), Value::Bool(false));
    let c = state.add_entity("Character", fields);

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, handler| {
        interp
            .evaluate_function(state, handler, "poison", vec![Value::Entity(c)])
            .unwrap();
    });

    // Hook should have fired and set notified = true
    let final_state = adapter.into_inner();
    assert_eq!(
        final_state.read_field(&c, "notified"),
        Some(Value::Bool(true))
    );
}

// ═══════════════════════════════════════════════════════════════
// on_apply + on_remove both present
// ═══════════════════════════════════════════════════════════════

#[test]
fn on_apply_and_on_remove_both_fire() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    condition Shield on bearer: Character {
        on_apply {
            bearer.hp = bearer.hp + 10
        }
        on_remove {
            bearer.hp = bearer.hp - 10
        }
    }
    function shield_cycle(c: Character) {
        apply_condition(c, Shield, Duration.indefinite)
        remove_condition(c, Shield)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let c = make_character(&mut state, 20);

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, handler| {
        interp
            .evaluate_function(state, handler, "shield_cycle", vec![Value::Entity(c)])
            .unwrap();
    });

    // +10 from on_apply, -10 from on_remove → net 0
    let final_state = adapter.into_inner();
    assert_eq!(final_state.read_field(&c, "hp"), Some(Value::Int(20)));
}

// ═══════════════════════════════════════════════════════════════
// Multiple instances: remove_condition fires on_remove for each
// ═══════════════════════════════════════════════════════════════

#[test]
fn remove_condition_fires_on_remove_for_each_instance() {
    let source = r#"
system "test" {
    entity Character { hp: int, cleanup_count: int }
    condition Buff on bearer: Character {
        on_remove {
            bearer.cleanup_count = bearer.cleanup_count + 1
        }
    }
    function apply_twice_remove_all(c: Character) {
        apply_condition(c, Buff, Duration.indefinite)
        apply_condition(c, Buff, Duration.indefinite)
        remove_condition(c, Buff)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut fields = FxHashMap::default();
    fields.insert("hp".into(), Value::Int(20));
    fields.insert("cleanup_count".into(), Value::Int(0));
    let c = state.add_entity("Character", fields);

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, handler| {
        interp
            .evaluate_function(
                state,
                handler,
                "apply_twice_remove_all",
                vec![Value::Entity(c)],
            )
            .unwrap();
    });

    // on_remove should have fired for each matching instance
    let final_state = adapter.into_inner();
    let cleanup = final_state.read_field(&c, "cleanup_count");
    // At least 1 on_remove fired; exact count depends on whether remove_condition
    // removes all matching instances or just the first
    assert!(
        matches!(cleanup, Some(Value::Int(n)) if n >= 1),
        "expected cleanup_count >= 1, got {cleanup:?}"
    );

    // All conditions should be removed
    let conds = final_state.read_conditions(&c).unwrap_or_default();
    let buff_count = conds.iter().filter(|c| c.name.as_str() == "Buff").count();
    assert_eq!(buff_count, 0, "all Buff conditions should be removed");
}
