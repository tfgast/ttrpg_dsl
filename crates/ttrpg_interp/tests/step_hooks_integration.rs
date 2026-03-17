//! Integration tests for the step-based hook and condition handler entry points.
//!
//! These tests verify that `Execution::start_hook`, `Execution::start_hooks`,
//! `Execution::start_condition_handler`, and `Execution::start_condition_handlers`
//! properly yield effects through the poll/respond protocol.

use std::collections::BTreeMap;
use std::sync::Arc;

use rustc_hash::FxHashMap;
use ttrpg_ast::diagnostic::Severity;
use ttrpg_ast::{FileId, Name, Span};
use ttrpg_interp::adapter::{self, StateAdapter};
use ttrpg_interp::effect::{Effect, EffectKind, Response, Step};
use ttrpg_interp::event;
use ttrpg_interp::execution::Execution;
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::runtime_core::RuntimeCore;
use ttrpg_interp::state::{ConditionArgs, EntityRef, StateProvider};
use ttrpg_interp::value::Value;

// ── Setup ──────────────────────────────────────────────────────

fn setup(
    source: &str,
) -> (
    Arc<ttrpg_ast::ast::Program>,
    Arc<ttrpg_checker::env::TypeEnv>,
) {
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
    (Arc::new(program), Arc::new(result.env))
}

fn make_payload(event_name: &str, fields: Vec<(&str, Value)>) -> Value {
    let mut map = BTreeMap::new();
    for (name, val) in fields {
        map.insert(Name::from(name), val);
    }
    Value::Struct {
        name: format!("__event_{event_name}").into(),
        fields: map,
    }
}

fn add_character(state: &mut GameState, hp: i64) -> EntityRef {
    let mut fields = FxHashMap::default();
    fields.insert(Name::from("HP"), Value::Int(hp));
    state.add_entity("Character", fields)
}

/// Drive an execution to completion, collecting all yielded effects.
/// Responds with Acknowledged to every effect. Mutation effects are
/// applied to state (since MutationYield frames yield them to the host).
fn run_to_completion(exec: &mut Execution<GameState>) -> (Value, Vec<Effect>) {
    let mut effects = Vec::new();
    loop {
        match exec.poll().expect("poll should not error") {
            Step::Yielded(effect) => {
                if adapter::MUTATION_KINDS.contains(&EffectKind::of(&effect)) {
                    exec.state().with_state_mut(|gs| {
                        adapter::apply_mutation(gs, &effect, &FxHashMap::default());
                    });
                }
                effects.push(*effect);
                exec.respond(Response::Acknowledged)
                    .expect("respond should not error");
            }
            Step::Done(val) => return (val, effects),
        }
    }
}

// ── start_hook (single) ────────────────────────────────────────

#[test]
fn start_hook_yields_effects() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    event damage(target: Character) {}
    hook OnDamage on target: Character (trigger: damage(target: target)) {
        target.HP -= 1
    }
}
"#;
    let (program, type_env) = setup(source);
    let core = RuntimeCore::new(program, type_env, 1, 1);
    let mut state = GameState::new();
    add_character(&mut state, 20);
    let adapter = StateAdapter::new(state);

    let payload = make_payload("damage", vec![("target", Value::Entity(EntityRef(1)))]);

    let mut exec = Execution::start_hook(
        core,
        adapter,
        "OnDamage",
        EntityRef(1),
        payload,
        Span::dummy(),
    )
    .expect("start_hook should succeed");

    let (_val, effects) = run_to_completion(&mut exec);

    // Step-based path yields ActionStarted and ActionCompleted as gating effects.
    // Field mutations go directly to WritableState (no MutateField effect).
    assert!(
        effects
            .iter()
            .any(|e| matches!(e, Effect::ActionStarted { .. })),
        "expected ActionStarted effect"
    );
    assert!(
        effects
            .iter()
            .any(|e| matches!(e, Effect::ActionCompleted { .. })),
        "expected ActionCompleted effect"
    );

    // Verify the mutation happened in state
    let state = exec.state();
    assert_eq!(
        state.read_field(&EntityRef(1), "HP"),
        Some(Value::Int(19)),
        "HP should have been decremented by hook body"
    );
}

// ── start_hooks (batch) ────────────────────────────────────────

#[test]
fn start_hooks_batch_fires_all() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    event damage(target: Character) {}
    hook First on target: Character (trigger: damage(target: target)) {
        target.HP -= 1
    }
    hook Second on target: Character (trigger: damage(target: target)) {
        target.HP -= 2
    }
}
"#;
    let (program, type_env) = setup(source);
    let core = RuntimeCore::new(program.clone(), type_env.clone(), 1, 1);
    let mut state = GameState::new();
    add_character(&mut state, 20);

    let payload = make_payload("damage", vec![("target", Value::Entity(EntityRef(1)))]);

    let hook_result = event::find_matching_hooks(
        &program,
        &type_env,
        &state,
        "damage",
        &payload,
        &[EntityRef(1)],
    )
    .expect("find_matching_hooks should succeed");

    assert_eq!(hook_result.hooks.len(), 2, "should find two hooks");

    let adapter = StateAdapter::new(state);
    let mut exec = Execution::start_hooks(core, adapter, hook_result.hooks, payload, Span::dummy());

    let (_val, effects) = run_to_completion(&mut exec);

    // Two hooks → two ActionStarted + two ActionCompleted
    let started_count = effects
        .iter()
        .filter(|e| matches!(e, Effect::ActionStarted { .. }))
        .count();
    assert_eq!(started_count, 2, "expected 2 ActionStarted effects");

    let completed_count = effects
        .iter()
        .filter(|e| matches!(e, Effect::ActionCompleted { .. }))
        .count();
    assert_eq!(completed_count, 2, "expected 2 ActionCompleted effects");

    // Verify the mutations: HP started at 20, First does -1, Second does -2 → 17
    let state = exec.state();
    assert_eq!(
        state.read_field(&EntityRef(1), "HP"),
        Some(Value::Int(17)),
        "HP should have been decremented by both hooks"
    );
}

#[test]
fn start_hooks_empty_completes_immediately() {
    let source = r#"
system "test" {
    entity Character { HP: int }
}
"#;
    let (program, type_env) = setup(source);
    let core = RuntimeCore::new(program, type_env, 1, 1);
    let state = GameState::new();
    let adapter = StateAdapter::new(state);

    let mut exec = Execution::start_hooks(core, adapter, vec![], Value::Void, Span::dummy());

    let (val, effects) = run_to_completion(&mut exec);
    assert_eq!(val, Value::Void);
    assert!(effects.is_empty(), "empty hooks should yield no effects");
}

// ── start_condition_handler (single) ───────────────────────────

#[test]
fn start_condition_handler_yields_set_state() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    event damage(target: Character) {}
    condition Burning on target: Character {
        state { ticks: int = 3 }
        on damage(target: target) {
            state.ticks -= 1
        }
    }
}
"#;
    let (program, type_env) = setup(source);
    let core = RuntimeCore::new(program.clone(), type_env.clone(), 1, 1);
    let mut state = GameState::new();
    add_character(&mut state, 20);

    let mut cond_state = BTreeMap::new();
    cond_state.insert(Name::from("ticks"), Value::Int(3));
    state.apply_condition(
        &EntityRef(1),
        "Burning",
        ConditionArgs {
            state_fields: cond_state,
            ..Default::default()
        },
    );

    let payload = make_payload("damage", vec![("target", Value::Entity(EntityRef(1)))]);

    let cond_result = event::find_matching_condition_handlers(
        &program,
        &type_env,
        &state,
        "damage",
        &payload,
        &[EntityRef(1)],
    )
    .expect("find_matching_condition_handlers should succeed");

    assert_eq!(cond_result.handlers.len(), 1, "should find one handler");

    let handler_info = &cond_result.handlers[0];
    let adapter = StateAdapter::new(state);

    let mut exec =
        Execution::start_condition_handler(core, adapter, handler_info, payload, Span::dummy())
            .expect("start_condition_handler should succeed");

    let (_val, effects) = run_to_completion(&mut exec);

    // SetConditionState is now yielded to the host in poll mode (not auto-applied
    // by StateAdapter). Verify it was yielded with the updated ticks value.
    let set_state = effects
        .iter()
        .find(|e| matches!(e, Effect::SetConditionState { .. }));
    assert!(
        set_state.is_some(),
        "expected SetConditionState to be yielded in poll mode"
    );
    if let Some(Effect::SetConditionState { fields, .. }) = set_state {
        assert_eq!(
            fields.get(&Name::from("ticks")),
            Some(&Value::Int(2)),
            "SetConditionState should carry ticks decremented from 3 to 2"
        );
    }
}

// ── start_condition_handlers (batch) ───────────────────────────

#[test]
fn start_condition_handlers_batch() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    event damage(target: Character) {}
    condition Burning on target: Character {
        state { ticks: int = 3 }
        on damage(target: target) {
            state.ticks -= 1
        }
    }
}
"#;
    let (program, type_env) = setup(source);
    let core = RuntimeCore::new(program.clone(), type_env.clone(), 1, 1);
    let mut state = GameState::new();
    add_character(&mut state, 20);

    let mut cond_state = BTreeMap::new();
    cond_state.insert(Name::from("ticks"), Value::Int(3));
    state.apply_condition(
        &EntityRef(1),
        "Burning",
        ConditionArgs {
            state_fields: cond_state,
            ..Default::default()
        },
    );

    let payload = make_payload("damage", vec![("target", Value::Entity(EntityRef(1)))]);

    let cond_result = event::find_matching_condition_handlers(
        &program,
        &type_env,
        &state,
        "damage",
        &payload,
        &[EntityRef(1)],
    )
    .expect("find_matching_condition_handlers should succeed");

    let adapter = StateAdapter::new(state);
    let mut exec =
        Execution::start_condition_handlers(core, adapter, cond_result.handlers, payload);

    let (_val, effects) = run_to_completion(&mut exec);

    // SetConditionState is now yielded in poll mode. Verify it was yielded.
    let set_state = effects
        .iter()
        .find(|e| matches!(e, Effect::SetConditionState { .. }));
    assert!(
        set_state.is_some(),
        "expected SetConditionState to be yielded in poll mode"
    );
    if let Some(Effect::SetConditionState { fields, .. }) = set_state {
        assert_eq!(
            fields.get(&Name::from("ticks")),
            Some(&Value::Int(2)),
            "SetConditionState should carry ticks decremented from 3 to 2"
        );
    }
}

#[test]
fn start_condition_handlers_empty_completes_immediately() {
    let source = r#"
system "test" {
    entity Character { HP: int }
}
"#;
    let (program, type_env) = setup(source);
    let core = RuntimeCore::new(program, type_env, 1, 1);
    let state = GameState::new();
    let adapter = StateAdapter::new(state);

    let mut exec = Execution::start_condition_handlers(core, adapter, vec![], Value::Void);

    let (val, effects) = run_to_completion(&mut exec);
    assert_eq!(val, Value::Void);
    assert!(effects.is_empty(), "empty handlers should yield no effects");
}

// ── start_hook with veto ───────────────────────────────────────

#[test]
fn start_hook_veto_skips_body() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    event damage(target: Character) {}
    hook OnDamage on target: Character (trigger: damage(target: target)) {
        target.HP -= 1
    }
}
"#;
    let (program, type_env) = setup(source);
    let core = RuntimeCore::new(program, type_env, 1, 1);
    let mut state = GameState::new();
    add_character(&mut state, 20);
    let adapter = StateAdapter::new(state);

    let payload = make_payload("damage", vec![("target", Value::Entity(EntityRef(1)))]);

    let mut exec = Execution::start_hook(
        core,
        adapter,
        "OnDamage",
        EntityRef(1),
        payload,
        Span::dummy(),
    )
    .expect("start_hook should succeed");

    // Drive manually: veto the ActionStarted effect
    let mut effects: Vec<Effect> = Vec::new();
    while let Step::Yielded(effect) = exec.poll().expect("poll ok") {
        let response = if matches!(&*effect, Effect::ActionStarted { .. }) {
            Response::Vetoed
        } else {
            Response::Acknowledged
        };
        effects.push(*effect);
        exec.respond(response).expect("respond ok");
    }

    // Vetoed → HP should remain 20
    let state = exec.state();
    assert_eq!(
        state.read_field(&EntityRef(1), "HP"),
        Some(Value::Int(20)),
        "HP should be unchanged after veto"
    );
}
