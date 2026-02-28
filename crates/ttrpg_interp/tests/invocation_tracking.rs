//! Integration tests for invocation tracking.
//!
//! Tests the full pipeline (parse → lower → check → interpret) for
//! invocation tracking, covering: concentration-like scenarios, cross-entity
//! revocation, nested invocations, ID continuity, failure outcomes,
//! and revoke(none) no-ops.

use std::collections::{BTreeMap, HashMap, VecDeque};

use ttrpg_ast::diagnostic::Severity;
use ttrpg_ast::FileId;
use ttrpg_interp::adapter::StateAdapter;
use ttrpg_interp::effect::{ActionOutcome, Effect, EffectHandler, EffectKind, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::{EntityRef, InvocationId, StateProvider};
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

fn standard_turn_budget() -> BTreeMap<ttrpg_ast::Name, Value> {
    let mut b = BTreeMap::new();
    b.insert("actions".into(), Value::Int(1));
    b.insert("bonus_actions".into(), Value::Int(1));
    b.insert("reactions".into(), Value::Int(1));
    b.insert("free_object_interactions".into(), Value::Int(1));
    b
}

// ── Helpers ────────────────────────────────────────────────────

/// Extract ActionCompleted effects from a handler log.
fn action_completed_effects(log: &[Effect]) -> Vec<(&str, ActionOutcome, Option<InvocationId>)> {
    log.iter()
        .filter_map(|e| match e {
            Effect::ActionCompleted {
                name,
                outcome,
                invocation,
                ..
            } => Some((name.as_str(), *outcome, *invocation)),
            _ => None,
        })
        .collect()
}

/// Extract ApplyCondition effects from a handler log.
fn apply_condition_effects(log: &[Effect]) -> Vec<(&str, EntityRef, Option<InvocationId>)> {
    log.iter()
        .filter_map(|e| match e {
            Effect::ApplyCondition {
                condition,
                target,
                invocation,
                ..
            } => Some((condition.as_str(), *target, *invocation)),
            _ => None,
        })
        .collect()
}

/// Extract RevokeInvocation effects from a handler log.
fn revoke_invocation_effects(log: &[Effect]) -> Vec<InvocationId> {
    log.iter()
        .filter_map(|e| match e {
            Effect::RevokeInvocation { invocation } => Some(*invocation),
            _ => None,
        })
        .collect()
}

// ── Tests ──────────────────────────────────────────────────────

#[test]
fn action_completed_carries_invocation_id() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    action Strike on actor: Character (target: Character) {
        resolve {
            target.HP -= 1
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(50));
    let actor = state.add_entity("Character", fields.clone());
    let target = state.add_entity("Character", fields);
    state.set_turn_budget(&actor, standard_turn_budget());

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "Strike",
                actor,
                vec![Value::Entity(target)],
            )
            .unwrap();
    });

    let completions = action_completed_effects(&handler.log);
    assert_eq!(completions.len(), 1);
    assert_eq!(completions[0].0, "Strike");
    assert_eq!(completions[0].1, ActionOutcome::Succeeded);
    assert_eq!(completions[0].2, Some(InvocationId(1)));
}

#[test]
fn apply_condition_tagged_with_current_invocation() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Blessed on bearer: Character {}
    action CastBless on caster: Character (target: Character) {
        resolve {
            apply_condition(target, Blessed, Duration.indefinite)
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(50));
    let caster = state.add_entity("Character", fields.clone());
    let target = state.add_entity("Character", fields);
    state.set_turn_budget(&caster, standard_turn_budget());

    let adapter = StateAdapter::new(state).pass_through(EffectKind::ApplyCondition);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "CastBless",
                caster,
                vec![Value::Entity(target)],
            )
            .unwrap();
    });

    let conditions = apply_condition_effects(&handler.log);
    assert_eq!(conditions.len(), 1);
    assert_eq!(conditions[0].0, "Blessed");
    assert_eq!(conditions[0].1, target);
    assert_eq!(
        conditions[0].2,
        Some(InvocationId(1)),
        "condition should be tagged with the action's invocation ID"
    );
}

#[test]
fn revoke_removes_conditions_across_entities() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Blessed on bearer: Character {}
    action CastBless on caster: Character (t1: Character, t2: Character) {
        resolve {
            apply_condition(t1, Blessed, Duration.indefinite)
            apply_condition(t2, Blessed, Duration.indefinite)
        }
    }
    action RevokeSpell on caster: Character (inv: Invocation) {
        resolve {
            revoke(inv)
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(50));
    let caster = state.add_entity("Character", fields.clone());
    let t1 = state.add_entity("Character", fields.clone());
    let t2 = state.add_entity("Character", fields);
    state.set_turn_budget(&caster, standard_turn_budget());

    // CastBless on t1 and t2
    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "CastBless",
                caster,
                vec![Value::Entity(t1), Value::Entity(t2)],
            )
            .unwrap();
    });

    let bless_inv = action_completed_effects(&handler.log)[0]
        .2
        .expect("CastBless should have invocation");

    let mut state = adapter.into_inner();
    // Both targets should have Blessed
    assert_eq!(state.read_conditions(&t1).unwrap().len(), 1);
    assert_eq!(state.read_conditions(&t2).unwrap().len(), 1);

    // Now revoke that invocation
    state.set_turn_budget(&caster, standard_turn_budget());
    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "RevokeSpell",
                caster,
                vec![Value::Invocation(bless_inv)],
            )
            .unwrap();
    });

    let state = adapter.into_inner();
    // Both targets' Blessed conditions should be removed
    assert_eq!(
        state.read_conditions(&t1).unwrap().len(),
        0,
        "Blessed on t1 should be revoked"
    );
    assert_eq!(
        state.read_conditions(&t2).unwrap().len(),
        0,
        "Blessed on t2 should be revoked"
    );
}

#[test]
fn concentration_scenario_cast_then_recast_revokes_first() {
    // Full concentration scenario: CastBless → store invocation → CastHex → hook
    // revokes first → verify only second spell's conditions remain.
    let source = r#"
system "test" {
    entity Character {
        HP: int,
        concentrating_on: option<Invocation>
    }
    tag #concentration
    condition Blessed on bearer: Character {}
    condition Hexed on bearer: Character {}
    event ConcentrationStarted(caster: Character, inv: Invocation) {}

    action CastBless on caster: Character (target: Character) #concentration {
        resolve {
            let inv = invocation()
            apply_condition(target, Blessed, Duration.indefinite)
            emit ConcentrationStarted(caster: caster, inv: inv)
        }
    }

    action CastHex on caster: Character (target: Character) #concentration {
        resolve {
            let inv = invocation()
            apply_condition(target, Hexed, Duration.indefinite)
            emit ConcentrationStarted(caster: caster, inv: inv)
        }
    }

    hook OnConcentration on caster: Character (
        trigger: ConcentrationStarted(caster: caster)
    ) {
        revoke(caster.concentrating_on)
        caster.concentrating_on = some(trigger.inv)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut caster_fields = HashMap::new();
    caster_fields.insert("HP".into(), Value::Int(50));
    caster_fields.insert("concentrating_on".into(), Value::Option(None));
    let caster = state.add_entity("Character", caster_fields);

    let mut target_fields = HashMap::new();
    target_fields.insert("HP".into(), Value::Int(30));
    let target = state.add_entity("Character", target_fields);

    state.set_turn_budget(&caster, standard_turn_budget());

    // Step 1: CastBless
    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "CastBless",
                caster,
                vec![Value::Entity(target)],
            )
            .unwrap();
    });

    let mut state = adapter.into_inner();

    // After CastBless: target has Blessed, caster.concentrating_on is set
    let target_conds = state.read_conditions(&target).unwrap();
    assert_eq!(target_conds.len(), 1);
    assert_eq!(target_conds[0].name, "Blessed");

    let conc_field = state.read_field(&caster, "concentrating_on").unwrap();
    assert!(
        matches!(&conc_field, Value::Option(Some(inner)) if matches!(inner.as_ref(), Value::Invocation(_))),
        "concentrating_on should be some(Invocation), got {:?}",
        conc_field
    );

    // Step 2: CastHex (should revoke Bless via hook)
    state.set_turn_budget(&caster, standard_turn_budget());
    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "CastHex",
                caster,
                vec![Value::Entity(target)],
            )
            .unwrap();
    });

    let state = adapter.into_inner();

    // After CastHex: target should only have Hexed (Blessed revoked by hook)
    let target_conds = state.read_conditions(&target).unwrap();
    assert_eq!(
        target_conds.len(),
        1,
        "expected 1 condition (Hexed only), got {}: {:?}",
        target_conds.len(),
        target_conds.iter().map(|c| &c.name).collect::<Vec<_>>()
    );
    assert_eq!(target_conds[0].name, "Hexed");

    // caster.concentrating_on should now hold the Hex invocation
    let conc_field = state.read_field(&caster, "concentrating_on").unwrap();
    assert!(
        matches!(&conc_field, Value::Option(Some(inner)) if matches!(inner.as_ref(), Value::Invocation(_))),
        "concentrating_on should be some(Invocation) after CastHex"
    );
}

#[test]
fn action_without_invocation_call_still_tags_conditions() {
    // An action that uses apply_condition but never calls invocation()
    // should still tag the condition with the automatically-allocated ID.
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Poisoned on bearer: Character {}
    action Poison on actor: Character (target: Character) {
        resolve {
            apply_condition(target, Poisoned, Duration.indefinite)
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(50));
    let actor = state.add_entity("Character", fields.clone());
    let target = state.add_entity("Character", fields);
    state.set_turn_budget(&actor, standard_turn_budget());

    let mut handler = ScriptedHandler::new();
    let adapter = StateAdapter::new(state).pass_through(EffectKind::ApplyCondition);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "Poison",
                actor,
                vec![Value::Entity(target)],
            )
            .unwrap();
    });

    // The ApplyCondition effect should still carry the invocation ID
    let conditions = apply_condition_effects(&handler.log);
    assert_eq!(conditions.len(), 1);
    assert_eq!(conditions[0].0, "Poisoned");
    assert!(
        conditions[0].2.is_some(),
        "condition should be tagged with invocation even without explicit invocation() call"
    );

    // And ActionCompleted should carry the same ID
    let completions = action_completed_effects(&handler.log);
    assert_eq!(completions[0].2, conditions[0].2);
}

#[test]
fn nested_invocations_hook_gets_own_id() {
    // When an action emits an event that fires a hook, the hook should
    // get its own unique invocation ID distinct from the action's.
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Blessed on bearer: Character {}
    condition HookApplied on bearer: Character {}
    event SpellCast(caster: Character) {}

    action CastBless on caster: Character (target: Character) {
        resolve {
            apply_condition(target, Blessed, Duration.indefinite)
            emit SpellCast(caster: caster)
        }
    }

    hook OnSpellCast on c: Character (trigger: SpellCast(caster: c)) {
        apply_condition(c, HookApplied, Duration.indefinite)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(50));
    let caster = state.add_entity("Character", fields.clone());
    let target = state.add_entity("Character", fields);
    state.set_turn_budget(&caster, standard_turn_budget());

    let mut handler = ScriptedHandler::new();
    let adapter = StateAdapter::new(state).pass_through(EffectKind::ApplyCondition);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "CastBless",
                caster,
                vec![Value::Entity(target)],
            )
            .unwrap();
    });

    // Should have two ActionCompleted effects: one for CastBless, one for OnSpellCast hook
    let completions = action_completed_effects(&handler.log);
    assert_eq!(
        completions.len(),
        2,
        "expected 2 ActionCompleted (action + hook), got {:?}",
        completions
    );

    let action_inv = completions
        .iter()
        .find(|c| c.0 == "CastBless")
        .expect("CastBless completion")
        .2;
    let hook_inv = completions
        .iter()
        .find(|c| c.0 == "OnSpellCast")
        .expect("OnSpellCast completion")
        .2;

    assert!(action_inv.is_some());
    assert!(hook_inv.is_some());
    assert_ne!(
        action_inv, hook_inv,
        "hook should have a distinct invocation ID from the action"
    );

    // The conditions should be tagged with their respective invocations
    let conditions = apply_condition_effects(&handler.log);
    let blessed = conditions.iter().find(|c| c.0 == "Blessed").unwrap();
    let hook_applied = conditions.iter().find(|c| c.0 == "HookApplied").unwrap();
    assert_eq!(blessed.2, action_inv);
    assert_eq!(hook_applied.2, hook_inv);
}

#[test]
fn revoke_stored_invocation_from_previous_action() {
    // Store an invocation in an entity field, then revoke it in a later action.
    let source = r#"
system "test" {
    entity Character {
        HP: int,
        last_spell: option<Invocation>
    }
    condition Blessed on bearer: Character {}

    action CastBless on caster: Character (target: Character) {
        resolve {
            let inv = invocation()
            apply_condition(target, Blessed, Duration.indefinite)
            caster.last_spell = some(inv)
        }
    }

    action DropSpell on caster: Character () {
        resolve {
            revoke(caster.last_spell)
            caster.last_spell = none
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut caster_fields = HashMap::new();
    caster_fields.insert("HP".into(), Value::Int(50));
    caster_fields.insert("last_spell".into(), Value::Option(None));
    let caster = state.add_entity("Character", caster_fields);

    let mut target_fields = HashMap::new();
    target_fields.insert("HP".into(), Value::Int(30));
    let target = state.add_entity("Character", target_fields);

    state.set_turn_budget(&caster, standard_turn_budget());

    // CastBless
    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "CastBless",
                caster,
                vec![Value::Entity(target)],
            )
            .unwrap();
    });

    let mut state = adapter.into_inner();
    assert_eq!(state.read_conditions(&target).unwrap().len(), 1);

    // DropSpell (separate action, separate interpreter invocation cycle)
    state.set_turn_budget(&caster, standard_turn_budget());
    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "DropSpell",
                caster,
                vec![],
            )
            .unwrap();
    });

    let state = adapter.into_inner();
    // Blessed should be removed
    assert_eq!(
        state.read_conditions(&target).unwrap().len(),
        0,
        "Blessed should be revoked by DropSpell"
    );
    // last_spell should be none
    assert_eq!(
        state.read_field(&caster, "last_spell"),
        Some(Value::None)
    );
}

#[test]
fn revoke_none_is_noop() {
    // revoke(none) should not emit RevokeInvocation and should not error.
    let source = r#"
system "test" {
    entity Character {
        HP: int,
        concentrating_on: option<Invocation>
    }
    action TryRevoke on actor: Character () {
        resolve {
            revoke(actor.concentrating_on)
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(50));
    fields.insert("concentrating_on".into(), Value::Option(None));
    let actor = state.add_entity("Character", fields);
    state.set_turn_budget(&actor, standard_turn_budget());

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(state, eff_handler, "TryRevoke", actor, vec![])
            .unwrap();
    });

    // No RevokeInvocation should be emitted
    let revokes = revoke_invocation_effects(&handler.log);
    assert!(
        revokes.is_empty(),
        "revoke(none) should not emit RevokeInvocation, got {:?}",
        revokes
    );

    // Action should still complete successfully
    let completions = action_completed_effects(&handler.log);
    assert_eq!(completions.len(), 1);
    assert_eq!(completions[0].1, ActionOutcome::Succeeded);
}

#[test]
fn invocation_id_continuity_across_interpreter_invocations() {
    // Using new_with_invocation_start to seed the counter simulates
    // persistence across CLI commands.
    let source = r#"
system "test" {
    entity Character { HP: int }
    action Strike on actor: Character () {
        resolve { 1 }
    }
}
"#;
    let (program, result) = setup(source);

    // First interpreter: starts at 1 (default)
    let interp1 = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(50));
    let actor = state.add_entity("Character", fields);
    state.set_turn_budget(&actor, standard_turn_budget());

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, eff_handler| {
        interp1
            .execute_action(state, eff_handler, "Strike", actor, vec![])
            .unwrap();
    });

    let completions = action_completed_effects(&handler.log);
    assert_eq!(completions[0].2, Some(InvocationId(1)));

    // Capture the counter after first interpreter
    let next_id = interp1.next_invocation_id();
    assert!(next_id > 1);

    // Second interpreter: seeded with the previous counter
    let interp2 =
        Interpreter::new_with_invocation_start(&program, &result.env, next_id).unwrap();
    let mut state = adapter.into_inner();
    state.set_turn_budget(&actor, standard_turn_budget());

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, eff_handler| {
        interp2
            .execute_action(state, eff_handler, "Strike", actor, vec![])
            .unwrap();
    });

    let completions = action_completed_effects(&handler.log);
    let second_inv = completions[0].2.unwrap();
    // The second interpreter's ID should continue from the first
    assert_eq!(second_inv.0, next_id, "second action should use seeded ID");
    assert!(second_inv.0 > 1, "seeded ID should be > 1");
}

#[test]
fn vetoed_action_has_no_invocation_id() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    action Strike on actor: Character () {
        resolve { 1 }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(50));
    let actor = state.add_entity("Character", fields);
    state.set_turn_budget(&actor, standard_turn_budget());

    // Host vetoes the action at ActionStarted
    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Vetoed, // veto ActionStarted
    ]);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(state, eff_handler, "Strike", actor, vec![])
            .unwrap();
    });

    let completions = action_completed_effects(&handler.log);
    assert_eq!(completions.len(), 1);
    assert_eq!(completions[0].1, ActionOutcome::Vetoed);
    assert_eq!(
        completions[0].2, None,
        "vetoed action should have no invocation ID"
    );
}

#[test]
fn failed_action_still_emits_action_completed() {
    // An action that fails at runtime should still emit ActionCompleted
    // with a Failed outcome and the allocated invocation ID.
    let source = r#"
system "test" {
    entity Character { HP: int }
    entity Monster { HP: int }
    action Strike on actor: Character (target: Monster) {
        requires { actor.HP > 100 }
        resolve { 1 }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut char_fields = HashMap::new();
    char_fields.insert("HP".into(), Value::Int(10)); // fails requires
    let actor = state.add_entity("Character", char_fields);

    let mut monster_fields = HashMap::new();
    monster_fields.insert("HP".into(), Value::Int(20));
    let target = state.add_entity("Monster", monster_fields);

    state.set_turn_budget(&actor, standard_turn_budget());

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "Strike",
                actor,
                vec![Value::Entity(target)],
            )
            .unwrap();
    });

    // Should have ActionCompleted with the requires-failure outcome
    let completions = action_completed_effects(&handler.log);
    assert_eq!(completions.len(), 1);
    assert_eq!(completions[0].0, "Strike");
    // RequiresCheck failure → ActionCompleted is still emitted
    // The invocation ID should be present (allocated before body execution)
    assert!(
        completions[0].2.is_some(),
        "even failed actions should have an invocation ID"
    );
}

#[test]
fn multiple_actions_get_distinct_invocation_ids() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    action Strike on actor: Character () {
        resolve { 1 }
    }
    action Dodge on actor: Character () {
        resolve { 2 }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(50));
    let actor = state.add_entity("Character", fields);
    state.set_turn_budget(&actor, standard_turn_budget());

    // Execute Strike
    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(state, eff_handler, "Strike", actor, vec![])
            .unwrap();
    });

    let mut state = adapter.into_inner();
    let strike_inv = action_completed_effects(&handler.log)[0].2.unwrap();

    // Execute Dodge
    state.set_turn_budget(&actor, standard_turn_budget());
    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(state, eff_handler, "Dodge", actor, vec![])
            .unwrap();
    });

    let dodge_inv = action_completed_effects(&handler.log)[0].2.unwrap();
    assert_ne!(
        strike_inv, dodge_inv,
        "each action should get a unique invocation ID"
    );
    assert_eq!(strike_inv, InvocationId(1));
    assert_eq!(dodge_inv, InvocationId(2));
}

#[test]
fn revoke_only_removes_matching_invocation() {
    // Conditions from different invocations: revoking one should preserve the other.
    let source = r#"
system "test" {
    entity Character {
        HP: int,
        spell_a: option<Invocation>,
        spell_b: option<Invocation>
    }
    condition Blessed on bearer: Character {}
    condition Shielded on bearer: Character {}

    action CastBless on caster: Character (target: Character) {
        resolve {
            let inv = invocation()
            apply_condition(target, Blessed, Duration.indefinite)
            caster.spell_a = some(inv)
        }
    }

    action CastShield on caster: Character (target: Character) {
        resolve {
            let inv = invocation()
            apply_condition(target, Shielded, Duration.indefinite)
            caster.spell_b = some(inv)
        }
    }

    action RevokeA on caster: Character () {
        resolve {
            revoke(caster.spell_a)
            caster.spell_a = none
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut caster_fields = HashMap::new();
    caster_fields.insert("HP".into(), Value::Int(50));
    caster_fields.insert("spell_a".into(), Value::Option(None));
    caster_fields.insert("spell_b".into(), Value::Option(None));
    let caster = state.add_entity("Character", caster_fields);

    let mut target_fields = HashMap::new();
    target_fields.insert("HP".into(), Value::Int(30));
    let target = state.add_entity("Character", target_fields);

    // Cast both spells
    state.set_turn_budget(&caster, standard_turn_budget());
    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "CastBless",
                caster,
                vec![Value::Entity(target)],
            )
            .unwrap();
    });
    let mut state = adapter.into_inner();

    state.set_turn_budget(&caster, standard_turn_budget());
    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "CastShield",
                caster,
                vec![Value::Entity(target)],
            )
            .unwrap();
    });
    let mut state = adapter.into_inner();

    // Target should have both conditions
    assert_eq!(state.read_conditions(&target).unwrap().len(), 2);

    // Revoke only spell_a (Blessed)
    state.set_turn_budget(&caster, standard_turn_budget());
    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(state, eff_handler, "RevokeA", caster, vec![])
            .unwrap();
    });

    let state = adapter.into_inner();
    let remaining = state.read_conditions(&target).unwrap();
    assert_eq!(remaining.len(), 1, "only Shielded should remain");
    assert_eq!(remaining[0].name, "Shielded");
}

#[test]
fn invocation_value_stored_and_read_back() {
    // An action stores invocation() in a field; a later mechanic reads it back.
    let source = r#"
system "test" {
    entity Character {
        HP: int,
        last_inv: option<Invocation>
    }

    action Store on actor: Character () {
        resolve {
            actor.last_inv = some(invocation())
        }
    }

    derive read_inv(c: Character) -> option<Invocation> {
        c.last_inv
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(50));
    fields.insert("last_inv".into(), Value::Option(None));
    let actor = state.add_entity("Character", fields);
    state.set_turn_budget(&actor, standard_turn_budget());

    // Store
    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(state, eff_handler, "Store", actor, vec![])
            .unwrap();
    });

    let state = adapter.into_inner();

    // Read back via derive
    let val = interp
        .evaluate_derive(&state, &mut ScriptedHandler::new(), "read_inv", vec![Value::Entity(actor)])
        .unwrap();

    assert!(
        matches!(&val, Value::Option(Some(inner)) if matches!(inner.as_ref(), Value::Invocation(InvocationId(1)))),
        "should read back the stored invocation, got {:?}",
        val
    );
}

#[test]
fn hook_invocation_is_independent_from_outer_action() {
    // The hook's invocation ID should be its own, not inherited from the action.
    // Revoking the hook's invocation should only remove the hook's conditions.
    let source = r#"
system "test" {
    entity Character {
        HP: int,
        hook_inv: option<Invocation>
    }
    condition ActionBuff on bearer: Character {}
    condition HookBuff on bearer: Character {}
    event BuffCast(target: Character) {}

    action CastBuff on caster: Character (target: Character) {
        resolve {
            apply_condition(target, ActionBuff, Duration.indefinite)
            emit BuffCast(target: target)
        }
    }

    hook OnBuffCast on c: Character (trigger: BuffCast(target: c)) {
        apply_condition(c, HookBuff, Duration.indefinite)
        c.hook_inv = some(invocation())
    }

    action RevokeHookBuff on actor: Character (target: Character) {
        resolve {
            revoke(target.hook_inv)
            target.hook_inv = none
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut caster_fields = HashMap::new();
    caster_fields.insert("HP".into(), Value::Int(50));
    caster_fields.insert("hook_inv".into(), Value::Option(None));
    let caster = state.add_entity("Character", caster_fields);

    let mut target_fields = HashMap::new();
    target_fields.insert("HP".into(), Value::Int(30));
    target_fields.insert("hook_inv".into(), Value::Option(None));
    let target = state.add_entity("Character", target_fields);

    state.set_turn_budget(&caster, standard_turn_budget());

    // CastBuff → hook fires → target has ActionBuff + HookBuff
    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "CastBuff",
                caster,
                vec![Value::Entity(target)],
            )
            .unwrap();
    });

    let mut state = adapter.into_inner();
    let conds = state.read_conditions(&target).unwrap();
    assert_eq!(conds.len(), 2);

    // Revoke the hook's invocation — only HookBuff should be removed
    state.set_turn_budget(&caster, standard_turn_budget());
    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "RevokeHookBuff",
                caster,
                vec![Value::Entity(target)],
            )
            .unwrap();
    });

    let state = adapter.into_inner();
    let remaining = state.read_conditions(&target).unwrap();
    assert_eq!(
        remaining.len(),
        1,
        "only ActionBuff should remain after revoking hook's invocation"
    );
    assert_eq!(remaining[0].name, "ActionBuff");
}
