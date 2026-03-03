//! Integration tests for `with_budget` statement.
//!
//! Covers: OSRIC pattern (receiver=payer), summoning pattern (receiver≠payer),
//! budget exhaustion, nested budgets, turn readability, and cleanup on error.

use std::collections::{BTreeMap, VecDeque};

use rustc_hash::FxHashMap;
use ttrpg_ast::diagnostic::Severity;
use ttrpg_ast::{FileId, Name};
use ttrpg_interp::adapter::StateAdapter;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::{EntityRef, StateProvider};
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

// ── Setup ──────────────────────────────────────────────────────

fn compile(source: &str) -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
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

// ── Scripted handler ───────────────────────────────────────────

struct ScriptedHandler {
    script: VecDeque<Response>,
    log: Vec<Effect>,
}

impl ScriptedHandler {
    fn ack_all() -> Self {
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

// ── Entity helpers ─────────────────────────────────────────────

fn make_character(state: &mut GameState, hp: i64) -> EntityRef {
    let mut fields = FxHashMap::default();
    fields.insert(Name::from("hp"), Value::Int(hp));
    state.add_entity("Character", fields)
}

// ── OSRIC pattern: receiver = payer ────────────────────────────

#[test]
fn osric_pattern_with_budget_provisions_and_clears() {
    // A function uses with_budget to provision a budget, call an action, then clean up.
    let source = r#"
system "test" {
    struct TurnBudget { attack: int }

    entity Character { hp: int }

    action MeleeAttack on attacker: Character (target: Character) {
        cost { attack }
        resolve {
            target.hp -= 1
        }
    }

    function resolve_attack(attacker: Character, target: Character) {
        with_budget(attacker, { attack: 1 }) {
            attacker.MeleeAttack(target)
        }
    }
}
"#;
    let (program, result) = compile(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut gs = GameState::new();
    let attacker = make_character(&mut gs, 10);
    let target = make_character(&mut gs, 10);

    let adapter = StateAdapter::new(gs);
    let mut handler = ScriptedHandler::ack_all();
    adapter
        .run(&mut handler, |state, h| {
            interp.evaluate_function(
                state,
                h,
                "resolve_attack",
                vec![Value::Entity(attacker), Value::Entity(target)],
            )
        })
        .unwrap();

    // DeductCost should target the attacker (who is both receiver and payer)
    let has_deduct = handler
        .log
        .iter()
        .any(|e| matches!(e, Effect::DeductCost { actor, .. } if *actor == attacker));
    assert!(has_deduct, "expected DeductCost for attacker");

    // Target should have been damaged: hp 10 → 9
    let gs = adapter.into_inner();
    assert_eq!(gs.read_field(&target, "hp"), Some(Value::Int(9)));

    // Budget should be cleared after with_budget exits
    assert!(gs.read_turn_budget(&attacker).is_none());
}

// ── Budget exhaustion: second action fails ─────────────────────

#[test]
fn budget_exhaustion_second_action_fails() {
    // with_budget(actor, { attack: 1 }) → first MeleeAttack succeeds,
    // second MeleeAttack fails due to budget enforcement.
    let source = r#"
system "test" {
    struct TurnBudget { attack: int }

    entity Character { hp: int }

    action MeleeAttack on attacker: Character (target: Character) {
        cost { attack }
        resolve {
            target.hp -= 1
        }
    }

    function resolve_two_attacks(attacker: Character, target: Character) {
        with_budget(attacker, { attack: 1 }) {
            attacker.MeleeAttack(target)
            attacker.MeleeAttack(target)
        }
    }
}
"#;
    let (program, result) = compile(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut gs = GameState::new();
    let attacker = make_character(&mut gs, 10);
    let target = make_character(&mut gs, 10);

    let adapter = StateAdapter::new(gs);
    let mut handler = ScriptedHandler::ack_all();
    adapter
        .run(&mut handler, |state, h| {
            interp.evaluate_function(
                state,
                h,
                "resolve_two_attacks",
                vec![Value::Entity(attacker), Value::Entity(target)],
            )
        })
        .unwrap();

    // First attack succeeds (budget 1→0), second fails (budget 0, enforcement fires)
    let gs = adapter.into_inner();
    // Only one damage dealt (hp 10 → 9, not 8)
    assert_eq!(
        gs.read_field(&target, "hp"),
        Some(Value::Int(9)),
        "only one attack should succeed"
    );

    // Verify enforcement fired: should see a RequiresCheck with passed=false
    let budget_checks: Vec<_> = handler
        .log
        .iter()
        .filter(|e| {
            matches!(
                e,
                Effect::RequiresCheck {
                    passed: false,
                    reason: Some(msg),
                    ..
                } if msg.contains("insufficient budget")
            )
        })
        .collect();
    assert_eq!(
        budget_checks.len(),
        1,
        "expected exactly one budget enforcement RequiresCheck"
    );
}

// ── Summoning pattern: receiver ≠ payer ────────────────────────

#[test]
fn summoning_pattern_cost_charged_to_payer_not_receiver() {
    // wizard's budget is charged even though skeleton performs the action
    let source = r#"
system "test" {
    struct TurnBudget { attack: int }

    entity Character { hp: int }

    action MeleeAttack on attacker: Character (target: Character) {
        cost { attack }
        resolve {
            target.hp -= 1
        }
    }

    function command_minion(wizard: Character, skeleton: Character, target: Character) {
        with_budget(wizard, { attack: 1 }) {
            skeleton.MeleeAttack(target)
        }
    }
}
"#;
    let (program, result) = compile(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut gs = GameState::new();
    let wizard = make_character(&mut gs, 10);
    let skeleton = make_character(&mut gs, 5);
    let target = make_character(&mut gs, 10);

    let adapter = StateAdapter::new(gs);
    let mut handler = ScriptedHandler::ack_all();
    adapter
        .run(&mut handler, |state, h| {
            interp.evaluate_function(
                state,
                h,
                "command_minion",
                vec![
                    Value::Entity(wizard),
                    Value::Entity(skeleton),
                    Value::Entity(target),
                ],
            )
        })
        .unwrap();

    // DeductCost should target the wizard (payer), not the skeleton (receiver)
    let deduct_cost = handler
        .log
        .iter()
        .find(|e| matches!(e, Effect::DeductCost { .. }));
    assert!(deduct_cost.is_some(), "expected DeductCost effect");
    if let Some(Effect::DeductCost { actor, .. }) = deduct_cost {
        assert_eq!(
            *actor, wizard,
            "cost should be charged to wizard, not skeleton"
        );
    }

    // Target should be damaged
    let gs = adapter.into_inner();
    assert_eq!(gs.read_field(&target, "hp"), Some(Value::Int(9)));
}

// ── Nested with_budget for different entities ──────────────────

#[test]
fn nested_with_budget_different_entities() {
    // Outer budget for entity A, inner budget for entity B.
    // Each attacks independently. Both budgets cleaned up.
    let source = r#"
system "test" {
    struct TurnBudget { attack: int }

    entity Character { hp: int }

    action MeleeAttack on attacker: Character (target: Character) {
        cost { attack }
        resolve {
            target.hp -= 1
        }
    }

    function resolve_pair(a: Character, b: Character, target: Character) {
        with_budget(a, { attack: 1 }) {
            a.MeleeAttack(target)
            with_budget(b, { attack: 1 }) {
                b.MeleeAttack(target)
            }
        }
    }
}
"#;
    let (program, result) = compile(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut gs = GameState::new();
    let a = make_character(&mut gs, 10);
    let b = make_character(&mut gs, 10);
    let target = make_character(&mut gs, 10);

    let adapter = StateAdapter::new(gs);
    let mut handler = ScriptedHandler::ack_all();
    adapter
        .run(&mut handler, |state, h| {
            interp.evaluate_function(
                state,
                h,
                "resolve_pair",
                vec![Value::Entity(a), Value::Entity(b), Value::Entity(target)],
            )
        })
        .unwrap();

    // Both attacks should land: target hp 10 → 8
    let gs = adapter.into_inner();
    assert_eq!(
        gs.read_field(&target, "hp"),
        Some(Value::Int(8)),
        "both attacks should deal 1 damage each"
    );

    // Both budgets should be cleared
    assert!(
        gs.read_turn_budget(&a).is_none(),
        "A's budget should be cleared"
    );
    assert!(
        gs.read_turn_budget(&b).is_none(),
        "B's budget should be cleared"
    );
}

// ── Turn readability ───────────────────────────────────────────

#[test]
fn turn_readable_reflects_budget() {
    // Read turn.attack inside with_budget and write to entity field to verify value.
    let source = r#"
system "test" {
    struct TurnBudget { attack: int }

    entity Character { hp: int }

    function read_budget(actor: Character) {
        with_budget(actor, { attack: 3 }) {
            actor.hp = turn.attack
        }
    }
}
"#;
    let (program, result) = compile(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut gs = GameState::new();
    let actor = make_character(&mut gs, 10);

    let adapter = StateAdapter::new(gs);
    let mut handler = ScriptedHandler::ack_all();
    adapter
        .run(&mut handler, |state, h| {
            interp.evaluate_function(state, h, "read_budget", vec![Value::Entity(actor)])
        })
        .unwrap();

    let gs = adapter.into_inner();
    assert_eq!(
        gs.read_field(&actor, "hp"),
        Some(Value::Int(3)),
        "turn.attack should reflect provisioned budget value"
    );
}

#[test]
fn turn_readable_after_deduction() {
    // After an action deducts from budget, turn reads should reflect the decremented value.
    // We store turn.attack into attacker.hp to observe it.
    let source = r#"
system "test" {
    struct TurnBudget { attack: int }

    entity Character { hp: int }

    action MeleeAttack on attacker: Character (target: Character) {
        cost { attack }
        resolve {
            target.hp -= 1
        }
    }

    function attack_and_read(attacker: Character, target: Character) {
        with_budget(attacker, { attack: 2 }) {
            attacker.MeleeAttack(target)
            attacker.hp = turn.attack
        }
    }
}
"#;
    let (program, result) = compile(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut gs = GameState::new();
    let attacker = make_character(&mut gs, 10);
    let target = make_character(&mut gs, 10);

    let adapter = StateAdapter::new(gs);
    let mut handler = ScriptedHandler::ack_all();
    adapter
        .run(&mut handler, |state, h| {
            interp.evaluate_function(
                state,
                h,
                "attack_and_read",
                vec![Value::Entity(attacker), Value::Entity(target)],
            )
        })
        .unwrap();

    let gs = adapter.into_inner();
    // Budget was 2, one attack deducted 1, so turn.attack was 1
    assert_eq!(
        gs.read_field(&attacker, "hp"),
        Some(Value::Int(1)),
        "turn.attack should be 1 after one deduction from budget of 2"
    );
}

// ── Cleanup on error ───────────────────────────────────────────

#[test]
fn cleanup_on_error_budget_cleared() {
    // If the body errors, budget should still be cleaned up.
    let source = r#"
system "test" {
    struct TurnBudget { attack: int }

    entity Character { hp: int }

    function will_error(actor: Character) {
        with_budget(actor, { attack: 1 }) {
            error("intentional error")
        }
    }
}
"#;
    let (program, result) = compile(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut gs = GameState::new();
    let actor = make_character(&mut gs, 10);

    let adapter = StateAdapter::new(gs);
    let mut handler = ScriptedHandler::ack_all();
    let err = adapter
        .run(&mut handler, |state, h| {
            interp.evaluate_function(state, h, "will_error", vec![Value::Entity(actor)])
        })
        .unwrap_err();

    assert!(
        err.message.contains("intentional error"),
        "expected body error to propagate, got: {}",
        err.message
    );

    // Budget should be cleared despite the error (adapter intercepts ClearBudget)
    let gs = adapter.into_inner();
    assert!(
        gs.read_turn_budget(&actor).is_none(),
        "budget should be cleared after error"
    );
}

// ── Host-approved overdraft via budget enforcement ─────────────

#[test]
fn budget_enforcement_host_override_allows_overdraft() {
    // Budget has attack: 0, but host overrides RequiresCheck to allow overdraft.
    let source = r#"
system "test" {
    struct TurnBudget { attack: int }

    entity Character { hp: int }

    action MeleeAttack on attacker: Character (target: Character) {
        cost { attack }
        resolve {
            target.hp -= 1
        }
    }

    function overdraft_attack(attacker: Character, target: Character) {
        with_budget(attacker, { attack: 0 }) {
            attacker.MeleeAttack(target)
        }
    }
}
"#;
    let (program, result) = compile(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut gs = GameState::new();
    let attacker = make_character(&mut gs, 10);
    let target = make_character(&mut gs, 10);

    let adapter = StateAdapter::new(gs);

    // Adapter intercepts ProvisionBudget, MutateField, ClearBudget (not forwarded).
    // Handler sees: ActionStarted, RequiresCheck(budget), DeductCost, ActionCompleted
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged,               // ActionStarted
        Response::Override(Value::Bool(true)), // RequiresCheck — allow overdraft
    ]);
    adapter
        .run(&mut handler, |state, h| {
            interp.evaluate_function(
                state,
                h,
                "overdraft_attack",
                vec![Value::Entity(attacker), Value::Entity(target)],
            )
        })
        .unwrap();

    // Action should succeed despite zero budget
    let gs = adapter.into_inner();
    assert_eq!(
        gs.read_field(&target, "hp"),
        Some(Value::Int(9)),
        "overdraft should allow the attack"
    );
}

// ── Same-entity nested: inner restores outer budget ────────────

#[test]
fn same_entity_nested_restores_outer_budget() {
    // with_budget(a, { attack: 2 }) → attack → with_budget(a, { attack: 99 }) →
    // inner exits → outer budget restored → second attack succeeds.
    // We store turn.attack into attacker.hp to observe the final budget state.
    let source = r#"
system "test" {
    struct TurnBudget { attack: int }

    entity Character { hp: int }

    action MeleeAttack on attacker: Character (target: Character) {
        cost { attack }
        resolve {
            target.hp -= 1
        }
    }

    function nested_same_entity(attacker: Character, target: Character) {
        with_budget(attacker, { attack: 2 }) {
            attacker.MeleeAttack(target)
            // After first attack, budget should be { attack: 1 }

            with_budget(attacker, { attack: 99 }) {
                // Inner budget is completely new: { attack: 99 }
                let inner_budget = turn.attack
            }

            // Outer budget restored to { attack: 1 }
            attacker.MeleeAttack(target)
            // After second attack, budget should be { attack: 0 }
            attacker.hp = turn.attack
        }
    }
}
"#;
    let (program, result) = compile(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut gs = GameState::new();
    let attacker = make_character(&mut gs, 10);
    let target = make_character(&mut gs, 10);

    let adapter = StateAdapter::new(gs);
    let mut handler = ScriptedHandler::ack_all();
    adapter
        .run(&mut handler, |state, h| {
            interp.evaluate_function(
                state,
                h,
                "nested_same_entity",
                vec![Value::Entity(attacker), Value::Entity(target)],
            )
        })
        .unwrap();

    let gs = adapter.into_inner();
    // Two attacks landed: target hp 10 → 8
    assert_eq!(
        gs.read_field(&target, "hp"),
        Some(Value::Int(8)),
        "both outer attacks should succeed"
    );

    // attacker.hp was set to turn.attack after second deduction: 2 - 1 - 1 = 0
    assert_eq!(
        gs.read_field(&attacker, "hp"),
        Some(Value::Int(0)),
        "turn.attack should be 0 after two deductions from budget of 2"
    );
}

// ── No budget: backward compatible, no enforcement ─────────────

#[test]
fn no_budget_no_enforcement() {
    // Host-managed turn: action has cost but no with_budget provisioning.
    // This is backward compatible — no enforcement.
    let source = r#"
system "test" {
    entity Character { hp: int }

    action MeleeAttack on attacker: Character (target: Character) {
        cost { action }
        resolve {
            target.hp -= 1
        }
    }
}
"#;
    let (program, result) = compile(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut gs = GameState::new();
    let attacker = make_character(&mut gs, 10);
    let target = make_character(&mut gs, 10);

    // Set up a turn budget on the host side (simulating host-managed turn)
    let mut budget = BTreeMap::new();
    budget.insert(Name::from("actions"), Value::Int(1));
    gs.set_turn_budget(&attacker, budget);

    let adapter = StateAdapter::new(gs);
    let mut handler = ScriptedHandler::ack_all();
    adapter
        .run(&mut handler, |state, h| {
            interp.execute_action(
                state,
                h,
                "MeleeAttack",
                attacker,
                vec![Value::Entity(target)],
            )
        })
        .unwrap();

    // Action should succeed — no budget enforcement RequiresCheck
    let gs = adapter.into_inner();
    assert_eq!(gs.read_field(&target, "hp"), Some(Value::Int(9)));

    // No budget-related RequiresCheck should have been emitted
    let budget_checks: Vec<_> = handler
        .log
        .iter()
        .filter(|e| {
            matches!(
                e,
                Effect::RequiresCheck {
                    reason: Some(msg),
                    ..
                } if msg.contains("insufficient budget")
            )
        })
        .collect();
    assert!(
        budget_checks.is_empty(),
        "no budget enforcement should fire without with_budget"
    );
}
