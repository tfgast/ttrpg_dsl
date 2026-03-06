//! Integration tests for `with_budget` statement.
//!
//! Script-suitable runtime coverage has moved to `tests/with_budget.ttrpg-cli`.
//! These Rust tests keep only error-path cleanup and host-override behavior
//! that still depends on custom effect-handler responses.

use std::collections::VecDeque;

use rustc_hash::FxHashMap;
use ttrpg_ast::diagnostic::Severity;
use ttrpg_ast::{FileId, Name};
use ttrpg_interp::adapter::StateAdapter;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::{EntityRef, StateProvider};
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

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

fn make_character(state: &mut GameState, hp: i64) -> EntityRef {
    let mut fields = FxHashMap::default();
    fields.insert(Name::from("hp"), Value::Int(hp));
    state.add_entity("Character", fields)
}

// ── Cleanup on error ───────────────────────────────────────────

#[test]
fn cleanup_on_error_budget_cleared() {
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

    let gs = adapter.into_inner();
    assert!(
        gs.read_turn_budget(&actor).is_none(),
        "budget should be cleared after error"
    );
}

// ── Host-approved overdraft via budget enforcement ─────────────

#[test]
fn budget_enforcement_host_override_allows_overdraft() {
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
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged,
        Response::Override(Value::Bool(true)),
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

    let gs = adapter.into_inner();
    assert_eq!(
        gs.read_field(&target, "hp"),
        Some(Value::Int(9)),
        "overdraft should allow the attack"
    );
}
