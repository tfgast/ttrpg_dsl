//! Integration tests for `with_budgets` (multi-entity budget provisioning).

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

// ── Basic multi-entity provisioning ─────────────────────────────

#[test]
fn with_budgets_provisions_multiple_entities() {
    let source = r#"
system "test" {
    struct TurnBudget { action: int }

    entity Character { hp: int }

    action MeleeAttack on attacker: Character (target: Character) {
        cost { action }
        resolve {
            target.hp -= 1
        }
    }

    function round(a: Character, b: Character, target: Character) {
        with_budgets([
            BudgetSpec { actor: a, budget: TurnBudget { action: 2 } },
            BudgetSpec { actor: b, budget: TurnBudget { action: 1 } },
        ]) {
            a.MeleeAttack(target)
            b.MeleeAttack(target)
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
                "round",
                vec![Value::Entity(a), Value::Entity(b), Value::Entity(target)],
            )
        })
        .unwrap();

    let gs = adapter.into_inner();
    assert_eq!(
        gs.read_field(&target, "hp"),
        Some(Value::Int(8)),
        "both attacks should have landed"
    );

    // Budgets should be cleared after scope exit
    assert!(
        gs.read_turn_budget(&a).is_none(),
        "budget for a should be cleared"
    );
    assert!(
        gs.read_turn_budget(&b).is_none(),
        "budget for b should be cleared"
    );
}

// ── Cleanup on error ────────────────────────────────────────────

#[test]
fn with_budgets_cleanup_on_error() {
    let source = r#"
system "test" {
    struct TurnBudget { action: int }
    entity Character { hp: int }

    function will_error(a: Character, b: Character) {
        with_budgets([
            BudgetSpec { actor: a, budget: TurnBudget { action: 1 } },
            BudgetSpec { actor: b, budget: TurnBudget { action: 1 } },
        ]) {
            error("intentional error")
        }
    }
}
"#;
    let (program, result) = compile(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut gs = GameState::new();
    let a = make_character(&mut gs, 10);
    let b = make_character(&mut gs, 10);

    let adapter = StateAdapter::new(gs);
    let mut handler = ScriptedHandler::ack_all();
    let err = adapter
        .run(&mut handler, |state, h| {
            interp.evaluate_function(
                state,
                h,
                "will_error",
                vec![Value::Entity(a), Value::Entity(b)],
            )
        })
        .unwrap_err();

    assert!(err.message.contains("intentional error"));

    let gs = adapter.into_inner();
    assert!(
        gs.read_turn_budget(&a).is_none(),
        "budget for a should be cleared after error"
    );
    assert!(
        gs.read_turn_budget(&b).is_none(),
        "budget for b should be cleared after error"
    );
}
