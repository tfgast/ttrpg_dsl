//! Integration tests for the `emit` statement.
//!
//! Script-suitable runtime coverage has moved to `tests/emit.ttrpg-cli`.
//! These Rust tests keep checker-only validation plus the reaction-trigger path
//! that still requires direct interpreter/event-payload control.

use std::collections::{BTreeMap, VecDeque};

use rustc_hash::FxHashMap;
use ttrpg_ast::FileId;
use ttrpg_ast::diagnostic::Severity;
use ttrpg_interp::Interpreter;
use ttrpg_interp::adapter::StateAdapter;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::StateProvider;
use ttrpg_interp::value::Value;

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

fn standard_turn_budget() -> BTreeMap<ttrpg_ast::Name, Value> {
    let mut b = BTreeMap::new();
    b.insert("actions".into(), Value::Int(1));
    b.insert("bonus_actions".into(), Value::Int(1));
    b.insert("reactions".into(), Value::Int(1));
    b.insert("free_object_interactions".into(), Value::Int(1));
    b
}

// ── Tests: checker errors ───────────────────────────────────────

#[test]
fn emit_outside_action_is_error() {
    let errors = setup_expect_errors(
        r#"
system "test" {
    entity Character { HP: int }
    event Damaged(target: Character) {}
    derive foo(c: Character) -> int {
        emit Damaged(target: c)
        0
    }
}
"#,
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("only allowed in action, reaction, hook,")),
        "expected context error, got: {errors:?}"
    );
}

#[test]
fn emit_undefined_event_is_error() {
    let errors = setup_expect_errors(
        r#"
system "test" {
    entity Character { HP: int }
    action Foo on actor: Character () {
        resolve {
            emit Nonexistent(x: 1)
        }
    }
}
"#,
    );
    assert!(
        errors.iter().any(|e| e.contains("undefined event")),
        "expected undefined event error, got: {errors:?}"
    );
}

#[test]
fn emit_missing_required_param_is_error() {
    let errors = setup_expect_errors(
        r#"
system "test" {
    entity Character { HP: int }
    event Damaged(target: Character, amount: int) {}
    action Foo on actor: Character () {
        resolve {
            emit Damaged(target: actor)
        }
    }
}
"#,
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("missing required argument")),
        "expected missing param error, got: {errors:?}"
    );
}

#[test]
fn emit_type_mismatch_is_error() {
    let errors = setup_expect_errors(
        r#"
system "test" {
    entity Character { HP: int }
    event Damaged(target: Character, amount: int) {}
    action Foo on actor: Character () {
        resolve {
            emit Damaged(target: actor, amount: "not_an_int")
        }
    }
}
"#,
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("type") && e.contains("amount")),
        "expected type mismatch error, got: {errors:?}"
    );
}

#[test]
fn emit_unknown_param_is_error() {
    let errors = setup_expect_errors(
        r#"
system "test" {
    entity Character { HP: int }
    event Damaged(target: Character) {}
    action Foo on actor: Character () {
        resolve {
            emit Damaged(target: actor, bogus: 1)
        }
    }
}
"#,
    );
    assert!(
        errors.iter().any(|e| e.contains("no parameter `bogus`")),
        "expected unknown param error, got: {errors:?}"
    );
}

// ── Tests: emit in reactions ───────────────────────────────────

#[test]
fn emit_in_reaction_works() {
    let source = r#"
system "test" {
    entity Character { HP: int, parry_count: int }

    event Attacked(target: Character, attacker: Character) {}
    event ParryUsed(by: Character) {}

    hook OnParry on c: Character (trigger: ParryUsed(by: c)) {
        c.parry_count += 1
    }

    reaction Parry on defender: Character (trigger: Attacked(target: defender)) {
        resolve {
            emit ParryUsed(by: defender)
        }
    }

    action Attack on attacker: Character (target: Character) {
        resolve {
            emit Attacked(target: target, attacker: attacker)
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut actor_fields = FxHashMap::default();
    actor_fields.insert("HP".into(), Value::Int(50));
    actor_fields.insert("parry_count".into(), Value::Int(0));
    let actor = state.add_entity("Character", actor_fields);

    let mut target_fields = FxHashMap::default();
    target_fields.insert("HP".into(), Value::Int(30));
    target_fields.insert("parry_count".into(), Value::Int(0));
    let target = state.add_entity("Character", target_fields);

    state.set_turn_budget(&target, standard_turn_budget());

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, eff_handler| {
        let payload = Value::Struct {
            name: "__event_Attacked".into(),
            fields: {
                let mut f = BTreeMap::new();
                f.insert("target".into(), Value::Entity(target));
                f.insert("attacker".into(), Value::Entity(actor));
                f
            },
        };
        interp
            .execute_reaction(state, eff_handler, "Parry", target, payload)
            .unwrap();
    });

    let state = adapter.into_inner();
    assert_eq!(
        state.read_field(&target, "parry_count"),
        Some(Value::Int(1)),
        "emit inside reaction should fire the OnParry hook"
    );
}
