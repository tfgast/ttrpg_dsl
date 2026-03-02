//! Tests for method-call syntax on actions: entity.Action(args)

use std::collections::{HashMap, VecDeque};

use ttrpg_ast::diagnostic::Severity;
use ttrpg_ast::FileId;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::adapter::StateAdapter;
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::StateProvider;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

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

fn setup_errors(source: &str) -> Vec<String> {
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

fn make_entity(gs: &mut GameState, hp: i64) -> ttrpg_interp::state::EntityRef {
    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(hp));
    gs.add_entity("Character", fields)
}

/// Extract effect names for easy comparison.
fn effect_names(log: &[Effect]) -> Vec<&'static str> {
    log.iter()
        .map(|e| match e {
            Effect::ActionStarted { .. } => "ActionStarted",
            Effect::ActionCompleted { .. } => "ActionCompleted",
            Effect::MutateField { .. } => "MutateField",
            Effect::RequiresCheck { .. } => "RequiresCheck",
            Effect::DeductCost { .. } => "DeductCost",
            _ => "other",
        })
        .collect()
}

// ── Basic method syntax ──────────────────────────────────────────

#[test]
fn action_method_syntax_basic() {
    let source = r#"
system "test" {
    entity Character { HP: int }

    action Heal on healer: Character (target: Character, amount: int) {
        resolve {
            target.HP += amount
        }
    }

    action DoubleHeal on actor: Character (target: Character, amount: int) {
        resolve {
            actor.Heal(target, amount * 2)
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut gs = GameState::new();
    let healer = make_entity(&mut gs, 50);
    let target = make_entity(&mut gs, 10);
    let mut handler = ScriptedHandler::ack_all();

    interp
        .execute_action(
            &gs,
            &mut handler,
            "DoubleHeal",
            healer,
            vec![Value::Entity(target), Value::Int(5)],
        )
        .unwrap();

    // Should see outer ActionStarted, then inner ActionStarted/MutateField/ActionCompleted,
    // then outer ActionCompleted. The MutateField proves the method call dispatched correctly.
    assert!(
        handler
            .log
            .iter()
            .any(|e| matches!(e, Effect::MutateField { .. })),
        "method-call action should produce MutateField effect, got: {:?}",
        effect_names(&handler.log)
    );
}

// ── Equivalence: both forms produce the same effects ─────────────

#[test]
fn action_method_syntax_equivalent_to_function_call() {
    let source_fn = r#"
system "test" {
    entity Character { HP: int }

    action Heal on healer: Character (target: Character, amount: int) {
        resolve {
            target.HP += amount
        }
    }

    action Driver on actor: Character (target: Character) {
        resolve {
            Heal(actor, target, 10)
        }
    }
}
"#;
    let source_method = r#"
system "test" {
    entity Character { HP: int }

    action Heal on healer: Character (target: Character, amount: int) {
        resolve {
            target.HP += amount
        }
    }

    action Driver on actor: Character (target: Character) {
        resolve {
            actor.Heal(target, 10)
        }
    }
}
"#;
    let fn_effects = {
        let (program, result) = setup(source_fn);
        let interp = Interpreter::new(&program, &result.env).unwrap();
        let mut gs = GameState::new();
        let actor = make_entity(&mut gs, 50);
        let target = make_entity(&mut gs, 10);
        let mut handler = ScriptedHandler::ack_all();
        interp
            .execute_action(
                &gs,
                &mut handler,
                "Driver",
                actor,
                vec![Value::Entity(target)],
            )
            .unwrap();
        effect_names(&handler.log)
    };

    let method_effects = {
        let (program, result) = setup(source_method);
        let interp = Interpreter::new(&program, &result.env).unwrap();
        let mut gs = GameState::new();
        let actor = make_entity(&mut gs, 50);
        let target = make_entity(&mut gs, 10);
        let mut handler = ScriptedHandler::ack_all();
        interp
            .execute_action(
                &gs,
                &mut handler,
                "Driver",
                actor,
                vec![Value::Entity(target)],
            )
            .unwrap();
        effect_names(&handler.log)
    };

    assert_eq!(
        fn_effects, method_effects,
        "function-call and method-call forms should produce identical effect sequences"
    );
}

// ── Named arguments ──────────────────────────────────────────────

#[test]
fn action_method_syntax_named_args() {
    let source = r#"
system "test" {
    entity Character { HP: int }

    action Heal on healer: Character (target: Character, amount: int) {
        resolve {
            target.HP += amount
        }
    }

    action Driver on actor: Character (target: Character) {
        resolve {
            actor.Heal(amount: 15, target: target)
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut gs = GameState::new();
    let actor = make_entity(&mut gs, 50);
    let target = make_entity(&mut gs, 10);
    let mut handler = ScriptedHandler::ack_all();

    interp
        .execute_action(
            &gs,
            &mut handler,
            "Driver",
            actor,
            vec![Value::Entity(target)],
        )
        .unwrap();

    // MutateField should be present proving the named args resolved correctly
    assert!(
        handler
            .log
            .iter()
            .any(|e| matches!(e, Effect::MutateField { .. })),
        "named args via method syntax should work, got: {:?}",
        effect_names(&handler.log)
    );
}

// ── Error: action in wrong context ───────────────────────────────

#[test]
fn action_method_syntax_wrong_context() {
    let source = r#"
system "test" {
    entity Character { HP: int }

    action Heal on healer: Character (target: Character, amount: int) {
        resolve {
            target.HP += amount
        }
    }

    derive bad(a: Character, b: Character) -> int {
        a.Heal(b, 10)
        0
    }
}
"#;
    let errors = setup_errors(source);
    assert!(
        errors
            .iter()
            .any(|e| e.contains("action") && e.contains("can only be called")),
        "expected context error, got: {:?}",
        errors
    );
}

// ── Error: receiver type mismatch ────────────────────────────────

#[test]
fn action_method_syntax_wrong_receiver_type() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    entity Monster { HP: int }

    action Heal on healer: Character (target: Character, amount: int) {
        resolve {
            target.HP += amount
        }
    }

    action Driver on m: Monster (target: Character) {
        resolve {
            m.Heal(target, 10)
        }
    }
}
"#;
    let errors = setup_errors(source);
    assert!(
        errors
            .iter()
            .any(|e| e.contains("expects receiver of type")),
        "expected receiver type mismatch error, got: {:?}",
        errors
    );
}

// ── Non-entity method call still works ───────────────────────────

#[test]
fn non_entity_method_call_unaffected() {
    let source = r#"
system "test" {
    derive f(xs: list<int>) -> int {
        xs.len()
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    struct NoopHandler;
    impl EffectHandler for NoopHandler {
        fn handle(&mut self, _: Effect) -> Response {
            Response::Acknowledged
        }
    }
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "f",
            vec![Value::List(vec![
                Value::Int(1),
                Value::Int(2),
                Value::Int(3),
            ])],
        )
        .unwrap();
    assert_eq!(val, Value::Int(3));
}

// ── Action with default parameters ──────────────────────────────

#[test]
fn action_method_syntax_with_defaults() {
    let source = r#"
system "test" {
    entity Character { HP: int }

    action Heal on healer: Character (target: Character, amount: int = 5) {
        resolve {
            target.HP += amount
        }
    }

    action Driver on actor: Character (target: Character) {
        resolve {
            actor.Heal(target)
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut gs = GameState::new();
    let actor = make_entity(&mut gs, 50);
    let target = make_entity(&mut gs, 10);
    let mut handler = ScriptedHandler::ack_all();

    interp
        .execute_action(
            &gs,
            &mut handler,
            "Driver",
            actor,
            vec![Value::Entity(target)],
        )
        .unwrap();

    // Should produce MutateField proving the default param was used
    assert!(
        handler
            .log
            .iter()
            .any(|e| matches!(e, Effect::MutateField { .. })),
        "method call with defaults should produce MutateField, got: {:?}",
        effect_names(&handler.log)
    );
}

// ── Entity field access doesn't break ────────────────────────────

#[test]
fn entity_field_access_still_works() {
    // Make sure entity.field (non-action) still resolves to field access, not action lookup
    let source = r#"
system "test" {
    entity Character { HP: int }

    derive get_hp(c: Character) -> int {
        c.HP
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut gs = GameState::new();
    let c = make_entity(&mut gs, 42);

    struct NoopHandler;
    impl EffectHandler for NoopHandler {
        fn handle(&mut self, _: Effect) -> Response {
            Response::Acknowledged
        }
    }
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(&gs, &mut handler, "get_hp", vec![Value::Entity(c)])
        .unwrap();
    assert_eq!(val, Value::Int(42));
}

// ── Bug fix: method defaults can reference receiver (tdsl-figw) ──

#[test]
fn action_method_default_references_receiver() {
    // Regression: dispatch_action_method called bind_args without the receiver
    // in scope, so default expressions referencing the receiver would fail with
    // an undefined-variable error on method-call syntax (entity.Action()).
    let source = r#"
system "test" {
    entity Character { HP: int }

    action HealSelf on healer: Character (amount: int = healer.HP) {
        resolve {
            healer.HP += amount
        }
    }

    action Wrapper on actor: Character () {
        resolve {
            actor.HealSelf()
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut gs = GameState::new();
    let entity = make_entity(&mut gs, 10);

    // Call via method syntax inside Wrapper — default should resolve healer.HP = 10
    let adapter = StateAdapter::new(gs);
    let mut handler = ScriptedHandler::ack_all();
    adapter
        .run(&mut handler, |state, eff_handler| {
            interp.execute_action(state, eff_handler, "Wrapper", entity, vec![])
        })
        .unwrap();

    // HP should be doubled: 10 + 10 = 20
    let gs = adapter.into_inner();
    let hp = gs.read_field(&entity, "HP").unwrap();
    assert_eq!(
        hp,
        Value::Int(20),
        "method-call default should be able to reference receiver (healer.HP)"
    );
}
