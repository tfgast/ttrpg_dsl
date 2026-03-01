//! Integration tests for the `emit` statement.
//!
//! Tests the full pipeline (parse → lower → check → interpret) for `emit`,
//! verifying that matching hooks are auto-executed inline.

use std::collections::{BTreeMap, HashMap, VecDeque};

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

fn standard_turn_budget() -> BTreeMap<ttrpg_ast::Name, Value> {
    let mut b = BTreeMap::new();
    b.insert("actions".into(), Value::Int(1));
    b.insert("bonus_actions".into(), Value::Int(1));
    b.insert("reactions".into(), Value::Int(1));
    b.insert("free_object_interactions".into(), Value::Int(1));
    b
}

// ── Tests: emit fires matching hooks ────────────────────────────

#[test]
fn emit_fires_matching_hook() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    event Damaged(target: Character, amount: int) {}
    hook OnDamage on c: Character (trigger: Damaged(target: c)) {
        c.HP -= trigger.amount
    }
    action DealDamage on actor: Character (target: Character, amount: int) {
        resolve {
            emit Damaged(target: target, amount: amount)
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut actor_fields = HashMap::new();
    actor_fields.insert("HP".into(), Value::Int(50));
    let actor = state.add_entity("Character", actor_fields);

    let mut target_fields = HashMap::new();
    target_fields.insert("HP".into(), Value::Int(30));
    let target = state.add_entity("Character", target_fields);

    state.set_turn_budget(&actor, standard_turn_budget());

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "DealDamage",
                actor,
                vec![Value::Entity(target), Value::Int(10)],
            )
            .unwrap();
    });

    let state = adapter.into_inner();
    // Hook should have reduced target HP by 10
    assert_eq!(
        state.read_field(&target, "HP"),
        Some(Value::Int(20)),
        "emit should have fired OnDamage hook, reducing HP from 30 to 20"
    );
    // Actor HP should be unchanged
    assert_eq!(state.read_field(&actor, "HP"), Some(Value::Int(50)));
}

#[test]
fn emit_fires_multiple_hooks() {
    let source = r#"
system "test" {
    entity Character { HP: int, log_count: int }
    event Damaged(target: Character, amount: int) {}
    hook First on c: Character (trigger: Damaged(target: c)) {
        c.HP -= trigger.amount
    }
    hook Second on c: Character (trigger: Damaged(target: c)) {
        c.log_count += 1
    }
    action DealDamage on actor: Character (target: Character, amount: int) {
        resolve {
            emit Damaged(target: target, amount: amount)
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut actor_fields = HashMap::new();
    actor_fields.insert("HP".into(), Value::Int(50));
    actor_fields.insert("log_count".into(), Value::Int(0));
    let actor = state.add_entity("Character", actor_fields);

    let mut target_fields = HashMap::new();
    target_fields.insert("HP".into(), Value::Int(30));
    target_fields.insert("log_count".into(), Value::Int(0));
    let target = state.add_entity("Character", target_fields);

    state.set_turn_budget(&actor, standard_turn_budget());

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "DealDamage",
                actor,
                vec![Value::Entity(target), Value::Int(5)],
            )
            .unwrap();
    });

    let state = adapter.into_inner();
    assert_eq!(state.read_field(&target, "HP"), Some(Value::Int(25)));
    assert_eq!(state.read_field(&target, "log_count"), Some(Value::Int(1)));
}

#[test]
fn emit_with_no_matching_hooks_succeeds() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    event Damaged(target: Character, amount: int) {}
    action DealDamage on actor: Character (target: Character) {
        resolve {
            target.HP -= 5
            emit Damaged(target: target, amount: 5)
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut actor_fields = HashMap::new();
    actor_fields.insert("HP".into(), Value::Int(50));
    let actor = state.add_entity("Character", actor_fields);

    let mut target_fields = HashMap::new();
    target_fields.insert("HP".into(), Value::Int(30));
    let target = state.add_entity("Character", target_fields);

    state.set_turn_budget(&actor, standard_turn_budget());

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "DealDamage",
                actor,
                vec![Value::Entity(target)],
            )
            .unwrap();
    });

    let state = adapter.into_inner();
    // Just the direct -= 5, no hook side effects
    assert_eq!(state.read_field(&target, "HP"), Some(Value::Int(25)));
}

#[test]
fn emit_with_default_params() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    event Damaged(target: Character, amount: int = 1) {}
    hook OnDamage on c: Character (trigger: Damaged(target: c)) {
        c.HP -= trigger.amount
    }
    action Poke on actor: Character (target: Character) {
        resolve {
            emit Damaged(target: target)
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut actor_fields = HashMap::new();
    actor_fields.insert("HP".into(), Value::Int(50));
    let actor = state.add_entity("Character", actor_fields);

    let mut target_fields = HashMap::new();
    target_fields.insert("HP".into(), Value::Int(10));
    let target = state.add_entity("Character", target_fields);

    state.set_turn_budget(&actor, standard_turn_budget());

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "Poke",
                actor,
                vec![Value::Entity(target)],
            )
            .unwrap();
    });

    let state = adapter.into_inner();
    // Default amount=1, so HP goes from 10 to 9
    assert_eq!(state.read_field(&target, "HP"), Some(Value::Int(9)));
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
            .any(|e| e.contains("only allowed in action, reaction, or hook")),
        "expected context error, got: {:?}",
        errors
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
        "expected undefined event error, got: {:?}",
        errors
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
        errors.iter().any(|e| e.contains("missing required argument")),
        "expected missing param error, got: {:?}",
        errors
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
        errors.iter().any(|e| e.contains("type") && e.contains("amount")),
        "expected type mismatch error, got: {:?}",
        errors
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
        "expected unknown param error, got: {:?}",
        errors
    );
}

// ── Tests: emit in hooks and reactions ──────────────────────────

#[test]
fn emit_in_hook_fires_cascade() {
    // Hook A emits event B, which fires hook B — a two-level cascade.
    let source = r#"
system "test" {
    entity Character { HP: int, shield: int }

    event Damaged(target: Character, amount: int) {}
    event ShieldBroken(target: Character) {}

    hook OnDamage on c: Character (trigger: Damaged(target: c)) {
        c.HP -= trigger.amount
        if c.shield > 0 {
            c.shield -= 1
            if c.shield == 0 {
                emit ShieldBroken(target: c)
            }
        }
    }

    hook OnShieldBroken on c: Character (trigger: ShieldBroken(target: c)) {
        c.HP -= 5
    }

    action DealDamage on actor: Character (target: Character, amount: int) {
        resolve {
            emit Damaged(target: target, amount: amount)
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut actor_fields = HashMap::new();
    actor_fields.insert("HP".into(), Value::Int(50));
    actor_fields.insert("shield".into(), Value::Int(0));
    let actor = state.add_entity("Character", actor_fields);

    let mut target_fields = HashMap::new();
    target_fields.insert("HP".into(), Value::Int(30));
    target_fields.insert("shield".into(), Value::Int(1));
    let target = state.add_entity("Character", target_fields);

    state.set_turn_budget(&actor, standard_turn_budget());

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "DealDamage",
                actor,
                vec![Value::Entity(target), Value::Int(3)],
            )
            .unwrap();
    });

    let state = adapter.into_inner();
    // OnDamage: HP 30 - 3 = 27, shield 1 - 1 = 0 → emits ShieldBroken
    // OnShieldBroken: HP 27 - 5 = 22
    assert_eq!(
        state.read_field(&target, "HP"),
        Some(Value::Int(22)),
        "cascading emit should fire ShieldBroken hook after shield reaches 0"
    );
    assert_eq!(state.read_field(&target, "shield"), Some(Value::Int(0)));
}

#[test]
fn emit_in_reaction_works() {
    // A reaction's resolve block emits an event that fires a hook.
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
            0
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

    let mut actor_fields = HashMap::new();
    actor_fields.insert("HP".into(), Value::Int(50));
    actor_fields.insert("parry_count".into(), Value::Int(0));
    let actor = state.add_entity("Character", actor_fields);

    let mut target_fields = HashMap::new();
    target_fields.insert("HP".into(), Value::Int(30));
    target_fields.insert("parry_count".into(), Value::Int(0));
    let target = state.add_entity("Character", target_fields);

    state.set_turn_budget(&target, standard_turn_budget());

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    adapter.run(&mut handler, |state, eff_handler| {
        // Construct event payload for the reaction trigger
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
    // The reaction emitted ParryUsed, which fired OnParry hook
    assert_eq!(
        state.read_field(&target, "parry_count"),
        Some(Value::Int(1)),
        "emit inside reaction should fire the OnParry hook"
    );
}

#[test]
fn emit_cascade_depth_limit() {
    // Circular emit: EventA fires hook that emits EventB,
    // EventB fires hook that emits EventA → should hit depth limit.
    let source = r#"
system "test" {
    entity Character { count: int }

    event Ping(target: Character) {}
    event Pong(target: Character) {}

    hook OnPing on c: Character (trigger: Ping(target: c)) {
        c.count += 1
        emit Pong(target: c)
    }

    hook OnPong on c: Character (trigger: Pong(target: c)) {
        c.count += 1
        emit Ping(target: c)
    }

    action StartPingPong on actor: Character (target: Character) {
        resolve {
            emit Ping(target: target)
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let mut actor_fields = HashMap::new();
    actor_fields.insert("count".into(), Value::Int(0));
    let actor = state.add_entity("Character", actor_fields);

    let mut target_fields = HashMap::new();
    target_fields.insert("count".into(), Value::Int(0));
    let target = state.add_entity("Character", target_fields);

    state.set_turn_budget(&actor, standard_turn_budget());

    let adapter = StateAdapter::new(state);
    let mut handler = ScriptedHandler::new();
    let result = adapter.run(&mut handler, |state, eff_handler| {
        interp.execute_action(
            state,
            eff_handler,
            "StartPingPong",
            actor,
            vec![Value::Entity(target)],
        )
    });

    assert!(result.is_err(), "circular emit should produce a runtime error");
    let err_msg = format!("{}", result.unwrap_err());
    assert!(
        err_msg.contains("depth limit"),
        "error should mention depth limit, got: {}",
        err_msg
    );
}
