//! Tests that action parameter defaults are evaluated AFTER ActionStarted/veto,
//! not before. (Regression test for tdsl-3ot)

use std::collections::{HashMap, VecDeque};

use ttrpg_ast::FileId;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

const PROGRAM_SOURCE: &str = r#"
system "ActionDefaultTest" {
    entity Character {
        HP: int
    }

    // Action with a default that references a field (pure but exercises default eval)
    action Heal on actor: Character (target: Character, amount: int = actor.HP) {
        resolve {
            target.HP += amount
        }
    }
}
"#;

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

fn setup() -> (ttrpg_ast::ast::Program, ttrpg_checker::env::TypeEnv) {
    let (program, parse_errors) = ttrpg_parser::parse(PROGRAM_SOURCE, FileId::SYNTH);
    assert!(parse_errors.is_empty(), "parse errors: {:?}", parse_errors);
    let mut lower_diags = Vec::new();
    let program = ttrpg_parser::lower_moves(program, &mut lower_diags);
    assert!(lower_diags.is_empty(), "lower errors: {:?}", lower_diags);
    let result = ttrpg_checker::check(&program);
    let errors: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.severity == ttrpg_ast::diagnostic::Severity::Error)
        .collect();
    assert!(errors.is_empty(), "check errors: {:?}", errors);
    (program, result.env)
}

fn make_entity(gs: &mut GameState, hp: i64) -> ttrpg_interp::state::EntityRef {
    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(hp));
    gs.add_entity("Character", fields)
}

#[test]
fn action_default_not_evaluated_on_veto() {
    let (program, type_env) = setup();
    let interp = Interpreter::new(&program, &type_env).unwrap();

    let mut gs = GameState::new();
    let actor = make_entity(&mut gs, 100);
    let target = make_entity(&mut gs, 5);

    // Veto the ActionStarted, then Ack the ActionCompleted
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Vetoed,       // ActionStarted → vetoed
        Response::Acknowledged, // ActionCompleted
    ]);

    // Call Heal without providing amount (should use default = actor.HP)
    // But since action is vetoed, default should never be evaluated
    let result = interp
        .execute_action(&gs, &mut handler, "Heal", actor, vec![Value::Entity(target)])
        .unwrap();

    assert_eq!(result, Value::None, "vetoed action should return None");

    // The effect log should only have ActionStarted and ActionCompleted
    // No MutateField effects should appear (no side effects from defaults or resolve)
    let effect_names: Vec<&str> = handler
        .log
        .iter()
        .map(|e| match e {
            Effect::ActionStarted { .. } => "ActionStarted",
            Effect::ActionCompleted { .. } => "ActionCompleted",
            Effect::MutateField { .. } => "MutateField",
            _ => "other",
        })
        .collect();

    assert_eq!(
        effect_names,
        vec!["ActionStarted", "ActionCompleted"],
        "vetoed action should only produce ActionStarted + ActionCompleted, got: {:?}",
        effect_names
    );
}

#[test]
fn action_default_evaluated_after_acknowledgement() {
    let (program, type_env) = setup();
    let interp = Interpreter::new(&program, &type_env).unwrap();

    let mut gs = GameState::new();
    let actor = make_entity(&mut gs, 100);
    let target = make_entity(&mut gs, 5);

    let mut handler = ScriptedHandler::new(); // all acknowledged

    let result = interp
        .execute_action(&gs, &mut handler, "Heal", actor, vec![Value::Entity(target)])
        .unwrap();

    // Default amount = actor.HP = 100. target.HP = 5 + 100 = 105
    assert_eq!(result, Value::None);

    // Verify ActionStarted appears before MutateField
    let mut saw_action_started = false;
    let mut saw_mutate = false;
    for effect in &handler.log {
        match effect {
            Effect::ActionStarted { .. } => {
                assert!(!saw_mutate, "ActionStarted should come before MutateField");
                saw_action_started = true;
            }
            Effect::MutateField { .. } => {
                assert!(saw_action_started, "MutateField should come after ActionStarted");
                saw_mutate = true;
            }
            _ => {}
        }
    }
    assert!(saw_action_started, "should have seen ActionStarted");
    assert!(saw_mutate, "should have seen MutateField");
}
