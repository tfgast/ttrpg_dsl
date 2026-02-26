//! OSE exploration orchestration integration tests.
//!
//! Verifies that ose/ose_exploration.ttrpg parses, lowers, type-checks, and
//! evaluates correctly with dependencies.

use std::collections::{BTreeMap, VecDeque};

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_ast::diagnostic::Severity;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::{DiceExpr, RollResult, Value};
use ttrpg_interp::Interpreter;

fn compile_ose_exploration() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    let core_source = include_str!("../../../ose/ose_core.ttrpg");
    let exploration_source = include_str!("../../../ose/ose_exploration.ttrpg");

    let sources = vec![
        ("ose/ose_core.ttrpg".to_string(), core_source.to_string()),
        (
            "ose/ose_exploration.ttrpg".to_string(),
            exploration_source.to_string(),
        ),
    ];

    let parse_result = ttrpg_parser::parse_multi(&sources);
    let parse_errors: Vec<_> = parse_result
        .diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .collect();
    assert!(
        parse_errors.is_empty(),
        "parse/lower errors: {:?}",
        parse_errors.iter().map(|d| &d.message).collect::<Vec<_>>()
    );

    let (program, module_map) = parse_result.ok().unwrap();
    let result = ttrpg_checker::check_with_modules(program, module_map);
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

    (program.clone(), result)
}

struct NullHandler;
impl EffectHandler for NullHandler {
    fn handle(&mut self, _effect: Effect) -> Response {
        Response::Acknowledged
    }
}

struct ScriptedHandler {
    script: VecDeque<Response>,
}

impl ScriptedHandler {
    fn with_responses(responses: Vec<Response>) -> Self {
        ScriptedHandler {
            script: responses.into(),
        }
    }
}

impl EffectHandler for ScriptedHandler {
    fn handle(&mut self, _effect: Effect) -> Response {
        self.script.pop_front().unwrap_or(Response::Acknowledged)
    }
}

fn action_val(name: &str) -> Value {
    Value::EnumVariant {
        enum_name: "ExplorationAction".into(),
        variant: name.into(),
        fields: BTreeMap::new(),
    }
}

fn scripted_roll(count: u32, sides: u32, die: i64) -> Response {
    Response::Rolled(RollResult {
        expr: DiceExpr {
            count,
            sides,
            filter: None,
            modifier: 0,
        },
        dice: vec![die],
        kept: vec![die],
        modifier: 0,
        total: die,
        unmodified: die,
    })
}

#[test]
fn ose_exploration_parses_and_typechecks() {
    let (program, _) = compile_ose_exploration();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSE"));
    assert!(system_names.contains(&"OSE Exploration"));
}

#[test]
fn ose_exploration_has_expected_decls() {
    let (program, _) = compile_ose_exploration();

    let mut has_action_enum = false;
    let mut has_turn_phases_derive = false;
    let mut has_action_phases_table = false;
    let mut has_skip_phase_derive = false;
    let mut has_wandering_roll = false;

    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSE Exploration" {
                for decl in &sys.decls {
                    match &decl.node {
                        DeclKind::Enum(e) if e.name == "ExplorationAction" => {
                            has_action_enum = true;
                            assert_eq!(e.variants.len(), 6);
                        }
                        DeclKind::Derive(d) if d.name == "exploration_turn_phases" => {
                            has_turn_phases_derive = true
                        }
                        DeclKind::Table(t) if t.name == "exploration_action_phases" => {
                            has_action_phases_table = true
                        }
                        DeclKind::Derive(d) if d.name == "skip_exploration_phase" => {
                            has_skip_phase_derive = true
                        }
                        DeclKind::Mechanic(m) if m.name == "wandering_monster_roll" => {
                            has_wandering_roll = true
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    assert!(has_action_enum, "expected ExplorationAction enum");
    assert!(has_turn_phases_derive, "expected exploration_turn_phases derive");
    assert!(has_action_phases_table, "expected exploration_action_phases table");
    assert!(has_skip_phase_derive, "expected skip_exploration_phase derive");
    assert!(has_wandering_roll, "expected wandering_monster_roll mechanic");
}

#[test]
fn exploration_phase_tables_and_derives() {
    let (program, result) = compile_ose_exploration();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let turn_phases = interp
        .evaluate_derive(&state, &mut handler, "exploration_turn_phases", vec![])
        .unwrap();
    assert!(matches!(turn_phases, Value::List(ref xs) if xs.len() == 6));

    let move_phases = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "exploration_action_phases",
            vec![action_val("exp_move")],
        )
        .unwrap();
    assert_eq!(
        move_phases,
        Value::List(vec![
            Value::Str("ValidateDoor".into()),
            Value::Str("TransitionRoom".into()),
            Value::Str("CheckTrap".into()),
            Value::Str("SpawnMonsters".into()),
        ])
    );
}

#[test]
fn skip_exploration_phase_logic() {
    let (program, result) = compile_ose_exploration();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let check_light = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "skip_exploration_phase",
            vec![
                Value::Str("CheckLight".into()),
                Value::Bool(false),
                Value::Bool(true),
            ],
        )
        .unwrap();
    assert_eq!(check_light, Value::Bool(false));

    let blocked_by_darkness = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "skip_exploration_phase",
            vec![
                Value::Str("AdvanceTime".into()),
                Value::Bool(false),
                Value::Bool(true),
            ],
        )
        .unwrap();
    assert_eq!(blocked_by_darkness, Value::Bool(true));

    let no_rest_needed = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "skip_exploration_phase",
            vec![
                Value::Str("CheckRest".into()),
                Value::Bool(true),
                Value::Bool(false),
            ],
        )
        .unwrap();
    assert_eq!(no_rest_needed, Value::Bool(true));
}

#[test]
fn wandering_search_and_listen_mechanics() {
    let (program, result) = compile_ose_exploration();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let mut handler = NullHandler;
    let interval = interp
        .evaluate_derive(&state, &mut handler, "wandering_monster_interval", vec![])
        .unwrap();
    assert_eq!(interval, Value::Int(2));

    // wandering_monster_roll: 1 triggers, 3 does not.
    let mut handler = ScriptedHandler::with_responses(vec![scripted_roll(1, 6, 1)]);
    let triggered = interp
        .evaluate_mechanic(&state, &mut handler, "wandering_monster_roll", vec![])
        .unwrap();
    assert_eq!(triggered, Value::Bool(true));

    let mut handler = ScriptedHandler::with_responses(vec![scripted_roll(1, 6, 3)]);
    let not_triggered = interp
        .evaluate_mechanic(&state, &mut handler, "wandering_monster_roll", vec![])
        .unwrap();
    assert_eq!(not_triggered, Value::Bool(false));

    // search_room_roll: elf threshold=2.
    let mut handler = ScriptedHandler::with_responses(vec![scripted_roll(1, 6, 2)]);
    let elf_search_success = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "search_room_roll",
            vec![Value::Bool(true)],
        )
        .unwrap();
    assert_eq!(elf_search_success, Value::Bool(true));

    // listen_at_door_roll: non-demihuman threshold=1, roll 2 fails.
    let mut handler = ScriptedHandler::with_responses(vec![scripted_roll(1, 6, 2)]);
    let human_listen_fail = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "listen_at_door_roll",
            vec![Value::Bool(false)],
        )
        .unwrap();
    assert_eq!(human_listen_fail, Value::Bool(false));
}
