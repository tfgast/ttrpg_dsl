//! OSE wilderness travel integration tests.
//!
//! Verifies that ose/ose_wilderness.ttrpg parses, lowers, type-checks, and
//! evaluates correctly.

use std::collections::{BTreeMap, VecDeque};

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_ast::diagnostic::Severity;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::{DiceExpr, RollResult, Value};
use ttrpg_interp::Interpreter;

fn compile_ose_wilderness() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    let source = include_str!("../../../ose/ose_wilderness.ttrpg");
    let (program, parse_errors) = ttrpg_parser::parse(source, ttrpg_ast::FileId::SYNTH);
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

fn terrain(name: &str) -> Value {
    Value::EnumVariant {
        enum_name: "WildernessTerrainKind".into(),
        variant: name.into(),
        fields: BTreeMap::new(),
    }
}

fn scripted_d6(die: i64) -> Response {
    Response::Rolled(RollResult {
        expr: DiceExpr::single(1, 6, None, 0),
        dice: vec![die],
        kept: vec![die],
        modifier: 0,
        total: die,
        unmodified: die,
    })
}

#[test]
fn ose_wilderness_parses_and_typechecks() {
    let (program, _) = compile_ose_wilderness();
    let has_system = program
        .items
        .iter()
        .any(|item| matches!(&item.node, TopLevel::System(sys) if sys.name == "OSE Wilderness"));
    assert!(has_system, "expected system named OSE Wilderness");
}

#[test]
fn ose_wilderness_has_expected_decls() {
    let (program, _) = compile_ose_wilderness();
    let mut has_terrain_enum = false;
    let mut table_count = 0;
    let mut has_lost_check = false;
    let mut has_starvation_penalty = false;

    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSE Wilderness" {
                for decl in &sys.decls {
                    match &decl.node {
                        DeclKind::Enum(e) if e.name == "WildernessTerrainKind" => {
                            has_terrain_enum = true;
                            assert_eq!(e.variants.len(), 11);
                        }
                        DeclKind::Table(_) => table_count += 1,
                        DeclKind::Mechanic(m) if m.name == "terrain_lost_check" => {
                            has_lost_check = true
                        }
                        DeclKind::Derive(d) if d.name == "starvation_penalty" => {
                            has_starvation_penalty = true
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    assert!(has_terrain_enum, "missing WildernessTerrainKind enum");
    assert!(table_count >= 4, "expected terrain property tables");
    assert!(has_lost_check, "missing terrain_lost_check mechanic");
    assert!(has_starvation_penalty, "missing starvation_penalty derive");
}

#[test]
fn terrain_tables_and_starvation_penalty() {
    let (program, result) = compile_ose_wilderness();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    assert_eq!(
        interp
            .evaluate_derive(
                &state,
                &mut handler,
                "terrain_move_cost_num",
                vec![terrain("wt_forest")],
            )
            .unwrap(),
        Value::Int(3)
    );
    assert_eq!(
        interp
            .evaluate_derive(
                &state,
                &mut handler,
                "terrain_lost_chance",
                vec![terrain("wt_jungle")],
            )
            .unwrap(),
        Value::Int(2)
    );
    assert_eq!(
        interp
            .evaluate_derive(
                &state,
                &mut handler,
                "terrain_can_forage",
                vec![terrain("wt_city")],
            )
            .unwrap(),
        Value::Bool(false)
    );
    assert_eq!(
        interp
            .evaluate_derive(
                &state,
                &mut handler,
                "starvation_penalty",
                vec![Value::Int(7)],
            )
            .unwrap(),
        Value::Int(-4)
    );
}

#[test]
fn wilderness_roll_mechanics() {
    let (program, result) = compile_ose_wilderness();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Forest lost chance is 2, roll 2 => lost.
    let mut handler = ScriptedHandler::with_responses(vec![scripted_d6(2)]);
    let lost = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "terrain_lost_check",
            vec![terrain("wt_forest")],
        )
        .unwrap();
    assert_eq!(lost, Value::Bool(true));

    // Clear encounter chance is 1, roll 3 => no encounter.
    let mut handler = ScriptedHandler::with_responses(vec![scripted_d6(3)]);
    let encounter = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "terrain_encounter_check",
            vec![terrain("wt_clear")],
        )
        .unwrap();
    assert_eq!(encounter, Value::Bool(false));

    // River forage chance is 2, roll 1 => forage succeeds.
    let mut handler = ScriptedHandler::with_responses(vec![scripted_d6(1)]);
    let forage = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "terrain_forage_check",
            vec![terrain("wt_river")],
        )
        .unwrap();
    assert_eq!(forage, Value::Bool(true));

    // Mountains orient chance = 6 - lost_chance(1) = 5, roll 6 => fail.
    let mut handler = ScriptedHandler::with_responses(vec![scripted_d6(6)]);
    let orient = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "terrain_orient_check",
            vec![terrain("wt_mountains")],
        )
        .unwrap();
    assert_eq!(orient, Value::Bool(false));
}
