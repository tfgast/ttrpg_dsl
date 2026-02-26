//! OSE time/economy constants integration tests.
//!
//! Verifies that ose/ose_time_economy.ttrpg parses, lowers, type-checks, and
//! evaluates correctly with dependencies.

use std::collections::BTreeMap;

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_ast::diagnostic::Severity;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

fn compile_ose_time_economy() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    let core_source = include_str!("../../../ose/ose_core.ttrpg");
    let time_source = include_str!("../../../ose/ose_time_economy.ttrpg");

    let sources = vec![
        ("ose/ose_core.ttrpg".to_string(), core_source.to_string()),
        ("ose/ose_time_economy.ttrpg".to_string(), time_source.to_string()),
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

fn light_kind(name: &str) -> Value {
    Value::EnumVariant {
        enum_name: "LightSourceKind".into(),
        variant: name.into(),
        fields: BTreeMap::new(),
    }
}

fn armour_kind(name: &str) -> Value {
    Value::EnumVariant {
        enum_name: "ArmourKind".into(),
        variant: name.into(),
        fields: BTreeMap::new(),
    }
}

#[test]
fn ose_time_economy_parses_and_typechecks() {
    let (program, _) = compile_ose_time_economy();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSE"));
    assert!(system_names.contains(&"OSE Time Economy"));
}

#[test]
fn ose_time_economy_has_expected_decls() {
    let (program, _) = compile_ose_time_economy();

    let mut has_light_enum = false;
    let mut has_armour_enum = false;
    let mut has_light_table = false;
    let mut has_coin_table = false;
    let mut has_armour_table = false;
    let mut has_rest_interval = false;
    let mut has_training_cost = false;

    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSE Time Economy" {
                for decl in &sys.decls {
                    match &decl.node {
                        DeclKind::Enum(e) if e.name == "LightSourceKind" => has_light_enum = true,
                        DeclKind::Enum(e) if e.name == "ArmourKind" => has_armour_enum = true,
                        DeclKind::Table(t) if t.name == "light_source_turns" => has_light_table = true,
                        DeclKind::Table(t) if t.name == "coin_gp_value_x100" => has_coin_table = true,
                        DeclKind::Table(t) if t.name == "armour_weight_cn" => has_armour_table = true,
                        DeclKind::Derive(d) if d.name == "rest_interval_turns" => has_rest_interval = true,
                        DeclKind::Derive(d) if d.name == "training_cost_gp" => has_training_cost = true,
                        _ => {}
                    }
                }
            }
        }
    }

    assert!(has_light_enum, "expected LightSourceKind enum");
    assert!(has_armour_enum, "expected ArmourKind enum");
    assert!(has_light_table, "expected light_source_turns table");
    assert!(has_coin_table, "expected coin_gp_value_x100 table");
    assert!(has_armour_table, "expected armour_weight_cn table");
    assert!(has_rest_interval, "expected rest_interval_turns derive");
    assert!(has_training_cost, "expected training_cost_gp derive");
}

#[test]
fn light_rest_day_and_training_values() {
    let (program, result) = compile_ose_time_economy();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    assert_eq!(
        interp
            .evaluate_derive(
                &state,
                &mut handler,
                "light_source_turns",
                vec![light_kind("torch")],
            )
            .unwrap(),
        Value::Int(6)
    );
    assert_eq!(
        interp
            .evaluate_derive(
                &state,
                &mut handler,
                "light_source_turns",
                vec![light_kind("lantern")],
            )
            .unwrap(),
        Value::Int(24)
    );

    assert_eq!(
        interp
            .evaluate_derive(&state, &mut handler, "rest_interval_turns", vec![])
            .unwrap(),
        Value::Int(5)
    );
    assert_eq!(
        interp
            .evaluate_derive(&state, &mut handler, "rest_overdue_penalty", vec![])
            .unwrap(),
        Value::Int(-1)
    );
    assert_eq!(
        interp
            .evaluate_derive(&state, &mut handler, "day_length_turns", vec![])
            .unwrap(),
        Value::Int(144)
    );
    assert_eq!(
        interp
            .evaluate_derive(
                &state,
                &mut handler,
                "training_cost_gp",
                vec![Value::Int(3)],
            )
            .unwrap(),
        Value::Int(300)
    );
}

#[test]
fn coin_and_armour_tables() {
    let (program, result) = compile_ose_time_economy();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    assert_eq!(
        interp
            .evaluate_derive(
                &state,
                &mut handler,
                "coin_gp_value_x100",
                vec![Value::Str("cp".into())],
            )
            .unwrap(),
        Value::Int(1)
    );
    assert_eq!(
        interp
            .evaluate_derive(
                &state,
                &mut handler,
                "coin_gp_value_x100",
                vec![Value::Str("pp".into())],
            )
            .unwrap(),
        Value::Int(500)
    );
    assert_eq!(
        interp
            .evaluate_derive(
                &state,
                &mut handler,
                "coin_gp_value_x100",
                vec![Value::Str("unknown".into())],
            )
            .unwrap(),
        Value::Int(0)
    );

    assert_eq!(
        interp
            .evaluate_derive(
                &state,
                &mut handler,
                "armour_weight_cn",
                vec![armour_kind("plate")],
            )
            .unwrap(),
        Value::Int(500)
    );
    assert_eq!(
        interp
            .evaluate_derive(
                &state,
                &mut handler,
                "armour_weight_cn",
                vec![armour_kind("shield")],
            )
            .unwrap(),
        Value::Int(100)
    );
}
