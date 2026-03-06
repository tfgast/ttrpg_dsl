//! OSE time/economy constants integration tests.
//!
//! Verifies that ose/ose_time_economy.ttrpg parses, lowers, and type-checks
//! with dependencies.
//!
//! Runtime value tests have been moved to ose/tests/ose_time_economy.ttrpg-cli.

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_ast::diagnostic::Severity;

fn compile_ose_time_economy() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    let core_source = include_str!("../../../ose/ose_core.ttrpg");
    let time_source = include_str!("../../../ose/ose_time_economy.ttrpg");

    let sources = vec![
        ("ose/ose_core.ttrpg".to_string(), core_source.to_string()),
        (
            "ose/ose_time_economy.ttrpg".to_string(),
            time_source.to_string(),
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
                        DeclKind::Table(t) if t.name == "light_source_turns" => {
                            has_light_table = true;
                        }
                        DeclKind::Table(t) if t.name == "coin_gp_value_x100" => {
                            has_coin_table = true;
                        }
                        DeclKind::Table(t) if t.name == "armour_weight_cn" => {
                            has_armour_table = true;
                        }
                        DeclKind::Derive(d) if d.name == "rest_interval_turns" => {
                            has_rest_interval = true;
                        }
                        DeclKind::Derive(d) if d.name == "training_cost_gp" => {
                            has_training_cost = true;
                        }
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
