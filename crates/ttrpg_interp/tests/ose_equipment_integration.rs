//! OSE starting equipment integration tests.
//!
//! Verifies that ose/ose_equipment.ttrpg parses, lowers, type-checks, and
//! evaluates correctly with dependencies.

use std::collections::BTreeMap;

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_ast::diagnostic::Severity;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

fn compile_ose_equipment() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    let core_source = include_str!("../../../ose/ose_core.ttrpg");
    let class_source = include_str!("../../../ose/ose_class.ttrpg");
    let equipment_source = include_str!("../../../ose/ose_equipment.ttrpg");

    let sources = vec![
        ("ose/ose_core.ttrpg".to_string(), core_source.to_string()),
        ("ose/ose_class.ttrpg".to_string(), class_source.to_string()),
        (
            "ose/ose_equipment.ttrpg".to_string(),
            equipment_source.to_string(),
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

fn class_val(name: &str) -> Value {
    Value::EnumVariant {
        enum_name: "Class".into(),
        variant: name.into(),
        fields: BTreeMap::new(),
    }
}

#[test]
fn ose_equipment_parses_and_typechecks() {
    let (program, _) = compile_ose_equipment();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSE"));
    assert!(system_names.contains(&"OSE Classes"));
    assert!(system_names.contains(&"OSE Equipment"));
}

#[test]
fn ose_equipment_has_expected_decls() {
    let (program, _) = compile_ose_equipment();
    let mut has_standard_gear = false;
    let mut has_default_armour = false;
    let mut has_equipment_package_table = false;
    let mut has_random_weapon_table = false;

    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSE Equipment" {
                for decl in &sys.decls {
                    match &decl.node {
                        DeclKind::Derive(d) if d.name == "standard_adventuring_gear" => {
                            has_standard_gear = true
                        }
                        DeclKind::Derive(d) if d.name == "default_starting_armour" => {
                            has_default_armour = true
                        }
                        DeclKind::Table(t) if t.name == "equipment_package" => {
                            has_equipment_package_table = true
                        }
                        DeclKind::Table(t) if t.name == "random_starting_weapon" => {
                            has_random_weapon_table = true
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    assert!(has_standard_gear, "expected standard_adventuring_gear");
    assert!(has_default_armour, "expected default_starting_armour");
    assert!(
        has_equipment_package_table,
        "expected equipment_package table"
    );
    assert!(has_random_weapon_table, "expected random_starting_weapon table");
}

#[test]
fn default_starting_armour_examples() {
    let (program, result) = compile_ose_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let fighter = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "default_starting_armour",
            vec![class_val("Fighter")],
        )
        .unwrap();
    assert_eq!(
        fighter,
        Value::List(vec![
            Value::Str("Chainmail".into()),
            Value::Str("Shield".into())
        ])
    );

    let magic_user = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "default_starting_armour",
            vec![class_val("MagicUser")],
        )
        .unwrap();
    assert_eq!(magic_user, Value::List(vec![]));
}

#[test]
fn equipment_package_table_examples() {
    let (program, result) = compile_ose_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let fighter = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "equipment_package",
            vec![class_val("Fighter")],
        )
        .unwrap();
    assert!(matches!(fighter, Value::List(ref xs) if xs.len() == 9));

    let gnome = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "equipment_package",
            vec![class_val("Gnome")],
        )
        .unwrap();
    assert!(matches!(gnome, Value::List(ref xs) if xs.len() == 9));
}

#[test]
fn random_weapon_table_and_wrapper_match() {
    let (program, result) = compile_ose_equipment();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let table = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "random_starting_weapon",
            vec![class_val("Dwarf"), Value::Int(4)],
        )
        .unwrap();
    let wrapper = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "get_random_starting_weapon",
            vec![class_val("Dwarf"), Value::Int(4)],
        )
        .unwrap();

    assert_eq!(table, Value::Str("War hammer".into()));
    assert_eq!(wrapper, table);
}
