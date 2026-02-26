//! OSE character generation integration tests.
//!
//! Verifies that ose/ose_chargen.ttrpg parses, lowers, type-checks, and
//! evaluates correctly with its dependencies.

use std::collections::{BTreeMap, VecDeque};

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_ast::diagnostic::Severity;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::{DiceExpr, RollResult, Value};
use ttrpg_interp::Interpreter;

fn compile_ose_chargen() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    let core_source = include_str!("../../../ose/ose_core.ttrpg");
    let class_source = include_str!("../../../ose/ose_class.ttrpg");
    let chargen_source = include_str!("../../../ose/ose_chargen.ttrpg");

    let sources = vec![
        ("ose/ose_core.ttrpg".to_string(), core_source.to_string()),
        ("ose/ose_class.ttrpg".to_string(), class_source.to_string()),
        ("ose/ose_chargen.ttrpg".to_string(), chargen_source.to_string()),
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

fn enum_variant(enum_name: &str, variant: &str) -> Value {
    Value::EnumVariant {
        enum_name: enum_name.into(),
        variant: variant.into(),
        fields: BTreeMap::new(),
    }
}

fn class_val(name: &str) -> Value {
    enum_variant("Class", name)
}

fn spell_list_val(name: &str) -> Value {
    enum_variant("SpellListType", name)
}

fn aptitude_val(name: &str) -> Value {
    enum_variant("CombatAptitude", name)
}

fn scripted_roll(count: u32, sides: u32, dice: Vec<i64>, total: i64) -> Response {
    Response::Rolled(RollResult {
        expr: DiceExpr {
            count,
            sides,
            filter: None,
            modifier: 0,
        },
        dice: dice.clone(),
        kept: dice,
        modifier: 0,
        total,
        unmodified: total,
    })
}

#[test]
fn ose_chargen_parses_and_typechecks() {
    let (program, _) = compile_ose_chargen();
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
    assert!(system_names.contains(&"OSE Chargen"));
}

#[test]
fn ose_chargen_has_expected_decls() {
    let (program, _) = compile_ose_chargen();
    let mut has_roll_ability = false;
    let mut has_roll_starting_hp = false;
    let mut has_thac0_table = false;
    let mut has_starting_spells_table = false;

    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSE Chargen" {
                for decl in &sys.decls {
                    match &decl.node {
                        DeclKind::Mechanic(m) if m.name == "roll_ability" => has_roll_ability = true,
                        DeclKind::Mechanic(m) if m.name == "roll_starting_hp" => has_roll_starting_hp = true,
                        DeclKind::Table(t) if t.name == "character_thac0" => has_thac0_table = true,
                        DeclKind::Table(t) if t.name == "available_starting_spells" => has_starting_spells_table = true,
                        _ => {}
                    }
                }
            }
        }
    }

    assert!(has_roll_ability, "expected roll_ability mechanic");
    assert!(has_roll_starting_hp, "expected roll_starting_hp mechanic");
    assert!(has_thac0_table, "expected character_thac0 table");
    assert!(
        has_starting_spells_table,
        "expected available_starting_spells table"
    );
}

#[test]
fn is_spellbook_caster_regression_checks() {
    let (program, result) = compile_ose_chargen();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    assert_eq!(
        interp
            .evaluate_derive(
                &state,
                &mut handler,
                "is_spellbook_caster",
                vec![class_val("MagicUser")],
            )
            .unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        interp
            .evaluate_derive(
                &state,
                &mut handler,
                "is_spellbook_caster",
                vec![class_val("HalfElf")],
            )
            .unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        interp
            .evaluate_derive(
                &state,
                &mut handler,
                "is_spellbook_caster",
                vec![class_val("Fighter")],
            )
            .unwrap(),
        Value::Bool(false)
    );
}

#[test]
fn spell_list_tables_regression_checks() {
    let (program, result) = compile_ose_chargen();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let none_list = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "available_starting_spells",
            vec![spell_list_val("NoList")],
        )
        .unwrap();
    assert_eq!(none_list, Value::List(vec![]));

    let druid = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "available_starting_spells",
            vec![spell_list_val("Druid")],
        )
        .unwrap();
    assert!(matches!(druid, Value::List(ref xs) if xs.len() == 8));
}

#[test]
fn thac0_table_and_wrapper_match() {
    let (program, result) = compile_ose_chargen();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let table = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "character_thac0",
            vec![aptitude_val("martial"), Value::Int(5)],
        )
        .unwrap();
    let wrapper = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "get_character_thac0",
            vec![aptitude_val("martial"), Value::Int(5)],
        )
        .unwrap();

    assert_eq!(table, Value::Int(17));
    assert_eq!(wrapper, table);
}

#[test]
fn roll_starting_hp_clamps_to_one() {
    let (program, result) = compile_ose_chargen();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = ScriptedHandler::with_responses(vec![scripted_roll(1, 4, vec![1], 1)]);

    let hp = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "roll_starting_hp",
            vec![Value::Int(4), Value::Int(-3)],
        )
        .unwrap();
    assert_eq!(hp, Value::Int(1));
}

#[test]
fn roll_starting_gold_multiplies_3d6_by_10() {
    let (program, result) = compile_ose_chargen();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler =
        ScriptedHandler::with_responses(vec![scripted_roll(3, 6, vec![3, 3, 4], 10)]);

    let gold = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "roll_starting_gold",
            vec![class_val("Fighter")],
        )
        .unwrap();
    assert_eq!(gold, Value::Int(100));
}
