//! OSE spell metadata integration tests.
//!
//! Verifies that ose/ose_spells.ttrpg parses, lowers, type-checks, and
//! evaluates correctly with dependencies.

use std::collections::BTreeMap;

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_ast::diagnostic::Severity;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

fn compile_ose_spells() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    let core_source = include_str!("../../../ose/ose_core.ttrpg");
    let spells_source = include_str!("../../../ose/ose_spells.ttrpg");

    let sources = vec![
        ("ose/ose_core.ttrpg".to_string(), core_source.to_string()),
        (
            "ose/ose_spells.ttrpg".to_string(),
            spells_source.to_string(),
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

fn spell_save_type_variant(name: &str) -> Value {
    Value::EnumVariant {
        enum_name: "SpellSaveType".into(),
        variant: name.into(),
        fields: BTreeMap::new(),
    }
}

#[test]
fn ose_spells_parses_and_typechecks() {
    let (program, _) = compile_ose_spells();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSE"));
    assert!(system_names.contains(&"OSE Spells"));
}

#[test]
fn ose_spells_has_expected_decls() {
    let (program, _) = compile_ose_spells();

    let mut has_spell_save_enum = false;
    let mut has_spell_save_table = false;
    let mut has_spell_damage_table = false;

    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSE Spells" {
                for decl in &sys.decls {
                    match &decl.node {
                        DeclKind::Enum(e) if e.name == "SpellSaveType" => {
                            has_spell_save_enum = true;
                            assert_eq!(e.variants.len(), 6);
                        }
                        DeclKind::Table(t) if t.name == "spell_save_type" => {
                            has_spell_save_table = true;
                        }
                        DeclKind::Table(t) if t.name == "spell_damage_dice" => {
                            has_spell_damage_table = true;
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    assert!(has_spell_save_enum, "expected SpellSaveType enum");
    assert!(has_spell_save_table, "expected spell_save_type table");
    assert!(has_spell_damage_table, "expected spell_damage_dice table");
}

#[test]
fn spell_save_type_lookup_examples() {
    let (program, result) = compile_ose_spells();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let cloudkill = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "spell_save_type",
            vec![Value::Str("Cloudkill".into())],
        )
        .unwrap();
    assert_eq!(cloudkill, spell_save_type_variant("sv_death"));

    let hold_person = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "spell_save_type",
            vec![Value::Str("Hold Person".into())],
        )
        .unwrap();
    assert_eq!(hold_person, spell_save_type_variant("sv_spells"));

    let unknown = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "spell_save_type",
            vec![Value::Str("Unknown Spell".into())],
        )
        .unwrap();
    assert_eq!(unknown, spell_save_type_variant("no_save"));
}

#[test]
fn spell_damage_dice_lookup_examples() {
    let (program, result) = compile_ose_spells();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let fire_ball = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "spell_damage_dice",
            vec![Value::Str("Fire Ball".into())],
        )
        .unwrap();
    assert_eq!(fire_ball, Value::Str("1d6 per caster level".into()));

    let sleep = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "spell_damage_dice",
            vec![Value::Str("Sleep".into())],
        )
        .unwrap();
    assert_eq!(sleep, Value::Str("2d8 HD affected".into()));

    let unknown = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "spell_damage_dice",
            vec![Value::Str("Unknown Spell".into())],
        )
        .unwrap();
    assert_eq!(unknown, Value::Str("".into()));
}
