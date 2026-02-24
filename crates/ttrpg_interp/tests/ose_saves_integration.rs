//! OSE saving throws integration test.
//!
//! Verifies that ose/ose_saves.ttrpg parses, lowers, and type-checks
//! through the full multi-file pipeline. Also tests table lookups via
//! convenience derives and the saving_throw_check mechanic at runtime.

use std::collections::BTreeMap;

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_ast::diagnostic::Severity;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

// ── Compile helpers ────────────────────────────────────────────

/// Compile both OSE files through the multi-file pipeline.
fn compile_ose_saves() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    let core_source = include_str!("../../../ose/ose_core.ttrpg");
    let saves_source = include_str!("../../../ose/ose_saves.ttrpg");

    let sources = vec![
        ("ose/ose_core.ttrpg".to_string(), core_source.to_string()),
        ("ose/ose_saves.ttrpg".to_string(), saves_source.to_string()),
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

/// Helper: create a SaveCategory enum variant value.
fn save_category(variant: &str) -> Value {
    Value::EnumVariant {
        enum_name: "SaveCategory".into(),
        variant: variant.into(),
        fields: BTreeMap::new(),
    }
}

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn ose_saves_parses_and_typechecks() {
    let (program, _) = compile_ose_saves();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSE"));
    assert!(system_names.contains(&"OSE Saves"));
}

// ── Table declaration structure ────────────────────────────────

#[test]
fn ose_saves_has_table_and_mechanic() {
    let (program, _) = compile_ose_saves();

    let mut has_table = false;
    let mut has_mechanic = false;

    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSE Saves" {
                for decl in &sys.decls {
                    match &decl.node {
                        DeclKind::Table(t) if t.name == "saving_throws" => {
                            has_table = true;
                            assert_eq!(t.params.len(), 2);
                        }
                        DeclKind::Mechanic(f) if f.name == "saving_throw_check" => {
                            has_mechanic = true;
                            assert_eq!(f.params.len(), 2);
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    assert!(has_table, "expected saving_throws table");
    assert!(has_mechanic, "expected saving_throw_check mechanic");
}

// ── Table entry count ──────────────────────────────────────────

#[test]
fn ose_saves_table_has_all_entries() {
    let (program, _) = compile_ose_saves();

    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSE Saves" {
                for decl in &sys.decls {
                    if let DeclKind::Table(t) = &decl.node {
                        if t.name == "saving_throws" {
                            // 13 categories × varying tiers = 49 entries
                            assert_eq!(t.entries.len(), 49);
                            return;
                        }
                    }
                }
            }
        }
    }
    panic!("saving_throws table not found");
}

// ── Runtime: Fighter saves at level 1 (via convenience derives) ──

#[test]
fn fighter_level_1_saves() {
    let (program, result) = compile_ose_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let cat = save_category("save_fighter");
    let lvl = Value::Int(1);

    let death = interp
        .evaluate_derive(&state, &mut handler, "get_save_death", vec![cat.clone(), lvl.clone()])
        .unwrap();
    assert_eq!(death, Value::Int(12));

    let wands = interp
        .evaluate_derive(&state, &mut handler, "get_save_wands", vec![cat.clone(), lvl.clone()])
        .unwrap();
    assert_eq!(wands, Value::Int(13));

    let paralysis = interp
        .evaluate_derive(&state, &mut handler, "get_save_paralysis", vec![cat.clone(), lvl.clone()])
        .unwrap();
    assert_eq!(paralysis, Value::Int(14));

    let breath = interp
        .evaluate_derive(&state, &mut handler, "get_save_breath", vec![cat.clone(), lvl.clone()])
        .unwrap();
    assert_eq!(breath, Value::Int(15));

    let spells = interp
        .evaluate_derive(&state, &mut handler, "get_save_spells", vec![cat.clone(), lvl.clone()])
        .unwrap();
    assert_eq!(spells, Value::Int(16));
}

// ── Runtime: Fighter saves at level 7 (tier boundary) ──────────

#[test]
fn fighter_level_7_saves() {
    let (program, result) = compile_ose_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let cat = save_category("save_fighter");
    let lvl = Value::Int(7);

    assert_eq!(
        interp.evaluate_derive(&state, &mut handler, "get_save_death", vec![cat.clone(), lvl.clone()]).unwrap(),
        Value::Int(8)
    );
    assert_eq!(
        interp.evaluate_derive(&state, &mut handler, "get_save_wands", vec![cat.clone(), lvl.clone()]).unwrap(),
        Value::Int(9)
    );
    assert_eq!(
        interp.evaluate_derive(&state, &mut handler, "get_save_paralysis", vec![cat.clone(), lvl.clone()]).unwrap(),
        Value::Int(10)
    );
    assert_eq!(
        interp.evaluate_derive(&state, &mut handler, "get_save_breath", vec![cat.clone(), lvl.clone()]).unwrap(),
        Value::Int(10)
    );
    assert_eq!(
        interp.evaluate_derive(&state, &mut handler, "get_save_spells", vec![cat.clone(), lvl.clone()]).unwrap(),
        Value::Int(12)
    );
}

// ── Runtime: Magic-User saves at level 11 ──────────────────────

#[test]
fn magic_user_level_11_saves() {
    let (program, result) = compile_ose_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let cat = save_category("save_magic_user");
    let lvl = Value::Int(11);

    assert_eq!(
        interp.evaluate_derive(&state, &mut handler, "get_save_death", vec![cat.clone(), lvl.clone()]).unwrap(),
        Value::Int(8)
    );
    assert_eq!(
        interp.evaluate_derive(&state, &mut handler, "get_save_spells", vec![cat.clone(), lvl.clone()]).unwrap(),
        Value::Int(8)
    );
    assert_eq!(
        interp.evaluate_derive(&state, &mut handler, "get_save_breath", vec![cat.clone(), lvl.clone()]).unwrap(),
        Value::Int(11)
    );
}

// ── Runtime: Dwarf saves at level 10 (demihuman high tier) ─────

#[test]
fn dwarf_level_10_saves() {
    let (program, result) = compile_ose_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let cat = save_category("save_dwarf");
    let lvl = Value::Int(10);

    assert_eq!(
        interp.evaluate_derive(&state, &mut handler, "get_save_death", vec![cat.clone(), lvl.clone()]).unwrap(),
        Value::Int(2)
    );
    assert_eq!(
        interp.evaluate_derive(&state, &mut handler, "get_save_wands", vec![cat.clone(), lvl.clone()]).unwrap(),
        Value::Int(3)
    );
    assert_eq!(
        interp.evaluate_derive(&state, &mut handler, "get_save_paralysis", vec![cat.clone(), lvl.clone()]).unwrap(),
        Value::Int(4)
    );
    assert_eq!(
        interp.evaluate_derive(&state, &mut handler, "get_save_breath", vec![cat.clone(), lvl.clone()]).unwrap(),
        Value::Int(4)
    );
    assert_eq!(
        interp.evaluate_derive(&state, &mut handler, "get_save_spells", vec![cat.clone(), lvl.clone()]).unwrap(),
        Value::Int(6)
    );
}

// ── Runtime: Thief saves tier transitions ──────────────────────

#[test]
fn thief_saves_tier_transitions() {
    let (program, result) = compile_ose_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let cat = save_category("save_thief");

    // Level 4 (tier 1): death=13
    assert_eq!(
        interp.evaluate_derive(&state, &mut handler, "get_save_death", vec![cat.clone(), Value::Int(4)]).unwrap(),
        Value::Int(13)
    );

    // Level 5 (tier 2): death=12
    assert_eq!(
        interp.evaluate_derive(&state, &mut handler, "get_save_death", vec![cat.clone(), Value::Int(5)]).unwrap(),
        Value::Int(12)
    );
}

// ── Runtime: Out-of-range level causes error ───────────────────

#[test]
fn out_of_range_level_errors() {
    let (program, result) = compile_ose_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Elf max level is 10, level 11 should produce a no-match error
    let err = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "get_save_death",
            vec![save_category("save_elf"), Value::Int(11)],
        )
        .unwrap_err();
    assert!(
        err.to_string().contains("no matching entry"),
        "expected 'no matching entry' error, got: {}",
        err
    );
}

// ── Convenience derives count ──────────────────────────────────

#[test]
fn ose_saves_has_convenience_derives() {
    let (program, _) = compile_ose_saves();

    let derive_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) if sys.name == "OSE Saves" => Some(
                sys.decls
                    .iter()
                    .filter_map(|d| match &d.node {
                        DeclKind::Derive(f) => Some(f.name.as_str()),
                        _ => None,
                    })
                    .collect::<Vec<_>>(),
            ),
            _ => None,
        })
        .flatten()
        .collect();

    assert!(derive_names.contains(&"get_save_death"));
    assert!(derive_names.contains(&"get_save_wands"));
    assert!(derive_names.contains(&"get_save_paralysis"));
    assert!(derive_names.contains(&"get_save_breath"));
    assert!(derive_names.contains(&"get_save_spells"));
}
