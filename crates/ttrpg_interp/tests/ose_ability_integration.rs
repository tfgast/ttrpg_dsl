//! OSE ability modifiers & encumbrance integration test.
//!
//! Verifies that ose/ose_ability.ttrpg parses, lowers, and type-checks
//! through the full multi-file pipeline. Also tests all ability modifier
//! tables and encumbrance tables at runtime.

use std::collections::BTreeMap;

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_ast::diagnostic::Severity;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

// ── Compile helpers ────────────────────────────────────────────

/// Compile both OSE files through the multi-file pipeline.
fn compile_ose_ability() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    let core_source = include_str!("../../../ose/ose_core.ttrpg");
    let ability_source = include_str!("../../../ose/ose_ability.ttrpg");

    let sources = vec![
        ("ose/ose_core.ttrpg".to_string(), core_source.to_string()),
        ("ose/ose_ability.ttrpg".to_string(), ability_source.to_string()),
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

fn enum_variant(enum_name: &str, variant: &str) -> Value {
    Value::EnumVariant {
        enum_name: enum_name.to_string(),
        variant: variant.to_string(),
        fields: BTreeMap::new(),
    }
}

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn ose_ability_parses_and_typechecks() {
    let (program, _) = compile_ose_ability();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSE"));
    assert!(system_names.contains(&"OSE Ability"));
}

// ── Declaration structure ──────────────────────────────────────

#[test]
fn ose_ability_has_all_tables() {
    let (program, _) = compile_ose_ability();

    let table_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) if sys.name == "OSE Ability" => Some(
                sys.decls
                    .iter()
                    .filter_map(|d| match &d.node {
                        DeclKind::Table(t) => Some(t.name.as_str()),
                        _ => None,
                    })
                    .collect::<Vec<_>>(),
            ),
            _ => None,
        })
        .flatten()
        .collect();

    let expected = [
        "str_melee_mod",
        "str_open_doors",
        "dex_mod",
        "dex_init_mod",
        "con_hp_mod",
        "int_extra_languages",
        "wis_magic_save_mod",
        "cha_reaction_mod",
        "cha_max_retainers",
        "cha_loyalty",
        "prime_req_xp_mod",
        "encumbrance_level",
        "movement_rate",
    ];

    for name in &expected {
        assert!(
            table_names.contains(name),
            "missing table: {name}"
        );
    }

    assert_eq!(table_names.len(), expected.len(),
        "expected {} tables, got {}: {:?}",
        expected.len(), table_names.len(), table_names);
}

// ── STR modifiers ──────────────────────────────────────────────

#[test]
fn str_melee_mod_values() {
    let (program, result) = compile_ose_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let cases: Vec<(i64, i64)> = vec![
        (3, -3), (4, -2), (5, -2), (6, -1), (8, -1),
        (9, 0), (12, 0), (13, 1), (15, 1), (16, 2),
        (17, 2), (18, 3),
    ];
    for (score, expected) in cases {
        let val = interp
            .evaluate_derive(&state, &mut handler, "str_melee_mod", vec![Value::Int(score)])
            .unwrap();
        assert_eq!(val, Value::Int(expected), "str_melee_mod({score})");
    }
}

#[test]
fn str_open_doors_values() {
    let (program, result) = compile_ose_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let cases: Vec<(i64, i64)> = vec![
        (3, 1), (5, 1), (8, 1), (9, 2), (12, 2),
        (13, 3), (15, 3), (16, 4), (17, 4), (18, 5),
    ];
    for (score, expected) in cases {
        let val = interp
            .evaluate_derive(&state, &mut handler, "str_open_doors", vec![Value::Int(score)])
            .unwrap();
        assert_eq!(val, Value::Int(expected), "str_open_doors({score})");
    }
}

// ── DEX modifiers ──────────────────────────────────────────────

#[test]
fn dex_mod_values() {
    let (program, result) = compile_ose_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let cases: Vec<(i64, i64)> = vec![
        (3, -3), (5, -2), (7, -1), (10, 0), (14, 1), (17, 2), (18, 3),
    ];
    for (score, expected) in cases {
        let val = interp
            .evaluate_derive(&state, &mut handler, "dex_mod", vec![Value::Int(score)])
            .unwrap();
        assert_eq!(val, Value::Int(expected), "dex_mod({score})");
    }
}

#[test]
fn dex_init_mod_values() {
    let (program, result) = compile_ose_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let cases: Vec<(i64, i64)> = vec![
        (3, -2), (5, -1), (7, -1), (10, 0), (14, 1), (17, 1), (18, 2),
    ];
    for (score, expected) in cases {
        let val = interp
            .evaluate_derive(&state, &mut handler, "dex_init_mod", vec![Value::Int(score)])
            .unwrap();
        assert_eq!(val, Value::Int(expected), "dex_init_mod({score})");
    }
}

// ── CON modifier ───────────────────────────────────────────────

#[test]
fn con_hp_mod_values() {
    let (program, result) = compile_ose_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let cases: Vec<(i64, i64)> = vec![
        (3, -3), (4, -2), (6, -1), (9, 0), (13, 1), (16, 2), (18, 3),
    ];
    for (score, expected) in cases {
        let val = interp
            .evaluate_derive(&state, &mut handler, "con_hp_mod", vec![Value::Int(score)])
            .unwrap();
        assert_eq!(val, Value::Int(expected), "con_hp_mod({score})");
    }
}

// ── INT modifier ───────────────────────────────────────────────

#[test]
fn int_extra_languages_values() {
    let (program, result) = compile_ose_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let cases: Vec<(i64, i64)> = vec![
        (3, 0), (8, 0), (12, 0), (13, 1), (15, 1), (16, 2), (17, 2), (18, 3),
    ];
    for (score, expected) in cases {
        let val = interp
            .evaluate_derive(&state, &mut handler, "int_extra_languages", vec![Value::Int(score)])
            .unwrap();
        assert_eq!(val, Value::Int(expected), "int_extra_languages({score})");
    }
}

// ── WIS modifier ───────────────────────────────────────────────

#[test]
fn wis_magic_save_mod_values() {
    let (program, result) = compile_ose_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let cases: Vec<(i64, i64)> = vec![
        (3, -3), (5, -2), (7, -1), (10, 0), (14, 1), (17, 2), (18, 3),
    ];
    for (score, expected) in cases {
        let val = interp
            .evaluate_derive(&state, &mut handler, "wis_magic_save_mod", vec![Value::Int(score)])
            .unwrap();
        assert_eq!(val, Value::Int(expected), "wis_magic_save_mod({score})");
    }
}

// ── CHA modifiers ──────────────────────────────────────────────

#[test]
fn cha_reaction_mod_values() {
    let (program, result) = compile_ose_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let cases: Vec<(i64, i64)> = vec![
        (3, -2), (5, -1), (7, -1), (10, 0), (14, 1), (17, 1), (18, 2),
    ];
    for (score, expected) in cases {
        let val = interp
            .evaluate_derive(&state, &mut handler, "cha_reaction_mod", vec![Value::Int(score)])
            .unwrap();
        assert_eq!(val, Value::Int(expected), "cha_reaction_mod({score})");
    }
}

#[test]
fn cha_max_retainers_values() {
    let (program, result) = compile_ose_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let cases: Vec<(i64, i64)> = vec![
        (3, 1), (5, 2), (7, 3), (10, 4), (14, 5), (17, 6), (18, 7),
    ];
    for (score, expected) in cases {
        let val = interp
            .evaluate_derive(&state, &mut handler, "cha_max_retainers", vec![Value::Int(score)])
            .unwrap();
        assert_eq!(val, Value::Int(expected), "cha_max_retainers({score})");
    }
}

#[test]
fn cha_loyalty_values() {
    let (program, result) = compile_ose_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let cases: Vec<(i64, i64)> = vec![
        (3, 4), (5, 5), (7, 6), (10, 7), (14, 8), (17, 9), (18, 10),
    ];
    for (score, expected) in cases {
        let val = interp
            .evaluate_derive(&state, &mut handler, "cha_loyalty", vec![Value::Int(score)])
            .unwrap();
        assert_eq!(val, Value::Int(expected), "cha_loyalty({score})");
    }
}

// ── Prime requisite XP modifier ────────────────────────────────

#[test]
fn prime_req_xp_mod_values() {
    let (program, result) = compile_ose_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let cases: Vec<(i64, i64)> = vec![
        (3, -20), (5, -20), (6, -10), (8, -10),
        (9, 0), (12, 0), (13, 5), (15, 5), (16, 10), (18, 10),
    ];
    for (score, expected) in cases {
        let val = interp
            .evaluate_derive(&state, &mut handler, "prime_req_xp_mod", vec![Value::Int(score)])
            .unwrap();
        assert_eq!(val, Value::Int(expected), "prime_req_xp_mod({score})");
    }
}

// ── Encumbrance ────────────────────────────────────────────────

#[test]
fn encumbrance_level_values() {
    let (program, result) = compile_ose_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let cases: Vec<(i64, &str)> = vec![
        (0, "unencumbered"),
        (400, "unencumbered"),
        (401, "light"),
        (600, "light"),
        (601, "heavy"),
        (800, "heavy"),
        (801, "severe"),
        (1600, "severe"),
        (1601, "overloaded"),
        (5000, "overloaded"),
    ];
    for (weight, expected) in cases {
        let val = interp
            .evaluate_derive(&state, &mut handler, "encumbrance_level", vec![Value::Int(weight)])
            .unwrap();
        assert_eq!(
            val,
            enum_variant("EncumbranceLevel", expected),
            "encumbrance_level({weight})"
        );
    }
}

#[test]
fn movement_rate_values() {
    let (program, result) = compile_ose_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let cases: Vec<(&str, i64)> = vec![
        ("unencumbered", 120),
        ("light", 90),
        ("heavy", 60),
        ("severe", 30),
        ("overloaded", 0),
    ];
    for (level, expected) in cases {
        let val = interp
            .evaluate_derive(
                &state,
                &mut handler,
                "movement_rate",
                vec![enum_variant("EncumbranceLevel", level)],
            )
            .unwrap();
        assert_eq!(val, Value::Int(expected), "movement_rate({level})");
    }
}

// ── Boundary tests ─────────────────────────────────────────────

#[test]
fn standard_modifier_boundaries() {
    // All "standard" modifiers (STR melee, DEX, CON, WIS) share the same
    // breakpoints. Verify the exact boundary values.
    let (program, result) = compile_ose_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let standard_derives = ["str_melee_mod", "dex_mod", "con_hp_mod", "wis_magic_save_mod"];

    for derive_name in &standard_derives {
        // Boundary: 3 → -3, then 4 → -2
        let v3 = interp
            .evaluate_derive(&state, &mut handler, derive_name, vec![Value::Int(3)])
            .unwrap();
        let v4 = interp
            .evaluate_derive(&state, &mut handler, derive_name, vec![Value::Int(4)])
            .unwrap();
        assert_eq!(v3, Value::Int(-3), "{derive_name}(3)");
        assert_eq!(v4, Value::Int(-2), "{derive_name}(4)");

        // Boundary: 8 → -1, then 9 → 0
        let v8 = interp
            .evaluate_derive(&state, &mut handler, derive_name, vec![Value::Int(8)])
            .unwrap();
        let v9 = interp
            .evaluate_derive(&state, &mut handler, derive_name, vec![Value::Int(9)])
            .unwrap();
        assert_eq!(v8, Value::Int(-1), "{derive_name}(8)");
        assert_eq!(v9, Value::Int(0), "{derive_name}(9)");

        // Boundary: 12 → 0, then 13 → +1
        let v12 = interp
            .evaluate_derive(&state, &mut handler, derive_name, vec![Value::Int(12)])
            .unwrap();
        let v13 = interp
            .evaluate_derive(&state, &mut handler, derive_name, vec![Value::Int(13)])
            .unwrap();
        assert_eq!(v12, Value::Int(0), "{derive_name}(12)");
        assert_eq!(v13, Value::Int(1), "{derive_name}(13)");

        // Boundary: 17 → +2, then 18 → +3
        let v17 = interp
            .evaluate_derive(&state, &mut handler, derive_name, vec![Value::Int(17)])
            .unwrap();
        let v18 = interp
            .evaluate_derive(&state, &mut handler, derive_name, vec![Value::Int(18)])
            .unwrap();
        assert_eq!(v17, Value::Int(2), "{derive_name}(17)");
        assert_eq!(v18, Value::Int(3), "{derive_name}(18)");
    }
}
