//! OSRIC spell slot progression integration test.
//!
//! Verifies that osric/osric_spells.ttrpg parses, lowers, and type-checks
//! through the full multi-file pipeline (core + class + spells). Exercises
//! per-class spell slot tables, WIS bonus table, and dispatch derives.

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_ast::diagnostic::Severity;
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

mod osric_common;
use osric_common::*;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_spells() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    let core_source = include_str!("../../../osric/osric_core.ttrpg");
    let class_source = include_str!("../../../osric/osric_class.ttrpg");
    let spells_source = include_str!("../../../osric/osric_spells.ttrpg");

    let sources = vec![
        (
            "osric/osric_core.ttrpg".to_string(),
            core_source.to_string(),
        ),
        (
            "osric/osric_class.ttrpg".to_string(),
            class_source.to_string(),
        ),
        (
            "osric/osric_spells.ttrpg".to_string(),
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

fn spell_progression(variant: &str) -> Value {
    enum_variant("SpellProgression", variant)
}

/// Call spell_slots_for(progression, class_level, spell_level) -> int
fn get_base_slots(
    interp: &Interpreter,
    state: &GameState,
    handler: &mut NullHandler,
    progression: &str,
    class_level: i64,
    spell_level: i64,
) -> i64 {
    let val = interp
        .evaluate_derive(
            state,
            handler,
            "spell_slots_for",
            vec![
                spell_progression(progression),
                Value::Int(class_level),
                Value::Int(spell_level),
            ],
        )
        .unwrap_or_else(|e| {
            panic!("spell_slots_for({progression}, {class_level}, {spell_level}) failed: {e}")
        });
    expect_int(val, "spell_slots_for")
}

/// Get all spell slots for a class level as a Vec (spell levels 1..=max).
fn get_all_slots(
    interp: &Interpreter,
    state: &GameState,
    handler: &mut NullHandler,
    progression: &str,
    class_level: i64,
    max_spell_level: i64,
) -> Vec<i64> {
    (1..=max_spell_level)
        .map(|sl| get_base_slots(interp, state, handler, progression, class_level, sl))
        .collect()
}

/// Call total_spell_slots(progression, class_level, spell_level, wis_score) -> int
fn get_total_slots(
    interp: &Interpreter,
    state: &GameState,
    handler: &mut NullHandler,
    progression: &str,
    class_level: i64,
    spell_level: i64,
    wis_score: i64,
) -> i64 {
    let val = interp
        .evaluate_derive(
            state,
            handler,
            "total_spell_slots",
            vec![
                spell_progression(progression),
                Value::Int(class_level),
                Value::Int(spell_level),
                Value::Int(wis_score),
            ],
        )
        .unwrap_or_else(|e| {
            panic!(
                "total_spell_slots({progression}, {class_level}, {spell_level}, {wis_score}) failed: {e}"
            )
        });
    expect_int(val, "total_spell_slots")
}

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn osric_spells_parses_and_typechecks() {
    let (program, _) = compile_osric_spells();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSRIC"));
    assert!(system_names.contains(&"OSRIC Classes"));
    assert!(system_names.contains(&"OSRIC Spells"));
}

// ── Table declaration structure ────────────────────────────────

#[test]
fn osric_spells_has_all_tables() {
    let (program, _) = compile_osric_spells();

    let mut table_names = Vec::new();
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSRIC Spells" {
                for decl in &sys.decls {
                    if let DeclKind::Table(t) = &decl.node {
                        table_names.push(t.name.to_string());
                    }
                }
            }
        }
    }

    let expected = [
        "cleric_slots",
        "druid_slots",
        "magic_user_slots",
        "illusionist_slots",
        "wis_bonus_slots",
    ];
    for name in &expected {
        assert!(
            table_names.iter().any(|n| n == name),
            "missing table: {name}, got: {table_names:?}"
        );
    }
    assert_eq!(
        table_names.len(),
        expected.len(),
        "expected {} tables, got: {table_names:?}",
        expected.len()
    );
}

#[test]
fn osric_spells_has_dispatch_derives() {
    let (program, _) = compile_osric_spells();

    let mut derive_names = Vec::new();
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSRIC Spells" {
                for decl in &sys.decls {
                    if let DeclKind::Derive(f) = &decl.node {
                        derive_names.push(f.name.to_string());
                    }
                }
            }
        }
    }

    let expected = [
        "spell_slots_for",
        "max_spell_level",
        "has_wis_bonus",
        "total_spell_slots",
    ];
    for name in &expected {
        assert!(
            derive_names.iter().any(|n| n == name),
            "missing derive: {name}, got: {derive_names:?}"
        );
    }
}

// ── Cleric spell slots ─────────────────────────────────────────

#[test]
fn cleric_level_1_slots() {
    let (program, result) = compile_osric_spells();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let slots = get_all_slots(&interp, &state, &mut handler, "Cleric", 1, 7);
    assert_eq!(slots, vec![1, 0, 0, 0, 0, 0, 0]);
}

#[test]
fn cleric_level_9_slots() {
    let (program, result) = compile_osric_spells();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let slots = get_all_slots(&interp, &state, &mut handler, "Cleric", 9, 7);
    assert_eq!(slots, vec![4, 4, 3, 2, 1, 0, 0]);
}

#[test]
fn cleric_level_20_slots() {
    let (program, result) = compile_osric_spells();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let slots = get_all_slots(&interp, &state, &mut handler, "Cleric", 20, 7);
    assert_eq!(slots, vec![9, 9, 9, 8, 7, 5, 2]);
}

// ── Druid spell slots ──────────────────────────────────────────

#[test]
fn druid_level_1_slots() {
    let (program, result) = compile_osric_spells();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let slots = get_all_slots(&interp, &state, &mut handler, "Druid", 1, 7);
    assert_eq!(slots, vec![2, 0, 0, 0, 0, 0, 0]);
}

#[test]
fn druid_level_14_slots() {
    let (program, result) = compile_osric_spells();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let slots = get_all_slots(&interp, &state, &mut handler, "Druid", 14, 7);
    assert_eq!(slots, vec![6, 6, 6, 6, 5, 4, 3]);
}

// ── Magic-User spell slots ─────────────────────────────────────

#[test]
fn magic_user_level_1_slots() {
    let (program, result) = compile_osric_spells();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let slots = get_all_slots(&interp, &state, &mut handler, "MagicUser", 1, 9);
    assert_eq!(slots, vec![1, 0, 0, 0, 0, 0, 0, 0, 0]);
}

#[test]
fn magic_user_level_18_slots() {
    let (program, result) = compile_osric_spells();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let slots = get_all_slots(&interp, &state, &mut handler, "MagicUser", 18, 9);
    assert_eq!(slots, vec![5, 5, 5, 5, 5, 3, 3, 2, 1]);
}

// ── Illusionist spell slots ────────────────────────────────────

#[test]
fn illusionist_level_1_slots() {
    let (program, result) = compile_osric_spells();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let slots = get_all_slots(&interp, &state, &mut handler, "Illusionist", 1, 7);
    assert_eq!(slots, vec![1, 0, 0, 0, 0, 0, 0]);
}

#[test]
fn illusionist_level_20_slots() {
    let (program, result) = compile_osric_spells();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let slots = get_all_slots(&interp, &state, &mut handler, "Illusionist", 20, 7);
    assert_eq!(slots, vec![6, 6, 6, 5, 5, 4, 2]);
}

// ── WIS bonus with total_spell_slots ───────────────────────────

#[test]
fn cleric_wis_18_bonus_applied() {
    let (program, result) = compile_osric_spells();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Cleric L3: base = [2,1,0,...], WIS 18 bonus = [+2,+2,+1,+1,0,0,0]
    // total first = 2+2=4, second = 1+2=3, third = 0 (base 0, no bonus)
    let first = get_total_slots(&interp, &state, &mut handler, "Cleric", 3, 1, 18);
    assert_eq!(first, 4, "Cleric L3 WIS 18: first-level should be 2+2=4");

    let second = get_total_slots(&interp, &state, &mut handler, "Cleric", 3, 2, 18);
    assert_eq!(second, 3, "Cleric L3 WIS 18: second-level should be 1+2=3");

    // Third level base is 0, so no bonus applied
    let third = get_total_slots(&interp, &state, &mut handler, "Cleric", 3, 3, 18);
    assert_eq!(third, 0, "Cleric L3 WIS 18: third-level base 0 means no bonus");
}

#[test]
fn wis_bonus_not_applied_to_magic_user() {
    let (program, result) = compile_osric_spells();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // MagicUser does not get WIS bonus
    let base = get_base_slots(&interp, &state, &mut handler, "MagicUser", 3, 1);
    let total = get_total_slots(&interp, &state, &mut handler, "MagicUser", 3, 1, 18);
    assert_eq!(base, total, "MagicUser should not get WIS bonus");
}

#[test]
fn wis_bonus_only_when_base_positive() {
    let (program, result) = compile_osric_spells();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Cleric L1 has 0 second-level slots; WIS bonus should not apply
    let total = get_total_slots(&interp, &state, &mut handler, "Cleric", 1, 2, 18);
    assert_eq!(total, 0, "WIS bonus should not apply when base slots = 0");
}

// ── NonCaster returns 0 ────────────────────────────────────────

#[test]
fn noncaster_returns_zero() {
    let (program, result) = compile_osric_spells();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let slots = get_base_slots(&interp, &state, &mut handler, "NonCaster", 10, 1);
    assert_eq!(slots, 0, "NonCaster should always return 0");
}

// ── max_spell_level derive ─────────────────────────────────────

#[test]
fn max_spell_level_values() {
    let (program, result) = compile_osric_spells();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let cases = [
        ("Cleric", 7),
        ("Druid", 7),
        ("Illusionist", 7),
        ("MagicUser", 9),
        ("NonCaster", 0),
        ("Paladin", 0),
        ("Ranger", 0),
    ];

    for (prog, expected) in &cases {
        let val = interp
            .evaluate_derive(
                &state,
                &mut handler,
                "max_spell_level",
                vec![spell_progression(prog)],
            )
            .unwrap_or_else(|e| panic!("max_spell_level({prog}) failed: {e}"));
        assert_eq!(
            expect_int(val, "max_spell_level"),
            *expected,
            "max_spell_level({prog})"
        );
    }
}

// ── has_wis_bonus derive ───────────────────────────────────────

#[test]
fn has_wis_bonus_values() {
    let (program, result) = compile_osric_spells();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let cases = [
        ("Cleric", true),
        ("Druid", true),
        ("MagicUser", false),
        ("Illusionist", false),
        ("NonCaster", false),
    ];

    for (prog, expected) in &cases {
        let val = interp
            .evaluate_derive(
                &state,
                &mut handler,
                "has_wis_bonus",
                vec![spell_progression(prog)],
            )
            .unwrap_or_else(|e| panic!("has_wis_bonus({prog}) failed: {e}"));
        assert_eq!(
            expect_bool(val, "has_wis_bonus"),
            *expected,
            "has_wis_bonus({prog})"
        );
    }
}
