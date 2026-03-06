//! OSRIC saving throw integration test.
//!
//! Verifies that osric/osric_saves.ttrpg parses, lowers, and type-checks
//! through the full multi-file pipeline (core + class + saves). AST
//! inspection tests (table structure, dispatch derive, entry counts) and
//! ResistSpell action tests (using ScriptedHandler) live here; per-class
//! saving throw value tests are in osric/tests/osric_saves.ttrpg-cli.

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_interp::adapter::StateAdapter;
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

mod osric_common;
use osric_common::*;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_saves() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn osric_saves_parses_and_typechecks() {
    let (program, _) = compile_osric_saves();
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
    assert!(system_names.contains(&"OSRIC Saves"));
}

// ── Table declaration structure ────────────────────────────────

#[test]
fn osric_saves_has_all_tables() {
    let (program, _) = compile_osric_saves();

    let mut table_names = Vec::new();
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSRIC Saves" {
                for decl in &sys.decls {
                    if let DeclKind::Table(t) = &decl.node {
                        table_names.push(t.name.as_str());
                    }
                }
            }
        }
    }

    let expected = [
        "fighter_saves",
        "paladin_saves",
        "cleric_saves",
        "druid_saves",
        "thief_saves",
        "magic_user_saves",
        "illusionist_saves",
        "monk_saves",
        "monster_saves_normal",
        "monster_saves_nonintelligent",
    ];
    for name in &expected {
        assert!(
            table_names.contains(name),
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
fn osric_saves_has_dispatch_derive() {
    let (program, _) = compile_osric_saves();

    let mut found = false;
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSRIC Saves" {
                for decl in &sys.decls {
                    if let DeclKind::Derive(f) = &decl.node {
                        if f.name == "saving_throws_for" {
                            assert_eq!(f.params.len(), 2, "saving_throws_for should take 2 params");
                            found = true;
                        }
                    }
                }
            }
        }
    }
    assert!(found, "expected saving_throws_for derive");
}

// ── Table entry counts ─────────────────────────────────────────

#[test]
fn osric_saves_table_entry_counts() {
    let (program, _) = compile_osric_saves();

    let expected_counts = [
        ("fighter_saves", 11), // 0, 1-2, 3-4, 5-6, 7-8, 9-10, 11-12, 13-14, 15-16, 17-18, _
        ("paladin_saves", 10), // 1-2, 3-4, 5-6, 7-8, 9-10, 11-12, 13-14, 15-16, 17-18, _
        ("cleric_saves", 7),   // 1-3, 4-6, 7-9, 10-12, 13-15, 16-18, _
        ("druid_saves", 5),    // 1-3, 4-6, 7-9, 10-12, _
        ("thief_saves", 5),    // 1-4, 5-8, 9-12, 13-16, _
        ("magic_user_saves", 4), // 1-5, 6-10, 11-15, _
        ("illusionist_saves", 4), // 1-5, 6-10, 11-15, _
        ("monk_saves", 5),     // 1-4, 5-8, 9-12, 13-16, _
    ];

    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSRIC Saves" {
                for decl in &sys.decls {
                    if let DeclKind::Table(t) = &decl.node {
                        if let Some(&(_, expected)) = expected_counts
                            .iter()
                            .find(|(name, _)| *name == t.name.as_str())
                        {
                            assert_eq!(
                                t.entries.len(),
                                expected,
                                "{} should have {} entries, got {}",
                                t.name,
                                expected,
                                t.entries.len()
                            );
                        }
                    }
                }
            }
        }
    }
}

// ── ResistSpell action ─────────────────────────────────────

fn save_category(variant: &str) -> Value {
    enum_variant("SaveCategory", variant)
}

/// Helper: call ResistSpell action with a scripted d20 roll.
#[allow(clippy::too_many_arguments)]
fn call_resist_spell(
    saver_class: &str,
    saver_level: i64,
    saver_ancestry: &str,
    abilities: &[(&str, i64)],
    category: &str,
    bonus: i64,
    is_mental: bool,
    d20_roll: i64,
) -> bool {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let saver = make_character(
        &mut state,
        "Saver",
        saver_class,
        saver_level,
        abilities,
        10,
        10,
        saver_ancestry,
    );

    use ttrpg_interp::effect::Response;
    let responses = vec![
        Response::Acknowledged, // ActionStarted
        scripted_roll(1, 20, 0, vec![d20_roll], vec![d20_roll], d20_roll, d20_roll),
    ];
    let mut handler = ScriptedHandler::with_responses(responses);

    let adapter = StateAdapter::new(state);
    let val = adapter
        .run(&mut handler, |s, h| {
            interp.execute_action(
                s,
                h,
                "ResistSpell",
                saver,
                vec![
                    Value::Option(Some(Box::new(save_category(category)))),
                    Value::Int(bonus),
                    Value::Bool(is_mental),
                ],
            )
        })
        .unwrap_or_else(|e| panic!("ResistSpell failed: {e}"));

    // Unwrap option<bool> → bool
    match val {
        Value::Option(Some(inner)) => expect_bool(*inner, "ResistSpell"),
        other => panic!("expected option<bool> from ResistSpell, got: {other:?}"),
    }
}

#[test]
fn resist_spell_passes_on_high_roll() {
    // Human Fighter L1, death target 14, roll 16 → pass
    let result = call_resist_spell(
        "Fighter",
        1,
        "Human",
        &standard_abilities(),
        "DeathParalysisPoison",
        0,
        false,
        16,
    );
    assert!(result, "roll 16 vs target 14 should pass");
}

#[test]
fn resist_spell_fails_on_low_roll() {
    // Human Fighter L1, death target 14, roll 5 → fail
    let result = call_resist_spell(
        "Fighter",
        1,
        "Human",
        &standard_abilities(),
        "DeathParalysisPoison",
        0,
        false,
        5,
    );
    assert!(!result, "roll 5 vs target 14 should fail");
}

#[test]
fn resist_spell_natural_1_always_fails() {
    // Human Fighter L19, death target 2, roll 1 → fail (natural 1)
    let result = call_resist_spell(
        "Fighter",
        19,
        "Human",
        &standard_abilities(),
        "DeathParalysisPoison",
        0,
        false,
        1,
    );
    assert!(!result, "natural 1 should always fail even vs target 2");
}

#[test]
fn resist_spell_stalwart_bonus_applies() {
    // Dwarf Fighter L1 CON 14 (+4 stalwart), death target 14, effective 10, roll 11 → pass
    let abilities: Vec<(&str, i64)> = vec![
        ("STR", 10),
        ("DEX", 10),
        ("CON", 14),
        ("INT", 10),
        ("WIS", 10),
        ("CHA", 10),
    ];
    let result = call_resist_spell(
        "Fighter",
        1,
        "Dwarf",
        &abilities,
        "DeathParalysisPoison",
        0,
        false,
        11,
    );
    assert!(
        result,
        "Dwarf CON 14 stalwart +4: roll 11 vs effective target 10 should pass"
    );
}

#[test]
fn resist_spell_stalwart_no_effect_on_breath() {
    // Dwarf Fighter L1 CON 14, breath target 17, no stalwart on breath, roll 11 → fail
    let abilities: Vec<(&str, i64)> = vec![
        ("STR", 10),
        ("DEX", 10),
        ("CON", 14),
        ("INT", 10),
        ("WIS", 10),
        ("CHA", 10),
    ];
    let result = call_resist_spell(
        "Fighter",
        1,
        "Dwarf",
        &abilities,
        "BreathWeapons",
        0,
        false,
        11,
    );
    assert!(
        !result,
        "stalwart does not apply to breath weapons: roll 11 vs 17 should fail"
    );
}

#[test]
fn resist_spell_no_stalwart_for_human() {
    // Human Fighter L1 CON 14, death target 14, no stalwart, roll 11 → fail
    let abilities: Vec<(&str, i64)> = vec![
        ("STR", 10),
        ("DEX", 10),
        ("CON", 14),
        ("INT", 10),
        ("WIS", 10),
        ("CHA", 10),
    ];
    let result = call_resist_spell(
        "Fighter",
        1,
        "Human",
        &abilities,
        "DeathParalysisPoison",
        0,
        false,
        11,
    );
    assert!(
        !result,
        "humans do not get stalwart: roll 11 vs 14 should fail"
    );
}

#[test]
fn resist_spell_mental_bonus_applies() {
    // Human Cleric L1 WIS 17 (+3 mental), spells target 15, effective 12, roll 12 → pass
    let abilities: Vec<(&str, i64)> = vec![
        ("STR", 10),
        ("DEX", 10),
        ("CON", 10),
        ("INT", 10),
        ("WIS", 17),
        ("CHA", 10),
    ];
    let result = call_resist_spell(
        "Cleric",
        1,
        "Human",
        &abilities,
        "SpellsUnlisted",
        0,
        true,
        12,
    );
    assert!(
        result,
        "WIS 17 mental +3: roll 12 vs effective target 12 should pass"
    );
}

#[test]
fn resist_spell_bonus_param_stacks() {
    // Human Fighter L1, death target 14, bonus 3, effective 11, roll 12 → pass
    let result = call_resist_spell(
        "Fighter",
        1,
        "Human",
        &standard_abilities(),
        "DeathParalysisPoison",
        3,
        false,
        12,
    );
    assert!(
        result,
        "bonus=3: roll 12 vs effective target 11 should pass"
    );
}
