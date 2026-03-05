//! OSRIC thief skill integration test.
//!
//! Verifies that osric/osric_thief_skills.ttrpg parses, lowers, and type-checks
//! through the full multi-file pipeline. Exercises the thief and assassin skill
//! base tables, DEX adjustment table, ancestry adjustment table, effective skill
//! computation, and the d100 skill check mechanic.

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

mod osric_common;
use osric_common::*;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_thief_skills() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

fn thief_skill(variant: &str) -> Value {
    enum_variant("ThiefSkill", variant)
}

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn osric_thief_skills_parses_and_typechecks() {
    let (program, _) = compile_osric_thief_skills();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSRIC Thief Skills"));
}

// ── Structure: expected tables, derives, mechanics ─────────────

#[test]
fn has_expected_tables() {
    let (program, _) = compile_osric_thief_skills();

    let mut table_names = Vec::new();
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSRIC Thief Skills" {
                for decl in &sys.decls {
                    if let DeclKind::Table(t) = &decl.node {
                        table_names.push(t.name.to_string());
                    }
                }
            }
        }
    }

    for expected in [
        "thief_skill_base",
        "assassin_skill_base",
        "dex_thief_adj",
        "ancestry_thief_adj",
    ] {
        assert!(
            table_names.iter().any(|n| n == expected),
            "missing table: {expected}, got: {table_names:?}"
        );
    }
}

#[test]
fn has_expected_derives() {
    let (program, _) = compile_osric_thief_skills();

    let mut derive_names = Vec::new();
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSRIC Thief Skills" {
                for decl in &sys.decls {
                    if let DeclKind::Derive(d) = &decl.node {
                        derive_names.push(d.name.to_string());
                    }
                }
            }
        }
    }

    for expected in [
        "skill_base_for_class",
        "effective_thief_skill",
        "character_thief_skill",
    ] {
        assert!(
            derive_names.iter().any(|n| n == expected),
            "missing derive: {expected}, got: {derive_names:?}"
        );
    }
}

#[test]
fn has_thief_skill_check_mechanic() {
    let (program, _) = compile_osric_thief_skills();

    let mut found = false;
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSRIC Thief Skills" {
                for decl in &sys.decls {
                    if let DeclKind::Mechanic(m) = &decl.node {
                        if m.name == "thief_skill_check" {
                            found = true;
                        }
                    }
                }
            }
        }
    }
    assert!(found, "expected thief_skill_check mechanic");
}

// ── Thief base table spot checks ───────────────────────────────

fn eval_thief_base(skill: &str, level: i64) -> i64 {
    let (program, result) = compile_osric_thief_skills();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "thief_skill_base",
            vec![thief_skill(skill), Value::Int(level)],
        )
        .unwrap_or_else(|e| panic!("thief_skill_base({skill}, {level}) failed: {e}"));

    expect_int(val, &format!("thief_skill_base({skill}, {level})"))
}

#[test]
fn thief_climb_walls_level_1() {
    assert_eq!(eval_thief_base("climb_walls", 1), 85);
}

#[test]
fn thief_climb_walls_level_10() {
    assert_eq!(eval_thief_base("climb_walls", 10), 99);
}

#[test]
fn thief_open_locks_level_1() {
    assert_eq!(eval_thief_base("open_locks", 1), 25);
}

#[test]
fn thief_open_locks_level_9() {
    assert_eq!(eval_thief_base("open_locks", 9), 62);
}

#[test]
fn thief_pick_pockets_level_1() {
    assert_eq!(eval_thief_base("pick_pockets", 1), 30);
}

#[test]
fn thief_pick_pockets_level_12() {
    // Pick pockets can exceed 100% — high level thieves are very good
    assert_eq!(eval_thief_base("pick_pockets", 12), 100);
}

#[test]
fn thief_hide_in_shadows_level_5() {
    assert_eq!(eval_thief_base("hide_in_shadows", 5), 30);
}

#[test]
fn thief_move_silently_level_7() {
    assert_eq!(eval_thief_base("move_silently", 7), 55);
}

#[test]
fn thief_find_traps_level_1() {
    assert_eq!(eval_thief_base("find_traps", 1), 20);
}

#[test]
fn thief_hear_noise_level_1() {
    assert_eq!(eval_thief_base("hear_noise", 1), 10);
}

#[test]
fn thief_read_languages_level_1() {
    assert_eq!(eval_thief_base("read_languages", 1), 1);
}

#[test]
fn thief_read_languages_level_10() {
    assert_eq!(eval_thief_base("read_languages", 10), 50);
}

// ── Assassin base table spot checks ────────────────────────────

fn eval_assassin_base(skill: &str, level: i64) -> i64 {
    let (program, result) = compile_osric_thief_skills();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "assassin_skill_base",
            vec![thief_skill(skill), Value::Int(level)],
        )
        .unwrap_or_else(|e| panic!("assassin_skill_base({skill}, {level}) failed: {e}"));

    expect_int(val, &format!("assassin_skill_base({skill}, {level})"))
}

#[test]
fn assassin_climb_walls_level_1() {
    assert_eq!(eval_assassin_base("climb_walls", 1), 85);
}

#[test]
fn assassin_climb_walls_level_4() {
    // Assassin stays at 85 for 1-3, then 86 at 4
    assert_eq!(eval_assassin_base("climb_walls", 4), 86);
}

#[test]
fn assassin_open_locks_level_1() {
    assert_eq!(eval_assassin_base("open_locks", 1), 25);
}

#[test]
fn assassin_open_locks_level_8() {
    assert_eq!(eval_assassin_base("open_locks", 8), 47);
}

#[test]
fn assassin_read_languages_level_3() {
    // Assassin: levels 1-3 = 1%
    assert_eq!(eval_assassin_base("read_languages", 3), 1);
}

#[test]
fn assassin_find_traps_level_15() {
    // Wildcard: 80
    assert_eq!(eval_assassin_base("find_traps", 15), 80);
}

// ── Skill base dispatch: Thief vs Assassin ─────────────────────

fn eval_skill_base_for_class(class: &str, skill: &str, level: i64) -> i64 {
    let (program, result) = compile_osric_thief_skills();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "skill_base_for_class",
            vec![class_variant(class), thief_skill(skill), Value::Int(level)],
        )
        .unwrap_or_else(|e| panic!("skill_base_for_class({class}, {skill}, {level}) failed: {e}"));

    expect_int(
        val,
        &format!("skill_base_for_class({class}, {skill}, {level})"),
    )
}

#[test]
fn dispatch_thief_uses_thief_table() {
    assert_eq!(eval_skill_base_for_class("Thief", "open_locks", 5), 42);
}

#[test]
fn dispatch_assassin_uses_assassin_table() {
    assert_eq!(eval_skill_base_for_class("Assassin", "open_locks", 5), 33);
}

#[test]
fn dispatch_monk_uses_thief_table() {
    // Monk has thief skills but should use the thief progression table
    assert_eq!(eval_skill_base_for_class("Monk", "open_locks", 5), 42);
}

// ── DEX adjustment table ───────────────────────────────────────

fn eval_dex_adj(skill: &str, dex: i64) -> i64 {
    let (program, result) = compile_osric_thief_skills();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "dex_thief_adj",
            vec![thief_skill(skill), Value::Int(dex)],
        )
        .unwrap_or_else(|e| panic!("dex_thief_adj({skill}, {dex}) failed: {e}"));

    expect_int(val, &format!("dex_thief_adj({skill}, {dex})"))
}

#[test]
fn dex_climb_always_zero() {
    assert_eq!(eval_dex_adj("climb_walls", 9), 0);
    assert_eq!(eval_dex_adj("climb_walls", 18), 0);
}

#[test]
fn dex_hear_always_zero() {
    assert_eq!(eval_dex_adj("hear_noise", 9), 0);
    assert_eq!(eval_dex_adj("hear_noise", 18), 0);
}

#[test]
fn dex_read_languages_always_zero() {
    assert_eq!(eval_dex_adj("read_languages", 9), 0);
    assert_eq!(eval_dex_adj("read_languages", 18), 0);
}

#[test]
fn dex_9_open_locks_penalty() {
    assert_eq!(eval_dex_adj("open_locks", 9), -10);
}

#[test]
fn dex_18_open_locks_bonus() {
    assert_eq!(eval_dex_adj("open_locks", 18), 15);
}

#[test]
fn dex_9_pick_pockets_penalty() {
    assert_eq!(eval_dex_adj("pick_pockets", 9), -15);
}

#[test]
fn dex_9_move_silently_penalty() {
    assert_eq!(eval_dex_adj("move_silently", 9), -20);
}

#[test]
fn dex_17_hide_bonus() {
    assert_eq!(eval_dex_adj("hide_in_shadows", 17), 5);
}

#[test]
fn dex_19_find_traps_bonus() {
    // DEX 19 hits the wildcard: +15
    assert_eq!(eval_dex_adj("find_traps", 19), 15);
}

// ── Ancestry adjustment table ──────────────────────────────────

fn eval_ancestry_adj(skill: &str, anc: &str) -> i64 {
    let (program, result) = compile_osric_thief_skills();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "ancestry_thief_adj",
            vec![thief_skill(skill), ancestry(anc)],
        )
        .unwrap_or_else(|e| panic!("ancestry_thief_adj({skill}, {anc}) failed: {e}"));

    expect_int(val, &format!("ancestry_thief_adj({skill}, {anc})"))
}

#[test]
fn dwarf_climb_penalty() {
    assert_eq!(eval_ancestry_adj("climb_walls", "Dwarf"), -10);
}

#[test]
fn dwarf_open_locks_bonus() {
    assert_eq!(eval_ancestry_adj("open_locks", "Dwarf"), 15);
}

#[test]
fn dwarf_find_traps_bonus() {
    assert_eq!(eval_ancestry_adj("find_traps", "Dwarf"), 15);
}

#[test]
fn elf_hide_bonus() {
    assert_eq!(eval_ancestry_adj("hide_in_shadows", "Elf"), 10);
}

#[test]
fn elf_read_languages_bonus() {
    assert_eq!(eval_ancestry_adj("read_languages", "Elf"), 10);
}

#[test]
fn halfling_move_silently_bonus() {
    assert_eq!(eval_ancestry_adj("move_silently", "Halfling"), 15);
}

#[test]
fn halfling_hide_bonus() {
    assert_eq!(eval_ancestry_adj("hide_in_shadows", "Halfling"), 15);
}

#[test]
fn human_climb_bonus() {
    assert_eq!(eval_ancestry_adj("climb_walls", "Human"), 5);
}

#[test]
fn human_open_locks_bonus() {
    assert_eq!(eval_ancestry_adj("open_locks", "Human"), 5);
}

#[test]
fn halforc_pick_pockets_penalty() {
    assert_eq!(eval_ancestry_adj("pick_pockets", "HalfOrc"), -5);
}

// ── Effective skill computation ────────────────────────────────

fn eval_effective(class: &str, skill: &str, level: i64, dex: i64, anc: &str) -> i64 {
    let (program, result) = compile_osric_thief_skills();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "effective_thief_skill",
            vec![
                class_variant(class),
                thief_skill(skill),
                Value::Int(level),
                Value::Int(dex),
                ancestry(anc),
            ],
        )
        .unwrap_or_else(|e| {
            panic!("effective_thief_skill({class}, {skill}, {level}, {dex}, {anc}) failed: {e}")
        });

    expect_int(
        val,
        &format!("effective_thief_skill({class}, {skill}, {level}, {dex}, {anc})"),
    )
}

#[test]
fn effective_thief_open_locks_human_dex12_level1() {
    // Base 25 + DEX 12 adj 0 + Human adj 5 = 30
    assert_eq!(eval_effective("Thief", "open_locks", 1, 12, "Human"), 30);
}

#[test]
fn effective_thief_climb_human_dex12_level1() {
    // Base 85 + DEX 0 + Human +5 = 90
    assert_eq!(eval_effective("Thief", "climb_walls", 1, 12, "Human"), 90);
}

#[test]
fn effective_thief_hide_halfling_dex17_level5() {
    // Base 30 + DEX 17 hide adj +5 + Halfling hide +15 = 50
    assert_eq!(
        eval_effective("Thief", "hide_in_shadows", 5, 17, "Halfling"),
        50
    );
}

#[test]
fn effective_thief_open_locks_dwarf_dex9_level1() {
    // Base 25 + DEX 9 adj -10 + Dwarf adj +15 = 30
    assert_eq!(eval_effective("Thief", "open_locks", 1, 9, "Dwarf"), 30);
}

#[test]
fn effective_assassin_find_traps_elf_dex18_level5() {
    // Assassin base find_traps L5 = 30, DEX 18 adj +10, Elf adj +5 = 45
    assert_eq!(eval_effective("Assassin", "find_traps", 5, 18, "Elf"), 45);
}

#[test]
fn effective_clamps_minimum_to_1() {
    // Gnome climb L1: base 85 + DEX 0 + Gnome -15 = 70.
    // But test a scenario that could go below 1:
    // Assassin read_languages L1 = 1%, DEX 0, HalfOrc -10 = -9 → clamped to 1
    assert_eq!(
        eval_effective("Assassin", "read_languages", 1, 12, "HalfOrc"),
        1
    );
}

#[test]
fn effective_clamps_maximum_to_99() {
    // Pick pockets at high level can exceed 100%
    // Thief L16 pick_pockets = 125, DEX 18 +10, HalfElf +10 = 145 → clamped to 99
    assert_eq!(
        eval_effective("Thief", "pick_pockets", 16, 18, "HalfElf"),
        99
    );
}

// ── Thief skill check mechanic (d100) ──────────────────────────

fn call_thief_skill_check(target_pct: i64, d100_roll: i64) -> bool {
    let (program, result) = compile_osric_thief_skills();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let responses = vec![scripted_roll(
        1,
        100,
        0,
        vec![d100_roll],
        vec![d100_roll],
        d100_roll,
        d100_roll,
    )];
    let mut handler = ScriptedHandler::with_responses(responses);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "thief_skill_check",
            vec![Value::Int(target_pct)],
        )
        .unwrap_or_else(|e| panic!("thief_skill_check({target_pct}) failed: {e}"));

    expect_bool(val, "thief_skill_check")
}

#[test]
fn skill_check_01_always_succeeds() {
    // Roll of 1 (01) always succeeds, even with 0% target
    assert!(call_thief_skill_check(1, 1));
}

#[test]
fn skill_check_00_always_fails() {
    // Roll of 100 (00) always fails, even with 99% target
    assert!(!call_thief_skill_check(99, 100));
}

#[test]
fn skill_check_passes_on_roll_equal_to_target() {
    // Roll 50 vs target 50 → pass (roll <= target)
    assert!(call_thief_skill_check(50, 50));
}

#[test]
fn skill_check_passes_on_roll_under_target() {
    // Roll 30 vs target 50 → pass
    assert!(call_thief_skill_check(50, 30));
}

#[test]
fn skill_check_fails_on_roll_over_target() {
    // Roll 51 vs target 50 → fail
    assert!(!call_thief_skill_check(50, 51));
}

#[test]
fn skill_check_low_skill_high_roll_fails() {
    // Roll 90 vs target 20 → fail
    assert!(!call_thief_skill_check(20, 90));
}

#[test]
fn skill_check_high_skill_low_roll_passes() {
    // Roll 2 vs target 95 → pass
    assert!(call_thief_skill_check(95, 2));
}

// ── Skills improve with level ──────────────────────────────────

#[test]
fn thief_skills_improve_with_level() {
    let skills = [
        "climb_walls",
        "find_traps",
        "hear_noise",
        "hide_in_shadows",
        "move_silently",
        "open_locks",
        "pick_pockets",
        "read_languages",
    ];
    for skill in &skills {
        let low = eval_thief_base(skill, 1);
        let high = eval_thief_base(skill, 15);
        assert!(
            high >= low,
            "{skill}: level 15 ({high}) should be >= level 1 ({low})"
        );
    }
}

#[test]
fn assassin_skills_improve_with_level() {
    let skills = [
        "climb_walls",
        "find_traps",
        "hear_noise",
        "hide_in_shadows",
        "move_silently",
        "open_locks",
        "pick_pockets",
        "read_languages",
    ];
    for skill in &skills {
        let low = eval_assassin_base(skill, 1);
        let high = eval_assassin_base(skill, 14);
        assert!(
            high >= low,
            "{skill}: level 14 ({high}) should be >= level 1 ({low})"
        );
    }
}

// ── Thief vs Assassin: Thief generally better at same level ────

#[test]
fn thief_better_than_assassin_at_same_level() {
    // At level 5, thieves should be at least as good as assassins in most skills
    let skills = [
        "open_locks",
        "find_traps",
        "hide_in_shadows",
        "move_silently",
        "pick_pockets",
        "read_languages",
    ];
    for skill in &skills {
        let thief_val = eval_skill_base_for_class("Thief", skill, 5);
        let assassin_val = eval_skill_base_for_class("Assassin", skill, 5);
        assert!(
            thief_val >= assassin_val,
            "{skill}: thief ({thief_val}) should be >= assassin ({assassin_val}) at level 5"
        );
    }
}
