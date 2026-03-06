//! OSRIC saving throw integration test.
//!
//! Verifies that osric/osric_saves.ttrpg parses, lowers, and type-checks
//! through the full multi-file pipeline (core + class + saves). Exercises
//! all 8 class-specific saving throw tables at representative levels and
//! tests the saving_throws_for dispatch derive.

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

mod osric_common;
use osric_common::*;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_saves() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

/// Call saving_throws_for and return the SavingThrows struct fields as a tuple:
/// (aimed_magic, breath, death_paralysis_poison, petrification_polymorph, spells)
fn get_saves(
    interp: &Interpreter,
    state: &GameState,
    handler: &mut NullHandler,
    class: &str,
    level: i64,
) -> (i64, i64, i64, i64, i64) {
    let val = interp
        .evaluate_derive(
            state,
            handler,
            "saving_throws_for",
            vec![class_variant(class), Value::Int(level)],
        )
        .unwrap_or_else(|e| panic!("saving_throws_for({class}, {level}) failed: {e}"));

    match val {
        Value::Struct { name, fields } => {
            assert_eq!(&*name, "SavingThrows");
            let get = |field: &str| match fields.get(field) {
                Some(Value::Int(n)) => *n,
                other => panic!("expected int for {field}, got: {other:?}"),
            };
            (
                get("aimed_magic"),
                get("breath"),
                get("death_paralysis_poison"),
                get("petrification_polymorph"),
                get("spells"),
            )
        }
        other => panic!("expected SavingThrows struct, got: {other:?}"),
    }
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

// ── Fighter saves ──────────────────────────────────────────────

#[test]
fn fighter_level_0_saves() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let saves = get_saves(&interp, &state, &mut handler, "Fighter", 0);
    assert_eq!(saves, (18, 20, 16, 17, 19));
}

#[test]
fn fighter_level_1_saves() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let saves = get_saves(&interp, &state, &mut handler, "Fighter", 1);
    assert_eq!(saves, (16, 17, 14, 15, 17));
}

#[test]
fn fighter_level_7_saves() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let saves = get_saves(&interp, &state, &mut handler, "Fighter", 7);
    assert_eq!(saves, (12, 12, 10, 11, 13));
}

#[test]
fn fighter_level_13_saves() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let saves = get_saves(&interp, &state, &mut handler, "Fighter", 13);
    assert_eq!(saves, (7, 5, 5, 6, 8));
}

#[test]
fn fighter_level_19_saves() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Wildcard tier (19+)
    let saves = get_saves(&interp, &state, &mut handler, "Fighter", 19);
    assert_eq!(saves, (4, 3, 2, 3, 5));
}

// ── Paladin saves ──────────────────────────────────────────────

#[test]
fn paladin_level_1_saves() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let saves = get_saves(&interp, &state, &mut handler, "Paladin", 1);
    assert_eq!(saves, (14, 15, 12, 13, 15));
}

#[test]
fn paladin_level_9_saves() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let saves = get_saves(&interp, &state, &mut handler, "Paladin", 9);
    assert_eq!(saves, (8, 7, 6, 7, 9));
}

#[test]
fn paladin_level_19_saves() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let saves = get_saves(&interp, &state, &mut handler, "Paladin", 19);
    assert_eq!(saves, (2, 2, 2, 2, 3));
}

// ── Cleric saves ───────────────────────────────────────────────

#[test]
fn cleric_level_1_saves() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let saves = get_saves(&interp, &state, &mut handler, "Cleric", 1);
    assert_eq!(saves, (14, 16, 10, 13, 15));
}

#[test]
fn cleric_level_7_saves() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let saves = get_saves(&interp, &state, &mut handler, "Cleric", 7);
    assert_eq!(saves, (11, 13, 7, 10, 12));
}

#[test]
fn cleric_level_16_saves() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let saves = get_saves(&interp, &state, &mut handler, "Cleric", 16);
    assert_eq!(saves, (8, 10, 4, 7, 9));
}

#[test]
fn cleric_level_19_saves() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Wildcard tier (19+)
    let saves = get_saves(&interp, &state, &mut handler, "Cleric", 19);
    assert_eq!(saves, (6, 8, 2, 5, 7));
}

// ── Druid saves ────────────────────────────────────────────────

#[test]
fn druid_level_1_saves() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let saves = get_saves(&interp, &state, &mut handler, "Druid", 1);
    assert_eq!(saves, (14, 16, 10, 13, 15));
}

#[test]
fn druid_level_10_saves() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let saves = get_saves(&interp, &state, &mut handler, "Druid", 10);
    assert_eq!(saves, (10, 12, 6, 9, 11));
}

#[test]
fn druid_level_13_saves() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Wildcard tier (13+)
    let saves = get_saves(&interp, &state, &mut handler, "Druid", 13);
    assert_eq!(saves, (9, 11, 5, 8, 10));
}

// ── Thief saves ────────────────────────────────────────────────

#[test]
fn thief_level_1_saves() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let saves = get_saves(&interp, &state, &mut handler, "Thief", 1);
    assert_eq!(saves, (14, 16, 13, 12, 15));
}

#[test]
fn thief_level_5_saves() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let saves = get_saves(&interp, &state, &mut handler, "Thief", 5);
    assert_eq!(saves, (12, 15, 12, 11, 13));
}

#[test]
fn thief_level_9_saves() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let saves = get_saves(&interp, &state, &mut handler, "Thief", 9);
    assert_eq!(saves, (10, 14, 11, 10, 11));
}

#[test]
fn thief_level_13_saves() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // 13-16 tier
    let saves = get_saves(&interp, &state, &mut handler, "Thief", 13);
    assert_eq!(saves, (8, 13, 10, 9, 9));
}

#[test]
fn thief_level_17_saves() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Wildcard tier (17+)
    let saves = get_saves(&interp, &state, &mut handler, "Thief", 17);
    assert_eq!(saves, (6, 12, 9, 8, 7));
}

// ── Magic-User saves ───────────────────────────────────────────

#[test]
fn magic_user_level_1_saves() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let saves = get_saves(&interp, &state, &mut handler, "MagicUser", 1);
    assert_eq!(saves, (11, 15, 14, 13, 12));
}

#[test]
fn magic_user_level_6_saves() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let saves = get_saves(&interp, &state, &mut handler, "MagicUser", 6);
    assert_eq!(saves, (9, 13, 13, 11, 10));
}

#[test]
fn magic_user_level_11_saves() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let saves = get_saves(&interp, &state, &mut handler, "MagicUser", 11);
    assert_eq!(saves, (7, 11, 11, 9, 8));
}

#[test]
fn magic_user_level_16_saves() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Wildcard tier (16+)
    let saves = get_saves(&interp, &state, &mut handler, "MagicUser", 16);
    assert_eq!(saves, (5, 9, 10, 7, 6));
}

// ── Illusionist saves ──────────────────────────────────────────

#[test]
fn illusionist_level_1_saves() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let saves = get_saves(&interp, &state, &mut handler, "Illusionist", 1);
    assert_eq!(saves, (11, 15, 14, 13, 12));
}

#[test]
fn illusionist_level_6_saves() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let saves = get_saves(&interp, &state, &mut handler, "Illusionist", 6);
    assert_eq!(saves, (9, 13, 13, 11, 10));
}

#[test]
fn illusionist_level_11_saves() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let saves = get_saves(&interp, &state, &mut handler, "Illusionist", 11);
    assert_eq!(saves, (7, 11, 11, 9, 8));
}

// ── Monk saves ─────────────────────────────────────────────────

#[test]
fn monk_level_1_saves() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let saves = get_saves(&interp, &state, &mut handler, "Monk", 1);
    assert_eq!(saves, (14, 16, 13, 12, 15));
}

#[test]
fn monk_level_5_saves() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let saves = get_saves(&interp, &state, &mut handler, "Monk", 5);
    assert_eq!(saves, (12, 15, 12, 11, 13));
}

#[test]
fn monk_level_13_saves() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let saves = get_saves(&interp, &state, &mut handler, "Monk", 13);
    assert_eq!(saves, (8, 13, 10, 9, 9));
}

#[test]
fn monk_level_17_saves() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Wildcard tier (17+)
    let saves = get_saves(&interp, &state, &mut handler, "Monk", 17);
    assert_eq!(saves, (6, 12, 9, 8, 7));
}

// ── Dispatch: saving_throws_for routes correctly ───────────────

#[test]
fn dispatch_ranger_uses_fighter_table() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let ranger = get_saves(&interp, &state, &mut handler, "Ranger", 1);
    let fighter = get_saves(&interp, &state, &mut handler, "Fighter", 1);
    assert_eq!(ranger, fighter, "Ranger should use fighter_saves table");
}

#[test]
fn dispatch_assassin_uses_thief_table() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let assassin = get_saves(&interp, &state, &mut handler, "Assassin", 5);
    let thief = get_saves(&interp, &state, &mut handler, "Thief", 5);
    assert_eq!(assassin, thief, "Assassin should use thief_saves table");
}

#[test]
fn dispatch_all_ten_classes() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let classes = [
        "Fighter",
        "Paladin",
        "Ranger",
        "Cleric",
        "Druid",
        "Thief",
        "Assassin",
        "MagicUser",
        "Illusionist",
        "Monk",
    ];
    for class in &classes {
        let saves = get_saves(&interp, &state, &mut handler, class, 1);
        // All 5 save values should be positive
        assert!(saves.0 > 0, "{class} aimed_magic should be > 0");
        assert!(saves.1 > 0, "{class} breath should be > 0");
        assert!(saves.2 > 0, "{class} death should be > 0");
        assert!(saves.3 > 0, "{class} petrification should be > 0");
        assert!(saves.4 > 0, "{class} spells should be > 0");
    }
}

// ── Level boundary transitions ─────────────────────────────────

#[test]
fn fighter_tier_boundary_at_level_3() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let level_2 = get_saves(&interp, &state, &mut handler, "Fighter", 2);
    let level_3 = get_saves(&interp, &state, &mut handler, "Fighter", 3);
    // Level 2 → tier 1..=2, level 3 → tier 3..=4
    assert_eq!(level_2, (16, 17, 14, 15, 17));
    assert_eq!(level_3, (15, 16, 13, 14, 16));
    assert_ne!(level_2, level_3, "saves should change at level 3 boundary");
}

#[test]
fn thief_tier_boundary_at_level_5() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let level_4 = get_saves(&interp, &state, &mut handler, "Thief", 4);
    let level_5 = get_saves(&interp, &state, &mut handler, "Thief", 5);
    assert_eq!(level_4, (14, 16, 13, 12, 15));
    assert_eq!(level_5, (12, 15, 12, 11, 13));
    assert_ne!(level_4, level_5, "saves should change at level 5 boundary");
}

#[test]
fn cleric_tier_boundary_at_level_4() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let level_3 = get_saves(&interp, &state, &mut handler, "Cleric", 3);
    let level_4 = get_saves(&interp, &state, &mut handler, "Cleric", 4);
    assert_eq!(level_3, (14, 16, 10, 13, 15));
    assert_eq!(level_4, (13, 15, 9, 12, 14));
    assert_ne!(level_3, level_4, "saves should change at level 4 boundary");
}

#[test]
fn magic_user_tier_boundary_at_level_6() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let level_5 = get_saves(&interp, &state, &mut handler, "MagicUser", 5);
    let level_6 = get_saves(&interp, &state, &mut handler, "MagicUser", 6);
    assert_eq!(level_5, (11, 15, 14, 13, 12));
    assert_eq!(level_6, (9, 13, 13, 11, 10));
    assert_ne!(level_5, level_6, "saves should change at level 6 boundary");
}

// ── Paladin vs Fighter: Paladin has better saves ───────────────

#[test]
fn paladin_saves_are_better_than_fighter() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let paladin = get_saves(&interp, &state, &mut handler, "Paladin", 1);
    let fighter = get_saves(&interp, &state, &mut handler, "Fighter", 1);
    // Lower is better for saving throws — Paladin should be <= Fighter in all categories
    assert!(
        paladin.0 <= fighter.0,
        "Paladin aimed_magic should be <= Fighter"
    );
    assert!(
        paladin.1 <= fighter.1,
        "Paladin breath should be <= Fighter"
    );
    assert!(paladin.2 <= fighter.2, "Paladin death should be <= Fighter");
    assert!(
        paladin.3 <= fighter.3,
        "Paladin petrification should be <= Fighter"
    );
    assert!(
        paladin.4 <= fighter.4,
        "Paladin spells should be <= Fighter"
    );
}

// ── Saves improve with level ───────────────────────────────────

#[test]
fn fighter_saves_improve_with_level() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let low = get_saves(&interp, &state, &mut handler, "Fighter", 1);
    let high = get_saves(&interp, &state, &mut handler, "Fighter", 17);
    // Lower is better — high level saves should be strictly lower
    assert!(high.0 < low.0, "aimed_magic should improve");
    assert!(high.1 < low.1, "breath should improve");
    assert!(high.2 < low.2, "death should improve");
    assert!(high.3 < low.3, "petrification should improve");
    assert!(high.4 < low.4, "spells should improve");
}

#[test]
fn cleric_saves_improve_with_level() {
    let (program, result) = compile_osric_saves();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let low = get_saves(&interp, &state, &mut handler, "Cleric", 1);
    let high = get_saves(&interp, &state, &mut handler, "Cleric", 16);
    assert!(high.0 < low.0, "aimed_magic should improve");
    assert!(high.1 < low.1, "breath should improve");
    assert!(high.2 < low.2, "death should improve");
    assert!(high.3 < low.3, "petrification should improve");
    assert!(high.4 < low.4, "spells should improve");
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

// ── make_saving_throw mechanic ─────────────────────────────────

fn save_category(variant: &str) -> Value {
    enum_variant("SaveCategory", variant)
}

/// Helper: call make_saving_throw with a scripted d20 roll.
fn call_make_saving_throw(
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

    let responses = vec![scripted_roll(
        1,
        20,
        0,
        vec![d20_roll],
        vec![d20_roll],
        d20_roll,
        d20_roll,
    )];
    let mut handler = ScriptedHandler::with_responses(responses);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "make_saving_throw",
            vec![
                Value::Entity(saver),
                save_category(category),
                Value::Int(bonus),
                Value::Bool(is_mental),
            ],
        )
        .unwrap_or_else(|e| panic!("make_saving_throw failed: {e}"));

    expect_bool(val, "make_saving_throw")
}

#[test]
fn make_saving_throw_passes_on_high_roll() {
    // Human Fighter L1, death target 14, roll 16 → pass
    let result = call_make_saving_throw(
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
fn make_saving_throw_fails_on_low_roll() {
    // Human Fighter L1, death target 14, roll 5 → fail
    let result = call_make_saving_throw(
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
fn make_saving_throw_natural_1_always_fails() {
    // Human Fighter L19, death target 2, roll 1 → fail (natural 1)
    let result = call_make_saving_throw(
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
fn make_saving_throw_stalwart_bonus_applies() {
    // Dwarf Fighter L1 CON 14 (+4 stalwart), death target 14, effective 10, roll 11 → pass
    let abilities: Vec<(&str, i64)> = vec![
        ("STR", 10),
        ("DEX", 10),
        ("CON", 14),
        ("INT", 10),
        ("WIS", 10),
        ("CHA", 10),
    ];
    let result = call_make_saving_throw(
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
fn make_saving_throw_stalwart_no_effect_on_breath() {
    // Dwarf Fighter L1 CON 14, breath target 17, no stalwart on breath, roll 11 → fail
    let abilities: Vec<(&str, i64)> = vec![
        ("STR", 10),
        ("DEX", 10),
        ("CON", 14),
        ("INT", 10),
        ("WIS", 10),
        ("CHA", 10),
    ];
    let result = call_make_saving_throw(
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
fn make_saving_throw_no_stalwart_for_human() {
    // Human Fighter L1 CON 14, death target 14, no stalwart, roll 11 → fail
    let abilities: Vec<(&str, i64)> = vec![
        ("STR", 10),
        ("DEX", 10),
        ("CON", 14),
        ("INT", 10),
        ("WIS", 10),
        ("CHA", 10),
    ];
    let result = call_make_saving_throw(
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
fn make_saving_throw_mental_bonus_applies() {
    // Human Cleric L1 WIS 17 (+3 mental), spells target 15, effective 12, roll 12 → pass
    let abilities: Vec<(&str, i64)> = vec![
        ("STR", 10),
        ("DEX", 10),
        ("CON", 10),
        ("INT", 10),
        ("WIS", 17),
        ("CHA", 10),
    ];
    let result = call_make_saving_throw(
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
fn make_saving_throw_bonus_param_stacks() {
    // Human Fighter L1, death target 14, bonus 3, effective 11, roll 12 → pass
    let result = call_make_saving_throw(
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
