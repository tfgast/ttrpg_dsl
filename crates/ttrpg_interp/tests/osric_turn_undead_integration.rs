//! OSRIC Turn Undead integration test.
//!
//! Verifies that osric/osric_turn_undead.ttrpg parses, lowers, and type-checks
//! through the full multi-file pipeline. Exercises the turn_undead_table,
//! effective_turning_level, alignment helpers, and resolve_turn_undead mechanic.

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

mod osric_common;
use osric_common::*;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_turn_undead() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

fn get_turn_undead_decls(program: &ttrpg_ast::ast::Program) -> &[ttrpg_ast::Spanned<DeclKind>] {
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSRIC Turn Undead" {
                return &sys.decls;
            }
        }
    }
    panic!("no system block named 'OSRIC Turn Undead' found");
}

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn osric_turn_undead_parses_and_typechecks() {
    let (program, _) = compile_osric_turn_undead();
    let has_system = program.items.iter().any(|item| {
        matches!(&item.node, TopLevel::System(sys) if sys.name == "OSRIC Turn Undead")
    });
    assert!(has_system, "expected system named 'OSRIC Turn Undead'");
}

// ── Structure verification ─────────────────────────────────────

#[test]
fn has_expected_enums() {
    let (program, _) = compile_osric_turn_undead();
    let decls = get_turn_undead_decls(&program);
    let enums: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Enum(e) => Some(e.name.to_string()),
            _ => None,
        })
        .collect();
    assert!(enums.contains(&"TurnOutcome".to_string()));
}

#[test]
fn has_expected_tables() {
    let (program, _) = compile_osric_turn_undead();
    let decls = get_turn_undead_decls(&program);
    let tables: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Table(t) => Some(t.name.to_string()),
            _ => None,
        })
        .collect();
    assert!(
        tables.contains(&"turn_undead_table".to_string()),
        "missing turn_undead_table, got: {tables:?}"
    );
}

#[test]
fn has_expected_derives() {
    let (program, _) = compile_osric_turn_undead();
    let decls = get_turn_undead_decls(&program);
    let derives: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Derive(d) => Some(d.name.to_string()),
            _ => None,
        })
        .collect();
    for expected in [
        "is_evil_alignment",
        "effective_turning_level",
        "character_can_turn",
    ] {
        assert!(
            derives.contains(&expected.to_string()),
            "missing derive: {expected}, got: {derives:?}"
        );
    }
}

#[test]
fn has_expected_mechanics() {
    let (program, _) = compile_osric_turn_undead();
    let decls = get_turn_undead_decls(&program);
    let mechanics: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Mechanic(m) => Some(m.name.to_string()),
            _ => None,
        })
        .collect();
    for expected in [
        "resolve_turn_undead",
        "roll_number_turned",
        "roll_number_destroyed",
        "roll_number_destroyed_star",
        "evil_control_check",
    ] {
        assert!(
            mechanics.contains(&expected.to_string()),
            "missing mechanic: {expected}, got: {mechanics:?}"
        );
    }
}

#[test]
fn has_turn_undead_action() {
    let (program, _) = compile_osric_turn_undead();
    let decls = get_turn_undead_decls(&program);
    let actions: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Action(a) => Some(a.name.to_string()),
            _ => None,
        })
        .collect();
    assert!(
        actions.contains(&"TurnUndeadAction".to_string()),
        "missing TurnUndeadAction, got: {actions:?}"
    );
}

// ── Table spot checks ──────────────────────────────────────────

#[test]
fn turn_undead_table_skeleton_level_1() {
    let (program, result) = compile_osric_turn_undead();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Type 1 (Skeleton), level 1 => 10
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "turn_undead_table",
            vec![Value::Int(1), Value::Int(1)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(10));
}

#[test]
fn turn_undead_table_skeleton_level_4_auto_turn() {
    let (program, result) = compile_osric_turn_undead();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Type 1, level 4 => 0 (T)
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "turn_undead_table",
            vec![Value::Int(1), Value::Int(4)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(0));
}

#[test]
fn turn_undead_table_skeleton_level_6_destroy() {
    let (program, result) = compile_osric_turn_undead();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Type 1, level 6 => -2 (D)
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "turn_undead_table",
            vec![Value::Int(1), Value::Int(6)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(-2));
}

#[test]
fn turn_undead_table_skeleton_level_8_destroy_star() {
    let (program, result) = compile_osric_turn_undead();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Type 1, level 8 => -3 (D*)
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "turn_undead_table",
            vec![Value::Int(1), Value::Int(8)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(-3));
}

#[test]
fn turn_undead_table_fiend_impossible_level_7() {
    let (program, result) = compile_osric_turn_undead();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Type 13 (Fiend), level 7 => -1 (impossible)
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "turn_undead_table",
            vec![Value::Int(13), Value::Int(7)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(-1));
}

#[test]
fn turn_undead_table_vampire_level_19() {
    let (program, result) = compile_osric_turn_undead();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Type 10 (Vampire), level 19+ => 4
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "turn_undead_table",
            vec![Value::Int(10), Value::Int(19)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(4));
}

#[test]
fn turn_undead_table_wraith_level_9() {
    let (program, result) = compile_osric_turn_undead();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Type 7 (Wraith), level 9 => 0 (T)
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "turn_undead_table",
            vec![Value::Int(7), Value::Int(9)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(0));
}

// ── Alignment helper ───────────────────────────────────────────

#[test]
fn is_evil_alignment_checks() {
    let (program, result) = compile_osric_turn_undead();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    for (variant, expected) in [
        ("LawfulEvil", true),
        ("NeutralEvil", true),
        ("ChaoticEvil", true),
        ("LawfulGood", false),
        ("TrueNeutral", false),
        ("ChaoticGood", false),
    ] {
        let val = interp
            .evaluate_derive(
                &state,
                &mut handler,
                "is_evil_alignment",
                vec![enum_variant("Alignment", variant)],
            )
            .unwrap();
        assert_eq!(
            val,
            Value::Bool(expected),
            "is_evil_alignment({variant})"
        );
    }
}

// ── Effective turning level ────────────────────────────────────

#[test]
fn effective_turning_level_cleric() {
    let (program, result) = compile_osric_turn_undead();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // Level 5 cleric => effective level 5
    let char_ref = make_turner(&mut state, "Brother Marcus", "Cleric", 5, "TrueNeutral");
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "effective_turning_level",
            vec![Value::Entity(char_ref)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(5));
}

#[test]
fn effective_turning_level_paladin() {
    let (program, result) = compile_osric_turn_undead();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // Level 5 paladin => effective level 3 (5 - 2)
    let char_ref = make_turner(&mut state, "Sir Galahad", "Paladin", 5, "LawfulGood");
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "effective_turning_level",
            vec![Value::Entity(char_ref)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(3));
}

#[test]
fn effective_turning_level_paladin_min() {
    let (program, result) = compile_osric_turn_undead();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // Level 1 paladin => effective level 1 (min, not -1)
    let char_ref = make_turner(&mut state, "Sir Newbie", "Paladin", 1, "LawfulGood");
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "effective_turning_level",
            vec![Value::Entity(char_ref)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(1));
}

// ── Resolve turn undead mechanic ───────────────────────────────

#[test]
fn resolve_turn_undead_impossible() {
    let (program, result) = compile_osric_turn_undead();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    // Level 1 cleric vs Type 6 (Ghast) => impossible (code -1)
    let char_ref = make_turner(&mut state, "Cleric", "Cleric", 1, "TrueNeutral");

    let mut handler = ScriptedHandler::with_responses(vec![]);
    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "resolve_turn_undead",
            vec![
                Value::Entity(char_ref),
                Value::Int(6),
                Value::Bool(false),
            ],
        )
        .unwrap();

    match &val {
        Value::EnumVariant { variant, .. } => assert_eq!(&**variant, "Impossible"),
        other => panic!("expected TurnOutcome.Impossible, got: {other:?}"),
    }
}

#[test]
fn resolve_turn_undead_auto_turn() {
    let (program, result) = compile_osric_turn_undead();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    // Level 4 cleric vs Type 1 (Skeleton) => auto-turn (code 0)
    let char_ref = make_turner(&mut state, "Cleric", "Cleric", 4, "TrueNeutral");

    let responses = vec![
        // 2d6 for number turned = 7
        scripted_roll(2, 6, 0, vec![3, 4], vec![3, 4], 7, 7),
    ];
    let mut handler = ScriptedHandler::with_responses(responses);
    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "resolve_turn_undead",
            vec![
                Value::Entity(char_ref),
                Value::Int(1),
                Value::Bool(false),
            ],
        )
        .unwrap();

    match &val {
        Value::EnumVariant {
            variant, fields, ..
        } => {
            assert_eq!(&**variant, "Turned");
            assert_eq!(fields.get("number_affected"), Some(&Value::Int(7)));
        }
        other => panic!("expected TurnOutcome.Turned, got: {other:?}"),
    }
}

#[test]
fn resolve_turn_undead_number_roll_success() {
    let (program, result) = compile_osric_turn_undead();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    // Level 1 cleric vs Type 1 (Skeleton) => need 10+ on d20
    let char_ref = make_turner(&mut state, "Cleric", "Cleric", 1, "TrueNeutral");

    let responses = vec![
        // d20 roll = 15 (success, >= 10)
        scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15),
        // 2d6 for number turned = 5
        scripted_roll(2, 6, 0, vec![2, 3], vec![2, 3], 5, 5),
    ];
    let mut handler = ScriptedHandler::with_responses(responses);
    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "resolve_turn_undead",
            vec![
                Value::Entity(char_ref),
                Value::Int(1),
                Value::Bool(false),
            ],
        )
        .unwrap();

    match &val {
        Value::EnumVariant {
            variant, fields, ..
        } => {
            assert_eq!(&**variant, "Turned");
            assert_eq!(fields.get("number_affected"), Some(&Value::Int(5)));
        }
        other => panic!("expected TurnOutcome.Turned, got: {other:?}"),
    }
}

#[test]
fn resolve_turn_undead_number_roll_failure() {
    let (program, result) = compile_osric_turn_undead();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    // Level 1 cleric vs Type 1 (Skeleton) => need 10+ on d20
    let char_ref = make_turner(&mut state, "Cleric", "Cleric", 1, "TrueNeutral");

    let responses = vec![
        // d20 roll = 5 (failure, < 10)
        scripted_roll(1, 20, 0, vec![5], vec![5], 5, 5),
    ];
    let mut handler = ScriptedHandler::with_responses(responses);
    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "resolve_turn_undead",
            vec![
                Value::Entity(char_ref),
                Value::Int(1),
                Value::Bool(false),
            ],
        )
        .unwrap();

    match &val {
        Value::EnumVariant { variant, .. } => assert_eq!(&**variant, "Failed"),
        other => panic!("expected TurnOutcome.Failed, got: {other:?}"),
    }
}

#[test]
fn resolve_turn_undead_destroy_good_cleric() {
    let (program, result) = compile_osric_turn_undead();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    // Level 6 good cleric vs Type 1 (Skeleton) => D (code -2) => Destroyed
    let char_ref = make_turner(&mut state, "Good Cleric", "Cleric", 6, "LawfulGood");

    let responses = vec![
        // 2d6 for number destroyed = 8
        scripted_roll(2, 6, 0, vec![3, 5], vec![3, 5], 8, 8),
    ];
    let mut handler = ScriptedHandler::with_responses(responses);
    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "resolve_turn_undead",
            vec![
                Value::Entity(char_ref),
                Value::Int(1),
                Value::Bool(false),
            ],
        )
        .unwrap();

    match &val {
        Value::EnumVariant {
            variant, fields, ..
        } => {
            assert_eq!(&**variant, "Destroyed");
            assert_eq!(fields.get("number_affected"), Some(&Value::Int(8)));
        }
        other => panic!("expected TurnOutcome.Destroyed, got: {other:?}"),
    }
}

#[test]
fn resolve_turn_undead_evil_cleric_controlled() {
    let (program, result) = compile_osric_turn_undead();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    // Level 6 evil cleric vs Type 1 (Skeleton) => D (code -2)
    // Evil: d100 check, roll 75 (>= 61) => Controlled
    let char_ref = make_turner(&mut state, "Evil Cleric", "Cleric", 6, "ChaoticEvil");

    let responses = vec![
        // 2d6 for number affected = 6
        scripted_roll(2, 6, 0, vec![2, 4], vec![2, 4], 6, 6),
        // d100 control check = 75 (>= 61, controlled)
        scripted_roll(1, 100, 0, vec![75], vec![75], 75, 75),
    ];
    let mut handler = ScriptedHandler::with_responses(responses);
    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "resolve_turn_undead",
            vec![
                Value::Entity(char_ref),
                Value::Int(1),
                Value::Bool(false),
            ],
        )
        .unwrap();

    match &val {
        Value::EnumVariant {
            variant, fields, ..
        } => {
            assert_eq!(&**variant, "Controlled");
            assert_eq!(fields.get("number_affected"), Some(&Value::Int(6)));
        }
        other => panic!("expected TurnOutcome.Controlled, got: {other:?}"),
    }
}

#[test]
fn resolve_turn_undead_evil_cleric_not_controlled() {
    let (program, result) = compile_osric_turn_undead();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    // Level 6 evil cleric vs Type 1 (Skeleton) => D (code -2)
    // Evil: d100 check, roll 30 (< 61) => NotControlled
    let char_ref = make_turner(&mut state, "Evil Cleric", "Cleric", 6, "NeutralEvil");

    let responses = vec![
        // 2d6 for number affected = 4
        scripted_roll(2, 6, 0, vec![1, 3], vec![1, 3], 4, 4),
        // d100 control check = 30 (< 61, not controlled)
        scripted_roll(1, 100, 0, vec![30], vec![30], 30, 30),
    ];
    let mut handler = ScriptedHandler::with_responses(responses);
    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "resolve_turn_undead",
            vec![
                Value::Entity(char_ref),
                Value::Int(1),
                Value::Bool(false),
            ],
        )
        .unwrap();

    match &val {
        Value::EnumVariant {
            variant, fields, ..
        } => {
            assert_eq!(&**variant, "NotControlled");
            assert_eq!(fields.get("number_affected"), Some(&Value::Int(4)));
        }
        other => panic!("expected TurnOutcome.NotControlled, got: {other:?}"),
    }
}

#[test]
fn resolve_turn_undead_destroy_star_fiend() {
    let (program, result) = compile_osric_turn_undead();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    // Level 8 good cleric vs Type 1 (Skeleton) => D* (code -3)
    // Fiend/paladin target: 1d2 affected
    let char_ref = make_turner(&mut state, "Good Cleric", "Cleric", 8, "LawfulGood");

    let responses = vec![
        // 1d2 for fiend/paladin target = 1
        scripted_roll(1, 2, 0, vec![1], vec![1], 1, 1),
    ];
    let mut handler = ScriptedHandler::with_responses(responses);
    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "resolve_turn_undead",
            vec![
                Value::Entity(char_ref),
                Value::Int(1),
                Value::Bool(true), // is_fiend_or_paladin
            ],
        )
        .unwrap();

    match &val {
        Value::EnumVariant {
            variant, fields, ..
        } => {
            assert_eq!(&**variant, "Destroyed");
            assert_eq!(fields.get("number_affected"), Some(&Value::Int(1)));
        }
        other => panic!("expected TurnOutcome.Destroyed, got: {other:?}"),
    }
}
