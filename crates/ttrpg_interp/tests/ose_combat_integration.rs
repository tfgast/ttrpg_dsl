//! OSE combat & morale integration test.
//!
//! Verifies that ose/ose_combat.ttrpg parses, lowers, and type-checks
//! through the full multi-file pipeline. Tests monster THAC0 table lookups,
//! target number derives, AC calculation, missile range modifiers, and
//! reaction roll interpretation at runtime.

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_ast::diagnostic::Severity;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

// ── Compile helpers ────────────────────────────────────────────

/// Compile core + combat files through the multi-file pipeline.
fn compile_ose_combat() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    let core_source = include_str!("../../../ose/ose_core.ttrpg");
    let combat_source = include_str!("../../../ose/ose_combat.ttrpg");

    let sources = vec![
        ("ose/ose_core.ttrpg".to_string(), core_source.to_string()),
        ("ose/ose_combat.ttrpg".to_string(), combat_source.to_string()),
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

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn ose_combat_parses_and_typechecks() {
    let (program, _) = compile_ose_combat();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSE"));
}

// ── Declaration structure ──────────────────────────────────────

#[test]
fn ose_combat_has_expected_declarations() {
    let (program, _) = compile_ose_combat();

    let mut mechanic_names = Vec::new();
    let mut derive_names = Vec::new();

    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSE" {
                for decl in &sys.decls {
                    match &decl.node {
                        DeclKind::Mechanic(f) => mechanic_names.push(f.name.as_str()),
                        DeclKind::Derive(f) => derive_names.push(f.name.as_str()),
                        _ => {}
                    }
                }
            }
        }
    }

    // monster_thac0 is a derive (not a table — 1D lookups use match)
    assert!(derive_names.contains(&"monster_thac0"), "expected monster_thac0 derive");

    // Mechanics
    assert!(mechanic_names.contains(&"attack_roll"), "expected attack_roll mechanic");
    assert!(mechanic_names.contains(&"morale_check"), "expected morale_check mechanic");
    assert!(mechanic_names.contains(&"reaction_roll"), "expected reaction_roll mechanic");

    // Derives
    assert!(derive_names.contains(&"target_number"), "expected target_number derive");
    assert!(derive_names.contains(&"missile_range_modifier"), "expected missile_range_modifier derive");
    assert!(derive_names.contains(&"is_in_range"), "expected is_in_range derive");
    assert!(derive_names.contains(&"calc_ac"), "expected calc_ac derive");
    assert!(derive_names.contains(&"reaction_hostile"), "expected reaction_hostile derive");
    assert!(derive_names.contains(&"reaction_unfriendly"), "expected reaction_unfriendly derive");
    assert!(derive_names.contains(&"reaction_neutral"), "expected reaction_neutral derive");
    assert!(derive_names.contains(&"reaction_indifferent"), "expected reaction_indifferent derive");
    assert!(derive_names.contains(&"reaction_friendly"), "expected reaction_friendly derive");
}

// ── Monster THAC0 derive structure ─────────────────────────────

#[test]
fn ose_combat_thac0_derive_exists() {
    let (program, _) = compile_ose_combat();

    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSE" {
                for decl in &sys.decls {
                    if let DeclKind::Derive(f) = &decl.node {
                        if f.name == "monster_thac0" {
                            assert_eq!(f.params.len(), 1, "monster_thac0 takes 1 param (hd)");
                            return;
                        }
                    }
                }
            }
        }
    }
    panic!("monster_thac0 derive not found");
}

// ── Runtime: monster THAC0 lookups ─────────────────────────────

#[test]
fn monster_thac0_normal_human() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // 0 HD (normal human) → THAC0 20
    let thac0 = interp
        .evaluate_derive(&state, &mut handler, "monster_thac0", vec![Value::Int(0)])
        .unwrap();
    assert_eq!(thac0, Value::Int(20));
}

#[test]
fn monster_thac0_low_hd() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // 1-3 HD → THAC0 19
    for hd in [1, 2, 3] {
        let thac0 = interp
            .evaluate_derive(&state, &mut handler, "monster_thac0", vec![Value::Int(hd)])
            .unwrap();
        assert_eq!(thac0, Value::Int(19), "HD {} should have THAC0 19", hd);
    }
}

#[test]
fn monster_thac0_mid_hd() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // 4-6 HD → THAC0 17
    for hd in [4, 5, 6] {
        let thac0 = interp
            .evaluate_derive(&state, &mut handler, "monster_thac0", vec![Value::Int(hd)])
            .unwrap();
        assert_eq!(thac0, Value::Int(17), "HD {} should have THAC0 17", hd);
    }

    // 7-9 HD → THAC0 14
    for hd in [7, 8, 9] {
        let thac0 = interp
            .evaluate_derive(&state, &mut handler, "monster_thac0", vec![Value::Int(hd)])
            .unwrap();
        assert_eq!(thac0, Value::Int(14), "HD {} should have THAC0 14", hd);
    }
}

#[test]
fn monster_thac0_high_hd() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // 10-12 HD → THAC0 12
    let thac0 = interp
        .evaluate_derive(&state, &mut handler, "monster_thac0", vec![Value::Int(10)])
        .unwrap();
    assert_eq!(thac0, Value::Int(12));

    // 13-15 HD → THAC0 10
    let thac0 = interp
        .evaluate_derive(&state, &mut handler, "monster_thac0", vec![Value::Int(13)])
        .unwrap();
    assert_eq!(thac0, Value::Int(10));

    // 16-18 HD → THAC0 8
    let thac0 = interp
        .evaluate_derive(&state, &mut handler, "monster_thac0", vec![Value::Int(16)])
        .unwrap();
    assert_eq!(thac0, Value::Int(8));

    // 19+ HD → THAC0 6
    let thac0 = interp
        .evaluate_derive(&state, &mut handler, "monster_thac0", vec![Value::Int(19)])
        .unwrap();
    assert_eq!(thac0, Value::Int(6));
}

// ── Runtime: target number ─────────────────────────────────────

#[test]
fn target_number_unarmoured() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // THAC0 19 vs AC 9 (unarmoured) = need 10
    let tn = interp
        .evaluate_derive(&state, &mut handler, "target_number", vec![Value::Int(19), Value::Int(9)])
        .unwrap();
    assert_eq!(tn, Value::Int(10));
}

#[test]
fn target_number_chain_mail() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // THAC0 19 vs AC 5 (chain mail) = need 14
    let tn = interp
        .evaluate_derive(&state, &mut handler, "target_number", vec![Value::Int(19), Value::Int(5)])
        .unwrap();
    assert_eq!(tn, Value::Int(14));
}

#[test]
fn target_number_plate_and_shield() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // THAC0 19 vs AC 2 (plate + shield) = need 17
    let tn = interp
        .evaluate_derive(&state, &mut handler, "target_number", vec![Value::Int(19), Value::Int(2)])
        .unwrap();
    assert_eq!(tn, Value::Int(17));
}

// ── Runtime: AC calculation ────────────────────────────────────

#[test]
fn calc_ac_unarmoured() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // No armour (AC 9), no shield, no DEX mod
    let ac = interp
        .evaluate_derive(
            &state, &mut handler, "calc_ac",
            vec![Value::Int(9), Value::Bool(false), Value::Int(0)],
        )
        .unwrap();
    assert_eq!(ac, Value::Int(9));
}

#[test]
fn calc_ac_chain_with_shield() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Chain mail (AC 5), with shield (-1), no DEX mod
    let ac = interp
        .evaluate_derive(
            &state, &mut handler, "calc_ac",
            vec![Value::Int(5), Value::Bool(true), Value::Int(0)],
        )
        .unwrap();
    assert_eq!(ac, Value::Int(4));
}

#[test]
fn calc_ac_leather_with_dex_bonus() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Leather (AC 7), no shield, DEX mod +1 (improves AC by 1 in descending)
    let ac = interp
        .evaluate_derive(
            &state, &mut handler, "calc_ac",
            vec![Value::Int(7), Value::Bool(false), Value::Int(1)],
        )
        .unwrap();
    assert_eq!(ac, Value::Int(6));
}

// ── Runtime: missile range modifiers ───────────────────────────

#[test]
fn missile_short_range_bonus() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Short range → +1
    let modifier = interp
        .evaluate_derive(
            &state, &mut handler, "missile_range_modifier",
            vec![Value::Int(10), Value::Int(30), Value::Int(60), Value::Int(90)],
        )
        .unwrap();
    assert_eq!(modifier, Value::Int(1));
}

#[test]
fn missile_medium_range_no_modifier() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Medium range → 0
    let modifier = interp
        .evaluate_derive(
            &state, &mut handler, "missile_range_modifier",
            vec![Value::Int(45), Value::Int(30), Value::Int(60), Value::Int(90)],
        )
        .unwrap();
    assert_eq!(modifier, Value::Int(0));
}

#[test]
fn missile_long_range_penalty() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Long range → -1
    let modifier = interp
        .evaluate_derive(
            &state, &mut handler, "missile_range_modifier",
            vec![Value::Int(75), Value::Int(30), Value::Int(60), Value::Int(90)],
        )
        .unwrap();
    assert_eq!(modifier, Value::Int(-1));
}

// ── Runtime: reaction roll interpretation ──────────────────────

#[test]
fn reaction_hostile_check() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // 2 → hostile
    assert_eq!(
        interp.evaluate_derive(&state, &mut handler, "reaction_hostile", vec![Value::Int(2)]).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        interp.evaluate_derive(&state, &mut handler, "reaction_hostile", vec![Value::Int(3)]).unwrap(),
        Value::Bool(false)
    );
}

#[test]
fn reaction_unfriendly_check() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // 3-5 → unfriendly
    assert_eq!(
        interp.evaluate_derive(&state, &mut handler, "reaction_unfriendly", vec![Value::Int(4)]).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        interp.evaluate_derive(&state, &mut handler, "reaction_unfriendly", vec![Value::Int(6)]).unwrap(),
        Value::Bool(false)
    );
}

#[test]
fn reaction_neutral_check() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // 6-8 → neutral
    assert_eq!(
        interp.evaluate_derive(&state, &mut handler, "reaction_neutral", vec![Value::Int(7)]).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        interp.evaluate_derive(&state, &mut handler, "reaction_neutral", vec![Value::Int(9)]).unwrap(),
        Value::Bool(false)
    );
}

#[test]
fn reaction_friendly_check() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // 12+ → friendly
    assert_eq!(
        interp.evaluate_derive(&state, &mut handler, "reaction_friendly", vec![Value::Int(12)]).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        interp.evaluate_derive(&state, &mut handler, "reaction_friendly", vec![Value::Int(11)]).unwrap(),
        Value::Bool(false)
    );
}

// ── Runtime: is_in_range ───────────────────────────────────────

#[test]
fn is_in_range_checks() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // In range
    assert_eq!(
        interp.evaluate_derive(&state, &mut handler, "is_in_range", vec![Value::Int(50), Value::Int(90)]).unwrap(),
        Value::Bool(true)
    );
    // Out of range
    assert_eq!(
        interp.evaluate_derive(&state, &mut handler, "is_in_range", vec![Value::Int(100), Value::Int(90)]).unwrap(),
        Value::Bool(false)
    );
    // Zero distance (invalid)
    assert_eq!(
        interp.evaluate_derive(&state, &mut handler, "is_in_range", vec![Value::Int(0), Value::Int(90)]).unwrap(),
        Value::Bool(false)
    );
}
