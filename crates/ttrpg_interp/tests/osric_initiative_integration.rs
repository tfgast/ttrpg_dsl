//! OSRIC initiative integration test.
//!
//! Verifies that osric/osric_initiative.ttrpg parses, lowers, and type-checks
//! through the full multi-file pipeline (core + ability + class + equipment +
//! combat + initiative). Exercises OSRIC's most distinctive mechanic — the
//! 10-segment combat round with d6 group initiative. Tests surprise_duration,
//! free_surprise_segments, wrap_segment, action_segment for all DeclaredActionTypes,
//! missile_init_segment with DEX adj, assign_segment, fighter_attack_segments at
//! various levels, spell_effect_segment, is_casting_at_segment,
//! spell_completed_at_segment, acts_first_by_speed, melee_order, movement_per_segment,
//! movement_through_segment, roll_surprise, roll_initiative (seeded),
//! CastingSpell condition (modifies #attack_resolution), SpellInterruption hook
//! (fires on Damaged event while casting), and BeginCasting action.

use std::collections::BTreeMap;

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_ast::diagnostic::Severity;
use ttrpg_interp::adapter::StateAdapter;
use ttrpg_interp::effect::{Effect, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::{EntityRef, StateProvider};
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

mod osric_common;
use osric_common::*;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_initiative() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    let core_source = include_str!("../../../osric/osric_core.ttrpg");
    let ability_source = include_str!("../../../osric/osric_ability.ttrpg");
    let character_source = include_str!("../../../osric/osric_character.ttrpg");
    let class_source = include_str!("../../../osric/osric_class.ttrpg");
    let equipment_source = include_str!("../../../osric/osric_equipment.ttrpg");
    let conditions_source = include_str!("../../../osric/osric_conditions.ttrpg");
    let combat_source = include_str!("../../../osric/osric_combat.ttrpg");
    let initiative_source = include_str!("../../../osric/osric_initiative.ttrpg");

    let sources = vec![
        (
            "osric/osric_core.ttrpg".to_string(),
            core_source.to_string(),
        ),
        (
            "osric/osric_ability.ttrpg".to_string(),
            ability_source.to_string(),
        ),
        (
            "osric/osric_character.ttrpg".to_string(),
            character_source.to_string(),
        ),
        (
            "osric/osric_class.ttrpg".to_string(),
            class_source.to_string(),
        ),
        (
            "osric/osric_equipment.ttrpg".to_string(),
            equipment_source.to_string(),
        ),
        (
            "osric/osric_conditions.ttrpg".to_string(),
            conditions_source.to_string(),
        ),
        (
            "osric/osric_combat.ttrpg".to_string(),
            combat_source.to_string(),
        ),
        (
            "osric/osric_initiative.ttrpg".to_string(),
            initiative_source.to_string(),
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

/// Extract all DeclKind items from the "OSRIC Initiative" system block.
fn get_initiative_decls(program: &ttrpg_ast::ast::Program) -> &[ttrpg_ast::Spanned<DeclKind>] {
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSRIC Initiative" {
                return &sys.decls;
            }
        }
    }
    panic!("no system block named 'OSRIC Initiative' found");
}

// ── File-specific helpers ──────────────────────────────────────

/// Call a mechanic that returns a struct and extract its fields.
fn call_mechanic_struct(
    interp: &Interpreter,
    state: &GameState,
    responses: Vec<Response>,
    name: &str,
    args: Vec<Value>,
    expected_struct: &str,
) -> (BTreeMap<String, Value>, Vec<Effect>) {
    let mut handler = ScriptedHandler::with_responses(responses);
    let val = interp
        .evaluate_mechanic(state, &mut handler, name, args)
        .unwrap_or_else(|e| panic!("{name} failed: {e}"));

    match val {
        Value::Struct { name, fields } => {
            assert_eq!(
                &*name, expected_struct,
                "expected {expected_struct}, got {name}"
            );
            let fields = fields
                .into_iter()
                .map(|(k, v)| (k.to_string(), v))
                .collect();
            (fields, handler.log)
        }
        other => panic!("expected {expected_struct} struct, got: {other:?}"),
    }
}

/// Call resolve_melee_attack and return the AttackResult fields.
fn resolve_melee(
    interp: &Interpreter,
    state: &GameState,
    responses: Vec<Response>,
    attacker: EntityRef,
    target: EntityRef,
    weapon: &str,
) -> (BTreeMap<String, Value>, Vec<Effect>) {
    let mut handler = ScriptedHandler::with_responses(responses);
    let val = interp
        .evaluate_mechanic(
            state,
            &mut handler,
            "resolve_melee_attack",
            vec![
                Value::Entity(attacker),
                Value::Entity(target),
                melee_variant(weapon),
            ],
        )
        .unwrap();

    match val {
        Value::Struct { name, fields } => {
            assert_eq!(&*name, "AttackResult");
            let fields = fields
                .into_iter()
                .map(|(k, v)| (k.to_string(), v))
                .collect();
            (fields, handler.log)
        }
        other => panic!("expected AttackResult struct, got: {other:?}"),
    }
}

// ══════════════════════════════════════════════════════════════
//  PARSE + TYPECHECK
// ══════════════════════════════════════════════════════════════

#[test]
fn osric_initiative_parses_and_typechecks() {
    let (program, _) = compile_osric_initiative();
    let has_system = program
        .items
        .iter()
        .any(|item| matches!(&item.node, TopLevel::System(sys) if sys.name == "OSRIC Initiative"));
    assert!(has_system, "expected system named 'OSRIC Initiative'");
}

// ══════════════════════════════════════════════════════════════
//  STRUCTURE VERIFICATION
// ══════════════════════════════════════════════════════════════

#[test]
fn initiative_has_declared_action_type_enum() {
    let (program, _) = compile_osric_initiative();
    let decls = get_initiative_decls(&program);
    let enums: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Enum(e) => Some((&*e.name, e.variants.len())),
            _ => None,
        })
        .collect();
    assert!(
        enums.contains(&("DeclaredActionType", 9)),
        "expected DeclaredActionType with 9 variants, got: {enums:?}"
    );
}

#[test]
fn initiative_has_structs() {
    let (program, _) = compile_osric_initiative();
    let decls = get_initiative_decls(&program);
    let structs: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Struct(s) => Some((&*s.name, s.fields.len())),
            _ => None,
        })
        .collect();
    assert!(
        structs.contains(&("InitiativeResult", 5)),
        "missing InitiativeResult with 5 fields"
    );
    assert!(
        structs.contains(&("SurpriseResult", 4)),
        "missing SurpriseResult with 4 fields"
    );
    assert!(
        structs.contains(&("SegmentAction", 3)),
        "missing SegmentAction with 3 fields"
    );
}

#[test]
fn initiative_has_derives() {
    let (program, _) = compile_osric_initiative();
    let decls = get_initiative_decls(&program);
    let derives: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Derive(d) => Some(&*d.name),
            _ => None,
        })
        .collect();
    for expected in &[
        "surprise_duration",
        "free_surprise_segments",
        "wrap_segment",
        "action_segment",
        "missile_init_segment",
        "assign_segment",
        "has_fighter_multi_attack",
        "fighter_attacks_this_round",
        "fighter_attack_segments",
        "spell_effect_segment",
        "is_casting_at_segment",
        "spell_completed_at_segment",
        "acts_first_by_speed",
        "melee_order",
        "movement_per_segment",
        "movement_through_segment",
    ] {
        assert!(derives.contains(expected), "missing derive: {expected}");
    }
}

#[test]
fn initiative_has_mechanics() {
    let (program, _) = compile_osric_initiative();
    let decls = get_initiative_decls(&program);
    let mechanics: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Mechanic(m) => Some(&*m.name),
            _ => None,
        })
        .collect();
    assert!(
        mechanics.contains(&"roll_surprise"),
        "missing roll_surprise"
    );
    assert!(
        mechanics.contains(&"roll_initiative"),
        "missing roll_initiative"
    );
}

#[test]
fn initiative_has_events() {
    let (program, _) = compile_osric_initiative();
    let decls = get_initiative_decls(&program);
    let events: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Event(e) => Some(&*e.name),
            _ => None,
        })
        .collect();
    assert!(
        events.contains(&"SpellInterrupted"),
        "missing SpellInterrupted event"
    );
}

#[test]
fn initiative_has_conditions() {
    let (program, _) = compile_osric_initiative();
    let decls = get_initiative_decls(&program);
    let conditions: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Condition(c) => Some(&*c.name),
            _ => None,
        })
        .collect();
    assert!(
        conditions.contains(&"CastingSpell"),
        "missing CastingSpell condition"
    );
}

#[test]
fn initiative_has_hooks() {
    let (program, _) = compile_osric_initiative();
    let decls = get_initiative_decls(&program);
    let hooks: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Hook(h) => Some(&*h.name),
            _ => None,
        })
        .collect();
    assert!(
        hooks.contains(&"SpellInterruption"),
        "missing SpellInterruption hook"
    );
}

#[test]
fn initiative_has_actions() {
    let (program, _) = compile_osric_initiative();
    let decls = get_initiative_decls(&program);
    let actions: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Action(a) => Some(&*a.name),
            _ => None,
        })
        .collect();
    assert!(
        actions.contains(&"BeginCasting"),
        "missing BeginCasting action"
    );
}

// ══════════════════════════════════════════════════════════════
//  SURPRISE SYSTEM
// ══════════════════════════════════════════════════════════════

#[test]
fn surprise_duration_roll_3_or_higher_not_surprised() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    for roll in 3..=6 {
        let val = interp
            .evaluate_derive(
                &state,
                &mut NullHandler,
                "surprise_duration",
                vec![Value::Int(roll), Value::Int(0)],
            )
            .unwrap();
        assert_eq!(val, Value::Int(0), "roll {roll} should not cause surprise");
    }
}

#[test]
fn surprise_duration_roll_1_no_dex_adj() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "surprise_duration",
            vec![Value::Int(1), Value::Int(0)],
        )
        .unwrap();
    assert_eq!(
        val,
        Value::Int(1),
        "roll 1 with no DEX adj = 1 segment surprised"
    );
}

#[test]
fn surprise_duration_roll_2_no_dex_adj() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "surprise_duration",
            vec![Value::Int(2), Value::Int(0)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(2), "roll 2 with no DEX adj = 2 segments");
}

#[test]
fn surprise_duration_roll_2_with_dex_adj_1() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "surprise_duration",
            vec![Value::Int(2), Value::Int(1)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(1), "roll 2 - DEX adj 1 = 1 segment");
}

#[test]
fn surprise_duration_dex_adj_fully_negates() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // DEX adj of 3 against roll 2 → max(0, 2-3) = 0
    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "surprise_duration",
            vec![Value::Int(2), Value::Int(3)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(0), "high DEX should fully negate surprise");
}

// ── Expanded surprise threshold (monster-specific ranges) ────

#[test]
fn surprise_duration_threshold_3_roll_3_is_surprised() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Monster "surprises on 1-3" → threshold 3. Roll 3, no DEX adj → 3 segments.
    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "surprise_duration",
            vec![Value::Int(3), Value::Int(0), Value::Int(3)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(3), "roll 3 with threshold 3 = 3 segments");
}

#[test]
fn surprise_duration_threshold_4_roll_4_is_surprised() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Monster "surprises on 1-4" → threshold 4. Roll 4, no DEX adj → 4 segments.
    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "surprise_duration",
            vec![Value::Int(4), Value::Int(0), Value::Int(4)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(4), "roll 4 with threshold 4 = 4 segments");
}

#[test]
fn surprise_duration_threshold_3_roll_4_not_surprised() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Threshold 3 but rolled 4 → not surprised.
    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "surprise_duration",
            vec![Value::Int(4), Value::Int(0), Value::Int(3)],
        )
        .unwrap();
    assert_eq!(
        val,
        Value::Int(0),
        "roll 4 with threshold 3 = not surprised"
    );
}

#[test]
fn surprise_duration_threshold_3_with_dex_adj() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Threshold 3, roll 3, DEX adj 1 → max(0, 3-1) = 2 segments.
    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "surprise_duration",
            vec![Value::Int(3), Value::Int(1), Value::Int(3)],
        )
        .unwrap();
    assert_eq!(
        val,
        Value::Int(2),
        "roll 3 with threshold 3 and DEX adj 1 = 2 segments"
    );
}

#[test]
fn free_surprise_segments_party_more_surprised() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "free_surprise_segments",
            vec![Value::Int(2), Value::Int(0)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(2), "monsters get 2 free segments");
}

#[test]
fn free_surprise_segments_monster_more_surprised() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "free_surprise_segments",
            vec![Value::Int(0), Value::Int(1)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(1), "party gets 1 free segment");
}

#[test]
fn free_surprise_segments_equal_is_zero() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "free_surprise_segments",
            vec![Value::Int(1), Value::Int(1)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(0), "equal surprise = no free segments");
}

// ══════════════════════════════════════════════════════════════
//  ROLL MECHANICS (seeded)
// ══════════════════════════════════════════════════════════════

#[test]
fn roll_surprise_returns_surprise_result() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Script: party rolls 1 (surprised 1 seg), monster rolls 4 (not surprised)
    let party_roll = scripted_roll(1, 6, 0, vec![1], vec![1], 1, 1);
    let monster_roll = scripted_roll(1, 6, 0, vec![4], vec![4], 4, 4);

    let (fields, _) = call_mechanic_struct(
        &interp,
        &state,
        vec![party_roll, monster_roll],
        "roll_surprise",
        vec![],
        "SurpriseResult",
    );

    assert_eq!(get_int(&fields, "party_roll"), 1);
    assert_eq!(get_int(&fields, "monster_roll"), 4);
    assert_eq!(get_int(&fields, "party_surprised_segments"), 1);
    assert_eq!(get_int(&fields, "monster_surprised_segments"), 0);
}

#[test]
fn roll_surprise_high_rolls_no_surprise() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let party_roll = scripted_roll(1, 6, 0, vec![5], vec![5], 5, 5);
    let monster_roll = scripted_roll(1, 6, 0, vec![3], vec![3], 3, 3);

    let (fields, _) = call_mechanic_struct(
        &interp,
        &state,
        vec![party_roll, monster_roll],
        "roll_surprise",
        vec![],
        "SurpriseResult",
    );

    assert_eq!(get_int(&fields, "party_surprised_segments"), 0);
    assert_eq!(get_int(&fields, "monster_surprised_segments"), 0);
}

#[test]
fn roll_surprise_both_surprised() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let party_roll = scripted_roll(1, 6, 0, vec![2], vec![2], 2, 2);
    let monster_roll = scripted_roll(1, 6, 0, vec![1], vec![1], 1, 1);

    let (fields, _) = call_mechanic_struct(
        &interp,
        &state,
        vec![party_roll, monster_roll],
        "roll_surprise",
        vec![],
        "SurpriseResult",
    );

    assert_eq!(get_int(&fields, "party_surprised_segments"), 2);
    assert_eq!(get_int(&fields, "monster_surprised_segments"), 1);
}

// ── roll_surprise with expanded thresholds ───────────────────

#[test]
fn roll_surprise_monster_threshold_3_surprises_party_on_3() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Party rolls 3 (normally not surprised, but monster has threshold 3).
    // Monster rolls 5 (not surprised at default threshold 2).
    let party_roll = scripted_roll(1, 6, 0, vec![3], vec![3], 3, 3);
    let monster_roll = scripted_roll(1, 6, 0, vec![5], vec![5], 5, 5);

    let (fields, _) = call_mechanic_struct(
        &interp,
        &state,
        vec![party_roll, monster_roll],
        "roll_surprise",
        vec![Value::Int(3), Value::Int(2)], // monster_surprise_threshold=3, party=2
        "SurpriseResult",
    );

    assert_eq!(get_int(&fields, "party_roll"), 3);
    assert_eq!(get_int(&fields, "party_surprised_segments"), 3);
    assert_eq!(get_int(&fields, "monster_surprised_segments"), 0);
}

#[test]
fn roll_surprise_party_threshold_3_surprises_monster_on_3() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Party rolls 5 (not surprised). Monster rolls 3 (party has threshold 3 → surprised).
    let party_roll = scripted_roll(1, 6, 0, vec![5], vec![5], 5, 5);
    let monster_roll = scripted_roll(1, 6, 0, vec![3], vec![3], 3, 3);

    let (fields, _) = call_mechanic_struct(
        &interp,
        &state,
        vec![party_roll, monster_roll],
        "roll_surprise",
        vec![Value::Int(2), Value::Int(3)], // monster_surprise_threshold=2, party=3
        "SurpriseResult",
    );

    assert_eq!(get_int(&fields, "party_surprised_segments"), 0);
    assert_eq!(get_int(&fields, "monster_surprised_segments"), 3);
}

#[test]
fn roll_surprise_asymmetric_thresholds() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Monster surprises on 1-4, party surprises on 1-2 (standard).
    // Party rolls 4 → surprised 4 segments. Monster rolls 3 → not surprised (threshold 2).
    let party_roll = scripted_roll(1, 6, 0, vec![4], vec![4], 4, 4);
    let monster_roll = scripted_roll(1, 6, 0, vec![3], vec![3], 3, 3);

    let (fields, _) = call_mechanic_struct(
        &interp,
        &state,
        vec![party_roll, monster_roll],
        "roll_surprise",
        vec![Value::Int(4), Value::Int(2)], // monster_surprise_threshold=4, party=2
        "SurpriseResult",
    );

    assert_eq!(get_int(&fields, "party_surprised_segments"), 4);
    assert_eq!(get_int(&fields, "monster_surprised_segments"), 0);
}

#[test]
fn roll_initiative_simultaneous() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Both roll 3 → simultaneous
    let party_roll = scripted_roll(1, 6, 0, vec![3], vec![3], 3, 3);
    let monster_roll = scripted_roll(1, 6, 0, vec![3], vec![3], 3, 3);

    let (fields, _) = call_mechanic_struct(
        &interp,
        &state,
        vec![party_roll, monster_roll],
        "roll_initiative",
        vec![],
        "InitiativeResult",
    );

    assert_eq!(get_int(&fields, "party_roll"), 3);
    assert_eq!(get_int(&fields, "monster_roll"), 3);
    assert_eq!(get_int(&fields, "party_segment"), 3);
    assert_eq!(get_int(&fields, "monster_segment"), 3);
    assert!(get_bool(&fields, "simultaneous"));
}

#[test]
fn roll_initiative_not_simultaneous() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Party rolls 2 (acts segment 2), monster rolls 5 (acts segment 5)
    let party_roll = scripted_roll(1, 6, 0, vec![2], vec![2], 2, 2);
    let monster_roll = scripted_roll(1, 6, 0, vec![5], vec![5], 5, 5);

    let (fields, _) = call_mechanic_struct(
        &interp,
        &state,
        vec![party_roll, monster_roll],
        "roll_initiative",
        vec![],
        "InitiativeResult",
    );

    assert_eq!(get_int(&fields, "party_segment"), 2);
    assert_eq!(get_int(&fields, "monster_segment"), 5);
    assert!(!get_bool(&fields, "simultaneous"));
}

// ══════════════════════════════════════════════════════════════
//  SEGMENT WRAPPING
// ══════════════════════════════════════════════════════════════

#[test]
fn wrap_segment_within_range_unchanged() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    for seg in 1..=10 {
        let val = interp
            .evaluate_derive(
                &state,
                &mut NullHandler,
                "wrap_segment",
                vec![Value::Int(seg)],
            )
            .unwrap();
        assert_eq!(val, Value::Int(seg), "segment {seg} should stay {seg}");
    }
}

#[test]
fn wrap_segment_11_wraps_to_1() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "wrap_segment",
            vec![Value::Int(11)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(1));
}

#[test]
fn wrap_segment_12_wraps_to_2() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "wrap_segment",
            vec![Value::Int(12)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(2));
}

#[test]
fn wrap_segment_20_wraps_to_10() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "wrap_segment",
            vec![Value::Int(20)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(10));
}

// ══════════════════════════════════════════════════════════════
//  ACTION SEGMENT ASSIGNMENT
// ══════════════════════════════════════════════════════════════

#[test]
fn action_segment_melee_equals_initiative() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "action_segment",
            vec![Value::Int(4), action_type("MeleeAttackAction")],
        )
        .unwrap();
    assert_eq!(val, Value::Int(4));
}

#[test]
fn action_segment_move_always_1() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    for init_seg in 1..=6 {
        let val = interp
            .evaluate_derive(
                &state,
                &mut NullHandler,
                "action_segment",
                vec![Value::Int(init_seg), action_type("MoveAction")],
            )
            .unwrap();
        assert_eq!(
            val,
            Value::Int(1),
            "MoveAction at init {init_seg} should be segment 1"
        );
    }
}

#[test]
fn action_segment_set_against_charge_always_1() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "action_segment",
            vec![Value::Int(5), action_type("SetAgainstChargeAction")],
        )
        .unwrap();
    assert_eq!(val, Value::Int(1));
}

#[test]
fn action_segment_cast_spell_with_casting_time() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Initiative 4, casting time 3 → 4 + 3 - 1 = 6
    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "action_segment",
            vec![
                Value::Int(4),
                action_type("CastSpellAction"),
                Value::Int(3), // casting_time
            ],
        )
        .unwrap();
    assert_eq!(val, Value::Int(6));
}

#[test]
fn action_segment_cast_spell_cross_round() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Initiative 6, casting time 7 → 6 + 7 - 1 = 12
    // NOT wrapped: value > 10 means spell continues into next round (§1.6.1.3).
    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "action_segment",
            vec![
                Value::Int(6),
                action_type("CastSpellAction"),
                Value::Int(7), // casting_time
            ],
        )
        .unwrap();
    assert_eq!(val, Value::Int(12));
}

#[test]
fn action_segment_missile_with_dex_adj() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Initiative 4, DEX missile adj -1 → max(1, 4 + (-1)) = 3
    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "action_segment",
            vec![
                Value::Int(4),
                action_type("MissileAttackAction"),
                Value::Int(0),  // casting_time (default)
                Value::Int(-1), // dex_missile_init_adj
            ],
        )
        .unwrap();
    assert_eq!(val, Value::Int(3));
}

#[test]
fn action_segment_missile_dex_adj_floors_to_1() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Initiative 1, DEX missile adj -3 → max(1, 1 + (-3)) = max(1, -2) = 1
    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "action_segment",
            vec![
                Value::Int(1),
                action_type("MissileAttackAction"),
                Value::Int(0),
                Value::Int(-3),
            ],
        )
        .unwrap();
    assert_eq!(val, Value::Int(1));
}

#[test]
fn action_segment_all_simple_types_equal_initiative() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // These action types all resolve at the initiative segment
    for variant in &["ChargeAction", "ParryAction", "FleeAction", "HoldAction"] {
        let val = interp
            .evaluate_derive(
                &state,
                &mut NullHandler,
                "action_segment",
                vec![Value::Int(3), action_type(variant)],
            )
            .unwrap();
        assert_eq!(
            val,
            Value::Int(3),
            "{variant} should resolve at initiative segment"
        );
    }
}

// ── missile_init_segment ──────────────────────────────────────

#[test]
fn missile_init_segment_dex_16_reduces_segment() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // DEX 16 → dex_init_missile = -1 → base 4 + (-1) = 3 → max(1, 3) = 3
    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "missile_init_segment",
            vec![Value::Int(4), Value::Int(16)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(3));
}

#[test]
fn missile_init_segment_dex_3_increases_segment() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // DEX 3 → dex_init_missile = +3 → base 2 + 3 = 5 → max(1, 5) = 5
    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "missile_init_segment",
            vec![Value::Int(2), Value::Int(3)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(5));
}

// ── assign_segment ────────────────────────────────────────────

#[test]
fn assign_segment_melee_returns_segment_action() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "assign_segment",
            vec![
                Value::Int(3),
                action_type("MeleeAttackAction"),
                Value::Int(5), // weapon_speed
            ],
        )
        .unwrap();

    match val {
        Value::Struct { name, fields } => {
            assert_eq!(&*name, "SegmentAction");
            let fields: BTreeMap<String, Value> = fields
                .into_iter()
                .map(|(k, v)| (k.to_string(), v))
                .collect();
            assert_eq!(get_int(&fields, "segment"), 3);
            assert_eq!(get_int(&fields, "speed_factor"), 5);
            assert_eq!(
                fields.get("action_type").unwrap(),
                &action_type("MeleeAttackAction")
            );
        }
        other => panic!("expected SegmentAction struct, got: {other:?}"),
    }
}

#[test]
fn assign_segment_casting_adjusts_for_casting_time() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "assign_segment",
            vec![
                Value::Int(2),
                action_type("CastSpellAction"),
                Value::Int(0), // weapon_speed
                Value::Int(5), // casting_time
            ],
        )
        .unwrap();

    match val {
        Value::Struct { name, fields } => {
            assert_eq!(&*name, "SegmentAction");
            let fields: BTreeMap<String, Value> = fields
                .into_iter()
                .map(|(k, v)| (k.to_string(), v))
                .collect();
            // 2 + 5 - 1 = 6
            assert_eq!(get_int(&fields, "segment"), 6);
        }
        other => panic!("expected SegmentAction struct, got: {other:?}"),
    }
}

// ══════════════════════════════════════════════════════════════
//  FIGHTER MULTIPLE ATTACKS
// ══════════════════════════════════════════════════════════════

#[test]
fn has_fighter_multi_attack_fighter_level_7() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "has_fighter_multi_attack",
            vec![class_variant("Fighter"), Value::Int(7)],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(true));
}

#[test]
fn has_fighter_multi_attack_fighter_level_6_no() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "has_fighter_multi_attack",
            vec![class_variant("Fighter"), Value::Int(6)],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(false));
}

#[test]
fn has_fighter_multi_attack_paladin_level_7() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Paladin is FighterGroup
    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "has_fighter_multi_attack",
            vec![class_variant("Paladin"), Value::Int(7)],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(true));
}

#[test]
fn has_fighter_multi_attack_thief_level_10_no() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Thief is ThiefGroup, not FighterGroup
    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "has_fighter_multi_attack",
            vec![class_variant("Thief"), Value::Int(10)],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(false));
}

#[test]
fn fighter_attacks_this_round_below_7_always_1() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    for round in 1..=4 {
        let val = interp
            .evaluate_derive(
                &state,
                &mut NullHandler,
                "fighter_attacks_this_round",
                vec![Value::Int(6), Value::Int(round)],
            )
            .unwrap();
        assert_eq!(
            val,
            Value::Int(1),
            "level 6, round {round} should be 1 attack"
        );
    }
}

#[test]
fn fighter_attacks_this_round_level_7_12_alternates() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Level 7-12: 3/2 rate — odd rounds: 1 attack, even rounds: 2 attacks
    let odd = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "fighter_attacks_this_round",
            vec![
                Value::Int(9),
                Value::Int(1), // odd round
            ],
        )
        .unwrap();
    assert_eq!(odd, Value::Int(1));

    let even = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "fighter_attacks_this_round",
            vec![
                Value::Int(9),
                Value::Int(2), // even round
            ],
        )
        .unwrap();
    assert_eq!(even, Value::Int(2));
}

#[test]
fn fighter_attacks_this_round_level_13_always_2() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    for round in 1..=4 {
        let val = interp
            .evaluate_derive(
                &state,
                &mut NullHandler,
                "fighter_attacks_this_round",
                vec![Value::Int(13), Value::Int(round)],
            )
            .unwrap();
        assert_eq!(
            val,
            Value::Int(2),
            "level 13+, round {round} should be 2 attacks"
        );
    }
}

#[test]
fn fighter_attack_segments_level_7_even_round() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Level 7, even round → 2 attacks → [1, 10]
    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "fighter_attack_segments",
            vec![Value::Int(7), Value::Int(2)],
        )
        .unwrap();
    assert_eq!(val, Value::List(vec![Value::Int(1), Value::Int(10)]));
}

#[test]
fn fighter_attack_segments_level_7_odd_round() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Level 7, odd round → 1 attack → [1]
    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "fighter_attack_segments",
            vec![Value::Int(7), Value::Int(1)],
        )
        .unwrap();
    assert_eq!(val, Value::List(vec![Value::Int(1)]));
}

#[test]
fn fighter_attack_segments_level_13_always_two() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    for round in 1..=3 {
        let val = interp
            .evaluate_derive(
                &state,
                &mut NullHandler,
                "fighter_attack_segments",
                vec![Value::Int(13), Value::Int(round)],
            )
            .unwrap();
        assert_eq!(
            val,
            Value::List(vec![Value::Int(1), Value::Int(10)]),
            "level 13, round {round}"
        );
    }
}

#[test]
fn fighter_attack_segments_below_7_empty() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "fighter_attack_segments",
            vec![Value::Int(5), Value::Int(1)],
        )
        .unwrap();
    assert_eq!(val, Value::List(vec![]));
}

// ══════════════════════════════════════════════════════════════
//  SPELL TIMING
// ══════════════════════════════════════════════════════════════

#[test]
fn spell_effect_segment_basic() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Initiative 4, casting time 3 → 4 + 3 - 1 = 6
    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "spell_effect_segment",
            vec![Value::Int(4), Value::Int(3)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(6));
}

#[test]
fn spell_effect_segment_cross_round() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Initiative 9, casting time 5 → 9 + 5 - 1 = 13
    // NOT wrapped: value > 10 means spell continues into next round (§1.6.1.3).
    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "spell_effect_segment",
            vec![Value::Int(9), Value::Int(5)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(13));
}

#[test]
fn spell_effect_segment_casting_time_1() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Initiative 2, casting time 1 → 2 + 1 - 1 = 2 (instant cast)
    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "spell_effect_segment",
            vec![Value::Int(2), Value::Int(1)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(2));
}

#[test]
fn is_casting_at_segment_during_casting() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Cast starts at segment 4, casting time 3 → casting during 4, 5, 6
    // At segment 4: 4 >= 4 && 4 < 7 → true
    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "is_casting_at_segment",
            vec![
                Value::Int(4), // cast_start_segment
                Value::Int(3), // casting_time
                Value::Int(4), // current_segment
            ],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(true));

    // At segment 5: 5 >= 4 && 5 < 7 → true
    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "is_casting_at_segment",
            vec![Value::Int(4), Value::Int(3), Value::Int(5)],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(true));
}

#[test]
fn is_casting_at_segment_before_start() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Current segment 3 < cast start 4 → false
    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "is_casting_at_segment",
            vec![Value::Int(4), Value::Int(3), Value::Int(3)],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(false));
}

#[test]
fn is_casting_at_segment_after_completion() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Cast starts 4, casting time 3 → completes at 6.
    // At segment 7: 7 >= 4 but 7 >= 7 → false (7 < 7 is false)
    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "is_casting_at_segment",
            vec![Value::Int(4), Value::Int(3), Value::Int(7)],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(false));
}

#[test]
fn spell_completed_at_segment_exact() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Cast starts 4, casting time 3 → completes at 4+3-1=6
    // At segment 6: 6 >= 6 → true
    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "spell_completed_at_segment",
            vec![Value::Int(4), Value::Int(3), Value::Int(6)],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(true));
}

#[test]
fn spell_completed_at_segment_after() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "spell_completed_at_segment",
            vec![Value::Int(4), Value::Int(3), Value::Int(8)],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(true));
}

#[test]
fn spell_completed_at_segment_before() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // At segment 5: 5 >= 6 → false
    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "spell_completed_at_segment",
            vec![Value::Int(4), Value::Int(3), Value::Int(5)],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(false));
}

// ══════════════════════════════════════════════════════════════
//  SPEED FACTOR TIE-BREAKING
// ══════════════════════════════════════════════════════════════

#[test]
fn acts_first_by_speed_lower_wins() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "acts_first_by_speed",
            vec![Value::Int(2), Value::Int(5)],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(true), "lower speed acts first");
}

#[test]
fn acts_first_by_speed_higher_loses() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "acts_first_by_speed",
            vec![Value::Int(5), Value::Int(2)],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(false));
}

#[test]
fn acts_first_by_speed_equal_is_false() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "acts_first_by_speed",
            vec![Value::Int(4), Value::Int(4)],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(false), "equal speed = not first");
}

#[test]
fn melee_order_dagger_vs_longsword() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Dagger SF=2, SwordLong SF=5 → dagger acts first
    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "melee_order",
            vec![melee_variant("Dagger"), melee_variant("SwordLong")],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(true));
}

#[test]
fn melee_order_longsword_vs_dagger() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "melee_order",
            vec![melee_variant("SwordLong"), melee_variant("Dagger")],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(false));
}

#[test]
fn melee_order_same_weapon_is_false() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "melee_order",
            vec![melee_variant("SwordLong"), melee_variant("SwordLong")],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(false), "same weapon = not first");
}

#[test]
fn melee_order_halberd_vs_fist() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Halberd SF=9, FistOrKick SF=1 → fist acts first
    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "melee_order",
            vec![melee_variant("Halberd"), melee_variant("FistOrKick")],
        )
        .unwrap();
    assert_eq!(
        val,
        Value::Bool(false),
        "halberd (SF=9) loses to fist (SF=1)"
    );

    let val2 = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "melee_order",
            vec![melee_variant("FistOrKick"), melee_variant("Halberd")],
        )
        .unwrap();
    assert_eq!(val2, Value::Bool(true));
}

// ══════════════════════════════════════════════════════════════
//  MOVEMENT SEGMENTS
// ══════════════════════════════════════════════════════════════

#[test]
fn movement_per_segment_base_120() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "movement_per_segment",
            vec![feet(120)],
        )
        .unwrap();
    assert_eq!(expect_feet(val, "movement_per_segment"), 12);
}

#[test]
fn movement_per_segment_base_60() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "movement_per_segment",
            vec![feet(60)],
        )
        .unwrap();
    assert_eq!(expect_feet(val, "movement_per_segment"), 6);
}

#[test]
fn movement_per_segment_base_90_floors() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // 90 / 10 = 9, no rounding needed
    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "movement_per_segment",
            vec![feet(90)],
        )
        .unwrap();
    assert_eq!(expect_feet(val, "movement_per_segment"), 9);
}

#[test]
fn movement_through_segment_1() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "movement_through_segment",
            vec![feet(120), Value::Int(1)],
        )
        .unwrap();
    assert_eq!(expect_feet(val, "movement_through_segment"), 12);
}

#[test]
fn movement_through_segment_5() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "movement_through_segment",
            vec![feet(120), Value::Int(5)],
        )
        .unwrap();
    assert_eq!(expect_feet(val, "movement_through_segment"), 60);
}

#[test]
fn movement_through_segment_10() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "movement_through_segment",
            vec![feet(120), Value::Int(10)],
        )
        .unwrap();
    assert_eq!(expect_feet(val, "movement_through_segment"), 120);
}

// ══════════════════════════════════════════════════════════════
//  CHARGE INTERACTION
// ══════════════════════════════════════════════════════════════

#[test]
fn set_weapon_damage_multiplier_is_2() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let val = interp
        .evaluate_derive(
            &state,
            &mut NullHandler,
            "set_weapon_damage_multiplier",
            vec![],
        )
        .unwrap();
    assert_eq!(val, Value::Int(2));
}

#[test]
fn can_set_against_charge_valid_weapons() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    for weapon in &["Spear", "Javelin", "Lance", "PoleArm", "Trident"] {
        let val = interp
            .evaluate_derive(
                &state,
                &mut NullHandler,
                "can_set_against_charge",
                vec![melee_variant(weapon)],
            )
            .unwrap();
        assert_eq!(
            val,
            Value::Bool(true),
            "{weapon} should be valid for set against charge"
        );
    }
}

#[test]
fn can_set_against_charge_invalid_weapons() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    for weapon in &["SwordLong", "Dagger", "Club", "Staff", "BattleAxe"] {
        let val = interp
            .evaluate_derive(
                &state,
                &mut NullHandler,
                "can_set_against_charge",
                vec![melee_variant(weapon)],
            )
            .unwrap();
        assert_eq!(
            val,
            Value::Bool(false),
            "{weapon} should NOT be valid for set against charge"
        );
    }
}

// ══════════════════════════════════════════════════════════════
//  CASTING SPELL CONDITION — modifies #attack_resolution
// ══════════════════════════════════════════════════════════════

/// Baseline: without CastingSpell, a melee attack hits normally.
#[test]
fn baseline_melee_attack_without_casting_spell() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities_12(),
        30,
        15,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities_12(),
        10,
        14,
        "Human",
    );

    let atk_roll = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    let dmg_roll = scripted_roll(1, 8, 0, vec![6], vec![6], 6, 6);

    let (fields, _) = resolve_melee(
        &interp,
        &state,
        vec![atk_roll, dmg_roll],
        attacker,
        target,
        "SwordLong",
    );

    assert_eq!(
        fields.get("outcome").unwrap(),
        &enum_variant("AttackOutcome", "Hit")
    );
    assert_eq!(get_int(&fields, "damage"), 6);
}

/// CastingSpell on attacker: forces attack to Miss with 0 damage.
#[test]
fn casting_spell_on_attacker_forces_miss() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities_12(),
        30,
        15,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities_12(),
        10,
        14,
        "Human",
    );

    state.apply_condition(
        &attacker,
        "CastingSpell",
        BTreeMap::new(),
        Value::None,
        None,
    );

    // The condition modifies the result post-call (Phase 2): outcome → Miss, damage → 0
    // Mechanic body runs first (dice rolls), then Phase 2 modify fires after
    let atk_roll = scripted_roll(1, 20, 0, vec![20], vec![20], 20, 20);
    let dmg_roll = scripted_roll(1, 8, 0, vec![8], vec![8], 8, 8);

    let (fields, log) = resolve_melee(
        &interp,
        &state,
        vec![atk_roll, dmg_roll, Response::Acknowledged],
        attacker,
        target,
        "SwordLong",
    );

    assert_eq!(
        fields.get("outcome").unwrap(),
        &enum_variant("AttackOutcome", "Miss"),
        "CastingSpell should force attack to Miss"
    );
    assert_eq!(
        get_int(&fields, "damage"),
        0,
        "CastingSpell should zero damage"
    );

    // Verify ModifyApplied was emitted
    assert!(
        log.iter()
            .any(|e| matches!(e, Effect::ModifyApplied { .. })),
        "expected ModifyApplied effect"
    );
}

/// CastingSpell on target: strips DEX AC bonus per §1.6.2.11 but does NOT
/// force a miss (that modify only fires when attacker = bearer).
/// With standard DEX 12 (AC adj 0), the effective AC is unchanged.
#[test]
fn casting_spell_on_target_strips_dex_ac_but_attack_hits() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities_12(),
        30,
        15,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities_12(),
        10,
        14,
        "Human",
    );

    // Apply CastingSpell to target, not attacker
    state.apply_condition(&target, "CastingSpell", BTreeMap::new(), Value::None, None);

    let atk_roll = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    let dmg_roll = scripted_roll(1, 8, 0, vec![6], vec![6], 6, 6);

    let (fields, log) = resolve_melee(
        &interp,
        &state,
        vec![
            Response::Acknowledged, // ModifyApplied (effective_target_ac DEX stripping)
            atk_roll,
            dmg_roll,
        ],
        attacker,
        target,
        "SwordLong",
    );

    // Attack hits normally — DEX 12 gives 0 AC bonus, so stripping it changes nothing
    assert_eq!(
        fields.get("outcome").unwrap(),
        &enum_variant("AttackOutcome", "Hit")
    );
    assert_eq!(get_int(&fields, "damage"), 6);

    // Verify the DEX AC modify fired
    assert!(
        log.iter()
            .any(|e| matches!(e, Effect::ModifyApplied { .. })),
        "expected ModifyApplied for effective_target_ac DEX stripping"
    );
}

/// CastingSpell on a high-DEX target strips their DEX AC bonus (§1.6.2.11),
/// making them easier to hit. DEX 16 → +2 AC bonus stripped → attack that
/// would miss now hits.
#[test]
fn casting_spell_strips_high_dex_ac_bonus() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let high_dex_abilities: Vec<(&str, i64)> = vec![
        ("STR", 12),
        ("DEX", 16),
        ("CON", 12),
        ("INT", 12),
        ("WIS", 12),
        ("CHA", 12),
    ];

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        1,
        &standard_abilities_12(),
        30,
        10,
        "Human",
    );
    // Target: armor_ac 14, DEX 16 → +2 AC bonus → effective AC 16
    let target = make_character(
        &mut state,
        "Target",
        "MagicUser",
        5,
        &high_dex_abilities,
        10,
        14,
        "Human",
    );

    // Roll 15 + BTHB 0 (Fighter 1) + STR 0 (12) = 15
    // Without CastingSpell: effective AC = 14 + 2 (DEX 16) = 16 → 15 < 16 → Miss
    // With CastingSpell: effective AC = 14 + 0 (DEX stripped) = 14 → 15 >= 14 → Hit!
    state.apply_condition(&target, "CastingSpell", BTreeMap::new(), Value::None, None);

    let atk_roll = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    let dmg_roll = scripted_roll(1, 8, 0, vec![6], vec![6], 6, 6);

    let (fields, log) = resolve_melee(
        &interp,
        &state,
        vec![
            Response::Acknowledged, // ModifyApplied (DEX AC stripping)
            atk_roll,
            dmg_roll,
        ],
        attacker,
        target,
        "SwordLong",
    );

    // Attack hits because CastingSpell stripped the DEX +2 AC bonus
    assert_eq!(
        fields.get("outcome").unwrap(),
        &enum_variant("AttackOutcome", "Hit"),
        "CastingSpell should strip DEX AC bonus, making target easier to hit"
    );
    assert_eq!(get_int(&fields, "damage"), 6);

    // Verify modify fired
    assert!(
        log.iter()
            .any(|e| matches!(e, Effect::ModifyApplied { .. })),
        "expected ModifyApplied for DEX AC stripping"
    );
}

// ══════════════════════════════════════════════════════════════
//  BEGIN CASTING ACTION
// ══════════════════════════════════════════════════════════════

#[test]
fn begin_casting_applies_casting_spell_condition() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let caster = make_caster(
        &mut state,
        "Mage",
        "MagicUser",
        5,
        &standard_abilities_12(),
        10,
        10,
        "Human",
    );
    state.set_turn_budget(&caster, combat_turn_budget());

    // Action pipeline: ActionStarted → Ack, DeductCost → Ack, resolve body
    // BeginCasting applies CastingSpell condition (ConditionApplied → Ack)
    // and sets casting_invocation (FieldSet → Ack)
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, // ActionStarted
        Response::Acknowledged, // DeductCost
        Response::Acknowledged, // ConditionApplied
        Response::Acknowledged, // FieldSet (casting_invocation)
        Response::Acknowledged, // ActionCompleted
    ]);

    let adapter = StateAdapter::new(state);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "BeginCasting",
                caster,
                vec![Value::Int(3)], // casting_time
            )
            .unwrap();
    });

    let final_state = adapter.into_inner();

    // Verify CastingSpell condition was applied
    let conditions = final_state.read_conditions(&caster).unwrap_or_default();
    assert!(
        conditions.iter().any(|c| &*c.name == "CastingSpell"),
        "expected CastingSpell condition on caster, got: {conditions:?}"
    );
}

// ══════════════════════════════════════════════════════════════
//  SPELL INTERRUPTION HOOK
// ══════════════════════════════════════════════════════════════

#[test]
fn spell_interruption_hook_fires_on_damage() {
    let (program, result) = compile_osric_initiative();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let caster = make_caster(
        &mut state,
        "Mage",
        "MagicUser",
        5,
        &standard_abilities_12(),
        20,
        10,
        "Human",
    );
    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities_12(),
        30,
        15,
        "Human",
    );
    state.set_turn_budget(&attacker, combat_turn_budget());

    // Equip weapon on attacker
    set_field(&mut state, &attacker, "wielded_main", wielded_melee_item("SwordLong"));

    // Manually apply CastingSpell to caster (as if BeginCasting was called)
    state.apply_condition(&caster, "CastingSpell", BTreeMap::new(), Value::None, None);

    // Verify condition is present before attack
    assert!(
        state
            .read_conditions(&caster)
            .unwrap_or_default()
            .iter()
            .any(|c| &*c.name == "CastingSpell"),
        "CastingSpell should be present before damage"
    );

    // Attack the caster — should trigger SpellInterruption hook via Damaged event
    // The hook removes CastingSpell and emits SpellInterrupted
    let atk_roll = scripted_roll(1, 20, 0, vec![18], vec![18], 18, 18);
    let dmg_roll = scripted_roll(1, 8, 0, vec![5], vec![5], 5, 5);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, // ActionStarted
        Response::Acknowledged, // DeductCost
        Response::Acknowledged, // RequiresCheck (wielded_melee requires)
        Response::Acknowledged, // ModifyApplied (CastingSpell strips DEX AC on caster)
        atk_roll,
        dmg_roll,
        Response::Acknowledged, // Damaged event
        Response::Acknowledged, // ConditionRemoved (CastingSpell)
        Response::Acknowledged, // SpellInterrupted event
        Response::Acknowledged, // ActionCompleted
    ]);

    let adapter = StateAdapter::new(state);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "MeleeAttack",
                attacker,
                vec![Value::Entity(caster)],
            )
            .unwrap();
    });

    let final_state = adapter.into_inner();

    // Verify CastingSpell was removed by the hook
    let conditions = final_state.read_conditions(&caster).unwrap_or_default();
    assert!(
        !conditions.iter().any(|c| &*c.name == "CastingSpell"),
        "CastingSpell should be removed after damage, got: {conditions:?}"
    );

    // Verify caster took damage
    let hp = final_state.read_field(&caster, "hp").unwrap();
    assert_eq!(hp, Value::Int(15), "caster HP should be 20 - 5 = 15");
}
