//! OSRIC combat integration tests.
//!
//! Runtime derive, mechanic, and character-facing action coverage has moved to
//! `osric/tests/osric_combat.ttrpg-cli`.
//! This Rust file keeps parse/typecheck and declaration checks for the real
//! OSRIC sources, plus the overloaded monster `MeleeAttack` action cases that
//! the CLI runner still cannot express directly.

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_interp::adapter::StateAdapter;
use ttrpg_interp::effect::Response;
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::StateProvider;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

mod osric_common;
use osric_common::*;

fn compile_osric_combat() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

fn get_combat_decls(program: &ttrpg_ast::ast::Program) -> &[ttrpg_ast::Spanned<DeclKind>] {
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSRIC Combat" {
                return &sys.decls;
            }
        }
    }
    panic!("no system block named 'OSRIC Combat' found");
}

#[test]
fn osric_combat_parses_and_typechecks() {
    let (program, _) = compile_osric_combat();
    let has_system = program
        .items
        .iter()
        .any(|item| matches!(&item.node, TopLevel::System(sys) if sys.name == "OSRIC Combat"));
    assert!(has_system, "expected system named 'OSRIC Combat'");
}

#[test]
fn osric_combat_has_enums() {
    let (program, _) = compile_osric_combat();
    let decls = get_combat_decls(&program);
    let enums: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Enum(e) => Some((&*e.name, e.variants.len())),
            _ => None,
        })
        .collect();
    assert!(enums.contains(&("AttackOutcome", 2)));
    assert!(enums.contains(&("Duration", 7)));
    assert!(enums.contains(&("SurpriseState", 4)));
    assert!(enums.contains(&("AssassinationOutcome", 3)));
}

#[test]
fn osric_combat_has_structs() {
    let (program, _) = compile_osric_combat();
    let decls = get_combat_decls(&program);
    let structs: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Struct(s) => Some((&*s.name, s.fields.len())),
            _ => None,
        })
        .collect();
    assert!(
        structs.contains(&("AttackResult", 3)),
        "missing AttackResult with 3 fields"
    );
    assert!(
        structs.contains(&("TurnBudget", 1)),
        "missing TurnBudget with 1 field"
    );
    assert!(
        structs.contains(&("EncounterStart", 4)),
        "missing EncounterStart with 4 fields"
    );
    assert!(
        structs.contains(&("AssassinationResult", 4)),
        "missing AssassinationResult with 4 fields"
    );
}

#[test]
fn osric_combat_has_tables() {
    let (program, _) = compile_osric_combat();
    let decls = get_combat_decls(&program);
    let tables: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Table(t) => Some(&*t.name),
            _ => None,
        })
        .collect();
    assert!(tables.contains(&"cleric_group_bthb"));
    assert!(tables.contains(&"thief_group_bthb"));
    assert!(tables.contains(&"magic_user_group_bthb"));
}

#[test]
fn osric_combat_has_derives() {
    let (program, _) = compile_osric_combat();
    let decls = get_combat_decls(&program);
    let derives: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Derive(d) => Some(&*d.name),
            _ => None,
        })
        .collect();
    assert!(derives.contains(&"fighter_group_bthb"));
    assert!(derives.contains(&"bthb"));
    assert!(derives.contains(&"monster_bthb"));
    assert!(derives.contains(&"fighter_attacks"));
    assert!(derives.contains(&"missile_range_penalty"));
    assert!(derives.contains(&"deal_damage"));
}

#[test]
fn osric_combat_has_mechanics() {
    let (program, _) = compile_osric_combat();
    let decls = get_combat_decls(&program);
    let mechanics: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Mechanic(m) => Some(&*m.name),
            _ => None,
        })
        .collect();
    assert!(mechanics.contains(&"attack_roll_aac"));
    assert!(mechanics.contains(&"damage_roll"));
    assert!(mechanics.contains(&"resolve_melee_attack"));
    assert!(mechanics.contains(&"resolve_missile_attack"));
    assert!(mechanics.contains(&"resolve_monster_attack"));
    assert!(mechanics.contains(&"surprise_roll"));
    assert!(mechanics.contains(&"encounter_distance"));
    assert!(mechanics.contains(&"group_initiative"));
    assert!(mechanics.contains(&"encounter_sequence"));
}

#[test]
fn osric_combat_has_events() {
    let (program, _) = compile_osric_combat();
    let decls = get_combat_decls(&program);
    let events: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Event(e) => Some(&*e.name),
            _ => None,
        })
        .collect();
    assert!(events.contains(&"Damaged"));
    assert!(events.contains(&"CreatureSlain"));
}

#[test]
fn osric_combat_has_actions() {
    let (program, _) = compile_osric_combat();
    let decls = get_combat_decls(&program);
    let actions: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Action(a) => Some(&*a.name),
            _ => None,
        })
        .collect();
    assert!(actions.contains(&"TakeDamage"));
    assert!(actions.contains(&"MeleeAttack"));
    assert!(actions.contains(&"MissileAttack"));
    assert!(actions.contains(&"Charge"));
}

#[test]
fn monster_melee_attack_hits_and_damages_character() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let ogre = make_monster(
        &mut state,
        "Ogre",
        (4, 8, 1),
        26,
        15,
        vec![monster_attack("Club", 1, 10, 0)],
    );
    let target = make_character(
        &mut state,
        "Victim",
        "Fighter",
        1,
        &standard_abilities_12(),
        10,
        14,
        "Human",
    );
    state.set_turn_budget(&ogre, combat_turn_budget());

    let atk_roll = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    let dmg_roll = scripted_roll(1, 10, 0, vec![6], vec![6], 6, 6);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged,
        Response::Acknowledged,
        atk_roll,
        dmg_roll,
        Response::Acknowledged,
        Response::Acknowledged,
        Response::Acknowledged,
        Response::Acknowledged,
        Response::Acknowledged,
    ]);

    let adapter = StateAdapter::new(state);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "MeleeAttack",
                ogre,
                vec![Value::Entity(target), monster_attack("Club", 1, 10, 0)],
            )
            .unwrap();
    });

    let final_state = adapter.into_inner();
    let hp = read_group_field(&final_state, &target, "HitPoints", "hp").unwrap();
    assert_eq!(hp, Value::Int(4), "target HP should be 10 - 6 = 4");
}

#[test]
fn monster_melee_attack_miss_preserves_hp() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let rat = make_monster(
        &mut state,
        "Rat",
        (0, 0, 0),
        1,
        10,
        vec![monster_attack("Bite", 1, 2, 0)],
    );
    let target = make_character(
        &mut state,
        "Warrior",
        "Fighter",
        5,
        &standard_abilities_12(),
        30,
        17,
        "Human",
    );
    state.set_turn_budget(&rat, combat_turn_budget());

    let atk_roll = scripted_roll(1, 20, 0, vec![10], vec![10], 10, 10);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged,
        Response::Acknowledged,
        atk_roll,
        Response::Acknowledged,
    ]);

    let adapter = StateAdapter::new(state);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "MeleeAttack",
                rat,
                vec![Value::Entity(target), monster_attack("Bite", 1, 2, 0)],
            )
            .unwrap();
    });

    let final_state = adapter.into_inner();
    let hp = read_group_field(&final_state, &target, "HitPoints", "hp").unwrap();
    assert_eq!(hp, Value::Int(30), "target HP should remain 30 on miss");
}

#[test]
fn monster_melee_attack_against_monster() {
    let (program, result) = compile_osric_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let ogre = make_monster(
        &mut state,
        "Ogre",
        (4, 8, 1),
        26,
        15,
        vec![monster_attack("Club", 1, 10, 0)],
    );
    let goblin = make_monster(
        &mut state,
        "Goblin",
        (1, 8, -1),
        5,
        14,
        vec![monster_attack("Sword", 1, 6, 0)],
    );
    state.set_turn_budget(&ogre, combat_turn_budget());

    let atk_roll = scripted_roll(1, 20, 0, vec![12], vec![12], 12, 12);
    let dmg_roll = scripted_roll(1, 10, 0, vec![4], vec![4], 4, 4);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged,
        Response::Acknowledged,
        atk_roll,
        dmg_roll,
        Response::Acknowledged,
        Response::Acknowledged,
        Response::Acknowledged,
        Response::Acknowledged,
        Response::Acknowledged,
    ]);

    let adapter = StateAdapter::new(state);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "MeleeAttack",
                ogre,
                vec![Value::Entity(goblin), monster_attack("Club", 1, 10, 0)],
            )
            .unwrap();
    });

    let final_state = adapter.into_inner();
    let hp = final_state.read_field(&goblin, "hp").unwrap();
    assert_eq!(hp, Value::Int(1), "goblin HP should be 5 - 4 = 1");
}
