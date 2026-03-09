//! OSRIC magic item enhancement bonus integration tests.
//!
//! Verifies:
//! 1. Mundane weapon attack/damage unchanged (weapon_bonus defaults to 0)
//! 2. +N weapon adds to attack roll and damage
//! 3. +N armor/shield improves AC
//! 4. RequiresMagicWeapon blocks mundane weapon damage
//! 5. RequiresMagicWeapon allows sufficient magic weapon
//! 6. ImmuneToNormalWeapons blocks non-magic attacks

use std::collections::BTreeMap;

use ttrpg_ast::Name;
use ttrpg_interp::adapter::StateAdapter;
use ttrpg_interp::effect::Response;
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::{EntityRef, StateProvider};
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

mod osric_common;
use osric_common::*;

fn compile_osric() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

fn read_monster_hp(state: &GameState, entity: &EntityRef) -> i64 {
    match state.read_field(entity, "hp").expect("monster should have hp") {
        Value::Int(n) => n,
        other => panic!("expected int for monster hp, got {other:?}"),
    }
}

// ── Test 1: Mundane weapon attack/damage unchanged ─────────────────

#[test]
fn mundane_weapon_attack_unchanged() {
    let (program, result) = compile_osric();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    // Fighter level 1, all 12s (no STR mod), wielding mundane longsword
    let attacker = make_armed_character(
        &mut state,
        "Fighter",
        "Fighter",
        1,
        &standard_abilities_12(),
        20,
        Value::Option(None),
        Value::Option(None),
        wielded_melee_item("SwordLong"),
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities_12(),
        20,
        10,
        "Human",
    );
    state.set_turn_budget(&attacker, combat_turn_budget());

    // Attack roll: d20 = 15 (hit vs AC 10)
    let atk_roll = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    // Damage roll: 1d8 = 5
    let dmg_roll = scripted_roll(1, 8, 0, vec![5], vec![5], 5, 5);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, // turn budget check
        Response::Acknowledged, // action cost
        atk_roll,
        dmg_roll,
        Response::Acknowledged, // TakeDamage
        Response::Acknowledged, // Damaged event
        Response::Acknowledged,
        Response::Acknowledged,
        Response::Acknowledged,
    ]);

    let final_state = run_action(
        &interp,
        state,
        &mut handler,
        "MeleeAttack",
        attacker,
        vec![Value::Entity(target)],
    );

    let hp = read_hp(&final_state, &target);
    // 1d8 = 5 damage, no bonus from mundane weapon
    assert_eq!(hp, 15, "mundane weapon should deal 5 damage (20 - 5 = 15)");
}

// ── Test 2: +N weapon adds to attack and damage ────────────────────

#[test]
fn magic_weapon_adds_bonus_to_damage() {
    let (program, result) = compile_osric();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    // Fighter with +2 longsword
    let attacker = make_armed_character(
        &mut state,
        "Fighter",
        "Fighter",
        1,
        &standard_abilities_12(),
        20,
        Value::Option(None),
        Value::Option(None),
        wielded_melee_item_magic("SwordLong", 2),
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities_12(),
        20,
        10,
        "Human",
    );
    state.set_turn_budget(&attacker, combat_turn_budget());

    // Attack roll: d20 = 15 (hit with +2 bonus)
    let atk_roll = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    // Damage roll: 1d8 = 5 (weapon_bonus +2 added by combat mechanic)
    let dmg_roll = scripted_roll(1, 8, 0, vec![5], vec![5], 5, 5);
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

    let final_state = run_action(
        &interp,
        state,
        &mut handler,
        "MeleeAttack",
        attacker,
        vec![Value::Entity(target)],
    );

    let hp = read_hp(&final_state, &target);
    // 1d8(5) + 2 magic bonus = 7 damage
    assert_eq!(hp, 13, "+2 weapon should deal 7 damage (20 - 7 = 13)");
}

// ── Test 3: +N armor improves AC ───────────────────────────────────

#[test]
fn magic_armor_improves_ac() {
    let (program, result) = compile_osric();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Character in +2 chain mail (base AC 15 + 2 = 17)
    let mut state_mut = state;
    let char_entity = make_armed_character(
        &mut state_mut,
        "Knight",
        "Fighter",
        1,
        &standard_abilities_12(),
        20,
        worn_armor_magic("ChainMail", 2),
        Value::Option(None),
        Value::Option(None),
        "Human",
    );

    let mut handler = RollHandler::new(vec![]);
    let adapter = StateAdapter::new(state_mut);
    let result_val = adapter.run(&mut handler, |state, eff_handler| {
        interp
            .evaluate_derive(state, eff_handler, "effective_target_ac", vec![Value::Entity(char_entity)])
            .unwrap()
    });

    // Chain mail base AC = 15, + 2 magic bonus = 17
    assert_eq!(result_val, Value::Int(17), "AC should be 15 (chain mail) + 2 (magic) = 17");
}

// ── Test 4: +N shield improves AC ──────────────────────────────────

#[test]
fn magic_shield_improves_ac() {
    let (program, result) = compile_osric();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    // Character in leather armor (AC 12) with +1 small shield (base +1, magic +1 = +2)
    let char_entity = make_armed_character(
        &mut state,
        "Knight",
        "Fighter",
        1,
        &standard_abilities_12(),
        20,
        worn_armor("Leather"),
        worn_shield_magic("SmallShield", 1),
        Value::Option(None),
        "Human",
    );

    let mut handler = RollHandler::new(vec![]);
    let adapter = StateAdapter::new(state);
    let result_val = adapter.run(&mut handler, |state, eff_handler| {
        interp
            .evaluate_derive(state, eff_handler, "effective_target_ac", vec![Value::Entity(char_entity)])
            .unwrap()
    });

    // Leather AC 12 + small shield base +1 + magic +1 = 14
    assert_eq!(result_val, Value::Int(14), "AC should be 12 (leather) + 1 (shield) + 1 (magic) = 14");
}

// ── Test 5: RequiresMagicWeapon blocks mundane weapon ──────────────

#[test]
fn require_magic_weapon_blocks_mundane_attack() {
    let (program, result) = compile_osric();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_armed_character(
        &mut state,
        "Fighter",
        "Fighter",
        1,
        &standard_abilities_12(),
        20,
        Value::Option(None),
        Value::Option(None),
        wielded_melee_item("SwordLong"), // mundane
        "Human",
    );

    // Monster with RequiresMagicWeapon(bonus: 1)
    let monster = make_monster(
        &mut state,
        "Gargoyle",
        (4, 8, 0),
        20,
        15,
        vec![monster_attack("Claw", 1, 4, 0)],
    );
    let mut params = BTreeMap::new();
    params.insert(Name::from("bonus"), Value::Int(1));
    state.apply_condition(&monster, "RequiresMagicWeapon", params, Value::Void, None);

    state.set_turn_budget(&attacker, combat_turn_budget());

    // Attack roll: d20 = 20 (would normally hit)
    let atk_roll = scripted_roll(1, 20, 0, vec![20], vec![20], 20, 20);
    // Damage roll: still provided but should be overridden to 0 by condition
    let dmg_roll = scripted_roll(1, 8, 0, vec![5], vec![5], 5, 5);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, // turn budget
        Response::Acknowledged, // action cost
        atk_roll,
        dmg_roll,
        Response::Acknowledged, // modify applied
        Response::Acknowledged,
        Response::Acknowledged,
        Response::Acknowledged,
        Response::Acknowledged,
        Response::Acknowledged,
    ]);

    let final_state = run_action(
        &interp,
        state,
        &mut handler,
        "MeleeAttack",
        attacker,
        vec![Value::Entity(monster)],
    );

    let hp = read_monster_hp(&final_state, &monster);
    assert_eq!(
        hp, 20,
        "mundane weapon should deal 0 damage to RequiresMagicWeapon monster"
    );
}

// ── Test 6: RequiresMagicWeapon allows sufficient bonus ─────────────

#[test]
fn require_magic_weapon_allows_magic_attack() {
    let (program, result) = compile_osric();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_armed_character(
        &mut state,
        "Fighter",
        "Fighter",
        1,
        &standard_abilities_12(),
        20,
        Value::Option(None),
        Value::Option(None),
        wielded_melee_item_magic("SwordLong", 1), // +1 weapon
        "Human",
    );

    let monster = make_monster(
        &mut state,
        "Gargoyle",
        (4, 8, 0),
        20,
        10,
        vec![monster_attack("Claw", 1, 4, 0)],
    );
    let mut params = BTreeMap::new();
    params.insert(Name::from("bonus"), Value::Int(1));
    state.apply_condition(&monster, "RequiresMagicWeapon", params, Value::Void, None);

    state.set_turn_budget(&attacker, combat_turn_budget());

    // Attack roll: d20 = 15 (hit)
    let atk_roll = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    // Damage roll: 1d8 = 5 (weapon_bonus +1 added by combat mechanic)
    let dmg_roll = scripted_roll(1, 8, 0, vec![5], vec![5], 5, 5);
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
        Response::Acknowledged,
    ]);

    let final_state = run_action(
        &interp,
        state,
        &mut handler,
        "MeleeAttack",
        attacker,
        vec![Value::Entity(monster)],
    );

    let hp = read_monster_hp(&final_state, &monster);
    // 1d8(5) + 1 weapon_bonus = 6 damage
    assert_eq!(hp, 14, "+1 weapon should deal 6 damage to RequiresMagicWeapon(1) monster (20 - 6 = 14)");
}

// ── Test 7: ImmuneToNormalWeapons blocks non-magic attacks ──────────

#[test]
fn immune_to_normal_weapons_blocks_mundane() {
    let (program, result) = compile_osric();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_armed_character(
        &mut state,
        "Fighter",
        "Fighter",
        1,
        &standard_abilities_12(),
        20,
        Value::Option(None),
        Value::Option(None),
        wielded_melee_item("SwordLong"), // mundane
        "Human",
    );

    let monster = make_monster(
        &mut state,
        "Wraith",
        (4, 8, 0),
        20,
        15,
        vec![monster_attack("Touch", 1, 6, 0)],
    );
    state.apply_condition(&monster, "ImmuneToNormalWeapons", BTreeMap::new(), Value::Void, None);

    state.set_turn_budget(&attacker, combat_turn_budget());

    let atk_roll = scripted_roll(1, 20, 0, vec![20], vec![20], 20, 20);
    let dmg_roll = scripted_roll(1, 8, 0, vec![5], vec![5], 5, 5);
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
        Response::Acknowledged,
    ]);

    let final_state = run_action(
        &interp,
        state,
        &mut handler,
        "MeleeAttack",
        attacker,
        vec![Value::Entity(monster)],
    );

    let hp = read_monster_hp(&final_state, &monster);
    assert_eq!(hp, 20, "mundane weapon should deal 0 damage to ImmuneToNormalWeapons monster");
}

// ── Test 8: ImmuneToNormalWeapons allows magic weapon ───────────────

#[test]
fn immune_to_normal_weapons_allows_magic() {
    let (program, result) = compile_osric();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_armed_character(
        &mut state,
        "Fighter",
        "Fighter",
        1,
        &standard_abilities_12(),
        20,
        Value::Option(None),
        Value::Option(None),
        wielded_melee_item_magic("SwordLong", 1),
        "Human",
    );

    let monster = make_monster(
        &mut state,
        "Wraith",
        (4, 8, 0),
        20,
        10,
        vec![monster_attack("Touch", 1, 6, 0)],
    );
    state.apply_condition(&monster, "ImmuneToNormalWeapons", BTreeMap::new(), Value::Void, None);

    state.set_turn_budget(&attacker, combat_turn_budget());

    let atk_roll = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    // Damage roll: 1d8 = 5 (weapon_bonus +1 added by combat mechanic)
    let dmg_roll = scripted_roll(1, 8, 0, vec![5], vec![5], 5, 5);
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
        Response::Acknowledged,
    ]);

    let final_state = run_action(
        &interp,
        state,
        &mut handler,
        "MeleeAttack",
        attacker,
        vec![Value::Entity(monster)],
    );

    let hp = read_monster_hp(&final_state, &monster);
    // 1d8(5) + 1 weapon_bonus = 6 damage
    assert_eq!(hp, 14, "+1 weapon should deal 6 damage to ImmuneToNormalWeapons monster (20 - 6 = 14)");
}
