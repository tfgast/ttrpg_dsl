//! OSRIC potions integration tests.
//!
//! Verifies:
//! 1. Potion of Healing restores HP
//! 2. Potion of Extra-Healing restores HP (full dose)
//! 3. DrinkPotion action consumes item from inventory
//! 4. Potion of Speed applies PotionSpeed condition
//! 5. Speed condition doubles movement
//! 6. Invulnerability improves AC
//! 7. Admixture table returns correct result categories
//! 8. potion_item derive creates correct Item
//! 9. Healing potion heals unconscious character

use std::collections::BTreeMap;

use ttrpg_ast::Name;
use ttrpg_interp::adapter::StateAdapter;
use ttrpg_interp::effect::Response;
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::StateProvider;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

mod osric_common;
use osric_common::*;

fn compile_osric() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

// ── Test 1: Potion of Healing restores HP ────────────────────

#[test]
fn potion_healing_restores_hp() {
    let (program, result) = compile_osric();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let drinker = make_character(
        &mut state,
        "Wounded",
        "Fighter",
        1,
        &standard_abilities_12(),
        20,
        10,
        "Human",
    );

    // Damage the character to 10 HP
    set_group_field(&mut state, &drinker, "HitPoints", "hp", Value::Int(10));

    // Roll 2d4+2: dice = [3, 4], total = 3+4+2 = 9, unmod = 7
    let heal_roll = scripted_roll(2, 4, 2, vec![3, 4], vec![3, 4], 9, 7);
    let final_state = run_function_with_rolls(
        &interp,
        state,
        vec![
            heal_roll,
            Response::Acknowledged, // PotionHealed event
        ],
        "resolve_potion_healing",
        vec![Value::Entity(drinker)],
    );

    let hp = read_hp(&final_state, &drinker);
    assert_eq!(hp, 19, "healing potion should restore 9 HP (10 + 9 = 19)");
}

// ── Test 2: Potion of Extra-Healing restores HP ──────────────

#[test]
fn potion_extra_healing_restores_hp() {
    let (program, result) = compile_osric();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let drinker = make_character(
        &mut state,
        "Wounded",
        "Fighter",
        1,
        &standard_abilities_12(),
        30,
        10,
        "Human",
    );

    // Damage to 5 HP
    set_group_field(&mut state, &drinker, "HitPoints", "hp", Value::Int(5));

    // Roll 3d8+3: dice = [6, 7, 5], total = 6+7+5+3 = 21, unmod = 18
    let heal_roll = scripted_roll(3, 8, 3, vec![6, 7, 5], vec![6, 7, 5], 21, 18);
    let final_state = run_function_with_rolls(
        &interp,
        state,
        vec![
            heal_roll,
            Response::Acknowledged, // PotionHealed event
        ],
        "resolve_potion_extra_healing",
        vec![Value::Entity(drinker)],
    );

    let hp = read_hp(&final_state, &drinker);
    // 5 + 21 = 26, capped at max_hp = 30 → 26
    assert_eq!(hp, 26, "extra-healing should restore 21 HP (5 + 21 = 26)");
}

// ── Test 3: DrinkPotion action consumes item ─────────────────

#[test]
fn drink_potion_action_consumes_item() {
    let (program, result) = compile_osric();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    // Create character with a Potion of Healing in inventory
    let potion = item_value("Potion of Healing", 0, 400);
    let drinker = make_character_with_inventory(
        &mut state,
        "Thirsty",
        "Fighter",
        1,
        &standard_abilities_12(),
        20,
        10,
        "Human",
        vec![potion],
    );

    // Damage to 10 HP
    set_group_field(&mut state, &drinker, "HitPoints", "hp", Value::Int(10));
    state.set_turn_budget(&drinker, combat_turn_budget());

    // Roll 2d4+2: dice = [2, 3], total = 2+3+2 = 7, unmod = 5
    let heal_roll = scripted_roll(2, 4, 2, vec![2, 3], vec![2, 3], 7, 5);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, // PotionDrunk event
        heal_roll,              // 2d4+2 healing roll
        Response::Acknowledged, // PotionHealed event
        Response::Acknowledged, // extra
        Response::Acknowledged, // extra
    ]);

    let final_state = run_action(
        &interp,
        state,
        &mut handler,
        "DrinkPotion",
        drinker,
        vec![enum_variant("PotionType", "Healing")],
    );

    let hp = read_hp(&final_state, &drinker);
    assert_eq!(hp, 17, "healing potion via action should restore 7 HP (10 + 7 = 17)");

    // Verify item was consumed from inventory
    let loose_items = read_group_field(&final_state, &drinker, "Inventory", "loose_items")
        .expect("should have Inventory.loose_items");
    match loose_items {
        Value::List(items) => {
            assert!(
                items.is_empty(),
                "potion should be consumed from inventory, but found {} items",
                items.len()
            );
        }
        other => panic!("expected list for loose_items, got {other:?}"),
    }
}

// ── Test 4: Speed potion applies condition ───────────────────

#[test]
fn potion_speed_applies_condition() {
    let (program, result) = compile_osric();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let drinker = make_character(
        &mut state,
        "Speedy",
        "Fighter",
        1,
        &standard_abilities_12(),
        20,
        10,
        "Human",
    );

    // Roll 5d4 for duration: dice = [3,2,4,3,2], total = 14
    let duration_roll = scripted_roll(5, 4, 0, vec![3, 2, 4, 3, 2], vec![3, 2, 4, 3, 2], 14, 14);
    let final_state = run_function_with_rolls(
        &interp,
        state,
        vec![
            duration_roll,
            Response::Acknowledged, // PotionEffectApplied event
        ],
        "resolve_potion_speed",
        vec![Value::Entity(drinker)],
    );

    // Verify PotionSpeed condition is active
    let conditions = final_state.read_conditions(&drinker).unwrap_or_default();
    let has_speed = conditions.iter().any(|c| c.name == "PotionSpeed");
    assert!(has_speed, "PotionSpeed condition should be active after drinking");
}

// ── Test 5: Speed condition doubles movement ─────────────────

#[test]
fn potion_speed_doubles_movement() {
    let (program, result) = compile_osric();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let drinker = make_character(
        &mut state,
        "Speedy",
        "Fighter",
        1,
        &standard_abilities_12(),
        20,
        10,
        "Human",
    );

    // Apply PotionSpeed condition directly
    state.apply_condition(
        &drinker,
        "PotionSpeed",
        BTreeMap::new(),
        Value::Void,
        None,
    );

    // Evaluate character_movement — should be doubled (120 * 2 = 240)
    let mut handler = RollHandler::new(vec![]);
    let adapter = StateAdapter::new(state);
    let result_val = adapter.run(&mut handler, |state, eff_handler| {
        interp
            .evaluate_derive(
                state,
                eff_handler,
                "character_movement",
                vec![Value::Entity(drinker)],
            )
            .unwrap()
    });

    assert_eq!(
        result_val,
        feet(240),
        "movement should be doubled from 120 to 240 with PotionSpeed"
    );
}

// ── Test 6: Invulnerability improves AC ──────────────────────

#[test]
fn potion_invulnerability_improves_ac() {
    let (program, result) = compile_osric();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    // Character with AC 10 (no armor)
    let drinker = make_character(
        &mut state,
        "Knight",
        "Fighter",
        1,
        &standard_abilities_12(),
        20,
        10,
        "Human",
    );

    // Apply PotionInvulnerability condition
    state.apply_condition(
        &drinker,
        "PotionInvulnerability",
        BTreeMap::new(),
        Value::Void,
        None,
    );

    let mut handler = RollHandler::new(vec![]);
    let adapter = StateAdapter::new(state);
    let result_val = adapter.run(&mut handler, |state, eff_handler| {
        interp
            .evaluate_derive(
                state,
                eff_handler,
                "effective_target_ac",
                vec![Value::Entity(drinker)],
            )
            .unwrap()
    });

    // AC 10 + 2 from PotionInvulnerability = 12
    assert_eq!(
        result_val,
        Value::Int(12),
        "AC should be 10 + 2 (PotionInvulnerability) = 12"
    );
}

// ── Test 7: Admixture table returns correct categories ───────

#[test]
fn admixture_result_table() {
    let (program, result) = compile_osric();
    let interp = Interpreter::new(&program, &result.env).unwrap();

    let test_cases = vec![
        (1, "EldritchBlast"),
        (2, "Poison"),
        (3, "Poison"),
        (5, "StrangeBrew"),
        (10, "BothCancelled"),
        (15, "OneCancelled"),
        (25, "BothHalved"),
        (50, "BothWork"),
        (90, "BothWork"),
        (95, "ExtraordinarySuccess"),
        (100, "PermanentEffect"),
    ];

    for (d100, expected_variant) in test_cases {
        let state = GameState::new();
        let mut handler = RollHandler::new(vec![]);
        let adapter = StateAdapter::new(state);
        let result_val = adapter.run(&mut handler, |state, eff_handler| {
            interp
                .evaluate_derive(
                    state,
                    eff_handler,
                    "admixture_result",
                    vec![Value::Int(d100)],
                )
                .unwrap()
        });

        match &result_val {
            Value::EnumVariant { variant, .. } => {
                assert_eq!(
                    variant.as_str(),
                    expected_variant,
                    "d100={d100}: expected {expected_variant}, got {variant}"
                );
            }
            other => panic!("expected enum variant for d100={d100}, got {other:?}"),
        }
    }
}

// ── Test 8: potion_item creates correct Item ─────────────────

#[test]
fn potion_item_derive() {
    let (program, result) = compile_osric();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let mut handler = RollHandler::new(vec![]);
    let adapter = StateAdapter::new(state);
    let result_val = adapter.run(&mut handler, |state, eff_handler| {
        interp
            .evaluate_derive(
                state,
                eff_handler,
                "potion_item",
                vec![enum_variant("PotionType", "Healing")],
            )
            .unwrap()
    });

    match &result_val {
        Value::Struct { name, fields } => {
            assert_eq!(name.as_str(), "Item");
            assert_eq!(
                fields.get(&Name::from("name")),
                Some(&Value::Str("Potion of Healing".to_string()))
            );
            assert_eq!(
                fields.get(&Name::from("weight")),
                Some(&Value::Int(0))
            );
            assert_eq!(
                fields.get(&Name::from("gp_value")),
                Some(&Value::Int(400))
            );
        }
        other => panic!("expected struct for potion_item, got {other:?}"),
    }
}

// ── Test 9: Healing potion heals unconscious character ───────

#[test]
fn potion_healing_heals_unconscious() {
    let (program, result) = compile_osric();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let drinker = make_character(
        &mut state,
        "Dying",
        "Fighter",
        1,
        &standard_abilities_12(),
        20,
        10,
        "Human",
    );

    // Set HP to -3 (unconscious)
    set_group_field(&mut state, &drinker, "HitPoints", "hp", Value::Int(-3));
    state.apply_condition(
        &drinker,
        "Unconscious",
        BTreeMap::new(),
        Value::Void,
        None,
    );
    state.apply_condition(&drinker, "Bleeding", BTreeMap::new(), Value::Void, None);

    // Roll 2d4+2: dice = [4, 4], total = 4+4+2 = 10, unmod = 8
    let heal_roll = scripted_roll(2, 4, 2, vec![4, 4], vec![4, 4], 10, 8);
    // heal_unconscious also rolls 1d6 for coma duration
    let coma_roll = scripted_roll(1, 6, 0, vec![3], vec![3], 3, 3);
    let final_state = run_function_with_rolls(
        &interp,
        state,
        vec![
            heal_roll,
            coma_roll,
            Response::Acknowledged, // PotionHealed event
        ],
        "resolve_potion_healing",
        vec![Value::Entity(drinker)],
    );

    let hp = read_hp(&final_state, &drinker);
    // -3 + 10 = 7
    assert_eq!(hp, 7, "healing potion should bring unconscious character to 7 HP (-3 + 10)");

    // Unconscious and Bleeding should be removed, Coma applied
    let conditions = final_state.read_conditions(&drinker).unwrap_or_default();
    let has_unconscious = conditions.iter().any(|c| c.name == "Unconscious");
    let has_coma = conditions.iter().any(|c| c.name == "Coma");
    assert!(!has_unconscious, "Unconscious should be removed after healing");
    assert!(has_coma, "Coma should be applied after healing from unconscious");
}
