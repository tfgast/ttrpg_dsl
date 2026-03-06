//! OSRIC encumbrance integration test.
//!
//! Verifies encumbrance derives, the EncumbranceState condition's modify clauses,
//! and their interaction with movement and surprise.
//!
//! Tests:
//! - effective_str_encumbrance: STR 10, 18, 18+exc50, 18+exc100
//! - character_encumbrance: various weight/STR combos
//! - character_movement + EncumbranceState: Human/Dwarf with each tier
//! - character_movement + armour cap: cap dominates when lower
//! - character_surprise_adj + EncumbranceState: tier × armour × DEX combos

use std::collections::BTreeMap;

use ttrpg_ast::ast::TopLevel;
use ttrpg_ast::Name;
use ttrpg_interp::adapter::StateAdapter;
use ttrpg_interp::effect::{Effect, FieldPathSegment};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::WritableState;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

mod osric_common;
use osric_common::*;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_encumbrance() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

fn expect_tier(val: Value, ctx: &str) -> String {
    match val {
        Value::EnumVariant { variant, .. } => variant.to_string(),
        other => panic!("{ctx}: expected EncumbranceTier variant, got {other:?}"),
    }
}

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn osric_encumbrance_parses_and_typechecks() {
    let (program, _) = compile_osric_encumbrance();
    let has_conditions = program
        .items
        .iter()
        .any(|item| matches!(&item.node, TopLevel::System(sys) if sys.name == "OSRIC Conditions"));
    assert!(has_conditions);
}

// ── effective_str_encumbrance ─────────────────────────────────

#[test]
fn effective_str_encumbrance_normal_str() {
    let (program, result) = compile_osric_encumbrance();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // STR 10 → str_encumbrance(10) = 35
    let char_ref = make_encumbrance_character(
        &mut state,
        "Test",
        &[
            ("STR", 10),
            ("DEX", 10),
            ("CON", 10),
            ("INT", 10),
            ("WIS", 10),
            ("CHA", 10),
        ],
        "Human",
        0,
        0,
    );
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "effective_str_encumbrance",
            vec![Value::Entity(char_ref)],
        )
        .unwrap();
    assert_eq!(expect_int(val, "STR 10"), 35);
}

#[test]
fn effective_str_encumbrance_str_18_no_exceptional() {
    let (program, result) = compile_osric_encumbrance();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // STR 18, no exceptional → str_encumbrance(18) = 110
    let char_ref = make_encumbrance_character(
        &mut state,
        "Test",
        &[
            ("STR", 18),
            ("DEX", 10),
            ("CON", 10),
            ("INT", 10),
            ("WIS", 10),
            ("CHA", 10),
        ],
        "Human",
        0,
        0,
    );
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "effective_str_encumbrance",
            vec![Value::Entity(char_ref)],
        )
        .unwrap();
    assert_eq!(expect_int(val, "STR 18 no exc"), 110);
}

#[test]
fn effective_str_encumbrance_str_18_exc_50() {
    let (program, result) = compile_osric_encumbrance();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // STR 18 + exc 50 → exc_str_encumbrance(50) = 135
    let char_ref = make_encumbrance_character(
        &mut state,
        "Test",
        &[
            ("STR", 18),
            ("DEX", 10),
            ("CON", 10),
            ("INT", 10),
            ("WIS", 10),
            ("CHA", 10),
        ],
        "Human",
        0,
        0,
    );
    // Grant ExceptionalStrength group
    state.write_field(
        &char_ref,
        &[FieldPathSegment::Field("ExceptionalStrength".into())],
        Value::Struct {
            name: "ExceptionalStrength".into(),
            fields: {
                let mut f = BTreeMap::new();
                f.insert("percentile".into(), Value::Int(50));
                f
            },
        },
    );

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "effective_str_encumbrance",
            vec![Value::Entity(char_ref)],
        )
        .unwrap();
    assert_eq!(expect_int(val, "STR 18 exc 50"), 135);
}

#[test]
fn effective_str_encumbrance_str_18_exc_100() {
    let (program, result) = compile_osric_encumbrance();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // STR 18 + exc 100 → exc_str_encumbrance(100) = 300
    let char_ref = make_encumbrance_character(
        &mut state,
        "Test",
        &[
            ("STR", 18),
            ("DEX", 10),
            ("CON", 10),
            ("INT", 10),
            ("WIS", 10),
            ("CHA", 10),
        ],
        "Human",
        0,
        0,
    );
    state.write_field(
        &char_ref,
        &[FieldPathSegment::Field("ExceptionalStrength".into())],
        Value::Struct {
            name: "ExceptionalStrength".into(),
            fields: {
                let mut f = BTreeMap::new();
                f.insert("percentile".into(), Value::Int(100));
                f
            },
        },
    );

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "effective_str_encumbrance",
            vec![Value::Entity(char_ref)],
        )
        .unwrap();
    assert_eq!(expect_int(val, "STR 18 exc 100"), 300);
}

// ── character_encumbrance ─────────────────────────────────────

#[test]
fn character_encumbrance_tiers() {
    let (program, result) = compile_osric_encumbrance();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // STR 10 → allowance 35
    let cases = [
        (35, "Unencumbered"), // 35 - 35 = 0
        (36, "Light"),        // 36 - 35 = 1
        (75, "Light"),        // 75 - 35 = 40
        (76, "Moderate"),     // 76 - 35 = 41
        (115, "Moderate"),    // 115 - 35 = 80
        (116, "Heavy"),       // 116 - 35 = 81
        (155, "Heavy"),       // 155 - 35 = 120
        (156, "Overloaded"),  // 156 - 35 = 121
    ];

    for (weight, expected) in cases {
        let char_ref = make_encumbrance_character(
            &mut state,
            &format!("Test-{weight}"),
            &[
                ("STR", 10),
                ("DEX", 10),
                ("CON", 10),
                ("INT", 10),
                ("WIS", 10),
                ("CHA", 10),
            ],
            "Human",
            weight,
            0,
        );
        let val = interp
            .evaluate_derive(
                &state,
                &mut handler,
                "character_encumbrance",
                vec![Value::Entity(char_ref)],
            )
            .unwrap();
        assert_eq!(
            expect_tier(val, &format!("weight={weight}")),
            expected,
            "weight={weight} (STR 10, allowance=35)"
        );
    }
}

// ── character_movement base derive (no condition) ─────────────

#[test]
fn character_movement_no_armour_cap() {
    let (program, result) = compile_osric_encumbrance();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // Human (base 120ft), no armour cap
    let char_ref =
        make_encumbrance_character(&mut state, "Test", &standard_abilities(), "Human", 0, 0);
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "character_movement",
            vec![Value::Entity(char_ref)],
        )
        .unwrap();
    assert_eq!(expect_feet(val, "human no cap"), 120);
}

#[test]
fn character_movement_with_armour_cap() {
    let (program, result) = compile_osric_encumbrance();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // Human (base 120ft), plate armour cap 60ft
    let char_ref =
        make_encumbrance_character(&mut state, "Test", &standard_abilities(), "Human", 0, 60);
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "character_movement",
            vec![Value::Entity(char_ref)],
        )
        .unwrap();
    assert_eq!(expect_feet(val, "human + plate cap"), 60);
}

// ── character_movement + EncumbranceState condition ───────────

#[test]
fn character_movement_human_all_tiers() {
    let (program, result) = compile_osric_encumbrance();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // Human 120ft base, no armour cap
    let cases = [
        ("Unencumbered", 120), // 120 * 4/4 = 120
        ("Light", 90),         // 120 * 3/4 = 90
        ("Moderate", 60),      // 120 * 2/4 = 60
        ("Heavy", 30),         // 120 * 1/4 = 30
        ("Overloaded", 0),     // 120 * 0/4 = 0
    ];

    for (tier_name, expected) in cases {
        let char_ref = make_encumbrance_character(
            &mut state,
            &format!("Test-{tier_name}"),
            &standard_abilities(),
            "Human",
            0,
            0,
        );
        apply_encumbrance(&mut state, &char_ref, tier_name);

        let val = interp
            .evaluate_derive(
                &state,
                &mut handler,
                "character_movement",
                vec![Value::Entity(char_ref)],
            )
            .unwrap();
        assert_eq!(
            expect_feet(val, &format!("Human {tier_name}")),
            expected,
            "Human + {tier_name}"
        );
    }
}

#[test]
fn character_movement_dwarf_with_encumbrance() {
    let (program, result) = compile_osric_encumbrance();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // Dwarf 90ft base
    let cases = [
        ("Unencumbered", 90), // 90 * 4/4 = 90
        ("Light", 67),        // floor(90 * 3/4) = floor(67.5) = 67
        ("Moderate", 45),     // floor(90 * 2/4) = 45
        ("Heavy", 22),        // floor(90 * 1/4) = floor(22.5) = 22
        ("Overloaded", 0),    // 90 * 0/4 = 0
    ];

    for (tier_name, expected) in cases {
        let char_ref = make_encumbrance_character(
            &mut state,
            &format!("Dwarf-{tier_name}"),
            &standard_abilities(),
            "Dwarf",
            0,
            0,
        );
        apply_encumbrance(&mut state, &char_ref, tier_name);

        let val = interp
            .evaluate_derive(
                &state,
                &mut handler,
                "character_movement",
                vec![Value::Entity(char_ref)],
            )
            .unwrap();
        assert_eq!(
            expect_feet(val, &format!("Dwarf {tier_name}")),
            expected,
            "Dwarf + {tier_name}"
        );
    }
}

#[test]
fn character_movement_armour_cap_dominates() {
    let (program, result) = compile_osric_encumbrance();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // Human 120ft base + plate 60ft cap. Armour cap applied first by derive,
    // then encumbrance fraction reduces further.
    // Unencumbered: min(120, 60) = 60, then 60 * 4/4 = 60
    let char1 = make_encumbrance_character(
        &mut state,
        "Plate-Unenc",
        &standard_abilities(),
        "Human",
        0,
        60,
    );
    apply_encumbrance(&mut state, &char1, "Unencumbered");
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "character_movement",
            vec![Value::Entity(char1)],
        )
        .unwrap();
    assert_eq!(expect_feet(val, "plate+unenc"), 60);

    // Light: min(120, 60) = 60, then 60 * 3/4 = 45
    let char2 = make_encumbrance_character(
        &mut state,
        "Plate-Light",
        &standard_abilities(),
        "Human",
        0,
        60,
    );
    apply_encumbrance(&mut state, &char2, "Light");
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "character_movement",
            vec![Value::Entity(char2)],
        )
        .unwrap();
    assert_eq!(expect_feet(val, "plate+light"), 45);
}

// ── character_surprise_adj + EncumbranceState ─────────────────

#[test]
fn surprise_adj_unencumbered_no_armour() {
    let (program, result) = compile_osric_encumbrance();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // DEX 16 → dex_surprise(16) = +1, Unencumbered + no armour → +1 bonus
    // Total: 1 + 1 = 2
    let char_ref = make_encumbrance_character(
        &mut state,
        "Test",
        &[
            ("STR", 10),
            ("DEX", 16),
            ("CON", 10),
            ("INT", 10),
            ("WIS", 10),
            ("CHA", 10),
        ],
        "Human",
        0,
        0, // no armour
    );
    apply_encumbrance(&mut state, &char_ref, "Unencumbered");

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "character_surprise_adj",
            vec![Value::Entity(char_ref)],
        )
        .unwrap();
    assert_eq!(expect_int(val, "DEX16 unenc no armour"), 2);
}

#[test]
fn surprise_adj_unencumbered_heavy_armour() {
    let (program, result) = compile_osric_encumbrance();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // DEX 16 → +1, Unencumbered + plate (cap 60ft) → no bonus (heavy armour)
    // Total: 1 + 0 = 1
    let char_ref = make_encumbrance_character(
        &mut state,
        "Test",
        &[
            ("STR", 10),
            ("DEX", 16),
            ("CON", 10),
            ("INT", 10),
            ("WIS", 10),
            ("CHA", 10),
        ],
        "Human",
        0,
        60, // plate armour cap
    );
    apply_encumbrance(&mut state, &char_ref, "Unencumbered");

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "character_surprise_adj",
            vec![Value::Entity(char_ref)],
        )
        .unwrap();
    assert_eq!(expect_int(val, "DEX16 unenc plate"), 1);
}

#[test]
fn surprise_adj_unencumbered_light_armour() {
    let (program, result) = compile_osric_encumbrance();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // DEX 16 → +1, Unencumbered + leather (cap 120ft) → +1 bonus (light armour)
    // Total: 1 + 1 = 2
    let char_ref = make_encumbrance_character(
        &mut state,
        "Test",
        &[
            ("STR", 10),
            ("DEX", 16),
            ("CON", 10),
            ("INT", 10),
            ("WIS", 10),
            ("CHA", 10),
        ],
        "Human",
        0,
        120, // leather armour cap (light)
    );
    apply_encumbrance(&mut state, &char_ref, "Unencumbered");

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "character_surprise_adj",
            vec![Value::Entity(char_ref)],
        )
        .unwrap();
    assert_eq!(expect_int(val, "DEX16 unenc leather"), 2);
}

#[test]
fn surprise_adj_light_encumbrance() {
    let (program, result) = compile_osric_encumbrance();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // DEX 16 → +1, Light encumbrance → normal (DEX applies, no bonus/penalty)
    // Total: 1
    let char_ref = make_encumbrance_character(
        &mut state,
        "Test",
        &[
            ("STR", 10),
            ("DEX", 16),
            ("CON", 10),
            ("INT", 10),
            ("WIS", 10),
            ("CHA", 10),
        ],
        "Human",
        0,
        0,
    );
    apply_encumbrance(&mut state, &char_ref, "Light");

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "character_surprise_adj",
            vec![Value::Entity(char_ref)],
        )
        .unwrap();
    assert_eq!(expect_int(val, "DEX16 light"), 1);
}

#[test]
fn surprise_adj_moderate_caps_bonuses() {
    let (program, result) = compile_osric_encumbrance();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // DEX 16 → +1, Moderate → min(0, 1) = 0. No bonuses.
    let char_ref = make_encumbrance_character(
        &mut state,
        "Test",
        &[
            ("STR", 10),
            ("DEX", 16),
            ("CON", 10),
            ("INT", 10),
            ("WIS", 10),
            ("CHA", 10),
        ],
        "Human",
        0,
        0,
    );
    apply_encumbrance(&mut state, &char_ref, "Moderate");

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "character_surprise_adj",
            vec![Value::Entity(char_ref)],
        )
        .unwrap();
    assert_eq!(expect_int(val, "DEX16 moderate"), 0);
}

#[test]
fn surprise_adj_moderate_preserves_penalties() {
    let (program, result) = compile_osric_encumbrance();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // DEX 3 → -3, Moderate → min(0, -3) = -3. Penalties preserved.
    let char_ref = make_encumbrance_character(
        &mut state,
        "Test",
        &[
            ("STR", 10),
            ("DEX", 3),
            ("CON", 10),
            ("INT", 10),
            ("WIS", 10),
            ("CHA", 10),
        ],
        "Human",
        0,
        0,
    );
    apply_encumbrance(&mut state, &char_ref, "Moderate");

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "character_surprise_adj",
            vec![Value::Entity(char_ref)],
        )
        .unwrap();
    assert_eq!(expect_int(val, "DEX3 moderate"), -3);
}

#[test]
fn surprise_adj_heavy_extra_penalty() {
    let (program, result) = compile_osric_encumbrance();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // DEX 16 → +1, Heavy → min(0, 1) - 1 = -1
    let char1 = make_encumbrance_character(
        &mut state,
        "HighDex",
        &[
            ("STR", 10),
            ("DEX", 16),
            ("CON", 10),
            ("INT", 10),
            ("WIS", 10),
            ("CHA", 10),
        ],
        "Human",
        0,
        0,
    );
    apply_encumbrance(&mut state, &char1, "Heavy");
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "character_surprise_adj",
            vec![Value::Entity(char1)],
        )
        .unwrap();
    assert_eq!(expect_int(val, "DEX16 heavy"), -1);

    // DEX 3 → -3, Heavy → min(0, -3) - 1 = -4
    let char2 = make_encumbrance_character(
        &mut state,
        "LowDex",
        &[
            ("STR", 10),
            ("DEX", 3),
            ("CON", 10),
            ("INT", 10),
            ("WIS", 10),
            ("CHA", 10),
        ],
        "Human",
        0,
        0,
    );
    apply_encumbrance(&mut state, &char2, "Heavy");
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "character_surprise_adj",
            vec![Value::Entity(char2)],
        )
        .unwrap();
    assert_eq!(expect_int(val, "DEX3 heavy"), -4);
}

#[test]
fn surprise_adj_overloaded() {
    let (program, result) = compile_osric_encumbrance();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // DEX 10 → 0, Overloaded → min(0, 0) - 1 = -1
    let char_ref =
        make_encumbrance_character(&mut state, "Test", &standard_abilities(), "Human", 0, 0);
    apply_encumbrance(&mut state, &char_ref, "Overloaded");

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "character_surprise_adj",
            vec![Value::Entity(char_ref)],
        )
        .unwrap();
    assert_eq!(expect_int(val, "DEX10 overloaded"), -1);
}

// ── update_encumbrance lifecycle ─────────────────────────────

#[test]
fn update_encumbrance_applies_correct_tier() {
    let (program, result) = compile_osric_encumbrance();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    // STR 10 → allowance 35. Weight 0 → Unencumbered.
    let char_ref =
        make_encumbrance_character(&mut state, "Test", &standard_abilities(), "Human", 0, 0);

    let adapter = StateAdapter::new(state);
    let mut handler = NullHandler;

    adapter.run(&mut handler, |s, h| {
        interp
            .evaluate_function(s, h, "update_encumbrance", vec![Value::Entity(char_ref)])
            .unwrap();
    });

    // Verify movement: Human 120ft, Unencumbered → 120ft
    let val = interp
        .evaluate_derive(
            &adapter,
            &mut handler,
            "character_movement",
            vec![Value::Entity(char_ref)],
        )
        .unwrap();
    assert_eq!(expect_feet(val, "unenc movement"), 120);

    let state = adapter.into_inner();

    // Now change weight to 76 (35 allowance + 41 over → Moderate) and recompute.
    let mut state = state;
    state.write_field(
        &char_ref,
        &[FieldPathSegment::Field(Name::from("current_weight"))],
        Value::Int(76),
    );

    let adapter = StateAdapter::new(state);
    adapter.run(&mut handler, |s, h| {
        interp
            .evaluate_function(s, h, "update_encumbrance", vec![Value::Entity(char_ref)])
            .unwrap();
    });

    // Moderate: 120 * 2/4 = 60
    let val = interp
        .evaluate_derive(
            &adapter,
            &mut handler,
            "character_movement",
            vec![Value::Entity(char_ref)],
        )
        .unwrap();
    assert_eq!(expect_feet(val, "moderate movement"), 60);
}

#[test]
fn update_encumbrance_replaces_previous_tier() {
    let (program, result) = compile_osric_encumbrance();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    // STR 10 → allowance 35. Weight 156 (121 over) → Overloaded.
    let char_ref =
        make_encumbrance_character(&mut state, "Test", &standard_abilities(), "Human", 156, 0);

    let adapter = StateAdapter::new(state);
    let mut handler = NullHandler;

    adapter.run(&mut handler, |s, h| {
        interp
            .evaluate_function(s, h, "update_encumbrance", vec![Value::Entity(char_ref)])
            .unwrap();
    });

    // Overloaded: 120 * 0/4 = 0
    let val = interp
        .evaluate_derive(
            &adapter,
            &mut handler,
            "character_movement",
            vec![Value::Entity(char_ref)],
        )
        .unwrap();
    assert_eq!(expect_feet(val, "overloaded"), 0);

    // Drop weight to 36 (1 over → Light). Call update again.
    adapter.run(&mut handler, |s, h| {
        h.handle(Effect::MutateField {
            entity: char_ref,
            path: vec![FieldPathSegment::Field(Name::from("current_weight"))],
            value: Value::Int(36),
            op: ttrpg_ast::ast::AssignOp::Eq,
            bounds: None,
        });
        interp
            .evaluate_function(s, h, "update_encumbrance", vec![Value::Entity(char_ref)])
            .unwrap();
    });

    // Light: 120 * 3/4 = 90
    let val = interp
        .evaluate_derive(
            &adapter,
            &mut handler,
            "character_movement",
            vec![Value::Entity(char_ref)],
        )
        .unwrap();
    assert_eq!(expect_feet(val, "light after update"), 90);
}
