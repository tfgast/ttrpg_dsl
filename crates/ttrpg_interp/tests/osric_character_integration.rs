//! OSRIC character integration test.
//!
//! Verifies that osric/osric_character.ttrpg parses, lowers, and type-checks
//! through the full multi-file pipeline (core + ability + character).
//! Tests all character derives at runtime.

use std::collections::BTreeMap;

use ttrpg_ast::ast::TopLevel;
use ttrpg_ast::Name;
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

mod osric_common;
use osric_common::*;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_character() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn osric_character_parses_and_typechecks() {
    let (program, _) = compile_osric_character();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSRIC"));
    assert!(system_names.contains(&"OSRIC Ability"));
    assert!(system_names.contains(&"OSRIC Character"));
}

// ── dex_ac_adj (AC = base + dex_ac_adj) ─────────────────────────

#[test]
fn dex_ac_adj_average_dex() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // DEX 10 → dex_ac_adj = 0
    let val = interp
        .evaluate_derive(&state, &mut handler, "dex_ac_adj", vec![Value::Int(10)])
        .unwrap();
    assert_eq!(expect_int(val, "dex_ac_adj"), 0);
}

#[test]
fn dex_ac_adj_high_dex() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // DEX 18 → dex_ac_adj = +4
    let val = interp
        .evaluate_derive(&state, &mut handler, "dex_ac_adj", vec![Value::Int(18)])
        .unwrap();
    assert_eq!(expect_int(val, "dex_ac_adj"), 4);
}

#[test]
fn dex_ac_adj_low_dex() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // DEX 3 → dex_ac_adj = -4
    let val = interp
        .evaluate_derive(&state, &mut handler, "dex_ac_adj", vec![Value::Int(3)])
        .unwrap();
    assert_eq!(expect_int(val, "dex_ac_adj"), -4);
}

#[test]
fn dex_ac_adj_good_dex() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // DEX 16 → dex_ac_adj = +2
    let val = interp
        .evaluate_derive(&state, &mut handler, "dex_ac_adj", vec![Value::Int(16)])
        .unwrap();
    assert_eq!(expect_int(val, "dex_ac_adj"), 2);
}

// ── apply_ancestry_mods ────────────────────────────────────────

#[test]
fn apply_ancestry_mods_human_no_change() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let scores = ability_map(&[
        ("STR", 14),
        ("DEX", 12),
        ("CON", 13),
        ("INT", 10),
        ("WIS", 11),
        ("CHA", 9),
    ]);

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "apply_ancestry_mods",
            vec![scores, ancestry("Human")],
        )
        .unwrap();

    match val {
        Value::Map(map) => {
            assert_eq!(map[&ability("STR")], Value::Int(14));
            assert_eq!(map[&ability("DEX")], Value::Int(12));
            assert_eq!(map[&ability("CON")], Value::Int(13));
            assert_eq!(map[&ability("INT")], Value::Int(10));
            assert_eq!(map[&ability("WIS")], Value::Int(11));
            assert_eq!(map[&ability("CHA")], Value::Int(9));
        }
        other => panic!("expected Map, got {other:?}"),
    }
}

#[test]
fn apply_ancestry_mods_dwarf() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Dwarf: CON +1, CHA -1
    let scores = ability_map(&[
        ("STR", 14),
        ("DEX", 12),
        ("CON", 13),
        ("INT", 10),
        ("WIS", 11),
        ("CHA", 9),
    ]);

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "apply_ancestry_mods",
            vec![scores, ancestry("Dwarf")],
        )
        .unwrap();

    match val {
        Value::Map(map) => {
            assert_eq!(map[&ability("STR")], Value::Int(14));
            assert_eq!(map[&ability("DEX")], Value::Int(12));
            assert_eq!(map[&ability("CON")], Value::Int(14)); // +1
            assert_eq!(map[&ability("INT")], Value::Int(10));
            assert_eq!(map[&ability("WIS")], Value::Int(11));
            assert_eq!(map[&ability("CHA")], Value::Int(8)); // -1
        }
        other => panic!("expected Map, got {other:?}"),
    }
}

#[test]
fn apply_ancestry_mods_elf() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Elf: DEX +1, CON -1
    let scores = ability_map(&[
        ("STR", 10),
        ("DEX", 14),
        ("CON", 12),
        ("INT", 15),
        ("WIS", 10),
        ("CHA", 13),
    ]);

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "apply_ancestry_mods",
            vec![scores, ancestry("Elf")],
        )
        .unwrap();

    match val {
        Value::Map(map) => {
            assert_eq!(map[&ability("STR")], Value::Int(10));
            assert_eq!(map[&ability("DEX")], Value::Int(15)); // +1
            assert_eq!(map[&ability("CON")], Value::Int(11)); // -1
            assert_eq!(map[&ability("INT")], Value::Int(15));
            assert_eq!(map[&ability("WIS")], Value::Int(10));
            assert_eq!(map[&ability("CHA")], Value::Int(13));
        }
        other => panic!("expected Map, got {other:?}"),
    }
}

#[test]
fn apply_ancestry_mods_half_orc() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // HalfOrc: STR +1, CON +1, CHA -2
    let scores = ability_map(&[
        ("STR", 14),
        ("DEX", 10),
        ("CON", 14),
        ("INT", 10),
        ("WIS", 10),
        ("CHA", 10),
    ]);

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "apply_ancestry_mods",
            vec![scores, ancestry("HalfOrc")],
        )
        .unwrap();

    match val {
        Value::Map(map) => {
            assert_eq!(map[&ability("STR")], Value::Int(15)); // +1
            assert_eq!(map[&ability("DEX")], Value::Int(10));
            assert_eq!(map[&ability("CON")], Value::Int(15)); // +1
            assert_eq!(map[&ability("INT")], Value::Int(10));
            assert_eq!(map[&ability("WIS")], Value::Int(10));
            assert_eq!(map[&ability("CHA")], Value::Int(8)); // -2
        }
        other => panic!("expected Map, got {other:?}"),
    }
}

#[test]
fn apply_ancestry_mods_halfling() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Halfling: STR -1, DEX +1
    let scores = ability_map(&[
        ("STR", 12),
        ("DEX", 14),
        ("CON", 12),
        ("INT", 10),
        ("WIS", 10),
        ("CHA", 10),
    ]);

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "apply_ancestry_mods",
            vec![scores, ancestry("Halfling")],
        )
        .unwrap();

    match val {
        Value::Map(map) => {
            assert_eq!(map[&ability("STR")], Value::Int(11)); // -1
            assert_eq!(map[&ability("DEX")], Value::Int(15)); // +1
            assert_eq!(map[&ability("CON")], Value::Int(12));
            assert_eq!(map[&ability("INT")], Value::Int(10));
            assert_eq!(map[&ability("WIS")], Value::Int(10));
            assert_eq!(map[&ability("CHA")], Value::Int(10));
        }
        other => panic!("expected Map, got {other:?}"),
    }
}

// ── check_ability_in_range ─────────────────────────────────────

#[test]
fn check_ability_in_range_within() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let range = Value::Struct {
        name: Name::from("AbilityRange"),
        fields: {
            let mut f = BTreeMap::new();
            f.insert(Name::from("min"), Value::Int(8));
            f.insert(Name::from("max"), Value::Int(18));
            f
        },
    };

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "check_ability_in_range",
            vec![Value::Int(12), range],
        )
        .unwrap();
    assert!(expect_bool(val, "check_ability_in_range(12, 8..18)"));
}

#[test]
fn check_ability_in_range_at_boundaries() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let make_range = |min: i64, max: i64| Value::Struct {
        name: Name::from("AbilityRange"),
        fields: {
            let mut f = BTreeMap::new();
            f.insert(Name::from("min"), Value::Int(min));
            f.insert(Name::from("max"), Value::Int(max));
            f
        },
    };

    // At min boundary
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "check_ability_in_range",
            vec![Value::Int(8), make_range(8, 18)],
        )
        .unwrap();
    assert!(expect_bool(val, "at min"));

    // At max boundary
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "check_ability_in_range",
            vec![Value::Int(18), make_range(8, 18)],
        )
        .unwrap();
    assert!(expect_bool(val, "at max"));

    // Below min
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "check_ability_in_range",
            vec![Value::Int(7), make_range(8, 18)],
        )
        .unwrap();
    assert!(!expect_bool(val, "below min"));

    // Above max
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "check_ability_in_range",
            vec![Value::Int(19), make_range(8, 18)],
        )
        .unwrap();
    assert!(!expect_bool(val, "above max"));
}

// ── validate_ancestry_scores ───────────────────────────────────

#[test]
fn validate_ancestry_scores_human_all_valid() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Human: all abilities 3-18
    let scores = ability_map(&[
        ("STR", 10),
        ("DEX", 10),
        ("CON", 10),
        ("INT", 10),
        ("WIS", 10),
        ("CHA", 10),
    ]);

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "validate_ancestry_scores",
            vec![scores, ancestry("Human")],
        )
        .unwrap();
    assert!(expect_bool(val, "human all 10s"));
}

#[test]
fn validate_ancestry_scores_dwarf_valid() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Dwarf ranges: STR 8-18, DEX 3-17, CON 12-19, INT 3-18, WIS 3-18, CHA 3-16
    let scores = ability_map(&[
        ("STR", 14),
        ("DEX", 12),
        ("CON", 15),
        ("INT", 10),
        ("WIS", 10),
        ("CHA", 10),
    ]);

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "validate_ancestry_scores",
            vec![scores, ancestry("Dwarf")],
        )
        .unwrap();
    assert!(expect_bool(val, "dwarf valid scores"));
}

#[test]
fn validate_ancestry_scores_dwarf_con_too_low() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Dwarf CON min is 12; score of 10 should fail
    let scores = ability_map(&[
        ("STR", 14),
        ("DEX", 12),
        ("CON", 10),
        ("INT", 10),
        ("WIS", 10),
        ("CHA", 10),
    ]);

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "validate_ancestry_scores",
            vec![scores, ancestry("Dwarf")],
        )
        .unwrap();
    assert!(!expect_bool(val, "dwarf CON too low"));
}

#[test]
fn validate_ancestry_scores_half_orc_cha_too_high() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // HalfOrc CHA max is 12; score of 14 should fail
    let scores = ability_map(&[
        ("STR", 14),
        ("DEX", 10),
        ("CON", 15),
        ("INT", 10),
        ("WIS", 10),
        ("CHA", 14),
    ]);

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "validate_ancestry_scores",
            vec![scores, ancestry("HalfOrc")],
        )
        .unwrap();
    assert!(!expect_bool(val, "half-orc CHA too high"));
}

// ── meets_class_requirements ───────────────────────────────────

#[test]
fn meets_class_requirements_fighter_passes() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Fighter: STR 9, DEX 6, CON 7, INT 3, WIS 6, CHA 6
    let scores = ability_map(&[
        ("STR", 15),
        ("DEX", 10),
        ("CON", 12),
        ("INT", 10),
        ("WIS", 10),
        ("CHA", 10),
    ]);

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "meets_class_requirements",
            vec![class_variant("Fighter"), scores],
        )
        .unwrap();
    assert!(expect_bool(val, "fighter passes"));
}

#[test]
fn meets_class_requirements_fighter_fails_str() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Fighter needs STR >= 9; STR 8 should fail
    let scores = ability_map(&[
        ("STR", 8),
        ("DEX", 10),
        ("CON", 12),
        ("INT", 10),
        ("WIS", 10),
        ("CHA", 10),
    ]);

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "meets_class_requirements",
            vec![class_variant("Fighter"), scores],
        )
        .unwrap();
    assert!(!expect_bool(val, "fighter fails STR"));
}

#[test]
fn meets_class_requirements_fighter_at_minimums() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Fighter exact minimums: STR 9, DEX 6, CON 7, INT 3, WIS 6, CHA 6
    let scores = ability_map(&[
        ("STR", 9),
        ("DEX", 6),
        ("CON", 7),
        ("INT", 3),
        ("WIS", 6),
        ("CHA", 6),
    ]);

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "meets_class_requirements",
            vec![class_variant("Fighter"), scores],
        )
        .unwrap();
    assert!(expect_bool(val, "fighter at minimums"));
}

#[test]
fn meets_class_requirements_paladin_passes() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Paladin: STR 12, DEX 6, CON 9, INT 9, WIS 13, CHA 17
    let scores = ability_map(&[
        ("STR", 16),
        ("DEX", 10),
        ("CON", 14),
        ("INT", 12),
        ("WIS", 16),
        ("CHA", 17),
    ]);

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "meets_class_requirements",
            vec![class_variant("Paladin"), scores],
        )
        .unwrap();
    assert!(expect_bool(val, "paladin passes"));
}

#[test]
fn meets_class_requirements_paladin_fails_cha() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Paladin needs CHA >= 17; CHA 16 should fail
    let scores = ability_map(&[
        ("STR", 16),
        ("DEX", 10),
        ("CON", 14),
        ("INT", 12),
        ("WIS", 16),
        ("CHA", 16),
    ]);

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "meets_class_requirements",
            vec![class_variant("Paladin"), scores],
        )
        .unwrap();
    assert!(!expect_bool(val, "paladin fails CHA"));
}

#[test]
fn meets_class_requirements_thief_minimal() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Thief requires STR 6, DEX 9, CON 6, INT 6, CHA 6
    let scores = ability_map(&[
        ("STR", 6),
        ("DEX", 9),
        ("CON", 6),
        ("INT", 6),
        ("WIS", 3),
        ("CHA", 6),
    ]);

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "meets_class_requirements",
            vec![class_variant("Thief"), scores],
        )
        .unwrap();
    assert!(expect_bool(val, "thief minimal"));
}

#[test]
fn meets_class_requirements_thief_fails() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Thief needs DEX >= 9; DEX 8 should fail
    let scores = ability_map(&[
        ("STR", 10),
        ("DEX", 8),
        ("CON", 10),
        ("INT", 10),
        ("WIS", 10),
        ("CHA", 10),
    ]);

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "meets_class_requirements",
            vec![class_variant("Thief"), scores],
        )
        .unwrap();
    assert!(!expect_bool(val, "thief fails DEX"));
}

#[test]
fn meets_class_requirements_ranger_passes() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Ranger: STR 13, DEX 6, CON 14, INT 13, WIS 14, CHA 6
    let scores = ability_map(&[
        ("STR", 15),
        ("DEX", 10),
        ("CON", 16),
        ("INT", 14),
        ("WIS", 15),
        ("CHA", 10),
    ]);

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "meets_class_requirements",
            vec![class_variant("Ranger"), scores],
        )
        .unwrap();
    assert!(expect_bool(val, "ranger passes"));
}

#[test]
fn meets_class_requirements_ranger_fails_con() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Ranger needs CON >= 14; CON 13 should fail
    let scores = ability_map(&[
        ("STR", 15),
        ("DEX", 10),
        ("CON", 13),
        ("INT", 14),
        ("WIS", 15),
        ("CHA", 10),
    ]);

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "meets_class_requirements",
            vec![class_variant("Ranger"), scores],
        )
        .unwrap();
    assert!(!expect_bool(val, "ranger fails CON"));
}

#[test]
fn meets_class_requirements_druid_passes() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Druid: STR 6, CON 6, INT 6, WIS 12, CHA 15
    let scores = ability_map(&[
        ("STR", 10),
        ("DEX", 10),
        ("CON", 10),
        ("INT", 10),
        ("WIS", 14),
        ("CHA", 16),
    ]);

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "meets_class_requirements",
            vec![class_variant("Druid"), scores],
        )
        .unwrap();
    assert!(expect_bool(val, "druid passes"));
}

#[test]
fn meets_class_requirements_druid_fails_cha() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Druid needs CHA >= 15; CHA 14 should fail
    let scores = ability_map(&[
        ("STR", 10),
        ("DEX", 10),
        ("CON", 10),
        ("INT", 10),
        ("WIS", 14),
        ("CHA", 14),
    ]);

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "meets_class_requirements",
            vec![class_variant("Druid"), scores],
        )
        .unwrap();
    assert!(!expect_bool(val, "druid fails CHA"));
}

#[test]
fn meets_class_requirements_illusionist_passes() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Illusionist: STR 6, DEX 16, INT 15, WIS 6, CHA 6
    let scores = ability_map(&[
        ("STR", 10),
        ("DEX", 17),
        ("CON", 10),
        ("INT", 16),
        ("WIS", 10),
        ("CHA", 10),
    ]);

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "meets_class_requirements",
            vec![class_variant("Illusionist"), scores],
        )
        .unwrap();
    assert!(expect_bool(val, "illusionist passes"));
}

#[test]
fn meets_class_requirements_illusionist_fails_dex() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Illusionist needs DEX >= 16; DEX 15 should fail
    let scores = ability_map(&[
        ("STR", 10),
        ("DEX", 15),
        ("CON", 10),
        ("INT", 16),
        ("WIS", 10),
        ("CHA", 10),
    ]);

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "meets_class_requirements",
            vec![class_variant("Illusionist"), scores],
        )
        .unwrap();
    assert!(!expect_bool(val, "illusionist fails DEX"));
}

// ── prime_req_xp_bonus ─────────────────────────────────────────

#[test]
fn prime_req_xp_bonus_fighter_at_boundary() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Fighter: 10% if STR >= 16
    // STR 15 → 0%
    let scores_15 = ability_map(&[
        ("STR", 15),
        ("DEX", 10),
        ("CON", 10),
        ("INT", 10),
        ("WIS", 10),
        ("CHA", 10),
    ]);
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "prime_req_xp_bonus",
            vec![class_variant("Fighter"), scores_15],
        )
        .unwrap();
    assert_eq!(expect_int(val, "fighter STR 15"), 0);

    // STR 16 → 10%
    let scores_16 = ability_map(&[
        ("STR", 16),
        ("DEX", 10),
        ("CON", 10),
        ("INT", 10),
        ("WIS", 10),
        ("CHA", 10),
    ]);
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "prime_req_xp_bonus",
            vec![class_variant("Fighter"), scores_16],
        )
        .unwrap();
    assert_eq!(expect_int(val, "fighter STR 16"), 10);
}

#[test]
fn prime_req_xp_bonus_paladin_both_required() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Paladin: 10% if STR 16+ AND WIS 16+
    // Both high → 10%
    let scores_both = ability_map(&[
        ("STR", 16),
        ("DEX", 10),
        ("CON", 10),
        ("INT", 10),
        ("WIS", 16),
        ("CHA", 17),
    ]);
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "prime_req_xp_bonus",
            vec![class_variant("Paladin"), scores_both],
        )
        .unwrap();
    assert_eq!(expect_int(val, "paladin both 16+"), 10);

    // Only STR high → 0%
    let scores_str_only = ability_map(&[
        ("STR", 16),
        ("DEX", 10),
        ("CON", 10),
        ("INT", 10),
        ("WIS", 15),
        ("CHA", 17),
    ]);
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "prime_req_xp_bonus",
            vec![class_variant("Paladin"), scores_str_only],
        )
        .unwrap();
    assert_eq!(expect_int(val, "paladin WIS 15"), 0);
}

#[test]
fn prime_req_xp_bonus_ranger_all_three_required() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Ranger: 10% if STR 16+ AND INT 16+ AND WIS 16+
    let scores_all = ability_map(&[
        ("STR", 16),
        ("DEX", 10),
        ("CON", 14),
        ("INT", 16),
        ("WIS", 16),
        ("CHA", 10),
    ]);
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "prime_req_xp_bonus",
            vec![class_variant("Ranger"), scores_all],
        )
        .unwrap();
    assert_eq!(expect_int(val, "ranger all 16+"), 10);

    // Missing INT → 0%
    let scores_no_int = ability_map(&[
        ("STR", 16),
        ("DEX", 10),
        ("CON", 14),
        ("INT", 15),
        ("WIS", 16),
        ("CHA", 10),
    ]);
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "prime_req_xp_bonus",
            vec![class_variant("Ranger"), scores_no_int],
        )
        .unwrap();
    assert_eq!(expect_int(val, "ranger INT 15"), 0);
}

#[test]
fn prime_req_xp_bonus_cleric() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Cleric: 10% if WIS 16+
    let scores = ability_map(&[
        ("STR", 10),
        ("DEX", 10),
        ("CON", 10),
        ("INT", 10),
        ("WIS", 16),
        ("CHA", 10),
    ]);
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "prime_req_xp_bonus",
            vec![class_variant("Cleric"), scores],
        )
        .unwrap();
    assert_eq!(expect_int(val, "cleric WIS 16"), 10);

    let scores_low = ability_map(&[
        ("STR", 10),
        ("DEX", 10),
        ("CON", 10),
        ("INT", 10),
        ("WIS", 15),
        ("CHA", 10),
    ]);
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "prime_req_xp_bonus",
            vec![class_variant("Cleric"), scores_low],
        )
        .unwrap();
    assert_eq!(expect_int(val, "cleric WIS 15"), 0);
}

#[test]
fn prime_req_xp_bonus_magic_user() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // MagicUser: 10% if INT 16+
    let scores = ability_map(&[
        ("STR", 10),
        ("DEX", 10),
        ("CON", 10),
        ("INT", 16),
        ("WIS", 10),
        ("CHA", 10),
    ]);
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "prime_req_xp_bonus",
            vec![class_variant("MagicUser"), scores],
        )
        .unwrap();
    assert_eq!(expect_int(val, "magic-user INT 16"), 10);
}

#[test]
fn prime_req_xp_bonus_thief() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Thief: 10% if DEX 16+
    let scores = ability_map(&[
        ("STR", 10),
        ("DEX", 16),
        ("CON", 10),
        ("INT", 10),
        ("WIS", 10),
        ("CHA", 10),
    ]);
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "prime_req_xp_bonus",
            vec![class_variant("Thief"), scores],
        )
        .unwrap();
    assert_eq!(expect_int(val, "thief DEX 16"), 10);
}

#[test]
fn prime_req_xp_bonus_no_bonus_classes() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Assassin, Illusionist, Monk: always 0 regardless of scores
    let high_scores = ability_map(&[
        ("STR", 18),
        ("DEX", 18),
        ("CON", 18),
        ("INT", 18),
        ("WIS", 18),
        ("CHA", 18),
    ]);

    for class_name in ["Assassin", "Illusionist", "Monk"] {
        let val = interp
            .evaluate_derive(
                &state,
                &mut handler,
                "prime_req_xp_bonus",
                vec![class_variant(class_name), high_scores.clone()],
            )
            .unwrap();
        assert_eq!(expect_int(val, &format!("{class_name} no bonus")), 0);
    }
}

#[test]
fn prime_req_xp_bonus_druid_both_required() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Druid: 10% if WIS 16+ AND CHA 16+
    let scores_both = ability_map(&[
        ("STR", 10),
        ("DEX", 10),
        ("CON", 10),
        ("INT", 10),
        ("WIS", 16),
        ("CHA", 16),
    ]);
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "prime_req_xp_bonus",
            vec![class_variant("Druid"), scores_both],
        )
        .unwrap();
    assert_eq!(expect_int(val, "druid both 16+"), 10);

    // Only WIS high → 0%
    let scores_wis_only = ability_map(&[
        ("STR", 10),
        ("DEX", 10),
        ("CON", 10),
        ("INT", 10),
        ("WIS", 16),
        ("CHA", 15),
    ]);
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "prime_req_xp_bonus",
            vec![class_variant("Druid"), scores_wis_only],
        )
        .unwrap();
    assert_eq!(expect_int(val, "druid CHA 15"), 0);
}

// ── base_movement ──────────────────────────────────────────────

#[test]
fn base_movement_per_ancestry() {
    let (program, result) = compile_osric_character();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Small ancestries: 90ft; Medium/Human: 120ft
    let cases = [
        ("Dwarf", 90),
        ("Elf", 120),
        ("Gnome", 90),
        ("HalfElf", 120),
        ("HalfOrc", 120),
        ("Halfling", 90),
        ("Human", 120),
    ];

    for (name, expected_ft) in cases {
        let val = interp
            .evaluate_derive(&state, &mut handler, "base_movement", vec![ancestry(name)])
            .unwrap();
        assert_eq!(
            expect_feet(val, &format!("base_movement({name})")),
            expected_ft,
            "base_movement({name})"
        );
    }
}
