//! OSRIC multi-classing integration tests.
//!
//! Verifies the multi-class rules from osric/osric_multiclass.ttrpg:
//! valid combo validation, XP splitting, HP averaging, and armour
//! permission aggregation.

use ttrpg_ast::ast::TopLevel;
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

mod osric_common;
use osric_common::*;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_multiclass() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn osric_multiclass_parses_and_typechecks() {
    let (program, _) = compile_osric_multiclass();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSRIC Multiclass"));
}

// ── is_valid_multiclass ────────────────────────────────────────

fn check_valid_multiclass(
    interp: &Interpreter,
    state: &GameState,
    ancestry_name: &str,
    classes: &[&str],
    expected: bool,
    label: &str,
) {
    let mut handler = NullHandler;
    let class_list = Value::List(classes.iter().map(|c| class_variant(c)).collect());
    let val = interp
        .evaluate_derive(
            state,
            &mut handler,
            "is_valid_multiclass",
            vec![ancestry(ancestry_name), class_list],
        )
        .unwrap();
    assert_eq!(expect_bool(val, label), expected, "{label}");
}

#[test]
fn multiclass_human_always_invalid() {
    let (program, result) = compile_osric_multiclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    check_valid_multiclass(
        &interp,
        &state,
        "Human",
        &["Fighter", "Thief"],
        false,
        "human fighter/thief",
    );
}

#[test]
fn multiclass_single_class_invalid() {
    let (program, result) = compile_osric_multiclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    check_valid_multiclass(
        &interp,
        &state,
        "Elf",
        &["Fighter"],
        false,
        "elf single class",
    );
}

#[test]
fn multiclass_dwarf_fighter_thief() {
    let (program, result) = compile_osric_multiclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    check_valid_multiclass(
        &interp,
        &state,
        "Dwarf",
        &["Fighter", "Thief"],
        true,
        "dwarf fighter/thief",
    );
}

#[test]
fn multiclass_dwarf_fighter_cleric_invalid() {
    let (program, result) = compile_osric_multiclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    check_valid_multiclass(
        &interp,
        &state,
        "Dwarf",
        &["Fighter", "Cleric"],
        false,
        "dwarf fighter/cleric",
    );
}

#[test]
fn multiclass_elf_valid_combos() {
    let (program, result) = compile_osric_multiclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    check_valid_multiclass(
        &interp,
        &state,
        "Elf",
        &["Fighter", "MagicUser"],
        true,
        "elf fighter/mu",
    );
    check_valid_multiclass(
        &interp,
        &state,
        "Elf",
        &["Fighter", "Thief"],
        true,
        "elf fighter/thief",
    );
    check_valid_multiclass(
        &interp,
        &state,
        "Elf",
        &["MagicUser", "Thief"],
        true,
        "elf mu/thief",
    );
    check_valid_multiclass(
        &interp,
        &state,
        "Elf",
        &["Fighter", "MagicUser", "Thief"],
        true,
        "elf f/mu/t",
    );
}

#[test]
fn multiclass_elf_invalid_combo() {
    let (program, result) = compile_osric_multiclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    check_valid_multiclass(
        &interp,
        &state,
        "Elf",
        &["Fighter", "Cleric"],
        false,
        "elf fighter/cleric",
    );
    check_valid_multiclass(
        &interp,
        &state,
        "Elf",
        &["Thief", "Cleric"],
        false,
        "elf thief/cleric",
    );
}

#[test]
fn multiclass_gnome_valid_combos() {
    let (program, result) = compile_osric_multiclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    check_valid_multiclass(
        &interp,
        &state,
        "Gnome",
        &["Fighter", "Illusionist"],
        true,
        "gnome f/i",
    );
    check_valid_multiclass(
        &interp,
        &state,
        "Gnome",
        &["Fighter", "Thief"],
        true,
        "gnome f/t",
    );
    check_valid_multiclass(
        &interp,
        &state,
        "Gnome",
        &["Illusionist", "Thief"],
        true,
        "gnome i/t",
    );
}

#[test]
fn multiclass_half_elf_valid_combos() {
    let (program, result) = compile_osric_multiclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    check_valid_multiclass(
        &interp,
        &state,
        "HalfElf",
        &["Cleric", "Fighter"],
        true,
        "he c/f",
    );
    check_valid_multiclass(
        &interp,
        &state,
        "HalfElf",
        &["Cleric", "Ranger"],
        true,
        "he c/r",
    );
    check_valid_multiclass(
        &interp,
        &state,
        "HalfElf",
        &["Cleric", "MagicUser"],
        true,
        "he c/mu",
    );
    check_valid_multiclass(
        &interp,
        &state,
        "HalfElf",
        &["Fighter", "MagicUser"],
        true,
        "he f/mu",
    );
    check_valid_multiclass(
        &interp,
        &state,
        "HalfElf",
        &["Fighter", "Thief"],
        true,
        "he f/t",
    );
    check_valid_multiclass(
        &interp,
        &state,
        "HalfElf",
        &["Cleric", "Fighter", "MagicUser"],
        true,
        "he c/f/mu",
    );
    check_valid_multiclass(
        &interp,
        &state,
        "HalfElf",
        &["Fighter", "MagicUser", "Thief"],
        true,
        "he f/mu/t",
    );
}

#[test]
fn multiclass_half_orc_valid_combos() {
    let (program, result) = compile_osric_multiclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    check_valid_multiclass(
        &interp,
        &state,
        "HalfOrc",
        &["Cleric", "Fighter"],
        true,
        "ho c/f",
    );
    check_valid_multiclass(
        &interp,
        &state,
        "HalfOrc",
        &["Cleric", "Thief"],
        true,
        "ho c/t",
    );
    check_valid_multiclass(
        &interp,
        &state,
        "HalfOrc",
        &["Assassin", "Cleric"],
        true,
        "ho a/c",
    );
    check_valid_multiclass(
        &interp,
        &state,
        "HalfOrc",
        &["Fighter", "Thief"],
        true,
        "ho f/t",
    );
    check_valid_multiclass(
        &interp,
        &state,
        "HalfOrc",
        &["Assassin", "Fighter"],
        true,
        "ho a/f",
    );
}

#[test]
fn multiclass_halfling_valid_combo() {
    let (program, result) = compile_osric_multiclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    check_valid_multiclass(
        &interp,
        &state,
        "Halfling",
        &["Fighter", "Thief"],
        true,
        "halfling f/t",
    );
    check_valid_multiclass(
        &interp,
        &state,
        "Halfling",
        &["Fighter", "Cleric"],
        false,
        "halfling f/c",
    );
}

#[test]
fn multiclass_reversed_order_still_valid() {
    let (program, result) = compile_osric_multiclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Classes listed in reverse order should still validate (sort_classes normalizes)
    check_valid_multiclass(
        &interp,
        &state,
        "Elf",
        &["Thief", "Fighter"],
        true,
        "elf thief/fighter reversed",
    );
    check_valid_multiclass(
        &interp,
        &state,
        "Elf",
        &["Thief", "MagicUser", "Fighter"],
        true,
        "elf t/mu/f reversed",
    );
}

// ── split_xp ───────────────────────────────────────────────────

#[test]
fn split_xp_two_classes() {
    let (program, result) = compile_osric_multiclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // 125 XP / 2 classes = 62 (drop fraction)
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "split_xp",
            vec![Value::Int(125), Value::Int(2)],
        )
        .unwrap();
    assert_eq!(expect_int(val, "125/2"), 62);
}

#[test]
fn split_xp_three_classes() {
    let (program, result) = compile_osric_multiclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // 100 XP / 3 classes = 33 (drop fraction)
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "split_xp",
            vec![Value::Int(100), Value::Int(3)],
        )
        .unwrap();
    assert_eq!(expect_int(val, "100/3"), 33);
}

#[test]
fn split_xp_even_division() {
    let (program, result) = compile_osric_multiclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // 300 XP / 3 classes = 100 (no fraction)
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "split_xp",
            vec![Value::Int(300), Value::Int(3)],
        )
        .unwrap();
    assert_eq!(expect_int(val, "300/3"), 100);
}

// ── multiclass_hp_gain ─────────────────────────────────────────

#[test]
fn multiclass_hp_gain_example_from_rules() {
    let (program, result) = compile_osric_multiclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // PG p.69 example: Erix the fighter/cleric/thief, CON 15 (+1 bonus).
    // Rolls 4 on thief d6. Total = 4 + 1 = 5. Divided by 3 = 1.67 → 1.
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "multiclass_hp_gain",
            vec![Value::Int(4), Value::Int(1), Value::Int(3)],
        )
        .unwrap();
    assert_eq!(expect_int(val, "4+1/3"), 1);
}

#[test]
fn multiclass_hp_gain_two_classes() {
    let (program, result) = compile_osric_multiclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Roll 8 on d10, CON mod +2 = 10. Divided by 2 = 5.
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "multiclass_hp_gain",
            vec![Value::Int(8), Value::Int(2), Value::Int(2)],
        )
        .unwrap();
    assert_eq!(expect_int(val, "8+2/2"), 5);
}

#[test]
fn multiclass_hp_gain_minimum_one() {
    let (program, result) = compile_osric_multiclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Roll 1 on d4, CON mod -2 = -1. Divided by 3 = 0 → min 1.
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "multiclass_hp_gain",
            vec![Value::Int(1), Value::Int(-2), Value::Int(3)],
        )
        .unwrap();
    assert_eq!(expect_int(val, "1-2/3 min 1"), 1);
}

// ── armour_permission_rank ─────────────────────────────────────

#[test]
fn armour_permission_rank_ordering() {
    let (program, result) = compile_osric_multiclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let cases = [
        ("NoArmour", 0),
        ("LeatherOnly", 1),
        ("LeatherWooden", 2),
        ("LeatherShield", 3),
        ("AnyArmour", 4),
    ];

    for (variant, expected) in cases {
        let val = interp
            .evaluate_derive(
                &state,
                &mut handler,
                "armour_permission_rank",
                vec![enum_variant("ArmourPermission", variant)],
            )
            .unwrap();
        assert_eq!(expect_int(val, variant), expected, "{variant}");
    }
}

// ── effective_armour_permission (entity-level) ─────────────────

#[test]
fn effective_armour_permission_fighter_thief() {
    let (program, result) = compile_osric_multiclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // Fighter = any_armour (rank 4), Thief = leather_only (rank 1)
    // Most restrictive = leather_only
    let char_ref =
        make_multiclass_character(&mut state, "Erix", &[("Fighter", 3), ("Thief", 3)], "Dwarf");
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "effective_armour_permission",
            vec![Value::Entity(char_ref)],
        )
        .unwrap();
    assert_eq!(val, enum_variant("ArmourPermission", "LeatherOnly"));
}

#[test]
fn effective_armour_permission_fighter_magic_user() {
    let (program, result) = compile_osric_multiclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // Fighter = any_armour (rank 4), MagicUser = no_armour (rank 0)
    // Most restrictive = no_armour
    let char_ref = make_multiclass_character(
        &mut state,
        "Elminster",
        &[("Fighter", 5), ("MagicUser", 5)],
        "Elf",
    );
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "effective_armour_permission",
            vec![Value::Entity(char_ref)],
        )
        .unwrap();
    assert_eq!(val, enum_variant("ArmourPermission", "NoArmour"));
}

#[test]
fn effective_armour_permission_cleric_fighter() {
    let (program, result) = compile_osric_multiclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // Cleric = any_armour (rank 4), Fighter = any_armour (rank 4)
    // Both any_armour → any_armour
    let char_ref = make_multiclass_character(
        &mut state,
        "Grom",
        &[("Cleric", 3), ("Fighter", 3)],
        "HalfOrc",
    );
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "effective_armour_permission",
            vec![Value::Entity(char_ref)],
        )
        .unwrap();
    assert_eq!(val, enum_variant("ArmourPermission", "AnyArmour"));
}

// ── num_classes ────────────────────────────────────────────────

#[test]
fn num_classes_single_and_multi() {
    let (program, result) = compile_osric_multiclass();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    let single_ref = make_multiclass_character(&mut state, "Solo", &[("Fighter", 5)], "Human");
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "num_classes",
            vec![Value::Entity(single_ref)],
        )
        .unwrap();
    assert_eq!(expect_int(val, "single class"), 1);

    let multi_ref =
        make_multiclass_character(&mut state, "Duo", &[("Fighter", 3), ("Thief", 3)], "Elf");
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "num_classes",
            vec![Value::Entity(multi_ref)],
        )
        .unwrap();
    assert_eq!(expect_int(val, "two classes"), 2);

    let triple_ref = make_multiclass_character(
        &mut state,
        "Trio",
        &[("Fighter", 3), ("MagicUser", 3), ("Thief", 3)],
        "Elf",
    );
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "num_classes",
            vec![Value::Entity(triple_ref)],
        )
        .unwrap();
    assert_eq!(expect_int(val, "three classes"), 3);
}
