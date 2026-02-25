//! OSE magic & turn undead integration test.
//!
//! Verifies that ose/ose_magic.ttrpg (combined with ose/ose_core.ttrpg)
//! parses, lowers, type-checks, and evaluates correctly through the full
//! pipeline: parse → lower → check → interpret.

use std::collections::BTreeMap;

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_ast::diagnostic::Severity;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

// ── Compile helpers ────────────────────────────────────────────

/// Test harness derives that wrap table lookups for direct evaluation.
/// Tables can't be called directly via evaluate_derive — they must be
/// invoked from within a derive/mechanic body.
const TEST_HARNESS: &str = r#"
system "OSE Magic" {
    derive test_spell_slots(progression: SpellProgression, level: int) -> list<int> {
        spell_slots(progression, level)
    }
}
"#;

/// Compile both OSE files through the multi-file pipeline.
fn compile_ose_magic() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    let core_source = include_str!("../../../ose/ose_core.ttrpg");
    let magic_source = include_str!("../../../ose/ose_magic.ttrpg");

    let sources = vec![
        ("ose/ose_core.ttrpg".to_string(), core_source.to_string()),
        ("ose/ose_magic.ttrpg".to_string(), magic_source.to_string()),
        ("test_harness.ttrpg".to_string(), TEST_HARNESS.to_string()),
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

/// Helper: create a SpellProgression enum variant value.
fn spell_prog(variant: &str) -> Value {
    Value::EnumVariant {
        enum_name: "SpellProgression".into(),
        variant: variant.into(),
        fields: BTreeMap::new(),
    }
}

/// Helper: create a list<int> value.
fn int_list(vals: &[i64]) -> Value {
    Value::List(vals.iter().map(|&v| Value::Int(v)).collect())
}

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn ose_magic_parses_and_typechecks() {
    let (program, _) = compile_ose_magic();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSE"));
    assert!(system_names.contains(&"OSE Magic"));
}

// ── Table + derive declarations ────────────────────────────────

#[test]
fn ose_magic_has_expected_declarations() {
    let (program, _) = compile_ose_magic();

    let mut has_spell_slots_table = false;
    let mut has_can_cast = false;
    let mut has_total_spell_slots = false;
    let mut has_turn_undead_result = false;
    let mut has_undead_rank_from_hd = false;

    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSE Magic" {
                for decl in &sys.decls {
                    match &decl.node {
                        DeclKind::Table(t) if t.name == "spell_slots" => {
                            has_spell_slots_table = true;
                            assert_eq!(t.params.len(), 2);
                        }
                        DeclKind::Derive(f) if f.name == "can_cast" => {
                            has_can_cast = true;
                        }
                        DeclKind::Derive(f) if f.name == "total_spell_slots" => {
                            has_total_spell_slots = true;
                        }
                        DeclKind::Derive(f) if f.name == "turn_undead_result" => {
                            has_turn_undead_result = true;
                        }
                        DeclKind::Derive(f) if f.name == "undead_rank_from_hd" => {
                            has_undead_rank_from_hd = true;
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    assert!(has_spell_slots_table, "expected spell_slots table");
    assert!(has_can_cast, "expected can_cast derive");
    assert!(has_total_spell_slots, "expected total_spell_slots derive");
    assert!(has_turn_undead_result, "expected turn_undead_result derive");
    assert!(has_undead_rank_from_hd, "expected undead_rank_from_hd derive");
}

// ── Spell slot table lookups ───────────────────────────────────

#[test]
fn non_caster_has_no_spells() {
    let (program, result) = compile_ose_magic();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "test_spell_slots",
            vec![spell_prog("NonCaster"), Value::Int(14)],
        )
        .unwrap();
    assert_eq!(val, int_list(&[0, 0, 0, 0, 0, 0]));
}

#[test]
fn cleric_no_spells_level_1() {
    let (program, result) = compile_ose_magic();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "can_cast",
            vec![spell_prog("Cleric"), Value::Int(1)],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(false));
}

#[test]
fn cleric_gets_spells_level_2() {
    let (program, result) = compile_ose_magic();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "test_spell_slots",
            vec![spell_prog("Cleric"), Value::Int(2)],
        )
        .unwrap();
    assert_eq!(val, int_list(&[1, 0, 0, 0, 0, 0]));

    let can = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "can_cast",
            vec![spell_prog("Cleric"), Value::Int(2)],
        )
        .unwrap();
    assert_eq!(can, Value::Bool(true));
}

#[test]
fn cleric_level_14() {
    let (program, result) = compile_ose_magic();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "test_spell_slots",
            vec![spell_prog("Cleric"), Value::Int(14)],
        )
        .unwrap();
    assert_eq!(val, int_list(&[6, 5, 5, 5, 4, 0]));
}

#[test]
fn magic_user_level_1() {
    let (program, result) = compile_ose_magic();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "test_spell_slots",
            vec![spell_prog("ArcaneFull"), Value::Int(1)],
        )
        .unwrap();
    assert_eq!(val, int_list(&[1, 0, 0, 0, 0, 0]));
}

#[test]
fn magic_user_level_14() {
    let (program, result) = compile_ose_magic();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "test_spell_slots",
            vec![spell_prog("ArcaneFull"), Value::Int(14)],
        )
        .unwrap();
    assert_eq!(val, int_list(&[4, 4, 4, 4, 3, 3]));
}

#[test]
fn druid_level_7() {
    let (program, result) = compile_ose_magic();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "test_spell_slots",
            vec![spell_prog("Druid"), Value::Int(7)],
        )
        .unwrap();
    assert_eq!(val, int_list(&[3, 3, 2, 2, 1, 0]));
}

#[test]
fn bard_level_2() {
    let (program, result) = compile_ose_magic();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "test_spell_slots",
            vec![spell_prog("Bard"), Value::Int(2)],
        )
        .unwrap();
    assert_eq!(val, int_list(&[1, 0, 0, 0, 0, 0]));
}

#[test]
fn bard_level_14() {
    let (program, result) = compile_ose_magic();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "test_spell_slots",
            vec![spell_prog("Bard"), Value::Int(14)],
        )
        .unwrap();
    assert_eq!(val, int_list(&[4, 4, 3, 3, 0, 0]));
}

#[test]
fn half_elf_level_8() {
    let (program, result) = compile_ose_magic();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "test_spell_slots",
            vec![spell_prog("HalfElf"), Value::Int(8)],
        )
        .unwrap();
    assert_eq!(val, int_list(&[2, 2, 1, 0, 0, 0]));
}

#[test]
fn paladin_no_spells_level_8() {
    let (program, result) = compile_ose_magic();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let can = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "can_cast",
            vec![spell_prog("Paladin"), Value::Int(8)],
        )
        .unwrap();
    assert_eq!(can, Value::Bool(false));
}

#[test]
fn paladin_gets_spells_level_9() {
    let (program, result) = compile_ose_magic();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "test_spell_slots",
            vec![spell_prog("Paladin"), Value::Int(9)],
        )
        .unwrap();
    assert_eq!(val, int_list(&[1, 0, 0, 0, 0, 0]));
}

#[test]
fn ranger_level_10() {
    let (program, result) = compile_ose_magic();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "test_spell_slots",
            vec![spell_prog("Ranger"), Value::Int(10)],
        )
        .unwrap();
    assert_eq!(val, int_list(&[2, 1, 0, 0, 0, 0]));
}

#[test]
fn drow_level_1() {
    let (program, result) = compile_ose_magic();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "test_spell_slots",
            vec![spell_prog("Drow"), Value::Int(1)],
        )
        .unwrap();
    assert_eq!(val, int_list(&[1, 0, 0, 0, 0, 0]));
}

#[test]
fn drow_level_10() {
    let (program, result) = compile_ose_magic();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "test_spell_slots",
            vec![spell_prog("Drow"), Value::Int(10)],
        )
        .unwrap();
    assert_eq!(val, int_list(&[4, 4, 4, 3, 3, 0]));
}

#[test]
fn total_slots_magic_user_5() {
    let (program, result) = compile_ose_magic();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "total_spell_slots",
            vec![spell_prog("ArcaneFull"), Value::Int(5)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(5));
}

// ── Turn undead ────────────────────────────────────────────────

/// Helper to build a TurnResult enum variant.
fn turn_result(variant: &str, target: Option<i64>) -> Value {
    let fields = match target {
        Some(t) => {
            let mut m = BTreeMap::new();
            m.insert("target".into(), Value::Int(t));
            m
        }
        None => BTreeMap::new(),
    };
    Value::EnumVariant {
        enum_name: "TurnResult".into(),
        variant: variant.into(),
        fields,
    }
}

// --- Skeleton (rank 1) ---

#[test]
fn skeleton_level_1() {
    let (program, result) = compile_ose_magic();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // diff = 0, need 7
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "turn_undead_result",
            vec![Value::Int(1), Value::Int(1)],
        )
        .unwrap();
    assert_eq!(val, turn_result("Roll", Some(7)));
}

#[test]
fn skeleton_level_2() {
    let (program, result) = compile_ose_magic();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // diff = 1, auto turn
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "turn_undead_result",
            vec![Value::Int(2), Value::Int(1)],
        )
        .unwrap();
    assert_eq!(val, turn_result("Turned", None));
}

#[test]
fn skeleton_level_4() {
    let (program, result) = compile_ose_magic();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // diff = 3, destroy
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "turn_undead_result",
            vec![Value::Int(4), Value::Int(1)],
        )
        .unwrap();
    assert_eq!(val, turn_result("Destroyed", None));
}

// --- Zombie (rank 2) ---

#[test]
fn zombie_level_1() {
    let (program, result) = compile_ose_magic();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // diff = -1, need 9
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "turn_undead_result",
            vec![Value::Int(1), Value::Int(2)],
        )
        .unwrap();
    assert_eq!(val, turn_result("Roll", Some(9)));
}

#[test]
fn zombie_level_5() {
    let (program, result) = compile_ose_magic();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // diff = 3, destroy
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "turn_undead_result",
            vec![Value::Int(5), Value::Int(2)],
        )
        .unwrap();
    assert_eq!(val, turn_result("Destroyed", None));
}

// --- Ghoul (rank 3) ---

#[test]
fn ghoul_level_1() {
    let (program, result) = compile_ose_magic();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // diff = -2, need 11
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "turn_undead_result",
            vec![Value::Int(1), Value::Int(3)],
        )
        .unwrap();
    assert_eq!(val, turn_result("Roll", Some(11)));
}

// --- Wight (rank 4) ---

#[test]
fn wight_level_1() {
    let (program, result) = compile_ose_magic();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // diff = -3, impossible
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "turn_undead_result",
            vec![Value::Int(1), Value::Int(4)],
        )
        .unwrap();
    assert_eq!(val, turn_result("Impossible", None));
}

// --- Vampire (rank 8) ---

#[test]
fn vampire_level_6() {
    let (program, result) = compile_ose_magic();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // diff = -2, need 11
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "turn_undead_result",
            vec![Value::Int(6), Value::Int(8)],
        )
        .unwrap();
    assert_eq!(val, turn_result("Roll", Some(11)));
}

#[test]
fn vampire_level_8() {
    let (program, result) = compile_ose_magic();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // diff = 0, need 7
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "turn_undead_result",
            vec![Value::Int(8), Value::Int(8)],
        )
        .unwrap();
    assert_eq!(val, turn_result("Roll", Some(7)));
}

#[test]
fn vampire_level_9() {
    let (program, result) = compile_ose_magic();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // diff = 1, auto turn
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "turn_undead_result",
            vec![Value::Int(9), Value::Int(8)],
        )
        .unwrap();
    assert_eq!(val, turn_result("Turned", None));
}

#[test]
fn vampire_level_11() {
    let (program, result) = compile_ose_magic();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // diff = 3, destroy
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "turn_undead_result",
            vec![Value::Int(11), Value::Int(8)],
        )
        .unwrap();
    assert_eq!(val, turn_result("Destroyed", None));
}

// --- Infernal (rank 9) ---

#[test]
fn infernal_level_6() {
    let (program, result) = compile_ose_magic();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // diff = -3, impossible
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "turn_undead_result",
            vec![Value::Int(6), Value::Int(9)],
        )
        .unwrap();
    assert_eq!(val, turn_result("Impossible", None));
}

#[test]
fn infernal_level_12() {
    let (program, result) = compile_ose_magic();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // diff = 3, destroy
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "turn_undead_result",
            vec![Value::Int(12), Value::Int(9)],
        )
        .unwrap();
    assert_eq!(val, turn_result("Destroyed", None));
}

// --- undead_rank_from_hd ---

#[test]
fn undead_rank_clamps_low() {
    let (program, result) = compile_ose_magic();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "undead_rank_from_hd",
            vec![Value::Int(0)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(1));
}

#[test]
fn undead_rank_direct_mapping() {
    let (program, result) = compile_ose_magic();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    for hd in 1..=8 {
        let val = interp
            .evaluate_derive(
                &state,
                &mut handler,
                "undead_rank_from_hd",
                vec![Value::Int(hd)],
            )
            .unwrap();
        assert_eq!(val, Value::Int(hd), "rank for HD {} should be {}", hd, hd);
    }
}

#[test]
fn undead_rank_clamps_high() {
    let (program, result) = compile_ose_magic();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val9 = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "undead_rank_from_hd",
            vec![Value::Int(9)],
        )
        .unwrap();
    assert_eq!(val9, Value::Int(9));

    let val15 = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "undead_rank_from_hd",
            vec![Value::Int(15)],
        )
        .unwrap();
    assert_eq!(val15, Value::Int(9));

    let val100 = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "undead_rank_from_hd",
            vec![Value::Int(100)],
        )
        .unwrap();
    assert_eq!(val100, Value::Int(9));
}
