//! Integration tests for `table` declarations: static lookup tables.
//!
//! Tests the full pipeline: parse → lower → check → interpret, verifying
//! that tables are properly parsed, type-checked, and evaluated at runtime.

use std::collections::{BTreeMap, HashMap};

use ttrpg_ast::diagnostic::Severity;
use ttrpg_ast::FileId;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

// ── Setup ──────────────────────────────────────────────────────

fn compile(source: &str) -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    let (program, parse_errors) = ttrpg_parser::parse(source, FileId::SYNTH);
    assert!(
        parse_errors.is_empty(),
        "parse errors: {:?}",
        parse_errors.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    let mut lower_diags = Vec::new();
    let program = ttrpg_parser::lower_moves(program, &mut lower_diags);
    assert!(
        lower_diags.is_empty(),
        "lowering errors: {:?}",
        lower_diags.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    let result = ttrpg_checker::check(&program);
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
    (program, result)
}

struct NullHandler;
impl EffectHandler for NullHandler {
    fn handle(&mut self, _effect: Effect) -> Response {
        Response::Acknowledged
    }
}

// ── 1D table: enum → enum mapping ─────────────────────────────

const SKILL_ABILITY_TABLE: &str = r#"
system "test" {
    enum Ability { STR, DEX, CON, INT, WIS, CHA }
    enum Skill { athletics, acrobatics, stealth, arcana, perception }

    table skill_ability(skill: Skill) -> Ability {
        athletics  => STR,
        acrobatics => DEX,
        stealth    => DEX,
        arcana     => INT,
        perception => WIS
    }

    derive test_athletics() -> Ability {
        skill_ability(athletics)
    }

    derive test_arcana() -> Ability {
        skill_ability(arcana)
    }

    derive test_stealth() -> Ability {
        skill_ability(stealth)
    }
}
"#;

#[test]
fn table_1d_enum_to_enum() {
    let (program, result) = compile(SKILL_ABILITY_TABLE);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "test_athletics", vec![])
        .unwrap();
    assert_eq!(
        val,
        Value::EnumVariant {
            enum_name: "Ability".into(),
            variant: "STR".into(),
            fields: BTreeMap::new()
        }
    );

    let val = interp
        .evaluate_derive(&state, &mut handler, "test_arcana", vec![])
        .unwrap();
    assert_eq!(
        val,
        Value::EnumVariant {
            enum_name: "Ability".into(),
            variant: "INT".into(),
            fields: BTreeMap::new()
        }
    );

    let val = interp
        .evaluate_derive(&state, &mut handler, "test_stealth", vec![])
        .unwrap();
    assert_eq!(
        val,
        Value::EnumVariant {
            enum_name: "Ability".into(),
            variant: "DEX".into(),
            fields: BTreeMap::new()
        }
    );
}

// ── 1D table: enum → int mapping ──────────────────────────────

const COVER_BONUS_TABLE: &str = r#"
system "test" {
    enum CoverType { no_cover, half_cover, three_quarters_cover, full_cover }

    table cover_AC_bonus(cover: CoverType) -> int {
        no_cover             => 0,
        half_cover           => 2,
        three_quarters_cover => 5,
        full_cover           => 0
    }

    derive test_half() -> int {
        cover_AC_bonus(half_cover)
    }

    derive test_none() -> int {
        cover_AC_bonus(no_cover)
    }

    derive test_three_quarters() -> int {
        cover_AC_bonus(three_quarters_cover)
    }
}
"#;

#[test]
fn table_1d_enum_to_int() {
    let (program, result) = compile(COVER_BONUS_TABLE);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "test_half", vec![])
        .unwrap();
    assert_eq!(val, Value::Int(2));

    let val = interp
        .evaluate_derive(&state, &mut handler, "test_none", vec![])
        .unwrap();
    assert_eq!(val, Value::Int(0));

    let val = interp
        .evaluate_derive(&state, &mut handler, "test_three_quarters", vec![])
        .unwrap();
    assert_eq!(val, Value::Int(5));
}

// ── 2D table with int ranges ──────────────────────────────────

const THAC0_TABLE: &str = r#"
system "test" {
    enum Class { Fighter, Cleric, Thief, MagicUser }

    table thac0(class: Class, level: int) -> int {
        [Fighter,   1..=3]  => 19,
        [Fighter,   4..=6]  => 17,
        [Fighter,   7..=9]  => 14,
        [Cleric,    1..=4]  => 19,
        [Cleric,    5..=8]  => 17,
        [Thief,     1..=4]  => 19,
        [Thief,     5..=8]  => 17,
        [MagicUser, 1..=5]  => 19,
        [MagicUser, 6..=10] => 17
    }

    derive test_fighter_1() -> int { thac0(Fighter, 1) }
    derive test_fighter_3() -> int { thac0(Fighter, 3) }
    derive test_fighter_5() -> int { thac0(Fighter, 5) }
    derive test_fighter_7() -> int { thac0(Fighter, 7) }
    derive test_cleric_3() -> int { thac0(Cleric, 3) }
    derive test_cleric_6() -> int { thac0(Cleric, 6) }
    derive test_mu_1() -> int { thac0(MagicUser, 1) }
    derive test_mu_10() -> int { thac0(MagicUser, 10) }
}
"#;

#[test]
fn table_2d_with_ranges() {
    let (program, result) = compile(THAC0_TABLE);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Fighter levels 1-3 → 19
    assert_eq!(
        interp
            .evaluate_derive(&state, &mut handler, "test_fighter_1", vec![])
            .unwrap(),
        Value::Int(19)
    );
    assert_eq!(
        interp
            .evaluate_derive(&state, &mut handler, "test_fighter_3", vec![])
            .unwrap(),
        Value::Int(19)
    );
    // Fighter levels 4-6 → 17
    assert_eq!(
        interp
            .evaluate_derive(&state, &mut handler, "test_fighter_5", vec![])
            .unwrap(),
        Value::Int(17)
    );
    // Fighter levels 7-9 → 14
    assert_eq!(
        interp
            .evaluate_derive(&state, &mut handler, "test_fighter_7", vec![])
            .unwrap(),
        Value::Int(14)
    );
    // Cleric levels 1-4 → 19
    assert_eq!(
        interp
            .evaluate_derive(&state, &mut handler, "test_cleric_3", vec![])
            .unwrap(),
        Value::Int(19)
    );
    // Cleric levels 5-8 → 17
    assert_eq!(
        interp
            .evaluate_derive(&state, &mut handler, "test_cleric_6", vec![])
            .unwrap(),
        Value::Int(17)
    );
    // MagicUser levels 1-5 → 19, 6-10 → 17
    assert_eq!(
        interp
            .evaluate_derive(&state, &mut handler, "test_mu_1", vec![])
            .unwrap(),
        Value::Int(19)
    );
    assert_eq!(
        interp
            .evaluate_derive(&state, &mut handler, "test_mu_10", vec![])
            .unwrap(),
        Value::Int(17)
    );
}

// ── Table with wildcard (default) entry ───────────────────────

const WILDCARD_TABLE: &str = r#"
system "test" {
    table proficiency_bonus(level: int) -> int {
        1..=4   => 2,
        5..=8   => 3,
        9..=12  => 4,
        13..=16 => 5,
        17..=20 => 6,
        _       => 0
    }

    derive test_level_1() -> int { proficiency_bonus(1) }
    derive test_level_10() -> int { proficiency_bonus(10) }
    derive test_level_20() -> int { proficiency_bonus(20) }
    derive test_level_99() -> int { proficiency_bonus(99) }
}
"#;

#[test]
fn table_wildcard_default() {
    let (program, result) = compile(WILDCARD_TABLE);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    assert_eq!(
        interp
            .evaluate_derive(&state, &mut handler, "test_level_1", vec![])
            .unwrap(),
        Value::Int(2)
    );
    assert_eq!(
        interp
            .evaluate_derive(&state, &mut handler, "test_level_10", vec![])
            .unwrap(),
        Value::Int(4)
    );
    assert_eq!(
        interp
            .evaluate_derive(&state, &mut handler, "test_level_20", vec![])
            .unwrap(),
        Value::Int(6)
    );
    // Out-of-range → wildcard default
    assert_eq!(
        interp
            .evaluate_derive(&state, &mut handler, "test_level_99", vec![])
            .unwrap(),
        Value::Int(0)
    );
}

// ── Table with struct values ──────────────────────────────────

const STRUCT_VALUE_TABLE: &str = r#"
system "test" {
    enum Class { Fighter, Thief }
    struct SavingThrows {
        death: int
        wand: int
        paralysis: int
        breath: int
        spell: int
    }

    table saving_throws(class: Class, level: int) -> SavingThrows {
        [Fighter, 1..=3] => SavingThrows { death: 12, wand: 13, paralysis: 14, breath: 15, spell: 16 },
        [Fighter, 4..=6] => SavingThrows { death: 10, wand: 11, paralysis: 12, breath: 13, spell: 14 },
        [Thief, 1..=4]   => SavingThrows { death: 13, wand: 14, paralysis: 13, breath: 16, spell: 15 },
        [Thief, 5..=8]   => SavingThrows { death: 12, wand: 13, paralysis: 11, breath: 14, spell: 13 }
    }

    derive fighter_death_save(level: int) -> int {
        saving_throws(Fighter, level).death
    }

    derive thief_wand_save(level: int) -> int {
        saving_throws(Thief, level).wand
    }
}
"#;

#[test]
fn table_struct_values() {
    let (program, result) = compile(STRUCT_VALUE_TABLE);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Fighter level 2 → death save 12
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "fighter_death_save",
            vec![Value::Int(2)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(12));

    // Fighter level 5 → death save 10
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "fighter_death_save",
            vec![Value::Int(5)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(10));

    // Thief level 3 → wand save 14
    let val = interp
        .evaluate_derive(&state, &mut handler, "thief_wand_save", vec![Value::Int(3)])
        .unwrap();
    assert_eq!(val, Value::Int(14));

    // Thief level 7 → wand save 13
    let val = interp
        .evaluate_derive(&state, &mut handler, "thief_wand_save", vec![Value::Int(7)])
        .unwrap();
    assert_eq!(val, Value::Int(13));
}

// ── Table no-match error ──────────────────────────────────────

const NO_MATCH_TABLE: &str = r#"
system "test" {
    table lookup(x: int) -> int {
        1 => 10,
        2 => 20,
        3 => 30
    }

    derive test_missing() -> int { lookup(99) }
}
"#;

#[test]
fn table_no_match_is_runtime_error() {
    let (program, result) = compile(NO_MATCH_TABLE);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let err = interp
        .evaluate_derive(&state, &mut handler, "test_missing", vec![])
        .unwrap_err();
    assert!(
        err.to_string().contains("no matching entry"),
        "expected 'no matching entry' error, got: {}",
        err
    );
}

// ── Table called with entity field values (dynamic keys) ──────

const DYNAMIC_KEY_TABLE: &str = r#"
system "test" {
    enum Ability { STR, DEX, CON, INT, WIS, CHA }

    entity Character {
        level: int = 1
    }

    table proficiency(level: int) -> int {
        1..=4   => 2,
        5..=8   => 3,
        9..=12  => 4,
        13..=16 => 5,
        17..=20 => 6
    }

    derive get_proficiency(actor: Character) -> int {
        proficiency(actor.level)
    }
}
"#;

#[test]
fn table_with_dynamic_entity_keys() {
    let (program, result) = compile(DYNAMIC_KEY_TABLE);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut fields = HashMap::new();
    fields.insert("level".into(), Value::Int(7));
    let hero = state.add_entity("Character", fields);

    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "get_proficiency",
            vec![Value::Entity(hero)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(3));
}

// ── Type checker rejects mismatched key types ─────────────────

#[test]
fn table_type_error_key_mismatch() {
    let source = r#"
    system "test" {
        enum Ability { STR, DEX }
        table bad_table(x: Ability) -> int {
            1 => 10
        }
    }
    "#;

    let (program, parse_errors) = ttrpg_parser::parse(source, FileId::SYNTH);
    assert!(parse_errors.is_empty());
    let mut lower_diags = Vec::new();
    let program = ttrpg_parser::lower_moves(program, &mut lower_diags);
    let result = ttrpg_checker::check(&program);
    let errors: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .collect();
    assert!(
        !errors.is_empty(),
        "expected type error for int key on Ability param"
    );
    assert!(
        errors
            .iter()
            .any(|d| d.message.contains("table key has type")),
        "expected 'table key has type' error, got: {:?}",
        errors.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

// ── Type checker rejects mismatched value types ───────────────

#[test]
fn table_type_error_value_mismatch() {
    let source = r#"
    system "test" {
        table bad_table(x: int) -> int {
            1 => "hello"
        }
    }
    "#;

    let (program, parse_errors) = ttrpg_parser::parse(source, FileId::SYNTH);
    assert!(parse_errors.is_empty());
    let mut lower_diags = Vec::new();
    let program = ttrpg_parser::lower_moves(program, &mut lower_diags);
    let result = ttrpg_checker::check(&program);
    let errors: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .collect();
    assert!(
        !errors.is_empty(),
        "expected type error for string value on int return"
    );
    assert!(
        errors
            .iter()
            .any(|d| d.message.contains("table entry value has type")),
        "expected 'table entry value has type' error, got: {:?}",
        errors.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

// ── Wildcard-not-last produces warning ────────────────────────

#[test]
fn table_wildcard_not_last_warns() {
    let source = r#"
    system "test" {
        table bad(x: int) -> int {
            _ => 0,
            1 => 10
        }
    }
    "#;

    let (program, parse_errors) = ttrpg_parser::parse(source, FileId::SYNTH);
    assert!(parse_errors.is_empty());
    let mut lower_diags = Vec::new();
    let program = ttrpg_parser::lower_moves(program, &mut lower_diags);
    let result = ttrpg_checker::check(&program);
    let warnings: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Warning)
        .collect();
    assert!(
        warnings
            .iter()
            .any(|d| d.message.contains("unreachable table entry")),
        "expected 'unreachable table entry' warning, got: {:?}",
        warnings.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

#[test]
fn table_wildcard_last_no_warning() {
    let source = r#"
    system "test" {
        table ok(x: int) -> int {
            1 => 10,
            _ => 0
        }
    }
    "#;

    let (program, parse_errors) = ttrpg_parser::parse(source, FileId::SYNTH);
    assert!(parse_errors.is_empty());
    let mut lower_diags = Vec::new();
    let program = ttrpg_parser::lower_moves(program, &mut lower_diags);
    let result = ttrpg_checker::check(&program);
    let warnings: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Warning)
        .collect();
    assert!(
        warnings.is_empty(),
        "expected no warnings for wildcard-last table, got: {:?}",
        warnings.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

// ── Type checker rejects range on non-int param ───────────────

#[test]
fn table_type_error_range_on_non_int() {
    let source = r#"
    system "test" {
        enum Ability { STR, DEX }
        table bad_table(x: Ability) -> int {
            STR..=DEX => 10
        }
    }
    "#;

    let (program, parse_errors) = ttrpg_parser::parse(source, FileId::SYNTH);
    assert!(parse_errors.is_empty());
    let mut lower_diags = Vec::new();
    let program = ttrpg_parser::lower_moves(program, &mut lower_diags);
    let result = ttrpg_checker::check(&program);
    let errors: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .collect();
    assert!(
        !errors.is_empty(),
        "expected type error for range on Ability param"
    );
    assert!(
        errors
            .iter()
            .any(|d| d.message.contains("range keys are only valid for int")),
        "expected 'range keys are only valid for int' error, got: {:?}",
        errors.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}
