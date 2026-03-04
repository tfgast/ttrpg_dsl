//! OSRIC ability modifier tables integration test.
//!
//! Verifies that osric/osric_ability.ttrpg parses, lowers, and type-checks
//! through the full multi-file pipeline. Tests all ability modifier tables
//! and ancestry definitions at runtime.

use std::collections::BTreeMap;

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_ast::diagnostic::Severity;
use ttrpg_ast::Name;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::{EntityRef, WritableState};
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_ability() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    let core_source = include_str!("../../../osric/osric_core.ttrpg");
    let ability_source = include_str!("../../../osric/osric_ability.ttrpg");

    let sources = vec![
        (
            "osric/osric_core.ttrpg".to_string(),
            core_source.to_string(),
        ),
        (
            "osric/osric_ability.ttrpg".to_string(),
            ability_source.to_string(),
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

struct NullHandler;
impl EffectHandler for NullHandler {
    fn handle(&mut self, _effect: Effect) -> Response {
        Response::Acknowledged
    }
}

fn enum_variant(enum_name: &str, variant: &str) -> Value {
    Value::EnumVariant {
        enum_name: ttrpg_ast::Name::from(enum_name),
        variant: ttrpg_ast::Name::from(variant),
        fields: BTreeMap::new(),
    }
}

fn ability(variant: &str) -> Value {
    enum_variant("Ability", variant)
}

fn ancestry(variant: &str) -> Value {
    enum_variant("Ancestry", variant)
}

/// Build a minimal Character entity in GameState and return its EntityRef.
fn make_character(state: &mut GameState, name: &str, abilities: &[(&str, i64)]) -> EntityRef {
    use rustc_hash::FxHashMap;
    use ttrpg_ast::Name;

    let mut ability_map = BTreeMap::new();
    for &(ab, score) in abilities {
        ability_map.insert(ability(ab), Value::Int(score));
    }

    let mut fields = FxHashMap::default();
    fields.insert(Name::from("name"), Value::Str(name.to_string()));
    fields.insert(Name::from("class"), enum_variant("Class", "Fighter"));
    fields.insert(Name::from("ancestry"), enum_variant("Ancestry", "Human"));
    fields.insert(Name::from("level"), Value::Int(1));
    fields.insert(
        Name::from("alignment"),
        enum_variant("Alignment", "TrueNeutral"),
    );
    fields.insert(Name::from("abilities"), Value::Map(ability_map));
    fields.insert(Name::from("max_hp"), Value::Int(10));
    fields.insert(Name::from("hp"), Value::Int(10));
    fields.insert(Name::from("armor_ac"), Value::Int(10));
    fields.insert(Name::from("shield_ac_bonus"), Value::Int(0));
    fields.insert(Name::from("xp"), Value::Int(0));
    fields.insert(
        Name::from("base_movement"),
        Value::Struct {
            name: Name::from("Feet"),
            fields: {
                let mut f = BTreeMap::new();
                f.insert(Name::from("value"), Value::Int(120));
                f
            },
        },
    );
    fields.insert(Name::from("gold"), Value::Int(0));
    fields.insert(Name::from("saving_throws"), Value::Option(None));

    state.add_entity("Character", fields)
}

/// Helper to run a table/derive with a single int argument.
fn eval_table(interp: &Interpreter, state: &GameState, name: &str, arg: i64) -> Value {
    let mut handler = NullHandler;
    interp
        .evaluate_derive(state, &mut handler, name, vec![Value::Int(arg)])
        .unwrap_or_else(|e| panic!("{name}({arg}) failed: {e}"))
}

/// Look up a field in a BTreeMap<Name, Value> without ambiguity.
fn field<'a>(fields: &'a BTreeMap<Name, Value>, key: &str) -> Option<&'a Value> {
    fields.get::<Name>(&key.into())
}

fn expect_int(val: Value, ctx: &str) -> i64 {
    match val {
        Value::Int(n) => n,
        other => panic!("{ctx}: expected Int, got {other:?}"),
    }
}

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn osric_ability_parses_and_typechecks() {
    let (program, _) = compile_osric_ability();
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
}

// ── Declaration structure ──────────────────────────────────────

#[test]
fn osric_ability_has_all_tables() {
    let (program, _) = compile_osric_ability();

    let table_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) if sys.name == "OSRIC Ability" => Some(
                sys.decls
                    .iter()
                    .filter_map(|d| match &d.node {
                        DeclKind::Table(t) => Some(t.name.as_str()),
                        _ => None,
                    })
                    .collect::<Vec<_>>(),
            ),
            _ => None,
        })
        .flatten()
        .collect();

    let expected = [
        // STR
        "str_to_hit",
        "str_damage",
        "str_encumbrance",
        "str_minor_test",
        "str_minor_extraordinary",
        "str_major_test",
        // Exceptional STR
        "exc_str_to_hit",
        "exc_str_damage",
        "exc_str_encumbrance",
        "exc_str_minor_test",
        "exc_str_minor_extraordinary",
        "exc_str_major_test",
        // DEX
        "dex_surprise",
        "dex_missile",
        "dex_ac_adj",
        "dex_init_missile",
        "dex_agility_save",
        // CON
        "con_hp_mod",
        "con_hp_mod_fighter",
        "con_resurrection",
        "con_system_shock",
        // INT
        "int_extra_languages",
        // WIS
        "wis_mental_save",
        // CHA
        "cha_max_henchmen",
        "cha_loyalty",
        "cha_reaction",
        // Stalwart
        "stalwart_save_bonus",
    ];

    for name in &expected {
        assert!(table_names.contains(name), "missing table: {name}");
    }

    assert_eq!(
        table_names.len(),
        expected.len(),
        "expected {} tables, got {}: {:?}",
        expected.len(),
        table_names.len(),
        table_names
    );
}

// ── STR tables ─────────────────────────────────────────────────

#[test]
fn str_to_hit_values() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // (score, expected)
    let cases = [
        (3, -3),
        (4, -2),
        (5, -2),
        (7, -1),
        (8, 0),
        (15, 0),
        (16, 0),
        (17, 1),
        (18, 1),
        (19, 3), // wildcard
    ];
    for (score, expected) in cases {
        let val = expect_int(
            eval_table(&interp, &state, "str_to_hit", score),
            "str_to_hit",
        );
        assert_eq!(val, expected, "str_to_hit({score})");
    }
}

#[test]
fn str_damage_values() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let cases = [
        (3, -1),
        (5, -1),
        (7, 0),
        (15, 0),
        (16, 1),
        (17, 1),
        (18, 2),
        (19, 6),
    ];
    for (score, expected) in cases {
        let val = expect_int(
            eval_table(&interp, &state, "str_damage", score),
            "str_damage",
        );
        assert_eq!(val, expected, "str_damage({score})");
    }
}

#[test]
fn str_encumbrance_values() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let cases = [
        (3, 0),
        (5, 10),
        (7, 20),
        (9, 35),
        (13, 45),
        (15, 55),
        (16, 70),
        (17, 85),
        (18, 110),
        (19, 300),
    ];
    for (score, expected) in cases {
        let val = expect_int(
            eval_table(&interp, &state, "str_encumbrance", score),
            "str_encumbrance",
        );
        assert_eq!(val, expected, "str_encumbrance({score})");
    }
}

#[test]
fn str_minor_test_values() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let cases = [(3, 1), (7, 1), (8, 2), (15, 2), (16, 3), (18, 3), (19, 5)];
    for (score, expected) in cases {
        let val = expect_int(
            eval_table(&interp, &state, "str_minor_test", score),
            "str_minor_test",
        );
        assert_eq!(val, expected, "str_minor_test({score})");
    }
}

#[test]
fn str_minor_extraordinary_values() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let cases = [(3, 0), (10, 0), (15, 0), (18, 0), (19, 2)];
    for (score, expected) in cases {
        let val = expect_int(
            eval_table(&interp, &state, "str_minor_extraordinary", score),
            "str_minor_extraordinary",
        );
        assert_eq!(val, expected, "str_minor_extraordinary({score})");
    }
}

#[test]
fn str_major_test_values() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let cases = [
        (3, 0),
        (9, 1),
        (11, 2),
        (13, 4),
        (15, 7),
        (16, 10),
        (17, 13),
        (18, 16),
        (19, 40),
    ];
    for (score, expected) in cases {
        let val = expect_int(
            eval_table(&interp, &state, "str_major_test", score),
            "str_major_test",
        );
        assert_eq!(val, expected, "str_major_test({score})");
    }
}

// ── Exceptional STR tables ─────────────────────────────────────

#[test]
fn exc_str_to_hit_values() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let cases = [
        (1, 1),
        (50, 1),
        (51, 2),
        (75, 2),
        (90, 2),
        (99, 2),
        (100, 3),
    ];
    for (pct, expected) in cases {
        let val = expect_int(
            eval_table(&interp, &state, "exc_str_to_hit", pct),
            "exc_str_to_hit",
        );
        assert_eq!(val, expected, "exc_str_to_hit({pct})");
    }
}

#[test]
fn exc_str_damage_values() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let cases = [
        (1, 3),
        (50, 3),
        (51, 3),
        (75, 3),
        (76, 4),
        (90, 4),
        (91, 5),
        (99, 5),
        (100, 6),
    ];
    for (pct, expected) in cases {
        let val = expect_int(
            eval_table(&interp, &state, "exc_str_damage", pct),
            "exc_str_damage",
        );
        assert_eq!(val, expected, "exc_str_damage({pct})");
    }
}

#[test]
fn exc_str_encumbrance_values() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let cases = [
        (1, 135),
        (50, 135),
        (75, 160),
        (90, 185),
        (99, 235),
        (100, 300),
    ];
    for (pct, expected) in cases {
        let val = expect_int(
            eval_table(&interp, &state, "exc_str_encumbrance", pct),
            "exc_str_encumbrance",
        );
        assert_eq!(val, expected, "exc_str_encumbrance({pct})");
    }
}

#[test]
fn exc_str_minor_test_values() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let cases = [(1, 3), (75, 3), (76, 4), (99, 4), (100, 5)];
    for (pct, expected) in cases {
        let val = expect_int(
            eval_table(&interp, &state, "exc_str_minor_test", pct),
            "exc_str_minor_test",
        );
        assert_eq!(val, expected, "exc_str_minor_test({pct})");
    }
}

#[test]
fn exc_str_minor_extraordinary_values() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let cases = [
        (1, 0),
        (50, 0),
        (75, 0),
        (90, 0),
        (91, 1),
        (99, 1),
        (100, 2),
    ];
    for (pct, expected) in cases {
        let val = expect_int(
            eval_table(&interp, &state, "exc_str_minor_extraordinary", pct),
            "exc_str_minor_extraordinary",
        );
        assert_eq!(val, expected, "exc_str_minor_extraordinary({pct})");
    }
}

#[test]
fn exc_str_major_test_values() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let cases = [(1, 20), (50, 20), (75, 25), (90, 30), (99, 35), (100, 40)];
    for (pct, expected) in cases {
        let val = expect_int(
            eval_table(&interp, &state, "exc_str_major_test", pct),
            "exc_str_major_test",
        );
        assert_eq!(val, expected, "exc_str_major_test({pct})");
    }
}

// ── DEX tables ─────────────────────────────────────────────────

#[test]
fn dex_surprise_values() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let cases = [
        (3, -3),
        (4, -2),
        (5, -1),
        (6, 0),
        (14, 0),
        (15, 0),
        (16, 1),
        (17, 2),
        (18, 3),
        (19, 3),
    ];
    for (score, expected) in cases {
        let val = expect_int(
            eval_table(&interp, &state, "dex_surprise", score),
            "dex_surprise",
        );
        assert_eq!(val, expected, "dex_surprise({score})");
    }
}

#[test]
fn dex_missile_values() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let cases = [
        (3, -3),
        (4, -2),
        (5, -1),
        (10, 0),
        (15, 0),
        (16, 1),
        (17, 2),
        (18, 3),
    ];
    for (score, expected) in cases {
        let val = expect_int(
            eval_table(&interp, &state, "dex_missile", score),
            "dex_missile",
        );
        assert_eq!(val, expected, "dex_missile({score})");
    }
}

#[test]
fn dex_ac_adj_values() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let cases = [
        (3, -4),
        (4, -3),
        (5, -2),
        (6, -1),
        (7, 0),
        (14, 0),
        (15, 1),
        (16, 2),
        (17, 3),
        (18, 4),
    ];
    for (score, expected) in cases {
        let val = expect_int(
            eval_table(&interp, &state, "dex_ac_adj", score),
            "dex_ac_adj",
        );
        assert_eq!(val, expected, "dex_ac_adj({score})");
    }
}

#[test]
fn dex_init_missile_values() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Note: positive = slower (bad), negative = faster (good)
    let cases = [
        (3, 3),
        (4, 2),
        (5, 1),
        (6, 0),
        (15, 0),
        (16, -1),
        (17, -2),
        (18, -3),
    ];
    for (score, expected) in cases {
        let val = expect_int(
            eval_table(&interp, &state, "dex_init_missile", score),
            "dex_init_missile",
        );
        assert_eq!(val, expected, "dex_init_missile({score})");
    }
}

#[test]
fn dex_agility_save_values() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let cases = [
        (3, -4),
        (4, -3),
        (5, -2),
        (6, -1),
        (10, 0),
        (15, 1),
        (16, 2),
        (17, 3),
        (18, 4),
    ];
    for (score, expected) in cases {
        let val = expect_int(
            eval_table(&interp, &state, "dex_agility_save", score),
            "dex_agility_save",
        );
        assert_eq!(val, expected, "dex_agility_save({score})");
    }
}

// ── CON tables ─────────────────────────────────────────────────

#[test]
fn con_hp_mod_values() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let cases = [
        (3, -2),
        (4, -1),
        (6, -1),
        (7, 0),
        (14, 0),
        (15, 1),
        (16, 2),
        (17, 2),
        (18, 2),
        (19, 2),
    ];
    for (score, expected) in cases {
        let val = expect_int(
            eval_table(&interp, &state, "con_hp_mod", score),
            "con_hp_mod",
        );
        assert_eq!(val, expected, "con_hp_mod({score})");
    }
}

#[test]
fn con_hp_mod_fighter_values() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Fighter-types get higher bonuses at 17+
    let cases = [
        (3, -2),
        (6, -1),
        (14, 0),
        (16, 2),
        (17, 3),
        (18, 4),
        (19, 5),
    ];
    for (score, expected) in cases {
        let val = expect_int(
            eval_table(&interp, &state, "con_hp_mod_fighter", score),
            "con_hp_mod_fighter",
        );
        assert_eq!(val, expected, "con_hp_mod_fighter({score})");
    }
}

#[test]
fn con_resurrection_values() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let cases = [(3, 40), (10, 75), (14, 92), (16, 96), (18, 100), (19, 100)];
    for (score, expected) in cases {
        let val = expect_int(
            eval_table(&interp, &state, "con_resurrection", score),
            "con_resurrection",
        );
        assert_eq!(val, expected, "con_resurrection({score})");
    }
}

#[test]
fn con_system_shock_values() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let cases = [(3, 35), (10, 70), (14, 88), (16, 95), (18, 99), (19, 99)];
    for (score, expected) in cases {
        let val = expect_int(
            eval_table(&interp, &state, "con_system_shock", score),
            "con_system_shock",
        );
        assert_eq!(val, expected, "con_system_shock({score})");
    }
}

// ── INT table ──────────────────────────────────────────────────

#[test]
fn int_extra_languages_values() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let cases = [
        (3, 0),
        (7, 0),
        (8, 1),
        (11, 2),
        (13, 3),
        (15, 4),
        (16, 5),
        (17, 6),
        (18, 7),
        (19, 8),
    ];
    for (score, expected) in cases {
        let val = expect_int(
            eval_table(&interp, &state, "int_extra_languages", score),
            "int_extra_languages",
        );
        assert_eq!(val, expected, "int_extra_languages({score})");
    }
}

// ── WIS table ──────────────────────────────────────────────────

#[test]
fn wis_mental_save_values() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let cases = [
        (3, -3),
        (4, -2),
        (5, -1),
        (7, -1),
        (8, 0),
        (14, 0),
        (15, 1),
        (16, 2),
        (17, 3),
        (18, 4),
        (19, 5),
    ];
    for (score, expected) in cases {
        let val = expect_int(
            eval_table(&interp, &state, "wis_mental_save", score),
            "wis_mental_save",
        );
        assert_eq!(val, expected, "wis_mental_save({score})");
    }
}

// ── CHA tables ─────────────────────────────────────────────────

#[test]
fn cha_max_henchmen_values() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let cases = [
        (3, 1),
        (4, 1),
        (5, 2),
        (7, 3),
        (9, 4),
        (12, 5),
        (14, 6),
        (15, 7),
        (16, 8),
        (17, 10),
        (18, 15),
        (19, 20),
    ];
    for (score, expected) in cases {
        let val = expect_int(
            eval_table(&interp, &state, "cha_max_henchmen", score),
            "cha_max_henchmen",
        );
        assert_eq!(val, expected, "cha_max_henchmen({score})");
    }
}

#[test]
fn cha_loyalty_values() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let cases = [
        (3, -30),
        (5, -20),
        (8, -5),
        (9, 0),
        (12, 0),
        (14, 5),
        (15, 15),
        (16, 20),
        (17, 30),
        (18, 40),
        (19, 50),
    ];
    for (score, expected) in cases {
        let val = expect_int(
            eval_table(&interp, &state, "cha_loyalty", score),
            "cha_loyalty",
        );
        assert_eq!(val, expected, "cha_loyalty({score})");
    }
}

#[test]
fn cha_reaction_values() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let cases = [
        (3, -25),
        (5, -15),
        (7, -5),
        (8, 0),
        (10, 0),
        (13, 5),
        (14, 10),
        (15, 15),
        (16, 25),
        (17, 30),
        (18, 35),
        (19, 40),
    ];
    for (score, expected) in cases {
        let val = expect_int(
            eval_table(&interp, &state, "cha_reaction", score),
            "cha_reaction",
        );
        assert_eq!(val, expected, "cha_reaction({score})");
    }
}

// ── Stalwart save bonus ────────────────────────────────────────

#[test]
fn stalwart_save_bonus_values() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    let cases = [
        (3, 1),
        (6, 1),
        (7, 2),
        (10, 2),
        (11, 3),
        (13, 3),
        (14, 4),
        (17, 4),
        (18, 5),
        (19, 5),
    ];
    for (con, expected) in cases {
        let val = expect_int(
            eval_table(&interp, &state, "stalwart_save_bonus", con),
            "stalwart_save_bonus",
        );
        assert_eq!(val, expected, "stalwart_save_bonus({con})");
    }
}

// ── has_stalwart derive ────────────────────────────────────────

#[test]
fn has_stalwart_by_ancestry() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let stalwart = ["Dwarf", "Gnome", "Halfling"];
    let non_stalwart = ["Elf", "HalfElf", "HalfOrc", "Human"];

    for name in stalwart {
        let val = interp
            .evaluate_derive(&state, &mut handler, "has_stalwart", vec![ancestry(name)])
            .unwrap();
        assert_eq!(val, Value::Bool(true), "has_stalwart({name})");
    }
    for name in non_stalwart {
        let val = interp
            .evaluate_derive(&state, &mut handler, "has_stalwart", vec![ancestry(name)])
            .unwrap();
        assert_eq!(val, Value::Bool(false), "has_stalwart({name})");
    }
}

// ── ancestry_def derive ────────────────────────────────────────

#[test]
fn ancestry_def_human() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "ancestry_def",
            vec![ancestry("Human")],
        )
        .unwrap();

    match val {
        Value::Struct { name, fields } => {
            assert_eq!(&*name, "AncestryDef");
            assert_eq!(field(&fields, "ancestry"), Some(&ancestry("Human")));
            assert_eq!(
                field(&fields, "size"),
                Some(&enum_variant("Size", "Medium"))
            );
            // base_movement = 120ft
            let mv = field(&fields, "base_movement").unwrap();
            match mv {
                Value::Struct { name, fields } => {
                    assert_eq!(&**name, "Feet");
                    assert_eq!(field(fields, "value"), Some(&Value::Int(120)));
                }
                other => panic!("expected Feet struct, got {other:?}"),
            }
            // infravision = 0ft
            let iv = field(&fields, "infravision").unwrap();
            match iv {
                Value::Struct { name, fields } => {
                    assert_eq!(&**name, "Feet");
                    assert_eq!(field(fields, "value"), Some(&Value::Int(0)));
                }
                other => panic!("expected Feet struct, got {other:?}"),
            }
            // All adjustments = 0
            for adj in [
                "str_adj", "dex_adj", "con_adj", "int_adj", "wis_adj", "cha_adj",
            ] {
                assert_eq!(
                    field(&fields, adj),
                    Some(&Value::Int(0)),
                    "Human {adj} should be 0"
                );
            }
        }
        other => panic!("expected Struct, got {other:?}"),
    }
}

#[test]
fn ancestry_def_dwarf() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "ancestry_def",
            vec![ancestry("Dwarf")],
        )
        .unwrap();

    match val {
        Value::Struct { name, fields } => {
            assert_eq!(&*name, "AncestryDef");
            assert_eq!(field(&fields, "size"), Some(&enum_variant("Size", "Small")));
            // Dwarf: CON +1, CHA -1, rest 0
            assert_eq!(field(&fields, "str_adj"), Some(&Value::Int(0)));
            assert_eq!(field(&fields, "con_adj"), Some(&Value::Int(1)));
            assert_eq!(field(&fields, "cha_adj"), Some(&Value::Int(-1)));
            // base_movement = 90ft
            let mv = field(&fields, "base_movement").unwrap();
            match mv {
                Value::Struct { fields, .. } => {
                    assert_eq!(field(fields, "value"), Some(&Value::Int(90)));
                }
                other => panic!("expected Feet struct, got {other:?}"),
            }
        }
        other => panic!("expected Struct, got {other:?}"),
    }
}

#[test]
fn ancestry_def_halfling() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "ancestry_def",
            vec![ancestry("Halfling")],
        )
        .unwrap();

    match val {
        Value::Struct { fields, .. } => {
            // Halfling: STR -1, DEX +1, rest 0
            assert_eq!(field(&fields, "str_adj"), Some(&Value::Int(-1)));
            assert_eq!(field(&fields, "dex_adj"), Some(&Value::Int(1)));
            assert_eq!(field(&fields, "con_adj"), Some(&Value::Int(0)));
            assert_eq!(field(&fields, "size"), Some(&enum_variant("Size", "Small")));
        }
        other => panic!("expected Struct, got {other:?}"),
    }
}

#[test]
fn ancestry_def_half_orc() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "ancestry_def",
            vec![ancestry("HalfOrc")],
        )
        .unwrap();

    match val {
        Value::Struct { fields, .. } => {
            // HalfOrc: STR +1, CON +1, CHA -2
            assert_eq!(field(&fields, "str_adj"), Some(&Value::Int(1)));
            assert_eq!(field(&fields, "con_adj"), Some(&Value::Int(1)));
            assert_eq!(field(&fields, "cha_adj"), Some(&Value::Int(-2)));
        }
        other => panic!("expected Struct, got {other:?}"),
    }
}

// ── ancestry_ability_range derive ──────────────────────────────

#[test]
fn ancestry_ability_range_human_all_3_18() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Humans have 3-18 for all abilities
    for ab in ["STR", "DEX", "CON", "INT", "WIS", "CHA"] {
        let val = interp
            .evaluate_derive(
                &state,
                &mut handler,
                "ancestry_ability_range",
                vec![ancestry("Human"), ability(ab)],
            )
            .unwrap();
        match val {
            Value::Struct { fields, .. } => {
                assert_eq!(
                    field(&fields, "min"),
                    Some(&Value::Int(3)),
                    "Human {ab} min"
                );
                assert_eq!(
                    field(&fields, "max"),
                    Some(&Value::Int(18)),
                    "Human {ab} max"
                );
            }
            other => panic!("expected AbilityRange struct, got {other:?}"),
        }
    }
}

#[test]
fn ancestry_ability_range_dwarf_restrictions() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Dwarf: STR 8-18, DEX 3-17, CON 12-19, CHA 3-16
    let cases = [
        ("STR", 8, 18),
        ("DEX", 3, 17),
        ("CON", 12, 19),
        ("INT", 3, 18),
        ("WIS", 3, 18),
        ("CHA", 3, 16),
    ];
    for (ab, exp_min, exp_max) in cases {
        let val = interp
            .evaluate_derive(
                &state,
                &mut handler,
                "ancestry_ability_range",
                vec![ancestry("Dwarf"), ability(ab)],
            )
            .unwrap();
        match val {
            Value::Struct { fields, .. } => {
                assert_eq!(
                    field(&fields, "min"),
                    Some(&Value::Int(exp_min)),
                    "Dwarf {ab} min"
                );
                assert_eq!(
                    field(&fields, "max"),
                    Some(&Value::Int(exp_max)),
                    "Dwarf {ab} max"
                );
            }
            other => panic!("expected AbilityRange struct, got {other:?}"),
        }
    }
}

#[test]
fn ancestry_ability_range_half_orc_restrictions() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // HalfOrc: CON 13-19, WIS 3-14, CHA 3-12
    let cases = [("CON", 13, 19), ("WIS", 3, 14), ("CHA", 3, 12)];
    for (ab, exp_min, exp_max) in cases {
        let val = interp
            .evaluate_derive(
                &state,
                &mut handler,
                "ancestry_ability_range",
                vec![ancestry("HalfOrc"), ability(ab)],
            )
            .unwrap();
        match val {
            Value::Struct { fields, .. } => {
                assert_eq!(
                    field(&fields, "min"),
                    Some(&Value::Int(exp_min)),
                    "HalfOrc {ab} min"
                );
                assert_eq!(
                    field(&fields, "max"),
                    Some(&Value::Int(exp_max)),
                    "HalfOrc {ab} max"
                );
            }
            other => panic!("expected AbilityRange struct, got {other:?}"),
        }
    }
}

// ── effective_str_to_hit (entity-based derive) ─────────────────

#[test]
fn effective_str_to_hit_normal_str() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // Fighter with STR 16 — no exceptional strength
    let entity = make_character(
        &mut state,
        "TestFighter",
        &[
            ("STR", 16),
            ("DEX", 10),
            ("CON", 10),
            ("INT", 10),
            ("WIS", 10),
            ("CHA", 10),
        ],
    );

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "effective_str_to_hit",
            vec![Value::Entity(entity)],
        )
        .unwrap();
    // STR 16 → str_to_hit(16) = 0
    assert_eq!(val, Value::Int(0));
}

#[test]
fn effective_str_to_hit_str_17() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    let entity = make_character(
        &mut state,
        "TestFighter17",
        &[
            ("STR", 17),
            ("DEX", 10),
            ("CON", 10),
            ("INT", 10),
            ("WIS", 10),
            ("CHA", 10),
        ],
    );

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "effective_str_to_hit",
            vec![Value::Entity(entity)],
        )
        .unwrap();
    // STR 17 → str_to_hit(17) = 1
    assert_eq!(val, Value::Int(1));
}

#[test]
fn effective_str_to_hit_str_18_no_exceptional() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // STR 18 but no ExceptionalStrength group (e.g. a cleric)
    let entity = make_character(
        &mut state,
        "TestCleric18",
        &[
            ("STR", 18),
            ("DEX", 10),
            ("CON", 10),
            ("INT", 10),
            ("WIS", 10),
            ("CHA", 10),
        ],
    );

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "effective_str_to_hit",
            vec![Value::Entity(entity)],
        )
        .unwrap();
    // STR 18, no exceptional → str_to_hit(18) = 1
    assert_eq!(val, Value::Int(1));
}

#[test]
fn effective_str_to_hit_str_18_with_exceptional() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    let entity = make_character(
        &mut state,
        "TestFighter18",
        &[
            ("STR", 18),
            ("DEX", 10),
            ("CON", 10),
            ("INT", 10),
            ("WIS", 10),
            ("CHA", 10),
        ],
    );

    // Grant ExceptionalStrength with percentile 76
    use ttrpg_interp::effect::FieldPathSegment;
    state.write_field(
        &entity,
        &[FieldPathSegment::Field("ExceptionalStrength".into())],
        Value::Struct {
            name: "ExceptionalStrength".into(),
            fields: {
                let mut f = BTreeMap::new();
                f.insert("percentile".into(), Value::Int(76));
                f
            },
        },
    );

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "effective_str_to_hit",
            vec![Value::Entity(entity)],
        )
        .unwrap();
    // STR 18, percentile 76 → exc_str_to_hit(76) = 2
    assert_eq!(val, Value::Int(2));
}

#[test]
fn effective_str_to_hit_str_18_exceptional_100() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    let entity = make_character(
        &mut state,
        "TestFighter18_100",
        &[
            ("STR", 18),
            ("DEX", 10),
            ("CON", 10),
            ("INT", 10),
            ("WIS", 10),
            ("CHA", 10),
        ],
    );

    use ttrpg_interp::effect::FieldPathSegment;
    state.write_field(
        &entity,
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
            "effective_str_to_hit",
            vec![Value::Entity(entity)],
        )
        .unwrap();
    // STR 18, percentile 100 → exc_str_to_hit(100) = 3
    assert_eq!(val, Value::Int(3));
}

// ── effective_str_damage (entity-based derive) ─────────────────

#[test]
fn effective_str_damage_normal() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    let entity = make_character(
        &mut state,
        "TestFighter",
        &[
            ("STR", 17),
            ("DEX", 10),
            ("CON", 10),
            ("INT", 10),
            ("WIS", 10),
            ("CHA", 10),
        ],
    );

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "effective_str_damage",
            vec![Value::Entity(entity)],
        )
        .unwrap();
    // STR 17 → str_damage(17) = 1
    assert_eq!(val, Value::Int(1));
}

#[test]
fn effective_str_damage_with_exceptional() {
    let (program, result) = compile_osric_ability();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    let entity = make_character(
        &mut state,
        "TestFighter18",
        &[
            ("STR", 18),
            ("DEX", 10),
            ("CON", 10),
            ("INT", 10),
            ("WIS", 10),
            ("CHA", 10),
        ],
    );

    use ttrpg_interp::effect::FieldPathSegment;
    state.write_field(
        &entity,
        &[FieldPathSegment::Field("ExceptionalStrength".into())],
        Value::Struct {
            name: "ExceptionalStrength".into(),
            fields: {
                let mut f = BTreeMap::new();
                f.insert("percentile".into(), Value::Int(91));
                f
            },
        },
    );

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "effective_str_damage",
            vec![Value::Entity(entity)],
        )
        .unwrap();
    // STR 18, percentile 91 → exc_str_damage(91) = 5
    assert_eq!(val, Value::Int(5));
}
