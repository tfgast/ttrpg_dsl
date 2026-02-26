//! OSE class definitions & XP tables integration test.
//!
//! Verifies that ose/ose_class.ttrpg parses, lowers, and type-checks
//! through the full multi-file pipeline. Tests class_def, xp_for_level,
//! check_level_up, meets_requirements, prime_req_xp_modifier, and
//! adjust_xp derives at runtime.

use std::collections::BTreeMap;

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_ast::diagnostic::Severity;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

// ── Compile helpers ────────────────────────────────────────────

fn compile_ose_class() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    let core_source = include_str!("../../../ose/ose_core.ttrpg");
    let class_source = include_str!("../../../ose/ose_class.ttrpg");

    let sources = vec![
        ("ose/ose_core.ttrpg".to_string(), core_source.to_string()),
        ("ose/ose_class.ttrpg".to_string(), class_source.to_string()),
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

/// Helper: create a Class enum variant value.
fn class_val(variant: &str) -> Value {
    Value::EnumVariant {
        enum_name: "Class".into(),
        variant: variant.into(),
        fields: BTreeMap::new(),
    }
}

/// Helper: create an abilities map with given scores.
/// Order: STR, DEX, CON, INT, WIS, CHA.
fn abilities_map(str_: i64, dex: i64, con: i64, int: i64, wis: i64, cha: i64) -> Value {
    let mut m = BTreeMap::new();
    let ability = |name: &str| -> Value {
        Value::EnumVariant {
            enum_name: "Ability".into(),
            variant: name.into(),
            fields: BTreeMap::new(),
        }
    };
    m.insert(ability("STR"), Value::Int(str_));
    m.insert(ability("DEX"), Value::Int(dex));
    m.insert(ability("CON"), Value::Int(con));
    m.insert(ability("INT"), Value::Int(int));
    m.insert(ability("WIS"), Value::Int(wis));
    m.insert(ability("CHA"), Value::Int(cha));
    Value::Map(m)
}

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn ose_class_parses_and_typechecks() {
    let (program, _) = compile_ose_class();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSE"));
    assert!(system_names.contains(&"OSE Classes"));
}

// ── Declaration structure ──────────────────────────────────────

#[test]
fn ose_class_has_xp_group_enum() {
    let (program, _) = compile_ose_class();

    let mut found = false;
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSE" {
                for decl in &sys.decls {
                    if let DeclKind::Enum(e) = &decl.node {
                        if e.name == "XpGroup" {
                            assert_eq!(e.variants.len(), 13);
                            found = true;
                        }
                    }
                }
            }
        }
    }
    assert!(found, "expected XpGroup enum with 13 variants");
}

#[test]
fn ose_class_has_table_and_derives() {
    let (program, _) = compile_ose_class();

    let mut has_table = false;
    let mut derive_names = Vec::new();

    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSE Classes" {
                for decl in &sys.decls {
                    match &decl.node {
                        DeclKind::Table(t) if t.name == "xp_table" => {
                            has_table = true;
                            assert_eq!(t.params.len(), 2);
                        }
                        DeclKind::Derive(f) => {
                            derive_names.push(f.name.as_str());
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    assert!(has_table, "expected xp_table");
    assert!(derive_names.contains(&"class_def"));
    assert!(derive_names.contains(&"xp_group"));
    assert!(derive_names.contains(&"xp_for_level"));
    assert!(derive_names.contains(&"check_level_up"));
    assert!(derive_names.contains(&"prime_req_xp_modifier"));
    assert!(derive_names.contains(&"meets_requirements"));
    assert!(derive_names.contains(&"adjust_xp"));
}

// ── Runtime: class_def ─────────────────────────────────────────

#[test]
fn class_def_fighter() {
    let (program, result) = compile_ose_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let def = interp
        .evaluate_derive(&state, &mut handler, "class_def", vec![class_val("Fighter")])
        .unwrap();

    if let Value::Struct { name, fields } = &def {
        assert_eq!(name, "ClassDef");
        assert_eq!(fields.get("hit_die"), Some(&Value::Int(8)));
        assert_eq!(fields.get("max_level"), Some(&Value::Int(14)));
        assert_eq!(fields.get("weapons_any"), Some(&Value::Bool(true)));
        assert_eq!(fields.get("is_demihuman"), Some(&Value::Bool(false)));
    } else {
        panic!("expected Struct, got {:?}", def);
    }
}

#[test]
fn class_def_magic_user() {
    let (program, result) = compile_ose_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let def = interp
        .evaluate_derive(&state, &mut handler, "class_def", vec![class_val("MagicUser")])
        .unwrap();

    if let Value::Struct { name, fields } = &def {
        assert_eq!(name, "ClassDef");
        assert_eq!(fields.get("hit_die"), Some(&Value::Int(4)));
        assert_eq!(fields.get("max_level"), Some(&Value::Int(14)));
        assert_eq!(fields.get("weapons_any"), Some(&Value::Bool(false)));
        assert_eq!(fields.get("weapons_blunt_only"), Some(&Value::Bool(false)));
    } else {
        panic!("expected Struct, got {:?}", def);
    }
}

#[test]
fn class_def_dwarf() {
    let (program, result) = compile_ose_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let def = interp
        .evaluate_derive(&state, &mut handler, "class_def", vec![class_val("Dwarf")])
        .unwrap();

    if let Value::Struct { name, fields } = &def {
        assert_eq!(name, "ClassDef");
        assert_eq!(fields.get("hit_die"), Some(&Value::Int(8)));
        assert_eq!(fields.get("max_level"), Some(&Value::Int(12)));
        assert_eq!(fields.get("is_demihuman"), Some(&Value::Bool(true)));
    } else {
        panic!("expected Struct, got {:?}", def);
    }
}

// ── Runtime: xp_for_level ──────────────────────────────────────

#[test]
fn xp_for_level_fighter() {
    let (program, result) = compile_ose_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Level 1 = 0 XP
    assert_eq!(
        interp.evaluate_derive(&state, &mut handler, "xp_for_level", vec![class_val("Fighter"), Value::Int(1)]).unwrap(),
        Value::Int(0)
    );
    // Level 2 = 2000 XP
    assert_eq!(
        interp.evaluate_derive(&state, &mut handler, "xp_for_level", vec![class_val("Fighter"), Value::Int(2)]).unwrap(),
        Value::Int(2000)
    );
    // Level 9 = 240000 XP
    assert_eq!(
        interp.evaluate_derive(&state, &mut handler, "xp_for_level", vec![class_val("Fighter"), Value::Int(9)]).unwrap(),
        Value::Int(240000)
    );
    // Level 14 = 840000 XP
    assert_eq!(
        interp.evaluate_derive(&state, &mut handler, "xp_for_level", vec![class_val("Fighter"), Value::Int(14)]).unwrap(),
        Value::Int(840000)
    );
}

#[test]
fn xp_for_level_shared_tables() {
    let (program, result) = compile_ose_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Knight shares Fighter table
    assert_eq!(
        interp.evaluate_derive(&state, &mut handler, "xp_for_level", vec![class_val("Knight"), Value::Int(2)]).unwrap(),
        Value::Int(2000)
    );

    // Acrobat shares Thief table
    assert_eq!(
        interp.evaluate_derive(&state, &mut handler, "xp_for_level", vec![class_val("Acrobat"), Value::Int(2)]).unwrap(),
        Value::Int(1200)
    );

    // Duergar shares Dwarf table
    assert_eq!(
        interp.evaluate_derive(&state, &mut handler, "xp_for_level", vec![class_val("Duergar"), Value::Int(5)]).unwrap(),
        Value::Int(17000)
    );
}

#[test]
fn xp_for_level_demihuman_tables() {
    let (program, result) = compile_ose_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Elf level 2 = 4000
    assert_eq!(
        interp.evaluate_derive(&state, &mut handler, "xp_for_level", vec![class_val("Elf"), Value::Int(2)]).unwrap(),
        Value::Int(4000)
    );

    // Halfling level 8 = 120000
    assert_eq!(
        interp.evaluate_derive(&state, &mut handler, "xp_for_level", vec![class_val("Halfling"), Value::Int(8)]).unwrap(),
        Value::Int(120000)
    );

    // Gnome level 4 = 12000
    assert_eq!(
        interp.evaluate_derive(&state, &mut handler, "xp_for_level", vec![class_val("Gnome"), Value::Int(4)]).unwrap(),
        Value::Int(12000)
    );
}

#[test]
fn xp_for_level_beyond_max_errors() {
    let (program, result) = compile_ose_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Halfling max level 8, level 9 should be no-match
    let err = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "xp_for_level",
            vec![class_val("Halfling"), Value::Int(9)],
        )
        .unwrap_err();
    assert!(
        err.to_string().contains("no matching entry"),
        "expected 'no matching entry' error, got: {}",
        err
    );
}

// ── Runtime: check_level_up ────────────────────────────────────

#[test]
fn check_level_up_ready() {
    let (program, result) = compile_ose_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Fighter level 1 with 2000 XP can advance to level 2
    assert_eq!(
        interp.evaluate_derive(
            &state, &mut handler, "check_level_up",
            vec![class_val("Fighter"), Value::Int(1), Value::Int(2000)]
        ).unwrap(),
        Value::Bool(true)
    );

    // Fighter level 1 with 3000 XP also can advance
    assert_eq!(
        interp.evaluate_derive(
            &state, &mut handler, "check_level_up",
            vec![class_val("Fighter"), Value::Int(1), Value::Int(3000)]
        ).unwrap(),
        Value::Bool(true)
    );
}

#[test]
fn check_level_up_not_ready() {
    let (program, result) = compile_ose_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Fighter level 1 with 1999 XP cannot advance
    assert_eq!(
        interp.evaluate_derive(
            &state, &mut handler, "check_level_up",
            vec![class_val("Fighter"), Value::Int(1), Value::Int(1999)]
        ).unwrap(),
        Value::Bool(false)
    );
}

#[test]
fn check_level_up_at_max() {
    let (program, result) = compile_ose_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Halfling at max level 8, cannot advance regardless of XP
    assert_eq!(
        interp.evaluate_derive(
            &state, &mut handler, "check_level_up",
            vec![class_val("Halfling"), Value::Int(8), Value::Int(999999)]
        ).unwrap(),
        Value::Bool(false)
    );
}

// ── Runtime: meets_requirements ────────────────────────────────

#[test]
fn meets_requirements_fighter_always() {
    let (program, result) = compile_ose_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Fighter has no requirements — all abilities at 3 should work
    assert_eq!(
        interp.evaluate_derive(
            &state, &mut handler, "meets_requirements",
            vec![class_val("Fighter"), abilities_map(3, 3, 3, 3, 3, 3)]
        ).unwrap(),
        Value::Bool(true)
    );
}

#[test]
fn meets_requirements_barbarian() {
    let (program, result) = compile_ose_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Barbarian needs STR 9, DEX 9, CON 9
    assert_eq!(
        interp.evaluate_derive(
            &state, &mut handler, "meets_requirements",
            vec![class_val("Barbarian"), abilities_map(9, 9, 9, 10, 10, 10)]
        ).unwrap(),
        Value::Bool(true)
    );

    // STR too low
    assert_eq!(
        interp.evaluate_derive(
            &state, &mut handler, "meets_requirements",
            vec![class_val("Barbarian"), abilities_map(8, 9, 9, 10, 10, 10)]
        ).unwrap(),
        Value::Bool(false)
    );

    // DEX too low
    assert_eq!(
        interp.evaluate_derive(
            &state, &mut handler, "meets_requirements",
            vec![class_val("Barbarian"), abilities_map(9, 8, 9, 10, 10, 10)]
        ).unwrap(),
        Value::Bool(false)
    );
}

#[test]
fn meets_requirements_dwarf() {
    let (program, result) = compile_ose_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Dwarf needs CON 9
    assert_eq!(
        interp.evaluate_derive(
            &state, &mut handler, "meets_requirements",
            vec![class_val("Dwarf"), abilities_map(10, 10, 9, 10, 10, 10)]
        ).unwrap(),
        Value::Bool(true)
    );

    assert_eq!(
        interp.evaluate_derive(
            &state, &mut handler, "meets_requirements",
            vec![class_val("Dwarf"), abilities_map(10, 10, 8, 10, 10, 10)]
        ).unwrap(),
        Value::Bool(false)
    );
}

// ── Runtime: prime_req_xp_modifier ─────────────────────────────

#[test]
fn prime_req_fighter_high_str() {
    let (program, result) = compile_ose_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Fighter prime req is STR. STR 16 → +10%
    assert_eq!(
        interp.evaluate_derive(
            &state, &mut handler, "prime_req_xp_modifier",
            vec![class_val("Fighter"), abilities_map(16, 10, 10, 10, 10, 10)]
        ).unwrap(),
        Value::Int(10)
    );
}

#[test]
fn prime_req_fighter_low_str() {
    let (program, result) = compile_ose_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Fighter STR 5 → -20%
    assert_eq!(
        interp.evaluate_derive(
            &state, &mut handler, "prime_req_xp_modifier",
            vec![class_val("Fighter"), abilities_map(5, 10, 10, 10, 10, 10)]
        ).unwrap(),
        Value::Int(-20)
    );
}

#[test]
fn prime_req_elf_dual() {
    let (program, result) = compile_ose_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Elf has STR + INT prime requisites, uses lowest.
    // STR 16, INT 10 → min is 10 → 0%
    assert_eq!(
        interp.evaluate_derive(
            &state, &mut handler, "prime_req_xp_modifier",
            vec![class_val("Elf"), abilities_map(16, 10, 10, 10, 10, 10)]
        ).unwrap(),
        Value::Int(0)
    );
}

// ── Runtime: adjust_xp ─────────────────────────────────────────

#[test]
fn adjust_xp_bonus() {
    let (program, result) = compile_ose_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    assert_eq!(
        interp.evaluate_derive(
            &state, &mut handler, "adjust_xp",
            vec![Value::Int(1000), Value::Int(10)]
        ).unwrap(),
        Value::Int(1100)
    );

    assert_eq!(
        interp.evaluate_derive(
            &state, &mut handler, "adjust_xp",
            vec![Value::Int(1000), Value::Int(5)]
        ).unwrap(),
        Value::Int(1050)
    );
}

#[test]
fn adjust_xp_penalty() {
    let (program, result) = compile_ose_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    assert_eq!(
        interp.evaluate_derive(
            &state, &mut handler, "adjust_xp",
            vec![Value::Int(1000), Value::Int(-10)]
        ).unwrap(),
        Value::Int(900)
    );

    assert_eq!(
        interp.evaluate_derive(
            &state, &mut handler, "adjust_xp",
            vec![Value::Int(1000), Value::Int(-20)]
        ).unwrap(),
        Value::Int(800)
    );
}

#[test]
fn adjust_xp_zero_mod() {
    let (program, result) = compile_ose_class();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    assert_eq!(
        interp.evaluate_derive(
            &state, &mut handler, "adjust_xp",
            vec![Value::Int(1000), Value::Int(0)]
        ).unwrap(),
        Value::Int(1000)
    );
}
