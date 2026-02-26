//! Tests for enum variant introspection API.

use ttrpg_ast::diagnostic::Severity;
use ttrpg_ast::FileId;
use ttrpg_interp::Interpreter;

fn setup(source: &str) -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
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

#[test]
fn enum_variants_simple() {
    let source = r#"
system "test" {
    enum Class { Fighter, MagicUser, Cleric, Thief }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();

    let variants = interp.enum_variants("Class").unwrap();
    assert_eq!(variants, vec!["Fighter", "MagicUser", "Cleric", "Thief"]);
}

#[test]
fn enum_variants_ordered() {
    let source = r#"
system "test" {
    enum Size ordered { Tiny, Small, Medium, Large, Huge, Gargantuan }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();

    let variants = interp.enum_variants("Size").unwrap();
    assert_eq!(
        variants,
        vec!["Tiny", "Small", "Medium", "Large", "Huge", "Gargantuan"]
    );
}

#[test]
fn enum_variants_with_fields() {
    let source = r#"
system "test" {
    enum Effect { timed(count: int), permanent }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();

    let variants = interp.enum_variants("Effect").unwrap();
    assert_eq!(variants, vec!["timed", "permanent"]);
}

#[test]
fn enum_variants_nonexistent_returns_none() {
    let source = r#"
system "test" {
    enum Color { Red, Green, Blue }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();

    assert!(interp.enum_variants("Nonexistent").is_none());
}

#[test]
fn enum_variants_struct_name_returns_none() {
    let source = r#"
system "test" {
    struct Stats { hp: int }
    enum Color { Red, Green, Blue }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();

    // "Stats" is a struct, not an enum — should return None
    assert!(interp.enum_variants("Stats").is_none());
    // "Color" works
    assert_eq!(
        interp.enum_variants("Color").unwrap(),
        vec!["Red", "Green", "Blue"]
    );
}

#[test]
fn type_env_accessor() {
    let source = r#"
system "test" {
    enum Ability { STR, DEX, CON, INT, WIS, CHA }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();

    // Access type_env directly and use get_enum for richer info
    let enum_info = interp.type_env().get_enum("Ability").unwrap();
    assert_eq!(enum_info.name.as_ref(), "Ability");
    assert!(!enum_info.ordered);
    assert_eq!(enum_info.variants.len(), 6);
    assert_eq!(enum_info.variants[0].name.as_ref(), "STR");
}

#[test]
fn type_env_enum_variant_fields() {
    let source = r#"
system "test" {
    enum Effect { timed(count: int, duration: int), permanent }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();

    let enum_info = interp.type_env().get_enum("Effect").unwrap();
    let timed = &enum_info.variants[0];
    assert_eq!(timed.name.as_ref(), "timed");
    assert_eq!(timed.fields.len(), 2);
    assert_eq!(timed.fields[0].0.as_ref(), "count");
    assert_eq!(timed.fields[1].0.as_ref(), "duration");

    let permanent = &enum_info.variants[1];
    assert_eq!(permanent.name.as_ref(), "permanent");
    assert!(permanent.fields.is_empty());
}

#[test]
fn multiple_enums() {
    let source = r#"
system "test" {
    enum Class { Fighter, MagicUser, Cleric, Thief }
    enum Alignment { Lawful, Neutral, Chaotic }
    enum SaveCategory { DeathPoison, Wands, Paralysis, Breath, Spells }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();

    let classes = interp.enum_variants("Class").unwrap();
    assert_eq!(classes, vec!["Fighter", "MagicUser", "Cleric", "Thief"]);

    let alignments = interp.enum_variants("Alignment").unwrap();
    assert_eq!(alignments, vec!["Lawful", "Neutral", "Chaotic"]);

    let saves = interp.enum_variants("SaveCategory").unwrap();
    assert_eq!(
        saves,
        vec!["DeathPoison", "Wands", "Paralysis", "Breath", "Spells"]
    );
}
