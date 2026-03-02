//! Integration tests for cross-system variant name resolution.
//!
//! Verifies that when two systems define enums with overlapping variant names,
//! alias-qualified access, calls, and pattern matching resolve to the correct
//! system's variant (not a global-uniqueness fallback).

use std::collections::BTreeMap;

use ttrpg_ast::diagnostic::Severity;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

struct NoopHandler;
impl EffectHandler for NoopHandler {
    fn handle(&mut self, _: Effect) -> Response {
        Response::Acknowledged
    }
}

fn compile_multi(
    sources: &[(&str, &str)],
) -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    let owned: Vec<(String, String)> = sources
        .iter()
        .map(|(name, src)| (name.to_string(), src.to_string()))
        .collect();
    let parse_result = ttrpg_parser::parse_multi(&owned);
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

// ── Shared fixture: two systems with overlapping "small" variant ──

const SYSTEM_A: (&str, &str) = (
    "a.ttrpg",
    r#"
system "A" {
    enum Size { small, medium, large }
}
"#,
);

const SYSTEM_B: (&str, &str) = (
    "b.ttrpg",
    r#"
system "B" {
    enum Priority { small, normal, high }
}
"#,
);

// ── Alias-qualified field access ─────────────────────────────────

#[test]
fn alias_field_access_resolves_to_correct_system() {
    let (program, result) = compile_multi(&[
        SYSTEM_A,
        SYSTEM_B,
        (
            "main.ttrpg",
            r#"
use "A" as A
use "B" as B
system "Main" {
    // A.small → Size::small, B.small → Priority::small
    derive get_a_small() -> Size     { A.small }
    derive get_b_small() -> Priority { B.small }
}
"#,
        ),
    ]);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let a_val = interp
        .evaluate_derive(&state, &mut handler, "get_a_small", vec![])
        .unwrap();
    assert_eq!(
        a_val,
        Value::EnumVariant {
            enum_name: "Size".into(),
            variant: "small".into(),
            fields: BTreeMap::new(),
        }
    );

    let b_val = interp
        .evaluate_derive(&state, &mut handler, "get_b_small", vec![])
        .unwrap();
    assert_eq!(
        b_val,
        Value::EnumVariant {
            enum_name: "Priority".into(),
            variant: "small".into(),
            fields: BTreeMap::new(),
        }
    );
}

// ── Alias-qualified variant constructor call ─────────────────────

#[test]
fn alias_variant_constructor_resolves_to_correct_system() {
    let (program, result) = compile_multi(&[
        (
            "a.ttrpg",
            r#"
system "A" {
    enum Effect { hit(amount: int), miss }
}
"#,
        ),
        (
            "b.ttrpg",
            r#"
system "B" {
    enum Result { hit(damage: int, critical: bool), miss }
}
"#,
        ),
        (
            "main.ttrpg",
            r#"
use "A" as A
use "B" as B
system "Main" {
    derive make_a_hit() -> Effect { A.hit(amount: 5) }
    derive make_b_hit() -> Result { B.hit(damage: 10, critical: true) }
}
"#,
        ),
    ]);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let a_val = interp
        .evaluate_derive(&state, &mut handler, "make_a_hit", vec![])
        .unwrap();
    assert_eq!(
        a_val,
        Value::EnumVariant {
            enum_name: "Effect".into(),
            variant: "hit".into(),
            fields: BTreeMap::from([("amount".into(), Value::Int(5))]),
        }
    );

    let b_val = interp
        .evaluate_derive(&state, &mut handler, "make_b_hit", vec![])
        .unwrap();
    assert_eq!(
        b_val,
        Value::EnumVariant {
            enum_name: "Result".into(),
            variant: "hit".into(),
            fields: BTreeMap::from([
                ("damage".into(), Value::Int(10)),
                ("critical".into(), Value::Bool(true)),
            ]),
        }
    );
}

// ── Bare variant in single-import context ────────────────────────

#[test]
fn bare_variant_resolves_when_only_one_system_imported() {
    // System C imports only A, so bare "small" is unambiguous → Size::small
    let (program, result) = compile_multi(&[
        SYSTEM_A,
        SYSTEM_B,
        (
            "c.ttrpg",
            r#"
use "A"
system "C" {
    derive get_size() -> Size { small }
}
"#,
        ),
    ]);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "get_size", vec![])
        .unwrap();
    assert_eq!(
        val,
        Value::EnumVariant {
            enum_name: "Size".into(),
            variant: "small".into(),
            fields: BTreeMap::new(),
        }
    );
}

// ── Pattern matching with alias-qualified variants ───────────────

#[test]
fn pattern_match_with_overlapping_variants() {
    let (program, result) = compile_multi(&[
        SYSTEM_A,
        SYSTEM_B,
        (
            "main.ttrpg",
            r#"
use "A"
system "Main" {
    derive classify(s: Size) -> int {
        match s {
            small  => 1
            medium => 2
            large  => 3
        }
    }
}
"#,
        ),
    ]);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let small_val = Value::EnumVariant {
        enum_name: "Size".into(),
        variant: "small".into(),
        fields: BTreeMap::new(),
    };
    let result_val = interp
        .evaluate_derive(&state, &mut handler, "classify", vec![small_val])
        .unwrap();
    assert_eq!(result_val, Value::Int(1));

    let large_val = Value::EnumVariant {
        enum_name: "Size".into(),
        variant: "large".into(),
        fields: BTreeMap::new(),
    };
    let result_val = interp
        .evaluate_derive(&state, &mut handler, "classify", vec![large_val])
        .unwrap();
    assert_eq!(result_val, Value::Int(3));
}

// ── If-let binding vs variant ─────────────────────────────────────

#[test]
fn if_let_binding_not_confused_with_variant() {
    // "val" is not a variant name, so it should bind in an if-let pattern
    // even when variants like "small" exist in scope
    let (program, result) = compile_multi(&[
        SYSTEM_A,
        (
            "main.ttrpg",
            r#"
use "A"
system "Main" {
    derive unwrap_or_zero(x: option<int>) -> int {
        if let some(val) = x {
            val
        } else {
            0
        }
    }
}
"#,
        ),
    ]);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "unwrap_or_zero",
            vec![Value::Option(Some(Box::new(Value::Int(42))))],
        )
        .unwrap();
    assert_eq!(val, Value::Int(42));

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "unwrap_or_zero",
            vec![Value::Option(None)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(0));
}

// ── Qualified enum type chaining through alias ───────────────────

#[test]
fn alias_qualified_enum_type_then_variant() {
    let (program, result) = compile_multi(&[
        SYSTEM_A,
        SYSTEM_B,
        (
            "main.ttrpg",
            r#"
use "A" as A
use "B" as B
system "Main" {
    // Fully qualified: Alias.EnumType.variant
    derive get_a() -> Size     { A.Size.small }
    derive get_b() -> Priority { B.Priority.small }
}
"#,
        ),
    ]);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let a_val = interp
        .evaluate_derive(&state, &mut handler, "get_a", vec![])
        .unwrap();
    assert_eq!(
        a_val,
        Value::EnumVariant {
            enum_name: "Size".into(),
            variant: "small".into(),
            fields: BTreeMap::new(),
        }
    );

    let b_val = interp
        .evaluate_derive(&state, &mut handler, "get_b", vec![])
        .unwrap();
    assert_eq!(
        b_val,
        Value::EnumVariant {
            enum_name: "Priority".into(),
            variant: "small".into(),
            fields: BTreeMap::new(),
        }
    );
}

// ── Alias-qualified condition from different systems ──────────────

#[test]
fn alias_condition_from_correct_system() {
    // v0 enforces global name uniqueness, so each system has distinct names.
    // This verifies alias-qualified condition access works across systems.
    let (program, result) = compile_multi(&[
        (
            "a.ttrpg",
            r#"
system "A" {
    entity Creature { HP: int = 10 }
    condition Stunned on bearer: Creature {
    }
}
"#,
        ),
        (
            "b.ttrpg",
            r#"
use "A"
system "B" {
    condition Dazed on bearer: Creature {
    }
}
"#,
        ),
        (
            "main.ttrpg",
            r#"
use "A" as A
use "B" as B
system "Main" {
    derive get_a_stunned() -> Condition { A.Stunned }
    derive get_b_dazed()   -> Condition { B.Dazed }
}
"#,
        ),
    ]);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let a_val = interp
        .evaluate_derive(&state, &mut handler, "get_a_stunned", vec![])
        .unwrap();
    assert!(matches!(a_val, Value::Condition { name, .. } if name == "Stunned"));

    let b_val = interp
        .evaluate_derive(&state, &mut handler, "get_b_dazed", vec![])
        .unwrap();
    assert!(matches!(b_val, Value::Condition { name, .. } if name == "Dazed"));
}
