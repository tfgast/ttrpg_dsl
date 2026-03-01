//! Spec audit: type system and arithmetic.
//!
//! Exhaustive verification of type system rules from 01_type_system.ttrpg and
//! 05_unit_types.ttrpg. Tests cover the full pipeline (parse → lower → check →
//! interpret) and also checker-only error rejection:
//!
//! 1. Coercion table: DiceExpr→RollResult (only via roll), RollResult→int
//!    (implicit in comparisons), and all NEVER cases.
//! 2. Arithmetic combinations: int, float, DiceExpr, Resource.
//! 3. Unit type arithmetic: same-type +/-, int*unit, unit/unit→float,
//!    and all error cases (unit+int, unit*unit, unit/int).
//! 4. Unit type comparisons.
//! 5. Resource type clamping on =, +=, -=.
//! 6. Float: no literals, only produced by division, floor/ceil.
//! 7. Composite types: list/set/map/option construction and access.

use std::collections::{BTreeMap, HashMap};

use ttrpg_ast::diagnostic::Severity;
use ttrpg_ast::FileId;
use ttrpg_interp::adapter::StateAdapter;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::StateProvider;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

// ── Setup ──────────────────────────────────────────────────────

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

fn expect_checker_errors(source: &str, expected_fragments: &[&str]) {
    let (program, parse_errors) = ttrpg_parser::parse(source, FileId::SYNTH);
    assert!(
        parse_errors.is_empty(),
        "parse errors: {:?}",
        parse_errors.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    let mut lower_diags = Vec::new();
    let program = ttrpg_parser::lower_moves(program, &mut lower_diags);
    let result = ttrpg_checker::check(&program);
    let errors: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .collect();
    for frag in expected_fragments {
        let found = errors.iter().any(|e| e.message.contains(frag));
        assert!(
            found,
            "expected error containing {:?}, but not found in: {:?}",
            frag,
            errors.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
    }
}

/// Evaluate a derive function with no entity/state dependencies.
fn eval_derive(source: &str, name: &str, args: Vec<Value>) -> Value {
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let adapter = StateAdapter::new(state);
    let mut handler = NoopHandler;
    adapter
        .run(&mut handler, |s, h| {
            interp.evaluate_derive(s, h, name, args)
        })
        .unwrap()
}

struct NoopHandler;
impl EffectHandler for NoopHandler {
    fn handle(&mut self, _: Effect) -> Response {
        Response::Acknowledged
    }
}

// ═══════════════════════════════════════════════════════════════
// 1. Coercion table
// ═══════════════════════════════════════════════════════════════

#[test]
fn coercion_dice_to_int_is_error() {
    // Spec: DiceExpr → int: NEVER (must roll() first)
    expect_checker_errors(
        r#"
system "test" {
    derive foo() -> int { 1d20 }
}
"#,
        &["function body has type DiceExpr, expected return type int"],
    );
}

#[test]
fn coercion_int_to_dice_is_error() {
    // Spec: int → DiceExpr: NEVER
    expect_checker_errors(
        r#"
system "test" {
    derive foo() -> DiceExpr { 5 }
}
"#,
        &["function body has type int, expected return type DiceExpr"],
    );
}

#[test]
fn coercion_dice_to_roll_result_only_via_roll() {
    // Spec: DiceExpr → RollResult: only via explicit roll() call
    expect_checker_errors(
        r#"
system "test" {
    derive foo() -> RollResult { 1d20 }
}
"#,
        &["function body has type DiceExpr, expected return type RollResult"],
    );
}

#[test]
fn coercion_roll_result_to_int_in_comparison() {
    // Spec: RollResult → int: implicit in comparison ops
    // Mechanics are not callable via evaluate_derive; just verify type-checking
    let source = r#"
system "test" {
    mechanic check_roll() -> bool {
        let r = roll(1d20)
        r >= 0
    }
}
"#;
    let (program, result) = setup(source);
    let _interp = Interpreter::new(&program, &result.env).unwrap();
}

#[test]
fn coercion_roll_result_explicit_total() {
    // Spec: RollResult → int via .total
    let source = r#"
system "test" {
    mechanic get_total() -> int {
        let r = roll(1d20)
        r.total
    }
}
"#;
    let (program, result) = setup(source);
    // Just checking that it type-checks OK
    let _interp = Interpreter::new(&program, &result.env).unwrap();
}

#[test]
fn coercion_roll_result_unmodified_field() {
    // Spec: .unmodified is sum of kept dice WITHOUT modifier
    let source = r#"
system "test" {
    mechanic get_unmod() -> int {
        let r = roll(1d20)
        r.unmodified
    }
}
"#;
    let (program, result) = setup(source);
    let _interp = Interpreter::new(&program, &result.env).unwrap();
}

#[test]
fn coercion_dice_in_comparison_rejected() {
    // Spec: DiceExpr cannot compare directly; must roll() first
    expect_checker_errors(
        r#"
system "test" {
    derive foo() -> bool {
        let x: DiceExpr = 1d20
        x >= 15
    }
}
"#,
        &["cannot compare DiceExpr directly"],
    );
}

// ═══════════════════════════════════════════════════════════════
// 2. Arithmetic combinations
// ═══════════════════════════════════════════════════════════════

// ── int arithmetic ───────────────────────────────────────────

#[test]
fn arith_int_add() {
    let val = eval_derive(
        r#"
system "test" {
    derive f(a: int, b: int) -> int { a + b }
}
"#,
        "f",
        vec![Value::Int(3), Value::Int(7)],
    );
    assert_eq!(val, Value::Int(10));
}

#[test]
fn arith_int_sub() {
    let val = eval_derive(
        r#"
system "test" {
    derive f(a: int, b: int) -> int { a - b }
}
"#,
        "f",
        vec![Value::Int(10), Value::Int(4)],
    );
    assert_eq!(val, Value::Int(6));
}

#[test]
fn arith_int_mul() {
    let val = eval_derive(
        r#"
system "test" {
    derive f(a: int, b: int) -> int { a * b }
}
"#,
        "f",
        vec![Value::Int(6), Value::Int(7)],
    );
    assert_eq!(val, Value::Int(42));
}

#[test]
fn arith_int_div_yields_float() {
    // Spec: int / int → float (ALWAYS)
    let val = eval_derive(
        r#"
system "test" {
    derive f(a: int, b: int) -> float { a / b }
}
"#,
        "f",
        vec![Value::Int(10), Value::Int(3)],
    );
    match val {
        Value::Float(f) => {
            let expected = 10.0 / 3.0;
            assert!((f - expected).abs() < 1e-10, "expected {}, got {}", expected, f);
        }
        other => panic!("expected Float, got {:?}", other),
    }
}

#[test]
fn arith_int_div_return_as_int_error() {
    // int / int → float, so returning as int should be a type error
    expect_checker_errors(
        r#"
system "test" {
    derive f(x: int) -> int { x / 2 }
}
"#,
        &["function body has type float, expected return type int"],
    );
}

// ── float arithmetic (numeric promotion) ─────────────────────

#[test]
fn arith_float_plus_int() {
    // Spec: float + int → float (numeric promotion)
    let val = eval_derive(
        r#"
system "test" {
    derive f(a: int, b: int) -> float { a / b + 1 }
}
"#,
        "f",
        vec![Value::Int(7), Value::Int(2)],
    );
    // 7/2 = 3.5, 3.5 + 1 = 4.5
    match val {
        Value::Float(f) => assert!((f - 4.5).abs() < 1e-10),
        other => panic!("expected Float, got {:?}", other),
    }
}

#[test]
fn arith_int_plus_float() {
    // Spec: int + float → float (commutative)
    let val = eval_derive(
        r#"
system "test" {
    derive f(a: int, b: int) -> float { 1 + a / b }
}
"#,
        "f",
        vec![Value::Int(7), Value::Int(2)],
    );
    // 1 + 3.5 = 4.5
    match val {
        Value::Float(f) => assert!((f - 4.5).abs() < 1e-10),
        other => panic!("expected Float, got {:?}", other),
    }
}

#[test]
fn arith_float_sub_int() {
    let val = eval_derive(
        r#"
system "test" {
    derive f(a: int, b: int) -> float { a / b - 1 }
}
"#,
        "f",
        vec![Value::Int(7), Value::Int(2)],
    );
    // 3.5 - 1 = 2.5
    match val {
        Value::Float(f) => assert!((f - 2.5).abs() < 1e-10),
        other => panic!("expected Float, got {:?}", other),
    }
}

#[test]
fn arith_float_mul_int() {
    let val = eval_derive(
        r#"
system "test" {
    derive f(a: int, b: int) -> float { a / b * 2 }
}
"#,
        "f",
        vec![Value::Int(7), Value::Int(2)],
    );
    // 3.5 * 2 = 7.0
    match val {
        Value::Float(f) => assert!((f - 7.0).abs() < 1e-10),
        other => panic!("expected Float, got {:?}", other),
    }
}

#[test]
fn arith_float_div_int() {
    let val = eval_derive(
        r#"
system "test" {
    derive f(a: int, b: int) -> float { a / b / 2 }
}
"#,
        "f",
        vec![Value::Int(7), Value::Int(2)],
    );
    // 3.5 / 2 = 1.75
    match val {
        Value::Float(f) => assert!((f - 1.75).abs() < 1e-10),
        other => panic!("expected Float, got {:?}", other),
    }
}

#[test]
fn arith_float_float() {
    let val = eval_derive(
        r#"
system "test" {
    derive f(a: int, b: int) -> float { a / b + a / b }
}
"#,
        "f",
        vec![Value::Int(7), Value::Int(2)],
    );
    // 3.5 + 3.5 = 7.0
    match val {
        Value::Float(f) => assert!((f - 7.0).abs() < 1e-10),
        other => panic!("expected Float, got {:?}", other),
    }
}

// ── DiceExpr algebra ─────────────────────────────────────────

#[test]
fn arith_dice_plus_int() {
    // Spec: DiceExpr + int → DiceExpr (add constant modifier)
    let source = r#"
system "test" {
    derive f() -> DiceExpr { 1d20 + 5 }
}
"#;
    let (program, result) = setup(source);
    let _interp = Interpreter::new(&program, &result.env).unwrap();
}

#[test]
fn arith_int_plus_dice() {
    // Spec: int + DiceExpr → DiceExpr (commutative)
    let source = r#"
system "test" {
    derive f() -> DiceExpr { 5 + 1d20 }
}
"#;
    let (program, result) = setup(source);
    let _interp = Interpreter::new(&program, &result.env).unwrap();
}

#[test]
fn arith_dice_plus_dice() {
    // Spec: DiceExpr + DiceExpr → DiceExpr (combine pools)
    let source = r#"
system "test" {
    derive f() -> DiceExpr { 1d8 + 1d6 }
}
"#;
    let (program, result) = setup(source);
    let _interp = Interpreter::new(&program, &result.env).unwrap();
}

#[test]
fn arith_dice_sub_int() {
    // Spec: DiceExpr - int → DiceExpr (subtract constant modifier)
    let source = r#"
system "test" {
    derive f() -> DiceExpr { 1d20 - 2 }
}
"#;
    let (program, result) = setup(source);
    let _interp = Interpreter::new(&program, &result.env).unwrap();
}

#[test]
fn arith_dice_mul_int_error() {
    // Spec: DiceExpr * int is a type error
    expect_checker_errors(
        r#"
system "test" {
    derive f() -> DiceExpr { 1d8 * 2 }
}
"#,
        &["cannot multiply DiceExpr"],
    );
}

#[test]
fn arith_int_mul_dice_error() {
    // Spec: int * DiceExpr is also a type error
    expect_checker_errors(
        r#"
system "test" {
    derive f() -> DiceExpr { 2 * 1d8 }
}
"#,
        &["cannot multiply DiceExpr"],
    );
}

#[test]
fn arith_dice_div_error() {
    // Spec: DiceExpr / anything is an error
    expect_checker_errors(
        r#"
system "test" {
    derive f() -> DiceExpr { 1d8 / 2 }
}
"#,
        &["cannot divide DiceExpr"],
    );
}

#[test]
fn arith_dice_sub_dice_error() {
    // Spec does NOT list DiceExpr - DiceExpr
    expect_checker_errors(
        r#"
system "test" {
    derive f() -> DiceExpr { 1d8 - 1d6 }
}
"#,
        &["cannot subtract"],
    );
}

#[test]
fn arith_int_sub_dice_error() {
    // Spec does NOT list int - DiceExpr
    expect_checker_errors(
        r#"
system "test" {
    derive f() -> DiceExpr { 5 - 1d8 }
}
"#,
        &["cannot subtract"],
    );
}

#[test]
fn arith_dice_plus_float_error() {
    // Only DiceExpr + int is valid, not DiceExpr + float
    expect_checker_errors(
        r#"
system "test" {
    derive f(a: int, b: int) -> DiceExpr {
        1d20 + a / b
    }
}
"#,
        &["cannot add"],
    );
}

#[test]
fn arith_neg_dice_error() {
    // Unary negation is not defined for DiceExpr
    expect_checker_errors(
        r#"
system "test" {
    derive f() -> DiceExpr { -1d20 }
}
"#,
        &["cannot negate"],
    );
}

// ── DiceExpr runtime evaluation ──────────────────────────────

#[test]
fn arith_dice_plus_int_runtime() {
    let val = eval_derive(
        r#"
system "test" {
    derive f() -> DiceExpr { 1d20 + 5 }
}
"#,
        "f",
        vec![],
    );
    match val {
        Value::DiceExpr(d) => {
            assert_eq!(d.groups.len(), 1);
            assert_eq!(d.groups[0].count, 1);
            assert_eq!(d.groups[0].sides, 20);
            assert_eq!(d.modifier, 5);
        }
        other => panic!("expected DiceExpr, got {:?}", other),
    }
}

#[test]
fn arith_dice_plus_dice_runtime() {
    // DiceExpr + DiceExpr concatenates groups, sums modifiers
    let val = eval_derive(
        r#"
system "test" {
    derive f() -> DiceExpr { 1d8 + 3 + 1d6 }
}
"#,
        "f",
        vec![],
    );
    match val {
        Value::DiceExpr(d) => {
            assert_eq!(d.groups.len(), 2, "should have two groups");
            assert_eq!(d.modifier, 3);
        }
        other => panic!("expected DiceExpr, got {:?}", other),
    }
}

#[test]
fn arith_dice_sub_int_runtime() {
    let val = eval_derive(
        r#"
system "test" {
    derive f() -> DiceExpr { 1d20 - 2 }
}
"#,
        "f",
        vec![],
    );
    match val {
        Value::DiceExpr(d) => {
            assert_eq!(d.modifier, -2);
        }
        other => panic!("expected DiceExpr, got {:?}", other),
    }
}

// ── multiply_dice builtin ────────────────────────────────────

#[test]
fn multiply_dice_runtime() {
    // Spec: multiply_dice(1d8 + 3, 2) => 2d8 + 3
    let val = eval_derive(
        r#"
system "test" {
    derive f() -> DiceExpr { multiply_dice(1d8 + 3, 2) }
}
"#,
        "f",
        vec![],
    );
    match val {
        Value::DiceExpr(d) => {
            assert_eq!(d.groups.len(), 1);
            assert_eq!(d.groups[0].count, 2);
            assert_eq!(d.groups[0].sides, 8);
            assert_eq!(d.modifier, 3, "modifier should be preserved, not doubled");
        }
        other => panic!("expected DiceExpr, got {:?}", other),
    }
}

#[test]
fn multiply_dice_heterogeneous() {
    // Spec: multiply_dice(1d8 + 1d6, 2) => 2d8 + 2d6
    let val = eval_derive(
        r#"
system "test" {
    derive f() -> DiceExpr { multiply_dice(1d8 + 1d6, 2) }
}
"#,
        "f",
        vec![],
    );
    match val {
        Value::DiceExpr(d) => {
            assert_eq!(d.groups.len(), 2);
            assert_eq!(d.groups[0].count, 2);
            assert_eq!(d.groups[1].count, 2);
        }
        other => panic!("expected DiceExpr, got {:?}", other),
    }
}

// ── String operations ────────────────────────────────────────

#[test]
fn arith_string_concat() {
    let val = eval_derive(
        r#"
system "test" {
    derive f(a: string, b: string) -> string { a + b }
}
"#,
        "f",
        vec![Value::Str("hello ".into()), Value::Str("world".into())],
    );
    assert_eq!(val, Value::Str("hello world".into()));
}

#[test]
fn arith_string_sub_error() {
    expect_checker_errors(
        r#"
system "test" {
    derive f(a: string, b: string) -> string { a - b }
}
"#,
        &["cannot subtract"],
    );
}

// ── Type mismatch errors ─────────────────────────────────────

#[test]
fn arith_bool_add_error() {
    expect_checker_errors(
        r#"
system "test" {
    derive f() -> bool { true + false }
}
"#,
        &["cannot add"],
    );
}

#[test]
fn arith_string_plus_int_error() {
    expect_checker_errors(
        r#"
system "test" {
    derive f(s: string) -> string { s + 1 }
}
"#,
        &["cannot add"],
    );
}

// ═══════════════════════════════════════════════════════════════
// 3. Unit type arithmetic
// ═══════════════════════════════════════════════════════════════

fn unit_source(body: &str) -> String {
    format!(
        r#"
system "test" {{
    unit Feet suffix ft {{ value: int }}
    unit GoldPieces suffix gp {{ value: int }}
    {body}
}}
"#
    )
}

#[test]
fn unit_add_same_type() {
    // Spec: unit + unit (same) → unit
    let val = eval_derive(
        &unit_source("derive f() -> Feet { 30ft + 10ft }"),
        "f",
        vec![],
    );
    match &val {
        Value::Struct { name, fields } => {
            assert_eq!(name.as_str(), "Feet");
            assert_eq!(fields.get("value"), Some(&Value::Int(40)));
        }
        other => panic!("expected Feet struct, got {:?}", other),
    }
}

#[test]
fn unit_sub_same_type() {
    // Spec: unit - unit (same) → unit
    let val = eval_derive(
        &unit_source("derive f() -> Feet { 30ft - 10ft }"),
        "f",
        vec![],
    );
    match &val {
        Value::Struct { name, fields } => {
            assert_eq!(name.as_str(), "Feet");
            assert_eq!(fields.get("value"), Some(&Value::Int(20)));
        }
        other => panic!("expected Feet struct, got {:?}", other),
    }
}

#[test]
fn unit_int_mul() {
    // Spec: int * unit → unit
    let val = eval_derive(
        &unit_source("derive f() -> Feet { 3 * 10ft }"),
        "f",
        vec![],
    );
    match &val {
        Value::Struct { name, fields } => {
            assert_eq!(name.as_str(), "Feet");
            assert_eq!(fields.get("value"), Some(&Value::Int(30)));
        }
        other => panic!("expected Feet struct, got {:?}", other),
    }
}

#[test]
fn unit_mul_int() {
    // Spec: unit * int → unit (commutative)
    let val = eval_derive(
        &unit_source("derive f() -> Feet { 10ft * 3 }"),
        "f",
        vec![],
    );
    match &val {
        Value::Struct { name, fields } => {
            assert_eq!(name.as_str(), "Feet");
            assert_eq!(fields.get("value"), Some(&Value::Int(30)));
        }
        other => panic!("expected Feet struct, got {:?}", other),
    }
}

#[test]
fn unit_div_same_type() {
    // Spec: unit / unit (same) → float (dimensionless ratio)
    let val = eval_derive(
        &unit_source("derive f() -> float { 60ft / 30ft }"),
        "f",
        vec![],
    );
    match val {
        Value::Float(f) => assert!((f - 2.0).abs() < 1e-10),
        other => panic!("expected Float, got {:?}", other),
    }
}

#[test]
fn unit_negate() {
    // Spec: -unit → unit (negates field value)
    let val = eval_derive(
        &unit_source("derive f() -> Feet { -30ft }"),
        "f",
        vec![],
    );
    match &val {
        Value::Struct { name, fields } => {
            assert_eq!(name.as_str(), "Feet");
            assert_eq!(fields.get("value"), Some(&Value::Int(-30)));
        }
        other => panic!("expected Feet struct, got {:?}", other),
    }
}

#[test]
fn unit_field_access() {
    // Spec: declared field accessible via dot notation
    let val = eval_derive(
        &unit_source("derive f() -> int { 30ft.value }"),
        "f",
        vec![],
    );
    assert_eq!(val, Value::Int(30));
}

#[test]
fn unit_struct_construction() {
    // Spec: struct construction always available
    let val = eval_derive(
        &unit_source("derive f() -> Feet { Feet { value: 42 } }"),
        "f",
        vec![],
    );
    match &val {
        Value::Struct { name, fields } => {
            assert_eq!(name.as_str(), "Feet");
            assert_eq!(fields.get("value"), Some(&Value::Int(42)));
        }
        other => panic!("expected Feet struct, got {:?}", other),
    }
}

// ── Unit type arithmetic error cases ─────────────────────────

#[test]
fn unit_add_different_type_error() {
    // Spec: unit + different_unit → ERROR
    expect_checker_errors(
        &unit_source("derive f() -> Feet { 30ft + 5gp }"),
        &["cannot add"],
    );
}

#[test]
fn unit_sub_different_type_error() {
    // Spec: unit - different_unit → ERROR
    expect_checker_errors(
        &unit_source("derive f() -> Feet { 30ft - 5gp }"),
        &["cannot subtract"],
    );
}

#[test]
fn unit_add_int_error() {
    // Spec: unit + int → ERROR
    expect_checker_errors(
        &unit_source("derive f() -> Feet { 30ft + 10 }"),
        &["cannot add"],
    );
}

#[test]
fn unit_sub_int_error() {
    // Spec: unit - int → ERROR
    expect_checker_errors(
        &unit_source("derive f() -> Feet { 30ft - 10 }"),
        &["cannot subtract"],
    );
}

#[test]
fn int_add_unit_error() {
    // Spec: int + unit → ERROR
    expect_checker_errors(
        &unit_source("derive f() -> Feet { 10 + 30ft }"),
        &["cannot add"],
    );
}

#[test]
fn int_sub_unit_error() {
    // Spec: int - unit → ERROR
    expect_checker_errors(
        &unit_source("derive f() -> Feet { 10 - 30ft }"),
        &["cannot subtract"],
    );
}

#[test]
fn unit_mul_unit_error() {
    // Spec: unit * unit → ERROR (no squared units)
    expect_checker_errors(
        &unit_source("derive f() -> Feet { 30ft * 10ft }"),
        &["cannot multiply"],
    );
}

#[test]
fn unit_div_int_error() {
    // Spec: unit / int → ERROR (force explicit rounding)
    expect_checker_errors(
        &unit_source("derive f() -> Feet { 30ft / 2 }"),
        &["cannot divide"],
    );
}

#[test]
fn int_div_unit_error() {
    // Spec: int / unit → ERROR (meaningless)
    expect_checker_errors(
        &unit_source("derive f() -> Feet { 30 / 10ft }"),
        &["cannot divide"],
    );
}

#[test]
fn unit_div_different_type_error() {
    // Different unit types: unit / different_unit → ERROR
    expect_checker_errors(
        &unit_source("derive f() -> float { 30ft / 5gp }"),
        &["cannot divide"],
    );
}

// ── Unit type: half_speed pattern from spec ──────────────────

#[test]
fn unit_half_speed_pattern() {
    // Spec example: Feet { value: floor(speed.value / 2) }
    let val = eval_derive(
        &unit_source(
            r#"
    derive half_speed(speed: Feet) -> Feet {
        Feet { value: floor(speed.value / 2) }
    }
"#,
        ),
        "half_speed",
        vec![{
            let mut f = BTreeMap::new();
            f.insert("value".into(), Value::Int(30));
            Value::Struct {
                name: "Feet".into(),
                fields: f,
            }
        }],
    );
    match &val {
        Value::Struct { name, fields } => {
            assert_eq!(name.as_str(), "Feet");
            assert_eq!(fields.get("value"), Some(&Value::Int(15)));
        }
        other => panic!("expected Feet struct, got {:?}", other),
    }
}

// ═══════════════════════════════════════════════════════════════
// 4. Unit type comparisons
// ═══════════════════════════════════════════════════════════════

#[test]
fn unit_eq_same_type() {
    let val = eval_derive(
        &unit_source("derive f() -> bool { 30ft == 30ft }"),
        "f",
        vec![],
    );
    assert_eq!(val, Value::Bool(true));
}

#[test]
fn unit_neq_same_type() {
    let val = eval_derive(
        &unit_source("derive f() -> bool { 30ft != 20ft }"),
        "f",
        vec![],
    );
    assert_eq!(val, Value::Bool(true));
}

#[test]
fn unit_gt_same_type() {
    let val = eval_derive(
        &unit_source("derive f() -> bool { 30ft > 20ft }"),
        "f",
        vec![],
    );
    assert_eq!(val, Value::Bool(true));
}

#[test]
fn unit_lt_same_type() {
    let val = eval_derive(
        &unit_source("derive f() -> bool { 20ft < 30ft }"),
        "f",
        vec![],
    );
    assert_eq!(val, Value::Bool(true));
}

#[test]
fn unit_gte_same_type() {
    let val = eval_derive(
        &unit_source("derive f() -> bool { 30ft >= 30ft }"),
        "f",
        vec![],
    );
    assert_eq!(val, Value::Bool(true));
}

#[test]
fn unit_lte_same_type() {
    let val = eval_derive(
        &unit_source("derive f() -> bool { 30ft <= 30ft }"),
        "f",
        vec![],
    );
    assert_eq!(val, Value::Bool(true));
}

#[test]
fn unit_cmp_different_type_error() {
    // Spec: unit CMP different_unit → ERROR
    expect_checker_errors(
        &unit_source("derive f() -> bool { 30ft > 5gp }"),
        &["cannot order"],
    );
}

#[test]
fn unit_cmp_int_error() {
    // Spec: unit CMP int → ERROR
    expect_checker_errors(
        &unit_source("derive f() -> bool { 30ft > 30 }"),
        &["cannot order"],
    );
}

#[test]
fn int_cmp_unit_error() {
    // Spec: int CMP unit → ERROR
    expect_checker_errors(
        &unit_source("derive f() -> bool { 30 > 30ft }"),
        &["cannot order"],
    );
}

#[test]
fn unit_eq_different_type_error() {
    expect_checker_errors(
        &unit_source("derive f() -> bool { 30ft == 5gp }"),
        &["cannot compare"],
    );
}

#[test]
fn unit_eq_int_error() {
    expect_checker_errors(
        &unit_source("derive f() -> bool { 30ft == 30 }"),
        &["cannot compare"],
    );
}

// ═══════════════════════════════════════════════════════════════
// 5. Resource type clamping
// ═══════════════════════════════════════════════════════════════

#[test]
fn resource_clamp_on_assign() {
    // Spec: resource(min..=max) — assignments clamp to [min, max]
    let source = r#"
system "test" {
    entity Character {
        HP: resource(0..=20)
    }
    action SetHP on actor: Character (val: int) {
        resolve {
            actor.HP = val
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(10));
    let entity = state.add_entity("Character", fields);
    let adapter = StateAdapter::new(state);
    let mut handler = NoopHandler;

    // Set HP to 100 — should clamp to 20
    adapter.run(&mut handler, |s, h| {
        interp
            .execute_action(s, h, "SetHP", entity, vec![Value::Int(100)])
            .unwrap();
    });
    assert_eq!(
        adapter.read_field(&entity, "HP"),
        Some(Value::Int(20)),
        "HP should be clamped to max 20"
    );

    // Set HP to -5 — should clamp to 0
    adapter.run(&mut handler, |s, h| {
        interp
            .execute_action(s, h, "SetHP", entity, vec![Value::Int(-5)])
            .unwrap();
    });
    assert_eq!(
        adapter.read_field(&entity, "HP"),
        Some(Value::Int(0)),
        "HP should be clamped to min 0"
    );
}

#[test]
fn resource_clamp_on_pluseq() {
    // Spec: += clamps the result
    let source = r#"
system "test" {
    entity Character {
        HP: resource(0..=20)
    }
    action Heal on actor: Character (amount: int) {
        resolve {
            actor.HP += amount
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(15));
    let entity = state.add_entity("Character", fields);
    let adapter = StateAdapter::new(state);
    let mut handler = NoopHandler;

    // Heal 100 from 15 — should clamp to 20
    adapter.run(&mut handler, |s, h| {
        interp
            .execute_action(s, h, "Heal", entity, vec![Value::Int(100)])
            .unwrap();
    });
    assert_eq!(
        adapter.read_field(&entity, "HP"),
        Some(Value::Int(20)),
        "HP should be clamped to max 20"
    );
}

#[test]
fn resource_clamp_on_minuseq() {
    // Spec: -= clamps the result
    let source = r#"
system "test" {
    entity Character {
        HP: resource(0..=20)
    }
    action Damage on actor: Character (amount: int) {
        resolve {
            actor.HP -= amount
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(5));
    let entity = state.add_entity("Character", fields);
    let adapter = StateAdapter::new(state);
    let mut handler = NoopHandler;

    // Damage 100 from 5 — should clamp to 0
    adapter.run(&mut handler, |s, h| {
        interp
            .execute_action(s, h, "Damage", entity, vec![Value::Int(100)])
            .unwrap();
    });
    assert_eq!(
        adapter.read_field(&entity, "HP"),
        Some(Value::Int(0)),
        "HP should be clamped to min 0"
    );
}

#[test]
fn resource_reads_as_int_in_arithmetic() {
    // Resource behaves as int in expressions
    let source = r#"
system "test" {
    entity Character {
        HP: resource(0..=20)
    }
    derive doubled_hp(c: Character) -> int {
        c.HP * 2
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(10));
    let entity = state.add_entity("Character", fields);
    let adapter = StateAdapter::new(state);
    let mut handler = NoopHandler;
    let val = adapter.run(&mut handler, |s, h| {
        interp.evaluate_derive(s, h, "doubled_hp", vec![Value::Entity(entity)])
    });
    assert_eq!(val.unwrap(), Value::Int(20));
}

#[test]
fn resource_in_division_yields_float() {
    // resource / int → float (resource is int-like)
    let source = r#"
system "test" {
    entity Character {
        HP: resource(0..=20)
    }
    derive half_hp(c: Character) -> float {
        c.HP / 2
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut fields = HashMap::new();
    fields.insert("HP".into(), Value::Int(15));
    let entity = state.add_entity("Character", fields);
    let adapter = StateAdapter::new(state);
    let mut handler = NoopHandler;
    let val = adapter.run(&mut handler, |s, h| {
        interp.evaluate_derive(s, h, "half_hp", vec![Value::Entity(entity)])
    });
    match val.unwrap() {
        Value::Float(f) => assert!((f - 7.5).abs() < 1e-10),
        other => panic!("expected Float, got {:?}", other),
    }
}

// ═══════════════════════════════════════════════════════════════
// 6. Float: no literals, only from division, floor/ceil
// ═══════════════════════════════════════════════════════════════

#[test]
fn float_no_literal_syntax() {
    // There is no float literal syntax — "3.14" is not valid
    let (_, parse_errors) = ttrpg_parser::parse(
        r#"
system "test" {
    derive f() -> float { 3.14 }
}
"#,
        FileId::SYNTH,
    );
    assert!(
        !parse_errors.is_empty(),
        "float literal 3.14 should be a parse error"
    );
}

#[test]
fn float_from_division() {
    // Spec: float produced only by / operator
    let val = eval_derive(
        r#"
system "test" {
    derive f() -> float { 10 / 3 }
}
"#,
        "f",
        vec![],
    );
    match val {
        Value::Float(f) => assert!((f - 10.0 / 3.0).abs() < 1e-10),
        other => panic!("expected Float, got {:?}", other),
    }
}

#[test]
fn float_floor_to_int() {
    // Spec: floor() converts float → int
    let val = eval_derive(
        r#"
system "test" {
    derive f(score: int) -> int {
        floor((score - 10) / 2)
    }
}
"#,
        "f",
        vec![Value::Int(9)],
    );
    // (9 - 10) / 2 = -1/2 = -0.5, floor(-0.5) = -1
    assert_eq!(val, Value::Int(-1));
}

#[test]
fn float_ceil_to_int() {
    let val = eval_derive(
        r#"
system "test" {
    derive f(a: int, b: int) -> int {
        ceil(a / b)
    }
}
"#,
        "f",
        vec![Value::Int(7), Value::Int(3)],
    );
    // 7/3 = 2.333..., ceil = 3
    assert_eq!(val, Value::Int(3));
}

#[test]
fn float_variable_typed_ok() {
    // Spec: Variables and fields CAN be typed float
    let source = r#"
system "test" {
    derive f(a: int, b: int) -> float {
        let x: float = a / b
        x
    }
}
"#;
    let (program, result) = setup(source);
    let _interp = Interpreter::new(&program, &result.env).unwrap();
}

#[test]
fn float_pluseq_int_is_error() {
    // Cannot assign float to int field
    expect_checker_errors(
        r#"
system "test" {
    entity Character { HP: int }
    action Foo on actor: Character () {
        resolve {
            actor.HP += 1 / 2
        }
    }
}
"#,
        &["float"],
    );
}

// ═══════════════════════════════════════════════════════════════
// 7. Composite types: list, set, map, option
// ═══════════════════════════════════════════════════════════════

#[test]
fn composite_list_construction() {
    let val = eval_derive(
        r#"
system "test" {
    derive f() -> list<int> { [1, 2, 3] }
}
"#,
        "f",
        vec![],
    );
    assert_eq!(
        val,
        Value::List(vec![Value::Int(1), Value::Int(2), Value::Int(3)])
    );
}

#[test]
fn composite_list_index() {
    let val = eval_derive(
        r#"
system "test" {
    derive f(xs: list<int>) -> int { xs[1] }
}
"#,
        "f",
        vec![Value::List(vec![
            Value::Int(10),
            Value::Int(20),
            Value::Int(30),
        ])],
    );
    assert_eq!(val, Value::Int(20));
}

#[test]
fn composite_list_len() {
    let val = eval_derive(
        r#"
system "test" {
    derive f(xs: list<int>) -> int { len(xs) }
}
"#,
        "f",
        vec![Value::List(vec![
            Value::Int(10),
            Value::Int(20),
            Value::Int(30),
        ])],
    );
    assert_eq!(val, Value::Int(3));
}

#[test]
fn composite_list_in_membership() {
    let val = eval_derive(
        r#"
system "test" {
    derive f() -> bool { 2 in [1, 2, 3] }
}
"#,
        "f",
        vec![],
    );
    assert_eq!(val, Value::Bool(true));
}

#[test]
fn composite_list_not_in() {
    let val = eval_derive(
        r#"
system "test" {
    derive f() -> bool { 5 in [1, 2, 3] }
}
"#,
        "f",
        vec![],
    );
    assert_eq!(val, Value::Bool(false));
}

#[test]
fn composite_map_construction_and_access() {
    let val = eval_derive(
        r#"
system "test" {
    derive f() -> int {
        let m: map<string, int> = {"a": 1, "b": 2}
        m["b"]
    }
}
"#,
        "f",
        vec![],
    );
    assert_eq!(val, Value::Int(2));
}

#[test]
fn composite_map_in_membership() {
    let val = eval_derive(
        r#"
system "test" {
    derive f() -> bool {
        let m: map<string, int> = {"a": 1, "b": 2}
        "a" in m
    }
}
"#,
        "f",
        vec![],
    );
    assert_eq!(val, Value::Bool(true));
}

#[test]
fn composite_set_in_membership() {
    // Pass a set as argument and test `in` on it
    let source = r#"
system "test" {
    derive f(s: set<int>, x: int) -> bool { x in s }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let adapter = StateAdapter::new(state);
    let mut handler = NoopHandler;
    let val = adapter
        .run(&mut handler, |s, h| {
            interp.evaluate_derive(
                s,
                h,
                "f",
                vec![
                    Value::Set([Value::Int(1), Value::Int(2), Value::Int(3)].into()),
                    Value::Int(2),
                ],
            )
        })
        .unwrap();
    assert_eq!(val, Value::Bool(true));
}

#[test]
fn composite_option_some_and_unwrap() {
    let val = eval_derive(
        r#"
system "test" {
    derive f() -> int {
        let x: option<int> = some(42)
        x.unwrap()
    }
}
"#,
        "f",
        vec![],
    );
    assert_eq!(val, Value::Int(42));
}

#[test]
fn composite_option_none_unwrap_or() {
    let val = eval_derive(
        r#"
system "test" {
    derive f() -> int {
        let x: option<int> = none
        x.unwrap_or(99)
    }
}
"#,
        "f",
        vec![],
    );
    assert_eq!(val, Value::Int(99));
}

#[test]
fn composite_option_some_unwrap_or() {
    let val = eval_derive(
        r#"
system "test" {
    derive f() -> int {
        let x: option<int> = some(42)
        x.unwrap_or(99)
    }
}
"#,
        "f",
        vec![],
    );
    assert_eq!(val, Value::Int(42));
}

#[test]
fn composite_option_equality_with_none() {
    let val = eval_derive(
        r#"
system "test" {
    derive f() -> bool {
        let x: option<int> = none
        x == none
    }
}
"#,
        "f",
        vec![],
    );
    assert_eq!(val, Value::Bool(true));
}

#[test]
fn composite_list_of_units() {
    // Spec: unit types work in list containers
    let val = eval_derive(
        &unit_source(
            r#"derive f() -> int {
        let distances: list<Feet> = [30ft, 60ft, 120ft]
        len(distances)
    }"#,
        ),
        "f",
        vec![],
    );
    assert_eq!(val, Value::Int(3));
}

#[test]
fn composite_option_unit_type() {
    // Spec: unit types work in option containers
    let source = unit_source(
        r#"derive f() -> int {
        let r: option<Feet> = some(30ft)
        r.unwrap().value
    }"#,
    );
    let val = eval_derive(&source, "f", vec![]);
    assert_eq!(val, Value::Int(30));
}

// ── Composite type errors ────────────────────────────────────

#[test]
fn composite_list_wrong_index_type() {
    expect_checker_errors(
        r#"
system "test" {
    derive f(xs: list<int>) -> int { xs["key"] }
}
"#,
        &["list index must be int"],
    );
}

#[test]
fn composite_map_wrong_key_type() {
    expect_checker_errors(
        r#"
system "test" {
    derive f() -> int {
        let m: map<string, int> = {"a": 1}
        m[42]
    }
}
"#,
        &["map key type"],
    );
}

#[test]
fn composite_in_on_non_collection() {
    expect_checker_errors(
        r#"
system "test" {
    derive f() -> bool { 1 in 2 }
}
"#,
        &["must be a collection"],
    );
}

// ═══════════════════════════════════════════════════════════════
// Additional edge cases
// ═══════════════════════════════════════════════════════════════

#[test]
fn roll_result_field_access_all_fields() {
    // Spec: RollResult has expr, dice, kept, modifier, total, unmodified
    let source = r#"
system "test" {
    mechanic check_fields() -> bool {
        let r = roll(1d20 + 5)
        let _t: int = r.total
        let _u: int = r.unmodified
        let _m: int = r.modifier
        let _d: list<int> = r.dice
        let _k: list<int> = r.kept
        let _e: DiceExpr = r.expr
        true
    }
}
"#;
    let (program, result) = setup(source);
    let _interp = Interpreter::new(&program, &result.env).unwrap();
}

#[test]
fn roll_result_kept_field_runtime() {
    // Spec: check individual die faces via `kept` list
    let source = r#"
system "test" {
    mechanic check_kept() -> bool {
        let r = roll(1d20)
        1 in r.kept
    }
}
"#;
    let (program, result) = setup(source);
    let _interp = Interpreter::new(&program, &result.env).unwrap();
}

#[test]
fn dice_constructor_builtin() {
    // Spec: dice(count, sides) → DiceExpr
    let val = eval_derive(
        r#"
system "test" {
    derive f(n: int) -> DiceExpr { dice(n, 8) }
}
"#,
        "f",
        vec![Value::Int(3)],
    );
    match val {
        Value::DiceExpr(d) => {
            assert_eq!(d.groups.len(), 1);
            assert_eq!(d.groups[0].count, 3);
            assert_eq!(d.groups[0].sides, 8);
        }
        other => panic!("expected DiceExpr, got {:?}", other),
    }
}

#[test]
fn dice_constructor_plus_modifier() {
    // Spec: dice(2, 6) + 3 => 2d6 + 3
    let val = eval_derive(
        r#"
system "test" {
    derive f() -> DiceExpr { dice(2, 6) + 3 }
}
"#,
        "f",
        vec![],
    );
    match val {
        Value::DiceExpr(d) => {
            assert_eq!(d.groups[0].count, 2);
            assert_eq!(d.groups[0].sides, 6);
            assert_eq!(d.modifier, 3);
        }
        other => panic!("expected DiceExpr, got {:?}", other),
    }
}

#[test]
fn division_by_zero_runtime_error() {
    let source = r#"
system "test" {
    derive f() -> float { 1 / 0 }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let adapter = StateAdapter::new(state);
    let mut handler = NoopHandler;
    let val = adapter.run(&mut handler, |s, h| {
        interp.evaluate_derive(s, h, "f", vec![])
    });
    assert!(val.is_err(), "division by zero should be a runtime error");
}

#[test]
fn unit_type_in_entity_field() {
    // Spec: unit types work as entity fields, including with defaults
    let source = r#"
system "test" {
    unit Feet suffix ft { value: int }
    entity Character {
        speed: Feet = 30ft
    }
    derive get_speed(c: Character) -> Feet {
        c.speed
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut fields = HashMap::new();
    let mut ft_fields = BTreeMap::new();
    ft_fields.insert("value".into(), Value::Int(30));
    fields.insert(
        "speed".into(),
        Value::Struct {
            name: "Feet".into(),
            fields: ft_fields,
        },
    );
    let entity = state.add_entity("Character", fields);
    let adapter = StateAdapter::new(state);
    let mut handler = NoopHandler;
    let val = adapter
        .run(&mut handler, |s, h| {
            interp.evaluate_derive(s, h, "get_speed", vec![Value::Entity(entity)])
        })
        .unwrap();
    match &val {
        Value::Struct { name, fields } => {
            assert_eq!(name.as_str(), "Feet");
            assert_eq!(fields.get("value"), Some(&Value::Int(30)));
        }
        other => panic!("expected Feet struct, got {:?}", other),
    }
}

#[test]
fn unit_without_suffix_struct_only() {
    // Spec: without suffix, only struct construction available
    let source = r#"
system "test" {
    unit AbstractDistance { value: int }
    derive f() -> AbstractDistance {
        AbstractDistance { value: 42 }
    }
}
"#;
    let val = eval_derive(source, "f", vec![]);
    match &val {
        Value::Struct { name, fields } => {
            assert_eq!(name.as_str(), "AbstractDistance");
            assert_eq!(fields.get("value"), Some(&Value::Int(42)));
        }
        other => panic!("expected AbstractDistance struct, got {:?}", other),
    }
}

#[test]
fn unit_duplicate_suffix_error() {
    // Spec: suffixes must be unique across entire program
    expect_checker_errors(
        r#"
system "test" {
    unit Feet suffix ft { value: int }
    unit Range suffix ft { value: int }
    derive f() -> int { 0 }
}
"#,
        &["duplicate unit suffix"],
    );
}

#[test]
fn unit_suffix_must_be_alpha() {
    // Spec: suffix must match [a-zA-Z][a-zA-Z0-9_]*
    // Underscored suffix like _x should be rejected
    // Note: this is enforced at checker level
    expect_checker_errors(
        r#"
system "test" {
    unit Foo suffix _x { value: int }
    derive f() -> int { 0 }
}
"#,
        &["suffix"],
    );
}

#[test]
fn unit_must_have_one_int_field() {
    // Spec: body must contain exactly one field of type int
    expect_checker_errors(
        r#"
system "test" {
    unit Bad { value: string }
    derive f() -> int { 0 }
}
"#,
        &["int"],
    );
}
