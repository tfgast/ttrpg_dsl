//! Snapshot tests for CLI value formatting.
//!
//! These tests capture `format_value()` output as snapshots for all Value
//! variants. Run `cargo insta review` after changes to update snapshots
//! interactively.

use std::collections::{BTreeMap, BTreeSet};

use ttrpg_ast::DiceFilter;
use ttrpg_cli::format::{format_value, UnitSuffixes};
use ttrpg_interp::state::EntityRef;
use ttrpg_interp::value::{DiceExpr, RollResult, Value};

fn no_units() -> UnitSuffixes {
    UnitSuffixes::new()
}

// ═══════════════════════════════════════════════════════════════
// Primitives
// ═══════════════════════════════════════════════════════════════

#[test]
fn format_primitives() {
    let u = no_units();
    let mut output = String::new();
    output.push_str(&format!("int: {}\n", format_value(&Value::Int(42), &u)));
    output.push_str(&format!(
        "negative_int: {}\n",
        format_value(&Value::Int(-7), &u)
    ));
    output.push_str(&format!("zero: {}\n", format_value(&Value::Int(0), &u)));
    output.push_str(&format!(
        "bool_true: {}\n",
        format_value(&Value::Bool(true), &u)
    ));
    output.push_str(&format!(
        "bool_false: {}\n",
        format_value(&Value::Bool(false), &u)
    ));
    output.push_str(&format!("none: {}\n", format_value(&Value::Void, &u)));
    output.push_str(&format!(
        "float: {}\n",
        format_value(&Value::Float(2.75), &u)
    ));
    output.push_str(&format!(
        "string: {}\n",
        format_value(&Value::Str("hello".into()), &u)
    ));
    insta::assert_snapshot!(output);
}

// ═══════════════════════════════════════════════════════════════
// String escaping
// ═══════════════════════════════════════════════════════════════

#[test]
fn format_string_escaping() {
    let u = no_units();
    let mut output = String::new();
    output.push_str(&format!(
        "embedded_quote: {}\n",
        format_value(&Value::Str("a\"b".into()), &u)
    ));
    output.push_str(&format!(
        "backslash: {}\n",
        format_value(&Value::Str("a\\b".into()), &u)
    ));
    output.push_str(&format!(
        "newline: {}\n",
        format_value(&Value::Str("line1\nline2".into()), &u)
    ));
    output.push_str(&format!(
        "tab: {}\n",
        format_value(&Value::Str("a\tb".into()), &u)
    ));
    output.push_str(&format!(
        "empty: {}\n",
        format_value(&Value::Str(String::new()), &u)
    ));
    insta::assert_snapshot!(output);
}

// ═══════════════════════════════════════════════════════════════
// Collections
// ═══════════════════════════════════════════════════════════════

#[test]
fn format_list() {
    let val = Value::List(vec![Value::Int(1), Value::Int(2), Value::Int(3)]);
    insta::assert_snapshot!(format_value(&val, &no_units()));
}

#[test]
fn format_empty_list() {
    let val = Value::List(vec![]);
    insta::assert_snapshot!(format_value(&val, &no_units()));
}

#[test]
fn format_set() {
    let mut s = BTreeSet::new();
    s.insert(Value::Int(1));
    s.insert(Value::Int(2));
    s.insert(Value::Int(3));
    insta::assert_snapshot!(format_value(&Value::Set(s), &no_units()));
}

#[test]
fn format_map() {
    let mut m = BTreeMap::new();
    m.insert(Value::Str("a".into()), Value::Int(1));
    m.insert(Value::Str("b".into()), Value::Int(2));
    insta::assert_snapshot!(format_value(&Value::Map(m), &no_units()));
}

// ═══════════════════════════════════════════════════════════════
// Structured types
// ═══════════════════════════════════════════════════════════════

#[test]
fn format_struct() {
    let mut fields = BTreeMap::new();
    fields.insert("x".into(), Value::Int(10));
    fields.insert("y".into(), Value::Int(20));
    let val = Value::Struct {
        name: "Point".into(),
        fields,
    };
    insta::assert_snapshot!(format_value(&val, &no_units()));
}

#[test]
fn format_enum_variant_no_fields() {
    let val = Value::EnumVariant {
        enum_name: "Color".into(),
        variant: "red".into(),
        fields: BTreeMap::new(),
    };
    insta::assert_snapshot!(format_value(&val, &no_units()));
}

#[test]
fn format_enum_variant_with_fields() {
    let mut fields = BTreeMap::new();
    fields.insert("value".into(), Value::Int(3));
    let val = Value::EnumVariant {
        enum_name: "Duration".into(),
        variant: "rounds".into(),
        fields,
    };
    insta::assert_snapshot!(format_value(&val, &no_units()));
}

#[test]
fn format_entity() {
    insta::assert_snapshot!(format_value(&Value::Entity(EntityRef(42)), &no_units()));
}

// ═══════════════════════════════════════════════════════════════
// Dice types
// ═══════════════════════════════════════════════════════════════

#[test]
fn format_dice_simple() {
    let val = Value::DiceExpr(DiceExpr::single(2, 6, None, 3));
    insta::assert_snapshot!(format_value(&val, &no_units()));
}

#[test]
fn format_dice_negative_modifier() {
    let val = Value::DiceExpr(DiceExpr::single(1, 20, None, -2));
    insta::assert_snapshot!(format_value(&val, &no_units()));
}

#[test]
fn format_dice_with_filter() {
    let val = Value::DiceExpr(DiceExpr::single(4, 6, Some(DiceFilter::KeepHighest(3)), 0));
    insta::assert_snapshot!(format_value(&val, &no_units()));
}

#[test]
fn format_roll_result() {
    let val = Value::RollResult(RollResult {
        expr: DiceExpr::single(2, 6, None, 0),
        dice: vec![3, 5],
        kept: vec![3, 5],
        modifier: 0,
        total: 8,
        unmodified: 8,
    });
    insta::assert_snapshot!(format_value(&val, &no_units()));
}

// ═══════════════════════════════════════════════════════════════
// Unit types with suffixes
// ═══════════════════════════════════════════════════════════════

#[test]
fn format_unit_with_suffix() {
    let mut units = UnitSuffixes::new();
    units.insert("Feet".into(), "ft".into());
    let mut fields = BTreeMap::new();
    fields.insert("value".into(), Value::Int(30));
    let val = Value::Struct {
        name: "Feet".into(),
        fields,
    };
    insta::assert_snapshot!(format_value(&val, &units));
}

#[test]
fn format_unit_without_suffix_falls_back() {
    let mut fields = BTreeMap::new();
    fields.insert("value".into(), Value::Int(30));
    let val = Value::Struct {
        name: "Feet".into(),
        fields,
    };
    insta::assert_snapshot!(format_value(&val, &no_units()));
}

#[test]
fn format_unit_in_list() {
    let mut units = UnitSuffixes::new();
    units.insert("Feet".into(), "ft".into());
    let mut fields = BTreeMap::new();
    fields.insert("value".into(), Value::Int(10));
    let item = Value::Struct {
        name: "Feet".into(),
        fields,
    };
    let val = Value::List(vec![item]);
    insta::assert_snapshot!(format_value(&val, &units));
}
