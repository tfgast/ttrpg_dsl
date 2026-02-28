use std::collections::HashMap;

use ttrpg_checker::ty::Ty;
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::Value;

/// Base fields + inline optional groups parsed from a spawn block.
pub(super) type SpawnBlock = (
    HashMap<String, Value>,
    Vec<(String, HashMap<String, Value>)>,
);

/// Split a trimmed line into the first whitespace-delimited token and the rest.
pub(super) fn split_first_token(s: &str) -> (&str, &str) {
    match s.find(char::is_whitespace) {
        Some(pos) => (&s[..pos], &s[pos + 1..]),
        None => (s, ""),
    }
}

/// Split on commas, respecting `()`, `[]`, `{}`, and `""` nesting.
pub(super) fn split_top_level_commas(s: &str) -> Vec<&str> {
    let mut result = Vec::new();
    let mut depth = 0i32;
    let mut in_string = false;
    let mut start = 0;
    let bytes = s.as_bytes();
    let mut i = 0;

    while i < bytes.len() {
        if in_string {
            if bytes[i] == b'\\' {
                i += 2;
                continue;
            }
            if bytes[i] == b'"' {
                in_string = false;
            }
        } else {
            match bytes[i] {
                b'"' => in_string = true,
                b'(' | b'[' | b'{' => depth += 1,
                b')' | b']' | b'}' => depth -= 1,
                b',' if depth == 0 => {
                    result.push(&s[start..i]);
                    start = i + 1;
                }
                _ => {}
            }
        }
        i += 1;
    }
    result.push(&s[start..]);
    result
}

/// Find the first unquoted occurrence of a character in a string.
pub(super) fn find_unquoted(s: &str, needle: char) -> Option<usize> {
    let bytes = s.as_bytes();
    let needle_byte = needle as u8;
    let mut in_string = false;
    let mut i = 0;
    while i < bytes.len() {
        if in_string {
            if bytes[i] == b'\\' {
                i += 2;
                continue;
            }
            if bytes[i] == b'"' {
                in_string = false;
            }
        } else if bytes[i] == b'"' {
            in_string = true;
        } else if bytes[i] == needle_byte {
            return Some(i);
        }
        i += 1;
    }
    None
}

/// Check that a handle name is a bare identifier: `[a-zA-Z_][a-zA-Z0-9_]*`.
pub(super) fn is_valid_handle(s: &str) -> bool {
    let mut chars = s.chars();
    match chars.next() {
        Some(c) if c.is_ascii_alphabetic() || c == '_' => {}
        _ => return false,
    }
    chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// Check that a runtime value matches the declared type, recursing into
/// container element types (list, set, map, option).
///
/// When `gs` is provided, entity values are checked against their concrete
/// type (e.g. a `Character` entity won't match a `Monster` field).
pub(super) fn value_matches_ty(val: &Value, ty: &Ty, gs: Option<&GameState>) -> bool {
    match (val, ty) {
        (Value::Int(_), Ty::Int | Ty::Resource) => true,
        (Value::Float(_), Ty::Float) => true,
        (Value::Bool(_), Ty::Bool) => true,
        (Value::Str(_), Ty::String) => true,
        (Value::None, Ty::Option(_)) => true,
        (Value::Option(inner), Ty::Option(inner_ty)) => match inner {
            Some(v) => value_matches_ty(v, inner_ty, gs),
            None => true,
        },
        (Value::Entity(_), Ty::AnyEntity) => true,
        (Value::Entity(eref), Ty::Entity(expected)) => {
            match gs.and_then(|g| g.entity_type_name(eref)) {
                Some(actual) => actual == expected.as_str(),
                // If we can't resolve the entity type, accept it (best-effort)
                None => true,
            }
        }
        (Value::List(elems), Ty::List(elem_ty)) => {
            elems.iter().all(|e| value_matches_ty(e, elem_ty, gs))
        }
        (Value::Set(elems), Ty::Set(elem_ty)) => {
            elems.iter().all(|e| value_matches_ty(e, elem_ty, gs))
        }
        (Value::Map(entries), Ty::Map(key_ty, val_ty)) => entries
            .iter()
            .all(|(k, v)| value_matches_ty(k, key_ty, gs) && value_matches_ty(v, val_ty, gs)),
        (Value::Struct { name, .. }, Ty::Struct(n)) => name == n,
        (Value::Struct { name, .. }, Ty::RollResult) => name == "RollResult",
        (Value::Struct { name, .. }, Ty::TurnBudget) => name == "TurnBudget",
        (Value::EnumVariant { enum_name, .. }, Ty::Enum(n)) => enum_name == n,
        (Value::DiceExpr(_), Ty::DiceExpr) => true,
        (Value::RollResult(_), Ty::RollResult) => true,
        (Value::Position(_), Ty::Position) => true,
        (Value::EnumVariant { enum_name, .. }, Ty::Duration) => enum_name == "Duration",
        (Value::Condition { .. }, Ty::Condition) => true,
        (Value::Invocation(_), Ty::Invocation) => true,
        _ => false,
    }
}

/// Human-readable type name for a runtime value (used in error messages).
pub(super) fn value_type_display(val: &Value) -> String {
    match val {
        Value::Int(_) => "int".into(),
        Value::Float(_) => "float".into(),
        Value::Bool(_) => "bool".into(),
        Value::Str(_) => "string".into(),
        Value::None => "none".into(),
        Value::Option(_) => "option".into(),
        Value::Entity(_) => "entity".into(),
        Value::List(_) => "list".into(),
        Value::Set(_) => "set".into(),
        Value::Map(_) => "map".into(),
        Value::Struct { name, .. } => name.to_string(),
        Value::EnumVariant { enum_name, .. } => enum_name.to_string(),
        Value::DiceExpr(_) => "DiceExpr".into(),
        Value::RollResult(_) => "RollResult".into(),
        Value::Position(_) => "Position".into(),
        Value::Condition { .. } => "Condition".into(),
        Value::Invocation(_) => "Invocation".into(),
        Value::EnumNamespace(name) => format!("{}(namespace)", name),
    }
}
