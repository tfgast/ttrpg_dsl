use ttrpg_ast::ast::PatternKind;
use ttrpg_ast::Name;
use ttrpg_checker::env::DeclInfo;

use crate::state::StateProvider;
use crate::value::Value;
use crate::Env;

// ── Exact cross-type int/float helpers ─────────────────────────

/// Exact equality between i64 and f64 without lossy `i64 as f64` cast.
/// Returns false when the float has a fractional part, is non-finite, or
/// falls outside the range exactly representable as i64.
pub(super) fn int_float_eq(i: i64, f: f64) -> bool {
    // Non-finite or fractional → never equal to an integer
    if !f.is_finite() || f.fract() != 0.0 {
        return false;
    }
    // Cast f→i64 instead of i→f64 to avoid rounding large values.
    // Upper bound uses `<` because `i64::MAX as f64` rounds up to 2^63,
    // which is outside i64 range; `f as i64` would saturate incorrectly.
    // Lower bound uses `>=` because `i64::MIN as f64` is exactly -2^63.
    if f >= (i64::MIN as f64) && f < (i64::MAX as f64) {
        (f as i64) == i
    } else {
        false
    }
}

/// Exact ordering between i64 and f64 without lossy `i64 as f64` cast.
pub(super) fn int_float_cmp(i: i64, f: f64) -> Option<std::cmp::Ordering> {
    if !f.is_finite() {
        // NaN → no ordering
        if f.is_nan() {
            return None;
        }
        // +inf / -inf
        return Some(if f == f64::INFINITY {
            std::cmp::Ordering::Less
        } else {
            std::cmp::Ordering::Greater
        });
    }

    // Compare integer part first
    let f_trunc = f.trunc();
    // Upper bound uses `<` because `i64::MAX as f64` rounds up to 2^63,
    // which is outside i64 range; `f_trunc as i64` would saturate incorrectly.
    // Lower bound uses `>=` because `i64::MIN as f64` is exactly -2^63.
    if f_trunc >= (i64::MIN as f64) && f_trunc < (i64::MAX as f64) {
        let f_int = f_trunc as i64;
        match i.cmp(&f_int) {
            std::cmp::Ordering::Equal => {
                // Integer parts equal — check fractional part
                let frac = f - f_trunc;
                if frac > 0.0 {
                    Some(std::cmp::Ordering::Less) // i < f because f has positive frac
                } else if frac < 0.0 {
                    Some(std::cmp::Ordering::Greater)
                } else {
                    Some(std::cmp::Ordering::Equal)
                }
            }
            other => Some(other),
        }
    } else {
        // f is outside i64 range
        Some(if f_trunc < (i64::MIN as f64) {
            std::cmp::Ordering::Greater
        } else {
            std::cmp::Ordering::Less
        })
    }
}

// ── Semantic value comparison ──────────────────────────────────

/// Semantic equality for runtime comparisons.
///
/// All runtime equality checks (BinOp ==/!=, pattern matching, trigger
/// binding comparisons, composite value equality) use this instead of
/// `Value::eq`.
///
/// Special cases:
/// - Float: standard f64 == (-0.0 == +0.0, NaN != NaN)
/// - Position: delegates to state.position_eq()
/// - Composites: recursive walk
pub(crate) fn value_eq(state: &dyn StateProvider, a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::None, Value::None) => true,
        (Value::None, Value::Option(None)) => true,
        (Value::Option(None), Value::None) => true,
        (Value::Bool(a), Value::Bool(b)) => a == b,
        (Value::Int(a), Value::Int(b)) => a == b,
        (Value::Float(a), Value::Float(b)) => a == b, // standard f64 ==
        (Value::Int(a), Value::Float(b)) => int_float_eq(*a, *b),
        (Value::Float(a), Value::Int(b)) => int_float_eq(*b, *a),
        (Value::Str(a), Value::Str(b)) => a == b,
        (Value::DiceExpr(a), Value::DiceExpr(b)) => a == b,
        (Value::RollResult(a), Value::RollResult(b)) => a == b,
        (Value::Entity(a), Value::Entity(b)) => a == b,
        (Value::Condition { name: n1, args: a1 }, Value::Condition { name: n2, args: a2 }) => {
            n1 == n2
                && a1.len() == a2.len()
                && a1
                    .iter()
                    .zip(a2.iter())
                    .all(|((k1, v1), (k2, v2))| k1 == k2 && value_eq(state, v1, v2))
        }

        // Position: delegate to host
        (Value::Position(_), Value::Position(_)) => state.position_eq(a, b),

        // Composites: recursive
        (Value::List(a), Value::List(b)) => {
            a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| value_eq(state, x, y))
        }
        (Value::Set(a), Value::Set(b)) => {
            // Sets use structural equality since elements are ordered
            a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| value_eq(state, x, y))
        }
        (Value::Map(a), Value::Map(b)) => {
            a.len() == b.len()
                && a.iter()
                    .zip(b.iter())
                    .all(|((k1, v1), (k2, v2))| value_eq(state, k1, k2) && value_eq(state, v1, v2))
        }
        (Value::Option(a), Value::Option(b)) => match (a, b) {
            (Some(a), Some(b)) => value_eq(state, a, b),
            (None, None) => true,
            _ => false,
        },
        (
            Value::Struct {
                name: n1,
                fields: f1,
            },
            Value::Struct {
                name: n2,
                fields: f2,
            },
        ) => {
            n1 == n2
                && f1.len() == f2.len()
                && f1
                    .iter()
                    .zip(f2.iter())
                    .all(|((k1, v1), (k2, v2))| k1 == k2 && value_eq(state, v1, v2))
        }
        (
            Value::EnumVariant {
                enum_name: e1,
                variant: v1,
                fields: f1,
            },
            Value::EnumVariant {
                enum_name: e2,
                variant: v2,
                fields: f2,
            },
        ) => {
            e1 == e2
                && v1 == v2
                && f1.len() == f2.len()
                && f1
                    .iter()
                    .zip(f2.iter())
                    .all(|((k1, v1), (k2, v2))| k1 == k2 && value_eq(state, v1, v2))
        }

        // Different variants are not equal
        _ => false,
    }
}

// ── Pattern matching ───────────────────────────────────────────

/// Try to match a pattern against a value, collecting bindings.
///
/// Takes `env` so literal comparisons route through `value_eq`.
/// Returns true if the pattern matches.
pub(super) fn match_pattern(
    env: &Env,
    pattern: &PatternKind,
    value: &Value,
    bindings: &mut std::collections::HashMap<Name, Value>,
) -> bool {
    match pattern {
        PatternKind::Wildcard => true,

        PatternKind::IntLit(n) => matches!(value, Value::Int(v) if v == n),

        PatternKind::StringLit(s) => matches!(value, Value::Str(v) if v == s),

        PatternKind::BoolLit(b) => matches!(value, Value::Bool(v) if v == b),

        PatternKind::NoneLit => matches!(value, Value::None | Value::Option(None)),

        PatternKind::Some(inner_pattern) => match value {
            Value::Option(Some(inner_val)) => {
                match_pattern(env, &inner_pattern.node, inner_val, bindings)
            }
            _ => false,
        },

        PatternKind::Ident(name) => {
            // Check if this ident is a known enum variant.
            // If so, match against the variant; otherwise bind as a variable.
            if env
                .interp
                .type_env
                .variant_to_enums
                .contains_key(name.as_str())
            {
                // It's a bare enum variant — the runtime value carries its own enum_name,
                // so we match by variant name (checker guarantees correctness).
                matches!(
                    value,
                    Value::EnumVariant { variant, .. }
                    if variant == name
                )
            } else {
                bindings.insert(name.clone(), value.clone());
                true
            }
        }

        PatternKind::QualifiedVariant { ty, variant } => {
            // Match by variant name only (checker rejects bare qualified patterns
            // for payload variants, but we match by name as safety net)
            matches!(
                value,
                Value::EnumVariant { enum_name, variant: v, .. }
                if enum_name == ty && v == variant
            )
        }

        PatternKind::QualifiedDestructure {
            ty,
            variant,
            fields: patterns,
        } => {
            if let Value::EnumVariant {
                enum_name,
                variant: v,
                fields,
            } = value
            {
                if enum_name != ty || v != variant {
                    return false;
                }
                // Match field patterns positionally against variant field values
                // Look up variant field names from type env
                if let Some(DeclInfo::Enum(enum_info)) = env.interp.type_env.types.get(ty.as_str())
                {
                    if let Some(variant_info) =
                        enum_info.variants.iter().find(|vi| vi.name == *variant)
                    {
                        if patterns.len() != variant_info.fields.len() {
                            return false;
                        }
                        for (pat, (field_name, _)) in
                            patterns.iter().zip(variant_info.fields.iter())
                        {
                            if let Some(field_val) = fields.get(field_name) {
                                if !match_pattern(env, &pat.node, field_val, bindings) {
                                    return false;
                                }
                            } else {
                                return false;
                            }
                        }
                        return true;
                    }
                }
                false
            } else {
                false
            }
        }

        PatternKind::BareDestructure {
            name,
            fields: patterns,
        } => {
            // Check if this is a known enum variant
            if env
                .interp
                .type_env
                .variant_to_enums
                .contains_key(name.as_str())
            {
                if let Value::EnumVariant {
                    enum_name: actual_enum,
                    variant,
                    fields,
                } = value
                {
                    if variant != name {
                        return false;
                    }
                    // Use the value's own enum_name for field info lookup
                    if let Some(DeclInfo::Enum(enum_info)) =
                        env.interp.type_env.types.get(actual_enum.as_str())
                    {
                        if let Some(variant_info) =
                            enum_info.variants.iter().find(|vi| vi.name == *name)
                        {
                            if patterns.len() != variant_info.fields.len() {
                                return false;
                            }
                            for (pat, (field_name, _)) in
                                patterns.iter().zip(variant_info.fields.iter())
                            {
                                if let Some(field_val) = fields.get(field_name) {
                                    if !match_pattern(env, &pat.node, field_val, bindings) {
                                        return false;
                                    }
                                } else {
                                    return false;
                                }
                            }
                            return true;
                        }
                    }
                }
                false
            } else {
                // Could be a struct destructure pattern
                if let Value::Struct {
                    name: struct_name,
                    fields,
                } = value
                {
                    if struct_name != name {
                        return false;
                    }
                    // Match fields positionally using struct field info
                    if let Some(DeclInfo::Struct(struct_info)) =
                        env.interp.type_env.types.get(name.as_str())
                    {
                        if patterns.len() != struct_info.fields.len() {
                            return false;
                        }
                        for (pat, field_info) in patterns.iter().zip(struct_info.fields.iter()) {
                            if let Some(field_val) = fields.get(&field_info.name) {
                                if !match_pattern(env, &pat.node, field_val, bindings) {
                                    return false;
                                }
                            } else {
                                return false;
                            }
                        }
                        return true;
                    }
                }
                false
            }
        }
    }
}
