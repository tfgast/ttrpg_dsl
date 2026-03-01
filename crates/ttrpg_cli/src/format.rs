use std::collections::HashMap;

use ttrpg_ast::DiceFilter;
use ttrpg_ast::Name;
use ttrpg_checker::env::{DeclInfo, TypeEnv};
use ttrpg_interp::effect::FieldPathSegment;
use ttrpg_interp::value::{DiceExpr, Value};

/// Maps unit type name → suffix string (e.g., "Feet" → "ft").
pub type UnitSuffixes = HashMap<Name, String>;

/// Build a reverse lookup from unit type name to suffix from the TypeEnv.
pub fn build_unit_suffixes(type_env: &TypeEnv) -> UnitSuffixes {
    type_env
        .types
        .iter()
        .filter_map(|(name, decl)| match decl {
            DeclInfo::Unit(info) => info.suffix.as_ref().map(|s| (name.clone(), s.clone())),
            _ => None,
        })
        .collect()
}

/// Format a runtime Value for human-readable CLI output.
pub fn format_value(val: &Value, units: &UnitSuffixes) -> String {
    match val {
        Value::Int(n) => n.to_string(),
        Value::Float(f) => format!("{}", f),
        Value::Bool(b) => b.to_string(),
        Value::Str(s) => {
            let escaped = s
                .replace('\\', "\\\\")
                .replace('"', "\\\"")
                .replace('\n', "\\n")
                .replace('\r', "\\r")
                .replace('\t', "\\t");
            format!("\"{}\"", escaped)
        }
        Value::None => "none".into(),

        Value::DiceExpr(expr) => format_dice_expr(expr),

        Value::RollResult(r) => {
            format!(
                "RollResult {{ dice: [{}], total: {} }}",
                r.dice
                    .iter()
                    .map(|d| d.to_string())
                    .collect::<Vec<_>>()
                    .join(", "),
                r.total,
            )
        }

        Value::List(items) => {
            let inner: Vec<String> = items.iter().map(|v| format_value(v, units)).collect();
            format!("[{}]", inner.join(", "))
        }

        Value::Set(items) => {
            let inner: Vec<String> = items.iter().map(|v| format_value(v, units)).collect();
            format!("{{{}}}", inner.join(", "))
        }

        Value::Map(entries) => {
            let inner: Vec<String> = entries
                .iter()
                .map(|(k, v)| {
                    format!("{}: {}", format_value(k, units), format_value(v, units))
                })
                .collect();
            format!("{{{}}}", inner.join(", "))
        }

        Value::Struct { name, fields } => {
            // Unit types with a suffix: display as e.g. "30ft" instead of "Feet { value: 30 }"
            if let Some(suffix) = units.get(name) {
                if fields.len() == 1 {
                    let val = fields.values().next().unwrap();
                    return format!("{}{}", format_value(val, units), suffix);
                }
            }
            let inner: Vec<String> = fields
                .iter()
                .map(|(k, v)| format!("{}: {}", k, format_value(v, units)))
                .collect();
            format!("{} {{ {} }}", name, inner.join(", "))
        }

        Value::Entity(e) => format!("Entity({})", e.0),

        Value::EnumVariant {
            enum_name,
            variant,
            fields,
        } => {
            if fields.is_empty() {
                format!("{}.{}", enum_name, variant)
            } else {
                let inner: Vec<String> = fields
                    .iter()
                    .map(|(k, v)| format!("{}: {}", k, format_value(v, units)))
                    .collect();
                format!("{}.{}({})", enum_name, variant, inner.join(", "))
            }
        }

        Value::Option(opt) => match opt {
            Some(v) => format!("some({})", format_value(v, units)),
            None => "none".into(),
        },

        Value::Position(_) => "Position(...)".into(),

        Value::Condition { name, args } => {
            if args.is_empty() {
                format!("Condition({})", name)
            } else {
                let inner: Vec<String> = args
                    .iter()
                    .map(|(k, v)| format!("{}: {}", k, format_value(v, units)))
                    .collect();
                format!("Condition({}({}))", name, inner.join(", "))
            }
        }
        Value::EnumNamespace(name) => format!("<enum {}>", name),
        Value::ModuleAlias(name) => format!("<module alias {}>", name),
        Value::Invocation(id) => format!("Invocation({})", id.0),
    }
}

/// Format a field path for effect logging (e.g., `HP` or `stats["STR"]`).
pub fn format_path(path: &[FieldPathSegment], units: &UnitSuffixes) -> String {
    let mut s = String::new();
    for (i, seg) in path.iter().enumerate() {
        match seg {
            FieldPathSegment::Field(f) => {
                if i > 0 {
                    s.push('.');
                }
                s.push_str(f);
            }
            FieldPathSegment::Index(key) => {
                s.push('[');
                s.push_str(&format_value(key, units));
                s.push(']');
            }
        }
    }
    s
}

pub fn format_dice_expr(expr: &DiceExpr) -> String {
    let mut parts: Vec<String> = Vec::new();
    for group in &expr.groups {
        let mut gs = format!("{}d{}", group.count, group.sides);
        if let Some(filter) = &group.filter {
            match filter {
                DiceFilter::KeepHighest(n) => gs.push_str(&format!("kh{}", n)),
                DiceFilter::KeepLowest(n) => gs.push_str(&format!("kl{}", n)),
                DiceFilter::DropHighest(n) => gs.push_str(&format!("dh{}", n)),
                DiceFilter::DropLowest(n) => gs.push_str(&format!("dl{}", n)),
            }
        }
        parts.push(gs);
    }
    let mut s = parts.join(" + ");
    if expr.modifier > 0 {
        s.push_str(&format!(" + {}", expr.modifier));
    } else if expr.modifier < 0 {
        // Use wrapping_abs to avoid panic on i64::MIN, then format as unsigned
        s.push_str(&format!(" - {}", (expr.modifier as i128).unsigned_abs()));
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::{BTreeMap, BTreeSet};
    use ttrpg_interp::state::EntityRef;
    use ttrpg_interp::value::RollResult;

    fn no_units() -> UnitSuffixes {
        UnitSuffixes::new()
    }

    #[test]
    fn format_int() {
        assert_eq!(format_value(&Value::Int(42), &no_units()), "42");
    }

    #[test]
    fn format_str() {
        assert_eq!(
            format_value(&Value::Str("hello".into()), &no_units()),
            "\"hello\""
        );
    }

    #[test]
    fn format_bool() {
        let u = no_units();
        assert_eq!(format_value(&Value::Bool(true), &u), "true");
        assert_eq!(format_value(&Value::Bool(false), &u), "false");
    }

    #[test]
    fn format_none() {
        assert_eq!(format_value(&Value::None, &no_units()), "none");
    }

    #[test]
    fn format_list() {
        let val = Value::List(vec![Value::Int(1), Value::Int(2), Value::Int(3)]);
        assert_eq!(format_value(&val, &no_units()), "[1, 2, 3]");
    }

    #[test]
    fn format_set() {
        let mut s = BTreeSet::new();
        s.insert(Value::Int(1));
        s.insert(Value::Int(2));
        assert_eq!(format_value(&Value::Set(s), &no_units()), "{1, 2}");
    }

    #[test]
    fn format_map() {
        let mut m = BTreeMap::new();
        m.insert(Value::Str("a".into()), Value::Int(1));
        m.insert(Value::Str("b".into()), Value::Int(2));
        assert_eq!(
            format_value(&Value::Map(m), &no_units()),
            "{\"a\": 1, \"b\": 2}"
        );
    }

    #[test]
    fn format_struct() {
        let mut fields = BTreeMap::new();
        fields.insert("x".into(), Value::Int(10));
        fields.insert("y".into(), Value::Int(20));
        let val = Value::Struct {
            name: "Point".into(),
            fields,
        };
        assert_eq!(format_value(&val, &no_units()), "Point { x: 10, y: 20 }");
    }

    #[test]
    fn format_enum_variant_no_fields() {
        let val = Value::EnumVariant {
            enum_name: "Color".into(),
            variant: "red".into(),
            fields: BTreeMap::new(),
        };
        assert_eq!(format_value(&val, &no_units()), "Color.red");
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
        assert_eq!(
            format_value(&val, &no_units()),
            "Duration.rounds(value: 3)"
        );
    }

    #[test]
    fn format_entity() {
        assert_eq!(
            format_value(&Value::Entity(EntityRef(42)), &no_units()),
            "Entity(42)"
        );
    }

    #[test]
    fn format_dice_expr_simple() {
        let val = Value::DiceExpr(DiceExpr::single(2, 6, None, 3));
        assert_eq!(format_value(&val, &no_units()), "2d6 + 3");
    }

    #[test]
    fn format_dice_expr_negative_modifier() {
        let val = Value::DiceExpr(DiceExpr::single(1, 20, None, -2));
        assert_eq!(format_value(&val, &no_units()), "1d20 - 2");
    }

    #[test]
    fn format_dice_expr_no_modifier() {
        let val = Value::DiceExpr(DiceExpr::single(4, 6, Some(DiceFilter::KeepHighest(3)), 0));
        assert_eq!(format_value(&val, &no_units()), "4d6kh3");
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
        assert_eq!(
            format_value(&val, &no_units()),
            "RollResult { dice: [3, 5], total: 8 }"
        );
    }

    // ── Regression: tdsl-t3c — format_value should escape strings ──

    #[test]
    fn format_str_with_embedded_quote() {
        let val = Value::Str("a\"b".into());
        let formatted = format_value(&val, &no_units());
        assert!(
            !formatted.contains("a\"b\"") || formatted.matches('"').count() == 2,
            "embedded quote should be escaped; got: {}",
            formatted,
        );
        assert_eq!(
            formatted.matches('"').count() - formatted.matches("\\\"").count(),
            2,
            "should have exactly 2 unescaped quotes (open/close); got: {}",
            formatted,
        );
    }

    #[test]
    fn format_str_with_backslash() {
        let val = Value::Str("a\\b".into());
        let formatted = format_value(&val, &no_units());
        assert!(
            formatted.contains("\\\\"),
            "backslash should be escaped; got: {}",
            formatted,
        );
    }

    // ── Regression: tdsl-tsn2 — i64::MIN modifier must not panic ──

    #[test]
    fn format_dice_expr_i64_min_modifier() {
        let expr = DiceExpr::single(1, 20, None, i64::MIN);
        let result = format_dice_expr(&expr);
        assert!(
            result.contains(" - 9223372036854775808"),
            "i64::MIN modifier should format without panic; got: {}",
            result,
        );
    }

    #[test]
    fn format_str_with_newline() {
        let val = Value::Str("line1\nline2".into());
        let formatted = format_value(&val, &no_units());
        assert!(
            !formatted.contains('\n') || formatted.contains("\\n"),
            "newline should be escaped; got: {:?}",
            formatted,
        );
    }

    // ── Unit suffix formatting ──

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
        assert_eq!(format_value(&val, &units), "30ft");
    }

    #[test]
    fn format_unit_without_suffix_falls_back() {
        let mut fields = BTreeMap::new();
        fields.insert("value".into(), Value::Int(30));
        let val = Value::Struct {
            name: "Feet".into(),
            fields,
        };
        // No unit suffixes registered — falls back to struct format
        assert_eq!(format_value(&val, &no_units()), "Feet { value: 30 }");
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
        assert_eq!(format_value(&val, &units), "[10ft]");
    }
}
