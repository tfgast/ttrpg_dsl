use ttrpg_ast::DiceFilter;
use ttrpg_interp::value::{DiceExpr, Value};

/// Format a runtime Value for human-readable CLI output.
pub fn format_value(val: &Value) -> String {
    match val {
        Value::Int(n) => n.to_string(),
        Value::Float(f) => format!("{}", f),
        Value::Bool(b) => b.to_string(),
        Value::Str(s) => format!("\"{}\"", s),
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
            let inner: Vec<String> = items.iter().map(format_value).collect();
            format!("[{}]", inner.join(", "))
        }

        Value::Set(items) => {
            let inner: Vec<String> = items.iter().map(format_value).collect();
            format!("{{{}}}", inner.join(", "))
        }

        Value::Map(entries) => {
            let inner: Vec<String> = entries
                .iter()
                .map(|(k, v)| format!("{}: {}", format_value(k), format_value(v)))
                .collect();
            format!("{{{}}}", inner.join(", "))
        }

        Value::Struct { name, fields } => {
            let inner: Vec<String> = fields
                .iter()
                .map(|(k, v)| format!("{}: {}", k, format_value(v)))
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
                    .map(|(k, v)| format!("{}: {}", k, format_value(v)))
                    .collect();
                format!("{}.{}({})", enum_name, variant, inner.join(", "))
            }
        }

        Value::Option(opt) => match opt {
            Some(v) => format!("some({})", format_value(v)),
            None => "none".into(),
        },

        Value::Position(_) => "Position(...)".into(),

        Value::Duration(d) => format!("{:?}", d),
        Value::Condition(name) => format!("Condition({})", name),
        Value::EnumNamespace(name) => format!("<enum {}>", name),
    }
}

fn format_dice_expr(expr: &DiceExpr) -> String {
    let mut s = format!("{}d{}", expr.count, expr.sides);
    if let Some(filter) = &expr.filter {
        match filter {
            DiceFilter::KeepHighest(n) => s.push_str(&format!("kh{}", n)),
            DiceFilter::KeepLowest(n) => s.push_str(&format!("kl{}", n)),
            DiceFilter::DropHighest(n) => s.push_str(&format!("dh{}", n)),
            DiceFilter::DropLowest(n) => s.push_str(&format!("dl{}", n)),
        }
    }
    if expr.modifier > 0 {
        s.push_str(&format!(" + {}", expr.modifier));
    } else if expr.modifier < 0 {
        s.push_str(&format!(" - {}", expr.modifier.abs()));
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::{BTreeMap, BTreeSet};
    use ttrpg_interp::state::EntityRef;
    use ttrpg_interp::value::RollResult;

    #[test]
    fn format_int() {
        assert_eq!(format_value(&Value::Int(42)), "42");
    }

    #[test]
    fn format_str() {
        assert_eq!(format_value(&Value::Str("hello".into())), "\"hello\"");
    }

    #[test]
    fn format_bool() {
        assert_eq!(format_value(&Value::Bool(true)), "true");
        assert_eq!(format_value(&Value::Bool(false)), "false");
    }

    #[test]
    fn format_none() {
        assert_eq!(format_value(&Value::None), "none");
    }

    #[test]
    fn format_list() {
        let val = Value::List(vec![Value::Int(1), Value::Int(2), Value::Int(3)]);
        assert_eq!(format_value(&val), "[1, 2, 3]");
    }

    #[test]
    fn format_set() {
        let mut s = BTreeSet::new();
        s.insert(Value::Int(1));
        s.insert(Value::Int(2));
        assert_eq!(format_value(&Value::Set(s)), "{1, 2}");
    }

    #[test]
    fn format_map() {
        let mut m = BTreeMap::new();
        m.insert(Value::Str("a".into()), Value::Int(1));
        m.insert(Value::Str("b".into()), Value::Int(2));
        assert_eq!(format_value(&Value::Map(m)), "{\"a\": 1, \"b\": 2}");
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
        assert_eq!(format_value(&val), "Point { x: 10, y: 20 }");
    }

    #[test]
    fn format_enum_variant_no_fields() {
        let val = Value::EnumVariant {
            enum_name: "Color".into(),
            variant: "red".into(),
            fields: BTreeMap::new(),
        };
        assert_eq!(format_value(&val), "Color.red");
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
        assert_eq!(format_value(&val), "Duration.rounds(value: 3)");
    }

    #[test]
    fn format_entity() {
        assert_eq!(format_value(&Value::Entity(EntityRef(42))), "Entity(42)");
    }

    #[test]
    fn format_dice_expr_simple() {
        let val = Value::DiceExpr(DiceExpr {
            count: 2,
            sides: 6,
            filter: None,
            modifier: 3,
        });
        assert_eq!(format_value(&val), "2d6 + 3");
    }

    #[test]
    fn format_dice_expr_negative_modifier() {
        let val = Value::DiceExpr(DiceExpr {
            count: 1,
            sides: 20,
            filter: None,
            modifier: -2,
        });
        assert_eq!(format_value(&val), "1d20 - 2");
    }

    #[test]
    fn format_dice_expr_no_modifier() {
        let val = Value::DiceExpr(DiceExpr {
            count: 4,
            sides: 6,
            filter: Some(DiceFilter::KeepHighest(3)),
            modifier: 0,
        });
        assert_eq!(format_value(&val), "4d6kh3");
    }

    #[test]
    fn format_roll_result() {
        let val = Value::RollResult(RollResult {
            expr: DiceExpr {
                count: 2,
                sides: 6,
                filter: None,
                modifier: 0,
            },
            dice: vec![3, 5],
            kept: vec![3, 5],
            modifier: 0,
            total: 8,
            unmodified: 8,
        });
        assert_eq!(format_value(&val), "RollResult { dice: [3, 5], total: 8 }");
    }
}
