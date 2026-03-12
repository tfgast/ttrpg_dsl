use std::collections::{HashMap, HashSet};

use rustc_hash::FxHashMap;
use ttrpg_ast::DiceFilter;
use ttrpg_ast::Name;
use ttrpg_checker::env::{ConditionInfo, DeclInfo, EventInfo, FnInfo, FnKind, ParamInfo, TypeEnv};
use ttrpg_checker::ty::Ty;
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
        Value::Float(f) => format!("{f}"),
        Value::Bool(b) => b.to_string(),
        Value::Str(s) => {
            let escaped = s
                .replace('\\', "\\\\")
                .replace('"', "\\\"")
                .replace('\n', "\\n")
                .replace('\r', "\\r")
                .replace('\t', "\\t");
            format!("\"{escaped}\"")
        }
        Value::Void => "none".into(),

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
                .map(|(k, v)| format!("{}: {}", format_value(k, units), format_value(v, units)))
                .collect();
            format!("{{{}}}", inner.join(", "))
        }

        Value::Struct { name, fields } => {
            // Unit types with a suffix: display as e.g. "30ft" instead of "Feet { value: 30 }"
            if let Some(suffix) = units.get(name)
                && fields.len() == 1
            {
                let val = fields.values().next().unwrap();
                return format!("{}{}", format_value(val, units), suffix);
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
                format!("{enum_name}.{variant}")
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

        Value::Position(pv) => format!("Position(#{})", pv.0),
        Value::Direction(dv) => format!("Direction(#{})", dv.0),

        Value::Condition { name, args } => {
            if args.is_empty() {
                format!("Condition({name})")
            } else {
                let inner: Vec<String> = args
                    .iter()
                    .map(|(k, v)| format!("{}: {}", k, format_value(v, units)))
                    .collect();
                format!("Condition({}({}))", name, inner.join(", "))
            }
        }
        Value::FnRef(name) => format!("<fn {name}>"),
        Value::EnumNamespace(name) => format!("<enum {name}>"),
        Value::ModuleAlias(name) => format!("<module alias {name}>"),
        Value::Invocation(id) => format!("Invocation({})", id.0),
    }
}

/// Returns true if a declaration named `name` is owned by the system `filter`,
/// according to the given owner map.
fn owned_by(name: &Name, owner_map: &FxHashMap<Name, Name>, filter: &str) -> bool {
    owner_map
        .get(name)
        .is_some_and(|sys| sys.as_str() == filter)
}

/// Format a single parameter including `with` group constraints.
fn format_param(p: &ParamInfo) -> String {
    let base = format!("{}: {}", p.name, p.ty.display());
    if p.with_groups.is_empty() {
        base
    } else {
        let sep = if p.with_disjunctive { " | " } else { ", " };
        let groups: Vec<&str> = p.with_groups.iter().map(|n| n.as_str()).collect();
        format!("{} with {}", base, groups.join(sep))
    }
}

/// Format sorted tags as ` #tag1 #tag2` (with leading space), or empty string.
fn format_tags(tags: &HashSet<Name>) -> String {
    if tags.is_empty() {
        String::new()
    } else {
        let mut sorted: Vec<&str> = tags.iter().map(|n| n.as_str()).collect();
        sorted.sort_unstable();
        let tag_str = sorted
            .iter()
            .map(|t| format!("#{t}"))
            .collect::<Vec<_>>()
            .join(" ");
        format!(" {tag_str}")
    }
}

/// Format all type declarations from a TypeEnv for human-readable output.
///
/// Returns one line per output row (header + indented fields/variants/groups).
/// Used by both `ttrpg query types` and the REPL `types` command.
pub fn format_types(env: &TypeEnv) -> Vec<String> {
    format_types_filtered(env, None)
}

/// Format type declarations, optionally filtered by owning system name.
pub fn format_types_filtered(env: &TypeEnv, system: Option<&str>) -> Vec<String> {
    let mut sorted: Vec<_> = env
        .types
        .iter()
        .filter(|(name, _)| match system {
            Some(s) => owned_by(name, &env.type_owner, s),
            None => true,
        })
        .collect();
    sorted.sort_by_key(|(name, _)| *name);

    let mut out = Vec::new();
    for (name, decl) in &sorted {
        match decl {
            DeclInfo::Entity(info) => {
                out.push(format!("entity {name} {{"));
                for fi in &info.fields {
                    out.push(format!("  {}: {}", fi.name, fi.ty.display()));
                }
                for group in &info.optional_groups {
                    let kw = if group.required {
                        "include"
                    } else {
                        "optional"
                    };
                    out.push(format!("  {kw} {} {{", group.name));
                    for fi in &group.fields {
                        out.push(format!("    {}: {}", fi.name, fi.ty.display()));
                    }
                    out.push("  }".to_string());
                }
                out.push("}".to_string());
            }
            DeclInfo::Struct(info) => {
                out.push(format!("struct {name} {{"));
                for fi in &info.fields {
                    out.push(format!("  {}: {}", fi.name, fi.ty.display()));
                }
                out.push("}".to_string());
            }
            DeclInfo::Enum(info) => {
                let ordered = if info.ordered { " ordered" } else { "" };
                out.push(format!("enum {name}{ordered} {{"));
                for variant in &info.variants {
                    if variant.fields.is_empty() {
                        out.push(format!("  {}", variant.name));
                    } else {
                        let fields: Vec<String> = variant
                            .fields
                            .iter()
                            .map(|(n, t)| format!("{}: {}", n, t.display()))
                            .collect();
                        out.push(format!("  {}({})", variant.name, fields.join(", ")));
                    }
                }
                out.push("}".to_string());
            }
            DeclInfo::Unit(info) => {
                let suffix_str = match &info.suffix {
                    Some(s) => format!(" suffix {s}"),
                    None => String::new(),
                };
                out.push(format!("unit {name}{suffix_str} {{"));
                for fi in &info.fields {
                    out.push(format!("  {}: {}", fi.name, fi.ty.display()));
                }
                out.push("}".to_string());
            }
        }
    }
    out
}

/// Format a single entity declaration from a TypeEnv for human-readable output.
///
/// Returns `Ok(lines)` on success, or `Err(message)` if the name is not found
/// or does not refer to an entity.
pub fn format_entity(env: &TypeEnv, name: &str, xref: bool) -> Result<Vec<String>, String> {
    match env.types.get(name) {
        Some(DeclInfo::Entity(info)) => {
            let mut out = Vec::new();
            out.push(format!("entity {} {{", info.name));
            for fi in &info.fields {
                let default_marker = if fi.has_default { " (default)" } else { "" };
                out.push(format!(
                    "  {}: {}{}",
                    fi.name,
                    fi.ty.display(),
                    default_marker
                ));
            }
            for group in &info.optional_groups {
                let kw = if group.required {
                    "include"
                } else {
                    "optional"
                };
                out.push(format!("  {kw} {} {{", group.name));
                for fi in &group.fields {
                    let default_marker = if fi.has_default { " (default)" } else { "" };
                    out.push(format!(
                        "    {}: {}{}",
                        fi.name,
                        fi.ty.display(),
                        default_marker
                    ));
                }
                out.push("  }".to_string());
            }
            out.push("}".to_string());

            if xref {
                let receiver_matches = |ty: &Ty| {
                    matches!(ty, Ty::Entity(n) if n == name) || matches!(ty, Ty::AnyEntity)
                };

                // Applicable conditions
                let mut conds: Vec<_> = env
                    .conditions
                    .values()
                    .filter(|ci| receiver_matches(&ci.receiver_type))
                    .collect();
                if !conds.is_empty() {
                    conds.sort_by(|a, b| a.name.cmp(&b.name));
                    out.push(String::new());
                    out.push("// applicable conditions".to_string());
                    for ci in conds {
                        out.push(format_condition_signature(ci));
                    }
                }

                // Available functions (actions, reactions, hooks) by receiver type
                let recv_fns: Vec<_> = env
                    .functions
                    .values()
                    .filter(|fi| {
                        matches!(fi.kind, FnKind::Action | FnKind::Reaction | FnKind::Hook)
                            && fi
                                .receiver
                                .as_ref()
                                .is_some_and(|r| receiver_matches(&r.ty))
                    })
                    .collect();

                for (label, kind) in [
                    ("actions", FnKind::Action),
                    ("reactions", FnKind::Reaction),
                    ("hooks", FnKind::Hook),
                ] {
                    let mut fns: Vec<_> = recv_fns.iter().filter(|fi| fi.kind == kind).collect();
                    if !fns.is_empty() {
                        fns.sort_by(|a, b| a.name.cmp(&b.name));
                        out.push(String::new());
                        out.push(format!("// {label}"));
                        for fi in fns {
                            out.push(format_fn_signature(fi));
                        }
                    }
                }
            }

            Ok(out)
        }
        Some(_) => Err(format!("'{name}' is not an entity")),
        None => Err(format!("unknown type: '{name}'")),
    }
}

/// Format a single function signature aligned with DSL declaration syntax.
pub fn format_fn_signature(fi: &FnInfo) -> String {
    match fi.kind {
        FnKind::Action => {
            let recv = fi.receiver.as_ref().expect("action must have receiver");
            let on_part = format!(" on {}", format_param(recv));
            let params: Vec<String> = fi.params.iter().map(format_param).collect();
            let params_str = if params.is_empty() {
                String::new()
            } else {
                format!("({})", params.join(", "))
            };
            let tags = format_tags(&fi.tags);
            format!("action {}{}{}{}", fi.name, on_part, params_str, tags)
        }
        FnKind::Reaction => {
            let recv = fi.receiver.as_ref().expect("reaction must have receiver");
            let trigger_part = fi
                .trigger
                .as_ref()
                .map(|t| format!(" (trigger: {})", t.event_name))
                .unwrap_or_default();
            format!(
                "reaction {} on {}{}",
                fi.name,
                format_param(recv),
                trigger_part
            )
        }
        FnKind::Hook => {
            let recv = fi.receiver.as_ref().expect("hook must have receiver");
            let trigger_part = fi
                .trigger
                .as_ref()
                .map(|t| format!(" (trigger: {})", t.event_name))
                .unwrap_or_default();
            format!("hook {} on {}{}", fi.name, format_param(recv), trigger_part)
        }
        FnKind::Function => {
            let params: Vec<String> = fi.params.iter().map(format_param).collect();
            let tags = format_tags(&fi.tags);
            format!(
                "function {}({}) -> {}{}",
                fi.name,
                params.join(", "),
                fi.return_type.display(),
                tags,
            )
        }
        FnKind::Derive => {
            let params: Vec<String> = fi.params.iter().map(format_param).collect();
            let tags = format_tags(&fi.tags);
            format!(
                "derive {}({}) -> {}{}",
                fi.name,
                params.join(", "),
                fi.return_type.display(),
                tags,
            )
        }
        FnKind::Mechanic => {
            let params: Vec<String> = fi.params.iter().map(format_param).collect();
            let tags = format_tags(&fi.tags);
            format!(
                "mechanic {}({}) -> {}{}",
                fi.name,
                params.join(", "),
                fi.return_type.display(),
                tags,
            )
        }
        FnKind::Prompt => {
            let params: Vec<String> = fi.params.iter().map(format_param).collect();
            format!(
                "prompt {}({}) -> {}",
                fi.name,
                params.join(", "),
                fi.return_type.display(),
            )
        }
        FnKind::Table | FnKind::Builtin => {
            let kind_label = match fi.kind {
                FnKind::Table => "table",
                FnKind::Builtin => "builtin",
                _ => unreachable!(),
            };
            let params: Vec<String> = fi.params.iter().map(format_param).collect();
            format!(
                "{} {}({}) -> {}",
                kind_label,
                fi.name,
                params.join(", "),
                fi.return_type.display(),
            )
        }
    }
}

/// Format all action declarations from a TypeEnv for human-readable output.
pub fn format_actions(env: &TypeEnv) -> Vec<String> {
    format_actions_filtered(env, None)
}

/// Format action declarations, optionally filtered by owning system name.
pub fn format_actions_filtered(env: &TypeEnv, system: Option<&str>) -> Vec<String> {
    format_fns_by_kind(env, &[FnKind::Action], system)
}

/// Format all mechanic and derive declarations from a TypeEnv for human-readable output.
pub fn format_mechanics(env: &TypeEnv) -> Vec<String> {
    format_mechanics_filtered(env, None)
}

/// Format mechanic and derive declarations, optionally filtered by owning system name.
pub fn format_mechanics_filtered(env: &TypeEnv, system: Option<&str>) -> Vec<String> {
    format_fns_by_kind(env, &[FnKind::Mechanic, FnKind::Derive], system)
}

/// Format all function block declarations from a TypeEnv for human-readable output.
pub fn format_functions(env: &TypeEnv) -> Vec<String> {
    format_functions_filtered(env, None)
}

/// Format function block declarations, optionally filtered by owning system name.
pub fn format_functions_filtered(env: &TypeEnv, system: Option<&str>) -> Vec<String> {
    format_fns_by_kind(env, &[FnKind::Function], system)
}

/// Format all reaction declarations from a TypeEnv for human-readable output.
pub fn format_reactions(env: &TypeEnv) -> Vec<String> {
    format_reactions_filtered(env, None)
}

/// Format reaction declarations, optionally filtered by owning system name.
pub fn format_reactions_filtered(env: &TypeEnv, system: Option<&str>) -> Vec<String> {
    format_fns_by_kind(env, &[FnKind::Reaction], system)
}

/// Format all hook declarations from a TypeEnv for human-readable output.
pub fn format_hooks(env: &TypeEnv) -> Vec<String> {
    format_hooks_filtered(env, None)
}

/// Format hook declarations, optionally filtered by owning system name.
pub fn format_hooks_filtered(env: &TypeEnv, system: Option<&str>) -> Vec<String> {
    format_fns_by_kind(env, &[FnKind::Hook], system)
}

/// Shared helper: format functions matching any of the given kinds, with optional system filter.
fn format_fns_by_kind(env: &TypeEnv, kinds: &[FnKind], system: Option<&str>) -> Vec<String> {
    let mut fns: Vec<_> = env
        .functions
        .values()
        .filter(|fi| kinds.contains(&fi.kind))
        .filter(|fi| match system {
            Some(s) => owned_by(&fi.name, &env.function_owner, s),
            None => true,
        })
        .collect();
    fns.sort_by(|a, b| a.name.cmp(&b.name));
    fns.iter().map(|fi| format_fn_signature(fi)).collect()
}

/// Format all event declarations from a TypeEnv for human-readable output.
pub fn format_events(env: &TypeEnv) -> Vec<String> {
    format_events_filtered(env, None)
}

/// Format event declarations, optionally filtered by owning system name.
pub fn format_events_filtered(env: &TypeEnv, system: Option<&str>) -> Vec<String> {
    let mut events: Vec<_> = env
        .events
        .values()
        .filter(|ei| match system {
            Some(s) => owned_by(&ei.name, &env.event_owner, s),
            None => true,
        })
        .collect();
    events.sort_by(|a, b| a.name.cmp(&b.name));
    events.iter().map(|ei| format_event_signature(ei)).collect()
}

/// Format a single event signature as `event Name(params) { fields }`.
fn format_event_signature(ei: &EventInfo) -> String {
    let params: Vec<String> = ei.params.iter().map(format_param).collect();
    let fields: Vec<String> = ei
        .fields
        .iter()
        .map(|(name, ty)| format!("{}: {}", name, ty.display()))
        .collect();

    if fields.is_empty() {
        format!("event {}({})", ei.name, params.join(", "))
    } else {
        format!(
            "event {}({}) {{ {} }}",
            ei.name,
            params.join(", "),
            fields.join(", ")
        )
    }
}

/// Format all condition declarations from a TypeEnv for human-readable output.
pub fn format_condition_decls(env: &TypeEnv) -> Vec<String> {
    format_condition_decls_filtered(env, None)
}

/// Format condition declarations, optionally filtered by owning system name.
pub fn format_condition_decls_filtered(env: &TypeEnv, system: Option<&str>) -> Vec<String> {
    let mut conds: Vec<_> = env
        .conditions
        .values()
        .filter(|ci| match system {
            Some(s) => owned_by(&ci.name, &env.condition_owner, s),
            None => true,
        })
        .collect();
    conds.sort_by(|a, b| a.name.cmp(&b.name));
    conds
        .iter()
        .map(|ci| format_condition_signature(ci))
        .collect()
}

/// Format a single condition signature as `condition Name(params) extends Parent on bearer: Type`.
fn format_condition_signature(ci: &ConditionInfo) -> String {
    let params: Vec<String> = ci.params.iter().map(format_param).collect();
    let params_str = if params.is_empty() {
        String::new()
    } else {
        format!("({})", params.join(", "))
    };
    format!(
        "condition {}{} on {}: {}",
        ci.name,
        params_str,
        ci.receiver_name,
        ci.receiver_type.display(),
    )
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
                DiceFilter::KeepHighest(n) => gs.push_str(&format!("kh{n}")),
                DiceFilter::KeepLowest(n) => gs.push_str(&format!("kl{n}")),
                DiceFilter::DropHighest(n) => gs.push_str(&format!("dh{n}")),
                DiceFilter::DropLowest(n) => gs.push_str(&format!("dl{n}")),
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
    use ttrpg_checker::env::{
        EntityInfo, EnumInfo, FieldInfo, OptionalGroupInfo, StructInfo, TriggerInfo, UnitInfo,
        VariantInfo,
    };
    use ttrpg_checker::ty::Ty;
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
        assert_eq!(format_value(&Value::Void, &no_units()), "none");
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
            variant: "Rounds".into(),
            fields,
        };
        assert_eq!(format_value(&val, &no_units()), "Duration.Rounds(value: 3)");
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
            "embedded quote should be escaped; got: {formatted}",
        );
        assert_eq!(
            formatted.matches('"').count() - formatted.matches("\\\"").count(),
            2,
            "should have exactly 2 unescaped quotes (open/close); got: {formatted}",
        );
    }

    #[test]
    fn format_str_with_backslash() {
        let val = Value::Str("a\\b".into());
        let formatted = format_value(&val, &no_units());
        assert!(
            formatted.contains("\\\\"),
            "backslash should be escaped; got: {formatted}",
        );
    }

    // ── Regression: tdsl-tsn2 — i64::MIN modifier must not panic ──

    #[test]
    fn format_dice_expr_i64_min_modifier() {
        let expr = DiceExpr::single(1, 20, None, i64::MIN);
        let result = format_dice_expr(&expr);
        assert!(
            result.contains(" - 9223372036854775808"),
            "i64::MIN modifier should format without panic; got: {result}",
        );
    }

    #[test]
    fn format_str_with_newline() {
        let val = Value::Str("line1\nline2".into());
        let formatted = format_value(&val, &no_units());
        assert!(
            !formatted.contains('\n') || formatted.contains("\\n"),
            "newline should be escaped; got: {formatted:?}",
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

    // ══════════════════════════════════════════════════════════
    // Declaration formatting (insta snapshots)
    // ══════════════════════════════════════════════════════════

    fn mk_param(name: &str, ty: Ty) -> ParamInfo {
        ParamInfo {
            name: name.into(),
            ty,
            has_default: false,
            with_groups: vec![],
            with_disjunctive: false,
        }
    }

    fn mk_param_with(name: &str, ty: Ty, groups: &[&str], disjunctive: bool) -> ParamInfo {
        ParamInfo {
            name: name.into(),
            ty,
            has_default: false,
            with_groups: groups.iter().map(|&g| g.into()).collect(),
            with_disjunctive: disjunctive,
        }
    }

    fn mk_fn(
        name: &str,
        kind: FnKind,
        receiver: Option<ParamInfo>,
        params: Vec<ParamInfo>,
        return_type: Ty,
        tags: &[&str],
    ) -> FnInfo {
        FnInfo {
            name: name.into(),
            kind,
            params,
            return_type,
            receiver,
            tags: tags.iter().map(|&t| t.into()).collect(),
            synthetic: false,
            trigger: None,
        }
    }

    fn mk_field(name: &str, ty: Ty) -> FieldInfo {
        FieldInfo {
            name: name.into(),
            ty,
            has_default: false,
            restricted: false,
        }
    }

    fn mk_field_default(name: &str, ty: Ty) -> FieldInfo {
        FieldInfo {
            name: name.into(),
            ty,
            has_default: true,
            restricted: false,
        }
    }

    // ── Function signatures ──

    #[test]
    fn sig_derive_basic() {
        let fi = mk_fn(
            "modifier",
            FnKind::Derive,
            None,
            vec![mk_param("score", Ty::Int)],
            Ty::Int,
            &[],
        );
        insta::assert_snapshot!(format_fn_signature(&fi));
    }

    #[test]
    fn sig_mechanic_with_tags() {
        let fi = mk_fn(
            "attack_roll",
            FnKind::Mechanic,
            None,
            vec![
                mk_param("attacker", Ty::Entity("Character".into())),
                mk_param("target", Ty::Entity("Character".into())),
            ],
            Ty::RollResult,
            &["attack"],
        );
        insta::assert_snapshot!(format_fn_signature(&fi));
    }

    #[test]
    fn sig_action_with_params() {
        let fi = mk_fn(
            "Attack",
            FnKind::Action,
            Some(mk_param("attacker", Ty::Entity("Character".into()))),
            vec![mk_param("target", Ty::Entity("Character".into()))],
            Ty::Unit,
            &[],
        );
        insta::assert_snapshot!(format_fn_signature(&fi));
    }

    #[test]
    fn sig_action_with_receiver_groups() {
        let fi = mk_fn(
            "CastSpell",
            FnKind::Action,
            Some(mk_param_with(
                "caster",
                Ty::Entity("Character".into()),
                &["Spellcasting"],
                false,
            )),
            vec![mk_param("target", Ty::Entity("Character".into()))],
            Ty::Unit,
            &[],
        );
        insta::assert_snapshot!(format_fn_signature(&fi));
    }

    #[test]
    fn sig_reaction() {
        let fi = mk_fn(
            "OpportunityAttack",
            FnKind::Reaction,
            Some(mk_param("reactor", Ty::Entity("Character".into()))),
            vec![],
            Ty::Unit,
            &[],
        );
        insta::assert_snapshot!(format_fn_signature(&fi));
    }

    #[test]
    fn sig_hook() {
        let fi = mk_fn(
            "DeathCheck",
            FnKind::Hook,
            Some(mk_param("actor", Ty::Entity("Character".into()))),
            vec![],
            Ty::Unit,
            &[],
        );
        insta::assert_snapshot!(format_fn_signature(&fi));
    }

    #[test]
    fn sig_reaction_with_trigger() {
        let mut fi = mk_fn(
            "OpportunityAttack",
            FnKind::Reaction,
            Some(mk_param("reactor", Ty::Entity("Character".into()))),
            vec![],
            Ty::Unit,
            &[],
        );
        fi.trigger = Some(TriggerInfo {
            event_name: "entity_leaves_reach".into(),
        });
        insta::assert_snapshot!(format_fn_signature(&fi));
    }

    #[test]
    fn sig_hook_with_trigger() {
        let mut fi = mk_fn(
            "DeathCheck",
            FnKind::Hook,
            Some(mk_param("actor", Ty::Entity("Character".into()))),
            vec![],
            Ty::Unit,
            &[],
        );
        fi.trigger = Some(TriggerInfo {
            event_name: "Damaged".into(),
        });
        insta::assert_snapshot!(format_fn_signature(&fi));
    }

    #[test]
    fn sig_prompt() {
        let fi = mk_fn(
            "choose",
            FnKind::Prompt,
            None,
            vec![
                mk_param("chooser", Ty::Entity("Character".into())),
                mk_param("options", Ty::List(Box::new(Ty::String))),
            ],
            Ty::String,
            &[],
        );
        insta::assert_snapshot!(format_fn_signature(&fi));
    }

    #[test]
    fn sig_derive_with_conjunctive() {
        let fi = mk_fn(
            "spell_dc",
            FnKind::Derive,
            None,
            vec![mk_param_with(
                "caster",
                Ty::Entity("Character".into()),
                &["Spellcasting"],
                false,
            )],
            Ty::Int,
            &[],
        );
        insta::assert_snapshot!(format_fn_signature(&fi));
    }

    #[test]
    fn sig_derive_with_disjunctive() {
        let fi = mk_fn(
            "foo",
            FnKind::Derive,
            None,
            vec![mk_param_with("x", Ty::AnyEntity, &["A", "B"], true)],
            Ty::Int,
            &[],
        );
        insta::assert_snapshot!(format_fn_signature(&fi));
    }

    // ── Condition signatures ──

    #[test]
    fn sig_condition_simple() {
        let ci = ConditionInfo {
            name: "Prone".into(),
            params: vec![],
            receiver_name: "bearer".into(),
            receiver_type: Ty::Entity("Character".into()),
            tags: HashSet::new(),
            state_fields: vec![],
        };
        insta::assert_snapshot!(format_condition_signature(&ci));
    }

    #[test]
    fn sig_condition_no_params() {
        let ci = ConditionInfo {
            name: "Paralyzed".into(),
            params: vec![],
            receiver_name: "bearer".into(),
            receiver_type: Ty::Entity("Character".into()),
            tags: HashSet::new(),
            state_fields: vec![],
        };
        insta::assert_snapshot!(format_condition_signature(&ci));
    }

    #[test]
    fn sig_condition_with_params() {
        let ci = ConditionInfo {
            name: "Frightened".into(),
            params: vec![mk_param("source", Ty::Entity("Character".into()))],
            receiver_name: "bearer".into(),
            receiver_type: Ty::Entity("Character".into()),
            tags: HashSet::new(),
            state_fields: vec![],
        };
        insta::assert_snapshot!(format_condition_signature(&ci));
    }

    // ── Event signatures ──

    #[test]
    fn sig_event_with_fields() {
        let ei = EventInfo {
            name: "Damaged".into(),
            params: vec![
                mk_param("target", Ty::Entity("Character".into())),
                mk_param("amount", Ty::Int),
            ],
            fields: vec![("total_hp".into(), Ty::Int)],
            builtin: false,
        };
        insta::assert_snapshot!(format_event_signature(&ei));
    }

    #[test]
    fn sig_event_without_fields() {
        let ei = EventInfo {
            name: "TurnStart".into(),
            params: vec![mk_param("actor", Ty::Entity("Character".into()))],
            fields: vec![],
            builtin: false,
        };
        insta::assert_snapshot!(format_event_signature(&ei));
    }

    // ── Type formatting ──

    #[test]
    fn type_entity_with_groups() {
        let mut env = TypeEnv::new();
        env.types.insert(
            "Character".into(),
            DeclInfo::Entity(EntityInfo {
                name: "Character".into(),
                fields: vec![mk_field("name", Ty::String), mk_field("level", Ty::Int)],
                optional_groups: vec![OptionalGroupInfo {
                    name: "Spellcasting".into(),
                    fields: vec![mk_field("spell_slots", Ty::Int)],
                    required: false,
                }],
            }),
        );
        let lines = format_types(&env);
        insta::assert_snapshot!(lines.join("\n"));
    }

    #[test]
    fn type_struct_braces() {
        let mut env = TypeEnv::new();
        env.types.insert(
            "Point".into(),
            DeclInfo::Struct(StructInfo {
                name: "Point".into(),
                fields: vec![mk_field("x", Ty::Int), mk_field("y", Ty::Int)],
            }),
        );
        let lines = format_types(&env);
        insta::assert_snapshot!(lines.join("\n"));
    }

    #[test]
    fn type_enum_basic() {
        let mut env = TypeEnv::new();
        env.types.insert(
            "Color".into(),
            DeclInfo::Enum(EnumInfo {
                name: "Color".into(),
                ordered: false,
                variants: vec![
                    VariantInfo {
                        name: "red".into(),
                        fields: vec![],
                        has_defaults: vec![],
                    },
                    VariantInfo {
                        name: "green".into(),
                        fields: vec![],
                        has_defaults: vec![],
                    },
                    VariantInfo {
                        name: "blue".into(),
                        fields: vec![],
                        has_defaults: vec![],
                    },
                ],
            }),
        );
        let lines = format_types(&env);
        insta::assert_snapshot!(lines.join("\n"));
    }

    #[test]
    fn type_enum_ordered() {
        let mut env = TypeEnv::new();
        env.types.insert(
            "Size".into(),
            DeclInfo::Enum(EnumInfo {
                name: "Size".into(),
                ordered: true,
                variants: vec![
                    VariantInfo {
                        name: "small".into(),
                        fields: vec![],
                        has_defaults: vec![],
                    },
                    VariantInfo {
                        name: "medium".into(),
                        fields: vec![],
                        has_defaults: vec![],
                    },
                    VariantInfo {
                        name: "large".into(),
                        fields: vec![],
                        has_defaults: vec![],
                    },
                ],
            }),
        );
        let lines = format_types(&env);
        insta::assert_snapshot!(lines.join("\n"));
    }

    #[test]
    fn type_unit_suffix() {
        let mut env = TypeEnv::new();
        env.types.insert(
            "Feet".into(),
            DeclInfo::Unit(UnitInfo {
                name: "Feet".into(),
                fields: vec![mk_field("value", Ty::Int)],
                suffix: Some("ft".into()),
            }),
        );
        let lines = format_types(&env);
        insta::assert_snapshot!(lines.join("\n"));
    }

    #[test]
    fn entity_detail_with_defaults() {
        let mut env = TypeEnv::new();
        env.types.insert(
            "Character".into(),
            DeclInfo::Entity(EntityInfo {
                name: "Character".into(),
                fields: vec![
                    mk_field("name", Ty::String),
                    mk_field_default("level", Ty::Int),
                ],
                optional_groups: vec![OptionalGroupInfo {
                    name: "Spellcasting".into(),
                    fields: vec![mk_field_default("spell_slots", Ty::Int)],
                    required: false,
                }],
            }),
        );
        // Use super:: to avoid shadowing by the format_entity test function
        let lines = super::format_entity(&env, "Character", false).unwrap();
        insta::assert_snapshot!(lines.join("\n"));
    }
}
