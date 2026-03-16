use std::collections::BTreeMap;

use ttrpg_ast::Span;
use ttrpg_ast::ast::ExprKind;
use ttrpg_ast::{Name, Spanned};
use ttrpg_checker::env::DeclInfo;

use crate::Env;
use crate::RuntimeError;
use crate::state::StateProvider;
use crate::value::Value;

use super::compare::value_eq;
use super::dispatch::eval_expr;
use super::helpers::type_name;

// ── Field access ───────────────────────────────────────────────

pub(super) fn eval_field_access(
    env: &mut Env,
    object_expr: &Spanned<ExprKind>,
    field: &str,
    expr: &Spanned<ExprKind>,
) -> Result<Value, RuntimeError> {
    let object = eval_expr(env, object_expr)?;

    match &object {
        // Entity fields via StateProvider
        Value::Entity(entity_ref) => {
            // Check for group alias resolution from the checker
            let resolved_field: std::borrow::Cow<str> = if let Some(real_name) =
                env.interp.type_env.resolved_group_aliases.get(&expr.span)
            {
                std::borrow::Cow::Owned(real_name.to_string())
            } else {
                std::borrow::Cow::Borrowed(field)
            };
            if let Some(val) = env.state.read_field(entity_ref, &resolved_field) {
                return Ok(val);
            }
            // Flattened included-group field: look up group, read struct, extract field
            if let Some(entity_type) = env.state.entity_type_name(entity_ref)
                && let Some(group_name) = env
                    .interp
                    .type_env
                    .lookup_flattened_field(&entity_type, field)
                && let Some(Value::Struct {
                    fields: group_fields,
                    ..
                }) = env.state.read_field(entity_ref, group_name)
                && let Some(val) = group_fields.get(field)
            {
                return Ok(val.clone());
            }
            Err(RuntimeError::with_span(
                format!("entity {} has no field '{}'", entity_ref.0, field),
                expr.span,
            ))
        }

        // Struct fields
        Value::Struct { fields, name, .. } => fields.get(field).cloned().ok_or_else(|| {
            RuntimeError::with_span(format!("struct '{name}' has no field '{field}'"), expr.span)
        }),

        // Enum variant fields
        Value::EnumVariant {
            enum_name,
            variant,
            fields,
        } => fields.get(field).cloned().ok_or_else(|| {
            RuntimeError::with_span(
                format!("variant '{enum_name}.{variant}' has no field '{field}'"),
                expr.span,
            )
        }),

        // RollResult built-in fields
        Value::RollResult(r) => match field {
            "total" => Ok(Value::Int(r.total)),
            "unmodified" => Ok(Value::Int(r.unmodified)),
            "modifier" => Ok(Value::Int(r.modifier)),
            "dice" => Ok(Value::List(r.dice.iter().map(|d| Value::Int(*d)).collect())),
            "kept" => Ok(Value::List(r.kept.iter().map(|d| Value::Int(*d)).collect())),
            "expr" => Ok(Value::DiceExpr(r.expr.clone())),
            _ => Err(RuntimeError::with_span(
                format!("RollResult has no field '{field}'"),
                expr.span,
            )),
        },

        // Module alias field access: Alias.Name → resolve in global namespace
        Value::ModuleAlias(alias_name) => {
            // The checker validated that `field` exists in the target system.
            // At runtime, all declarations are in a flat global namespace,
            // so we look up `field` directly.

            // 1. Enum type → produce EnumNamespace for further chaining
            if let Some(DeclInfo::Enum(_)) = env.interp.type_env.types.get(field) {
                return Ok(Value::EnumNamespace(Name::from(field)));
            }

            // 2. Bare enum variant — use checker resolution or system-scoped fallback
            let resolved_variant = env
                .interp
                .type_env
                .resolved_variants
                .get(&expr.span)
                .cloned()
                .or_else(|| {
                    let target = env
                        .interp
                        .type_env
                        .system_aliases
                        .values()
                        .find_map(|aliases| aliases.get(alias_name.as_str()))
                        .cloned();
                    target.and_then(|target_sys| {
                        let owners = env.interp.type_env.variant_to_enums.get(field)?;
                        let matching: Vec<_> = owners
                            .iter()
                            .filter(|e| {
                                env.interp.type_env.type_owner.get(e.as_str()) == Some(&target_sys)
                            })
                            .collect();
                        (matching.len() == 1).then(|| matching[0].clone())
                    })
                });
            if let Some(enum_name) = resolved_variant
                && let Some(DeclInfo::Enum(enum_info)) =
                    env.interp.type_env.types.get(enum_name.as_str())
                && let Some(variant) = enum_info.variants.iter().find(|v| v.name == field)
            {
                if variant.fields.is_empty() {
                    return Ok(Value::EnumVariant {
                        enum_name,
                        variant: Name::from(field),
                        fields: BTreeMap::new(),
                    });
                }
                return Err(RuntimeError::with_span(
                    format!(
                        "variant '{enum_name}.{field}' has fields and must be called as a constructor"
                    ),
                    expr.span,
                ));
            }

            // 3. Condition reference (bare use → materialize defaults)
            if let Some(cond_decl) = env.interp.program.conditions.get(field) {
                let cond_decl = cond_decl.clone();
                let mut args = BTreeMap::new();
                for param in &cond_decl.params {
                    if let Some(ref default_expr) = param.default {
                        let val = eval_expr(env, default_expr)?;
                        args.insert(param.name.clone(), val);
                    }
                }
                return Ok(Value::Condition {
                    name: Name::from(field),
                    args,
                });
            }

            Err(RuntimeError::with_span(
                format!("no type, variant, or condition '{field}' in module alias"),
                expr.span,
            ))
        }

        // Qualified enum variant access: EnumType.variant
        Value::EnumNamespace(enum_name) => {
            if let Some(DeclInfo::Enum(enum_info)) =
                env.interp.type_env.types.get(enum_name.as_str())
                && let Some(variant) = enum_info.variants.iter().find(|v| v.name == field)
            {
                if variant.fields.is_empty() {
                    return Ok(Value::EnumVariant {
                        enum_name: enum_name.clone(),
                        variant: Name::from(field),
                        fields: BTreeMap::new(),
                    });
                }
                return Err(RuntimeError::with_span(
                    format!(
                        "enum variant '{enum_name}.{field}' has fields and must be called as a function"
                    ),
                    expr.span,
                ));
            }
            Err(RuntimeError::with_span(
                format!("enum '{enum_name}' has no variant '{field}'"),
                expr.span,
            ))
        }

        _ => Err(RuntimeError::with_span(
            format!(
                "cannot access field '{}' on {:?}",
                field,
                type_name(&object)
            ),
            expr.span,
        )),
    }
}

// ── Index access ───────────────────────────────────────────────

pub(super) fn eval_index(
    env: &mut Env,
    object_expr: &Spanned<ExprKind>,
    index_expr: &Spanned<ExprKind>,
    expr: &Spanned<ExprKind>,
) -> Result<Value, RuntimeError> {
    let object = eval_expr(env, object_expr)?;
    let index = eval_expr(env, index_expr)?;

    match (&object, &index) {
        (Value::List(items), Value::Int(i)) => {
            let idx = if *i < 0 {
                // Negative indexing from end
                let positive = items.len() as i64 + i;
                if positive < 0 {
                    return Err(RuntimeError::with_span(
                        format!("list index {} out of bounds, length {}", i, items.len()),
                        expr.span,
                    ));
                }
                positive as usize
            } else {
                *i as usize
            };
            items.get(idx).cloned().ok_or_else(|| {
                RuntimeError::with_span(
                    format!("list index {} out of bounds, length {}", i, items.len()),
                    expr.span,
                )
            })
        }
        (Value::Map(map), key) => {
            // Use semantic equality (value_eq) for lookup so that e.g. none
            // and option<T>.none are treated as the same key, consistent with `in`.
            map.iter()
                .find(|(k, _)| value_eq(env.state, k, key))
                .map(|(_, v)| v.clone())
                .ok_or_else(|| {
                    RuntimeError::with_span(format!("map key {key:?} not found"), expr.span)
                })
        }
        _ => Err(RuntimeError::with_span(
            format!(
                "cannot index {:?} with {:?}",
                type_name(&object),
                type_name(&index)
            ),
            expr.span,
        )),
    }
}

// ── Value-level wrappers for ExprEval frame ─────────────────────

/// Field access on an already-evaluated object value.
///
/// Handles Entity, Struct, EnumVariant, RollResult, EnumNamespace,
/// and collection-length fields. Does NOT handle ModuleAlias (requires
/// program access) or Condition (requires eval_expr for defaults).
pub(crate) fn field_access_on_value(
    object: &Value,
    field: &str,
    span: Span,
    type_env: &ttrpg_checker::env::TypeEnv,
    state: &dyn StateProvider,
) -> Result<Value, RuntimeError> {
    match object {
        // Entity fields via StateProvider
        Value::Entity(entity_ref) => {
            // Check for group alias resolution from the checker
            let resolved_field: std::borrow::Cow<str> =
                if let Some(real_name) = type_env.resolved_group_aliases.get(&span) {
                    std::borrow::Cow::Owned(real_name.to_string())
                } else {
                    std::borrow::Cow::Borrowed(field)
                };
            if let Some(val) = state.read_field(entity_ref, &resolved_field) {
                return Ok(val);
            }
            // Flattened included-group field
            if let Some(entity_type) = state.entity_type_name(entity_ref)
                && let Some(group_name) = type_env.lookup_flattened_field(&entity_type, field)
                && let Some(Value::Struct {
                    fields: group_fields,
                    ..
                }) = state.read_field(entity_ref, group_name)
                && let Some(val) = group_fields.get(field)
            {
                return Ok(val.clone());
            }
            Err(RuntimeError::with_span(
                format!("entity {} has no field '{}'", entity_ref.0, field),
                span,
            ))
        }

        // Struct fields
        Value::Struct { fields, name, .. } => fields.get(field).cloned().ok_or_else(|| {
            RuntimeError::with_span(format!("struct '{name}' has no field '{field}'"), span)
        }),

        // Enum variant fields
        Value::EnumVariant {
            enum_name,
            variant,
            fields,
        } => fields.get(field).cloned().ok_or_else(|| {
            RuntimeError::with_span(
                format!("variant '{enum_name}.{variant}' has no field '{field}'"),
                span,
            )
        }),

        // RollResult built-in fields
        Value::RollResult(r) => match field {
            "total" => Ok(Value::Int(r.total)),
            "unmodified" => Ok(Value::Int(r.unmodified)),
            "modifier" => Ok(Value::Int(r.modifier)),
            "dice" => Ok(Value::List(r.dice.iter().map(|d| Value::Int(*d)).collect())),
            "kept" => Ok(Value::List(r.kept.iter().map(|d| Value::Int(*d)).collect())),
            "expr" => Ok(Value::DiceExpr(r.expr.clone())),
            _ => Err(RuntimeError::with_span(
                format!("RollResult has no field '{field}'"),
                span,
            )),
        },

        // Qualified enum variant access: EnumType.variant
        Value::EnumNamespace(enum_name) => {
            if let Some(DeclInfo::Enum(enum_info)) = type_env.types.get(enum_name.as_str())
                && let Some(variant) = enum_info.variants.iter().find(|v| v.name == field)
            {
                if variant.fields.is_empty() {
                    return Ok(Value::EnumVariant {
                        enum_name: enum_name.clone(),
                        variant: Name::from(field),
                        fields: BTreeMap::new(),
                    });
                }
                return Err(RuntimeError::with_span(
                    format!(
                        "enum variant '{enum_name}.{field}' has fields and must be called as a function"
                    ),
                    span,
                ));
            }
            Err(RuntimeError::with_span(
                format!("enum '{enum_name}' has no variant '{field}'"),
                span,
            ))
        }

        // Option built-in fields
        Value::Option(inner) => match field {
            "is_some" => Ok(Value::Bool(inner.is_some())),
            "is_none" => Ok(Value::Bool(inner.is_none())),
            "value" => match inner {
                Some(v) => Ok(v.as_ref().clone()),
                None => Err(RuntimeError::with_span(
                    "cannot access .value on none",
                    span,
                )),
            },
            _ => Err(RuntimeError::with_span(
                format!("option has no field '{field}'"),
                span,
            )),
        },

        // Condition name field
        Value::Condition { name, args } => match field {
            "name" => Ok(Value::Str(name.to_string())),
            _ => args.get(field).cloned().ok_or_else(|| {
                RuntimeError::with_span(
                    format!("condition '{name}' has no field '{field}'"),
                    span,
                )
            }),
        },

        // Collection length fields
        Value::List(items) => match field {
            "length" => Ok(Value::Int(items.len() as i64)),
            _ => Err(RuntimeError::with_span(
                format!("list has no field '{field}'"),
                span,
            )),
        },
        Value::Map(map) => match field {
            "length" => Ok(Value::Int(map.len() as i64)),
            _ => Err(RuntimeError::with_span(
                format!("map has no field '{field}'"),
                span,
            )),
        },
        Value::Set(set) => match field {
            "length" => Ok(Value::Int(set.len() as i64)),
            _ => Err(RuntimeError::with_span(
                format!("set has no field '{field}'"),
                span,
            )),
        },

        // DiceExpr built-in fields
        Value::DiceExpr(d) => match field {
            "modifier" => Ok(Value::Int(d.modifier)),
            _ => Err(RuntimeError::with_span(
                format!("DiceExpr has no field '{field}'"),
                span,
            )),
        },

        _ => Err(RuntimeError::with_span(
            format!("cannot access field '{}' on {:?}", field, type_name(object)),
            span,
        )),
    }
}

/// Index access on already-evaluated object and index values.
pub(crate) fn index_on_value(
    object: &Value,
    index: &Value,
    span: Span,
    state: &dyn StateProvider,
) -> Result<Value, RuntimeError> {
    match (object, index) {
        (Value::List(items), Value::Int(i)) => {
            let idx = if *i < 0 {
                let positive = items.len() as i64 + i;
                if positive < 0 {
                    return Err(RuntimeError::with_span(
                        format!("list index {} out of bounds, length {}", i, items.len()),
                        span,
                    ));
                }
                positive as usize
            } else {
                *i as usize
            };
            items.get(idx).cloned().ok_or_else(|| {
                RuntimeError::with_span(
                    format!("list index {} out of bounds, length {}", i, items.len()),
                    span,
                )
            })
        }
        (Value::Map(map), key) => map
            .iter()
            .find(|(k, _)| value_eq(state, k, key))
            .map(|(_, v)| v.clone())
            .ok_or_else(|| {
                RuntimeError::with_span(format!("map key {key:?} not found"), span)
            }),
        _ => Err(RuntimeError::with_span(
            format!(
                "cannot index {:?} with {:?}",
                type_name(object),
                type_name(index)
            ),
            span,
        )),
    }
}
