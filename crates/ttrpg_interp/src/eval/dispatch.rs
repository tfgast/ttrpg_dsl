use std::collections::BTreeMap;

use ttrpg_ast::ast::ExprKind;
use ttrpg_ast::{Name, Spanned};
use ttrpg_checker::env::DeclInfo;

use crate::value::{DiceExpr, Value};
use crate::Env;
use crate::RuntimeError;

use super::access::{eval_field_access, eval_index};
use super::compare::match_pattern;
use super::control::{eval_arm_body, eval_for, eval_if, eval_if_let, eval_list_comprehension};
use super::helpers::{find_struct_defaults, type_name};
use super::ops::{eval_binop, eval_unary};

// ── Expression evaluator ───────────────────────────────────────

/// Evaluate an expression in the given environment.
pub(crate) fn eval_expr(env: &mut Env, expr: &Spanned<ExprKind>) -> Result<Value, RuntimeError> {
    match &expr.node {
        ExprKind::IntLit(n) => Ok(Value::Int(*n)),

        ExprKind::StringLit(s) => Ok(Value::Str(s.clone())),

        ExprKind::BoolLit(b) => Ok(Value::Bool(*b)),

        ExprKind::NoneLit => Ok(Value::None),

        ExprKind::DiceLit {
            count,
            sides,
            filter,
        } => Ok(Value::DiceExpr(DiceExpr {
            count: *count,
            sides: *sides,
            filter: *filter,
            modifier: 0,
        })),

        ExprKind::Paren(inner) => eval_expr(env, inner),

        ExprKind::Ident(name) => eval_ident(env, name, expr),

        ExprKind::UnaryOp { op, operand } => eval_unary(env, *op, operand, expr),

        ExprKind::BinOp { op, lhs, rhs } => eval_binop(env, *op, lhs, rhs, expr),

        ExprKind::FieldAccess { object, field } => eval_field_access(env, object, field, expr),

        ExprKind::Index { object, index } => eval_index(env, object, index, expr),

        ExprKind::ListLit(elements) => {
            let vals: Result<Vec<_>, _> = elements.iter().map(|e| eval_expr(env, e)).collect();
            Ok(Value::List(vals?))
        }

        ExprKind::MapLit(entries) => {
            let mut map = std::collections::BTreeMap::new();
            for (key_expr, val_expr) in entries {
                let key = eval_expr(env, key_expr)?;
                let val = eval_expr(env, val_expr)?;
                map.insert(key, val);
            }
            Ok(Value::Map(map))
        }

        ExprKind::StructLit { name, fields, base } => {
            // Start from base fields if ..base spread was provided.
            let mut field_map = if let Some(base_expr) = base {
                match eval_expr(env, base_expr)? {
                    Value::Struct {
                        fields: base_fields,
                        ..
                    } => base_fields,
                    other => {
                        return Err(RuntimeError::with_span(
                            format!("expected struct in ..base, got {}", type_name(&other)),
                            base_expr.span,
                        ));
                    }
                }
            } else {
                BTreeMap::new()
            };

            // Explicit fields override base values.
            for f in fields {
                let val = eval_expr(env, &f.value)?;
                field_map.insert(f.name.clone(), val);
            }

            // Fill in defaults for any omitted fields.
            let defaults: Vec<_> = find_struct_defaults(env, name)
                .into_iter()
                .filter(|(n, _)| !field_map.contains_key(n))
                .collect();
            for (fname, default_expr) in &defaults {
                let val = eval_expr(env, default_expr)?;
                field_map.insert(fname.clone(), val);
            }

            Ok(Value::Struct {
                name: name.clone(),
                fields: field_map,
            })
        }

        ExprKind::If {
            condition,
            then_block,
            else_branch,
        } => eval_if(env, condition, then_block, else_branch),

        ExprKind::IfLet {
            pattern,
            scrutinee,
            then_block,
            else_branch,
        } => eval_if_let(env, pattern, scrutinee, then_block, else_branch),

        ExprKind::PatternMatch { scrutinee, arms } => {
            let scrutinee_val = eval_expr(env, scrutinee)?;
            for arm in arms {
                let mut bindings = std::collections::HashMap::new();
                if match_pattern(env, &arm.pattern.node, &scrutinee_val, &mut bindings) {
                    env.push_scope();
                    for (name, val) in bindings {
                        env.bind(name, val);
                    }
                    let result = eval_arm_body(env, &arm.body);
                    env.pop_scope();
                    return result;
                }
            }
            // No arm matched — in a well-checked program this shouldn't happen
            // (the checker ensures exhaustive matching)
            Err(RuntimeError::with_span(
                "no pattern matched in match expression",
                expr.span,
            ))
        }

        ExprKind::GuardMatch { arms } => {
            use ttrpg_ast::ast::GuardKind;
            for arm in arms {
                match &arm.guard {
                    GuardKind::Wildcard => {
                        return eval_arm_body(env, &arm.body);
                    }
                    GuardKind::Expr(guard_expr) => {
                        let guard_val = eval_expr(env, guard_expr)?;
                        match guard_val {
                            Value::Bool(true) => return eval_arm_body(env, &arm.body),
                            Value::Bool(false) => {}
                            _ => {
                                return Err(RuntimeError::with_span(
                                    "guard expression must be Bool",
                                    guard_expr.span,
                                ));
                            }
                        }
                    }
                }
            }
            // No guard matched
            Err(RuntimeError::with_span(
                "no guard matched in match expression",
                expr.span,
            ))
        }

        ExprKind::Call { callee, args } => crate::call::eval_call(env, callee, args, expr.span),

        ExprKind::For {
            pattern,
            iterable,
            body,
        } => eval_for(env, pattern, iterable, body),

        ExprKind::ListComprehension {
            element,
            pattern,
            iterable,
            filter,
        } => eval_list_comprehension(env, element, pattern, iterable, filter.as_deref()),

        ExprKind::Has { entity, group_name, .. } => {
            let entity_val = eval_expr(env, entity)?;
            let entity_ref = match entity_val {
                Value::Entity(r) => r,
                _ => {
                    return Err(RuntimeError::with_span(
                        "has: expected entity value",
                        entity.span,
                    ))
                }
            };
            let has = env.state.read_field(&entity_ref, group_name).is_some();
            Ok(Value::Bool(has))
        }

        ExprKind::UnitLit { value, suffix } => {
            // Look up suffix → unit type name, then find the field name
            let unit_name = env
                .interp
                .type_env
                .suffix_to_unit
                .get(suffix.as_str())
                .ok_or_else(|| {
                    RuntimeError::with_span(format!("unknown unit suffix `{}`", suffix), expr.span)
                })?
                .clone();
            let field_name = match env.interp.type_env.types.get(&unit_name) {
                Some(DeclInfo::Unit(info)) => info.fields[0].name.clone(),
                _ => {
                    return Err(RuntimeError::with_span(
                        format!("unit type `{}` not found", unit_name),
                        expr.span,
                    ))
                }
            };
            let mut fields = BTreeMap::new();
            fields.insert(field_name, Value::Int(*value));
            Ok(Value::Struct {
                name: unit_name,
                fields,
            })
        }
    }
}

// ── Identifier evaluation ──────────────────────────────────────

fn eval_ident(env: &mut Env, name: &str, expr: &Spanned<ExprKind>) -> Result<Value, RuntimeError> {
    // 1. Check local scopes
    if let Some(val) = env.lookup(name) {
        return Ok(val.clone());
    }

    // 2. Check if it's an enum type name (for qualified access like `Duration.rounds`)
    //    Returns EnumNamespace so field access can resolve variants via eval_expr.
    if let Some(DeclInfo::Enum(_)) = env.interp.type_env.types.get(name) {
        return Ok(Value::EnumNamespace(Name::from(name)));
    }

    // 3. Check if it's a bare enum variant name
    //    Use the resolution table (populated by the checker) first, then fall back to
    //    unique_variant_owner for CLI eval expressions that weren't checker-resolved.
    let resolved = env
        .interp
        .type_env
        .resolved_variants
        .get(&expr.span)
        .cloned()
        .or_else(|| env.interp.type_env.unique_variant_owner(name).cloned());
    if let Some(enum_name) = resolved {
        // Look up the variant info to check if it has fields
        if let Some(DeclInfo::Enum(enum_info)) = env.interp.type_env.types.get(enum_name.as_str()) {
            if let Some(variant) = enum_info.variants.iter().find(|v| v.name == name) {
                if variant.fields.is_empty() {
                    // Fieldless variant — can be used as a value directly
                    return Ok(Value::EnumVariant {
                        enum_name: enum_name.clone(),
                        variant: Name::from(name),
                        fields: BTreeMap::new(),
                    });
                }
                // Variant with fields — this will be handled as a Call
                // Fall through to error
            }
        }
    }

    // 4. Check if it's a condition name (bare use = no args, but materialize defaults)
    if let Some(cond_decl) = env.interp.program.conditions.get(name) {
        let cond_decl = cond_decl.clone();
        let mut args = BTreeMap::new();
        // Evaluate default expressions for all params (checker ensures all have defaults)
        for param in &cond_decl.params {
            if let Some(ref default_expr) = param.default {
                let val = eval_expr(env, default_expr)?;
                args.insert(param.name.clone(), val);
            }
        }
        return Ok(Value::Condition {
            name: Name::from(name),
            args,
        });
    }

    Err(RuntimeError::with_span(
        format!("undefined variable '{}'", name),
        expr.span,
    ))
}
