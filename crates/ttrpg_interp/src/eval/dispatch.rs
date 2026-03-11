use std::collections::BTreeMap;

use rustc_hash::FxHashMap;
use ttrpg_ast::ast::{ExprKind, GroupInit, StructFieldInit};
use ttrpg_ast::{Name, Span, Spanned};
use ttrpg_checker::env::{DeclInfo, FnKind};

use crate::Env;
use crate::RuntimeError;
use crate::coverage::{BranchKind, BranchPoint};
use crate::effect::{Effect, Response};
use crate::value::{DiceExpr, Value};

use super::access::{eval_field_access, eval_index};
use super::compare::match_pattern;
use super::control::{eval_arm_body, eval_for, eval_if, eval_if_let, eval_list_comprehension};
use super::helpers::{
    eval_expr_with_hint, find_entity_defaults, find_optional_group_fields, find_required_groups,
    find_struct_defaults, type_name,
};
use super::ops::{eval_binop, eval_unary};

// ── Expression evaluator ───────────────────────────────────────

/// Evaluate an expression in the given environment.
pub(crate) fn eval_expr(env: &mut Env, expr: &Spanned<ExprKind>) -> Result<Value, RuntimeError> {
    match &expr.node {
        ExprKind::IntLit(n) => Ok(Value::Int(*n)),

        ExprKind::StringLit(s) => Ok(Value::Str(s.clone())),

        ExprKind::BoolLit(b) => Ok(Value::Bool(*b)),

        ExprKind::NoneLit => Ok(Value::Void),

        ExprKind::DiceLit {
            count,
            sides,
            filter,
        } => Ok(Value::DiceExpr(DiceExpr::single(
            *count, *sides, *filter, 0,
        ))),

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

        ExprKind::StructLit {
            name,
            fields,
            groups,
            base,
        } => {
            // Check if this is an entity type
            let is_entity = matches!(
                env.interp.type_env.types.get(name.as_str()),
                Some(DeclInfo::Entity(_))
            );

            if is_entity {
                return eval_entity_construction(env, name, fields, groups, expr.span);
            }
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
            // Look up the struct schema to get type hints for fields, allowing
            // disambiguation of bare enum variants (e.g. Cleric → Class.Cleric).
            let schema_fields = env.interp.type_env.lookup_fields(name);
            for f in fields {
                let val = if let Some(hint) = schema_fields
                    .and_then(|sf| sf.iter().find(|fi| fi.name == f.name))
                    .map(|fi| &fi.ty)
                {
                    eval_expr_with_hint(env, &f.value, hint)?
                } else {
                    eval_expr(env, &f.value)?
                };
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
        } => eval_if(env, condition, then_block, else_branch, expr.span),

        ExprKind::IfLet {
            pattern,
            scrutinee,
            then_block,
            else_branch,
        } => eval_if_let(env, pattern, scrutinee, then_block, else_branch, expr.span),

        ExprKind::PatternMatch { scrutinee, arms } => {
            let scrutinee_val = eval_expr(env, scrutinee)?;
            for (i, arm) in arms.iter().enumerate() {
                let mut bindings = FxHashMap::default();
                if match_pattern(env, &arm.pattern, &scrutinee_val, &mut bindings) {
                    let arm_span = match &arm.body {
                        ttrpg_ast::ast::ArmBody::Expr(e) => e.span,
                        ttrpg_ast::ast::ArmBody::Block(b) => b.span,
                    };
                    env.record_branch(BranchPoint {
                        parent_span: expr.span,
                        kind: BranchKind::MatchArm(i),
                        arm_span,
                    });
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
            for (i, arm) in arms.iter().enumerate() {
                match &arm.guard {
                    GuardKind::Wildcard => {
                        let arm_span = match &arm.body {
                            ttrpg_ast::ast::ArmBody::Expr(e) => e.span,
                            ttrpg_ast::ast::ArmBody::Block(b) => b.span,
                        };
                        env.record_branch(BranchPoint {
                            parent_span: expr.span,
                            kind: BranchKind::GuardArm(i),
                            arm_span,
                        });
                        return eval_arm_body(env, &arm.body);
                    }
                    GuardKind::Expr(guard_expr) => {
                        let guard_val = eval_expr(env, guard_expr)?;
                        match guard_val {
                            Value::Bool(true) => {
                                let arm_span = match &arm.body {
                                    ttrpg_ast::ast::ArmBody::Expr(e) => e.span,
                                    ttrpg_ast::ast::ArmBody::Block(b) => b.span,
                                };
                                env.record_branch(BranchPoint {
                                    parent_span: expr.span,
                                    kind: BranchKind::GuardArm(i),
                                    arm_span,
                                });
                                return eval_arm_body(env, &arm.body);
                            }
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

        ExprKind::Has {
            entity, group_name, ..
        } => {
            let entity_val = eval_expr(env, entity)?;
            let entity_ref = match entity_val {
                Value::Entity(r) => r,
                _ => {
                    return Err(RuntimeError::with_span(
                        "has: expected entity value",
                        entity.span,
                    ));
                }
            };
            let has = env.state.read_field(&entity_ref, group_name).is_some();
            Ok(Value::Bool(has))
        }

        ExprKind::Is {
            entity,
            entity_type,
        } => {
            let entity_val = eval_expr(env, entity)?;
            let entity_ref = match entity_val {
                Value::Entity(r) => r,
                _ => {
                    return Err(RuntimeError::with_span(
                        "is: expected entity value",
                        entity.span,
                    ));
                }
            };
            let matches = match env.state.entity_type_name(&entity_ref) {
                Some(actual_type) => actual_type.as_ref() == entity_type.as_ref(),
                None => false,
            };
            Ok(Value::Bool(matches))
        }

        ExprKind::UnitLit { value, suffix } => {
            // Look up suffix → unit type name, then find the field name
            let unit_name = env
                .interp
                .type_env
                .suffix_to_unit
                .get(suffix.as_str())
                .ok_or_else(|| {
                    RuntimeError::with_span(format!("unknown unit suffix `{suffix}`"), expr.span)
                })?
                .clone();
            let field_name = match env.interp.type_env.types.get(&unit_name) {
                Some(DeclInfo::Unit(info)) => info.fields[0].name.clone(),
                _ => {
                    return Err(RuntimeError::with_span(
                        format!("unit type `{unit_name}` not found"),
                        expr.span,
                    ));
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

    // 2. Check if it's a named const (lazy evaluation)
    if let Some(val) = env.interp.consts.borrow().get(name).cloned() {
        return Ok(val);
    }
    if let Some(const_decl) = env.interp.program.consts.get(name) {
        let const_decl = const_decl.clone();
        let val = eval_expr(env, &const_decl.value)?;
        env.interp
            .consts
            .borrow_mut()
            .insert(Name::from(name), val.clone());
        return Ok(val);
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
        if let Some(DeclInfo::Enum(enum_info)) = env.interp.type_env.types.get(enum_name.as_str())
            && let Some(variant) = enum_info.variants.iter().find(|v| v.name == name)
            && variant.fields.is_empty()
        {
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

    // 3. Check if it's a condition name (bare use = no args, but materialize defaults)
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

    // 4. Check if it's a function reference (bare function name in value position)
    //    Use the resolution table (populated by the checker) first.
    if env
        .interp
        .type_env
        .resolved_fn_refs
        .contains_key(&expr.span)
    {
        return Ok(Value::FnRef(Name::from(name)));
    }
    // Fallback for CLI eval expressions that weren't checker-resolved:
    // if the name is a FnKind::Function with no with-constraints, treat it as a fn ref.
    if let Some(fn_info) = env.interp.type_env.lookup_fn(name)
        && fn_info.kind == FnKind::Function
        && fn_info.params.iter().all(|p| p.with_groups.is_empty())
    {
        return Ok(Value::FnRef(Name::from(name)));
    }

    // 5. Check if it's an enum type name (for qualified access like `Duration.Rounds`)
    //    Returns EnumNamespace so field access can resolve variants via eval_expr.
    if let Some(DeclInfo::Enum(_)) = env.interp.type_env.types.get(name) {
        return Ok(Value::EnumNamespace(Name::from(name)));
    }

    // 5. Check if it's a module alias (e.g., `Core` from `use "..." as Core`)
    if env
        .interp
        .type_env
        .system_aliases
        .values()
        .any(|aliases| aliases.contains_key(name))
    {
        return Ok(Value::ModuleAlias(Name::from(name)));
    }

    // 6. `turn` keyword — materialize current actor's turn budget as a struct
    if name == "turn" {
        let actor = env.turn_actor.ok_or_else(|| {
            RuntimeError::with_span("cannot access `turn` outside of turn context", expr.span)
        })?;
        let budget = env.state.read_turn_budget(&actor).ok_or_else(|| {
            RuntimeError::with_span("no turn budget provisioned for actor", expr.span)
        })?;
        return Ok(Value::Struct {
            name: Name::from("TurnBudget"),
            fields: budget,
        });
    }

    Err(RuntimeError::with_span(
        format!("undefined variable '{name}'"),
        expr.span,
    ))
}

/// Evaluate entity construction from a struct literal with an entity type name.
fn eval_entity_construction(
    env: &mut Env,
    name: &Name,
    fields: &[StructFieldInit],
    groups: &[GroupInit],
    span: Span,
) -> Result<Value, RuntimeError> {
    // 1. Evaluate base fields with type hints
    let schema_fields = env.interp.type_env.lookup_fields(name);
    let mut field_map: FxHashMap<Name, Value> = FxHashMap::default();
    for f in fields {
        let val = if let Some(hint) = schema_fields
            .and_then(|sf| sf.iter().find(|fi| fi.name == f.name))
            .map(|fi| &fi.ty)
        {
            eval_expr_with_hint(env, &f.value, hint)?
        } else {
            eval_expr(env, &f.value)?
        };
        field_map.insert(f.name.clone(), val);
    }

    // 2. Fill defaults for omitted entity fields
    let defaults: Vec<_> = find_entity_defaults(env, name)
        .into_iter()
        .filter(|(n, _)| !field_map.contains_key(n))
        .collect();
    for (fname, default_expr) in &defaults {
        let val = eval_expr(env, default_expr)?;
        field_map.insert(fname.clone(), val);
    }

    // 3. Spawn the entity via effect
    let effect = Effect::SpawnEntity {
        entity_type: name.clone(),
        fields: field_map,
    };
    let response = env.handler.handle(effect);
    let entity_ref = match response {
        Response::EntitySpawned(r) => r,
        Response::Vetoed => {
            return Err(RuntimeError::with_span(
                format!("entity construction for `{name}` was vetoed by host"),
                span,
            ));
        }
        _ => {
            return Err(RuntimeError::with_span(
                format!("unexpected response to SpawnEntity for `{name}`"),
                span,
            ));
        }
    };

    // 4. Process inline groups
    for group in groups {
        let mut group_fields = BTreeMap::new();
        for init in &group.fields {
            let val = eval_expr(env, &init.value)?;
            group_fields.insert(init.name.clone(), val);
        }

        // Fill defaults for omitted group fields
        let group_defaults: Vec<_> =
            find_optional_group_fields(env, Some(name.as_str()), &group.name)
                .into_iter()
                .flatten()
                .filter_map(|fd| {
                    if group_fields.contains_key(&fd.name) {
                        return None;
                    }
                    fd.default.clone().map(|d| (fd.name.clone(), d))
                })
                .collect();
        for (fname, default_expr) in &group_defaults {
            let val = eval_expr(env, default_expr)?;
            group_fields.insert(fname.clone(), val);
        }

        let struct_val = Value::Struct {
            name: group.name.clone(),
            fields: group_fields,
        };

        let grant_effect = Effect::GrantGroup {
            entity: entity_ref,
            group_name: group.name.clone(),
            fields: struct_val,
        };
        env.handler.handle(grant_effect);
    }

    // 5. Auto-materialize required include groups not already provided
    let provided_groups: std::collections::HashSet<&Name> =
        groups.iter().map(|g| &g.name).collect();
    let required = find_required_groups(env, name);
    for group_name in &required {
        if provided_groups.contains(group_name) {
            continue;
        }
        // Build group with all defaults
        let mut group_fields = BTreeMap::new();
        let group_defaults: Vec<_> =
            find_optional_group_fields(env, Some(name.as_str()), group_name)
                .into_iter()
                .flatten()
                .filter_map(|fd| fd.default.clone().map(|d| (fd.name.clone(), d)))
                .collect();
        for (fname, default_expr) in &group_defaults {
            let val = eval_expr(env, default_expr)?;
            group_fields.insert(fname.clone(), val);
        }

        let struct_val = Value::Struct {
            name: group_name.clone(),
            fields: group_fields,
        };
        let grant_effect = Effect::GrantGroup {
            entity: entity_ref,
            group_name: group_name.clone(),
            fields: struct_val,
        };
        env.handler.handle(grant_effect);
    }

    Ok(Value::Entity(entity_ref))
}
