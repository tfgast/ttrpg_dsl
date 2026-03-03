use std::collections::BTreeMap;

use rustc_hash::FxHashMap;
use ttrpg_ast::ast::{ArmBody, ElseBranch, ExprKind, ForIterable, PatternKind};
use ttrpg_ast::{Span, Spanned};

use crate::effect::{Effect, Response};
use crate::state::EntityRef;
use crate::value::Value;
use crate::Env;
use crate::RuntimeError;

use ttrpg_ast::Name;

use super::compare::match_pattern;
use super::dispatch::eval_expr;
use super::helpers::{find_optional_group_fields, type_name};

// ── If expression evaluation ───────────────────────────────────

pub(super) fn eval_if(
    env: &mut Env,
    condition: &Spanned<ExprKind>,
    then_block: &ttrpg_ast::ast::Block,
    else_branch: &Option<ElseBranch>,
) -> Result<Value, RuntimeError> {
    let cond_val = eval_expr(env, condition)?;
    match cond_val {
        Value::Bool(true) => eval_block(env, then_block),
        Value::Bool(false) => match else_branch {
            Some(ElseBranch::Block(block)) => eval_block(env, block),
            Some(ElseBranch::If(if_expr)) => eval_expr(env, if_expr),
            None => Ok(Value::None),
        },
        _ => Err(RuntimeError::with_span(
            "if condition must be Bool",
            condition.span,
        )),
    }
}

pub(super) fn eval_if_let(
    env: &mut Env,
    pattern: &Spanned<PatternKind>,
    scrutinee: &Spanned<ExprKind>,
    then_block: &ttrpg_ast::ast::Block,
    else_branch: &Option<ElseBranch>,
) -> Result<Value, RuntimeError> {
    let scrutinee_val = eval_expr(env, scrutinee)?;
    let mut bindings = FxHashMap::default();

    if match_pattern(env, pattern, &scrutinee_val, &mut bindings) {
        env.push_scope();
        for (name, val) in bindings {
            env.bind(name, val);
        }
        let result = eval_block(env, then_block);
        env.pop_scope();
        result
    } else {
        match else_branch {
            Some(ElseBranch::Block(block)) => eval_block(env, block),
            Some(ElseBranch::If(if_expr)) => eval_expr(env, if_expr),
            None => Ok(Value::None),
        }
    }
}

// ── For-loop evaluation ───────────────────────────────────────

pub(super) fn eval_for(
    env: &mut Env,
    pattern: &Spanned<PatternKind>,
    iterable: &ForIterable,
    body: &ttrpg_ast::ast::Block,
) -> Result<Value, RuntimeError> {
    let items: Vec<Value> = match iterable {
        ForIterable::Collection(expr) => match eval_expr(env, expr)? {
            Value::List(items) => items,
            Value::Set(items) => items.into_iter().collect(),
            other => {
                return Err(RuntimeError::with_span(
                    format!("expected list or set, got {}", type_name(&other)),
                    expr.span,
                ));
            }
        },
        ForIterable::Range {
            start,
            end,
            inclusive,
        } => {
            let s = match eval_expr(env, start)? {
                Value::Int(n) => n,
                other => {
                    return Err(RuntimeError::with_span(
                        format!("range start must be int, got {}", type_name(&other)),
                        start.span,
                    ));
                }
            };
            let e = match eval_expr(env, end)? {
                Value::Int(n) => n,
                other => {
                    return Err(RuntimeError::with_span(
                        format!("range end must be int, got {}", type_name(&other)),
                        end.span,
                    ));
                }
            };
            if *inclusive {
                (s..=e).map(Value::Int).collect()
            } else {
                (s..e).map(Value::Int).collect()
            }
        }
    };

    for item in items {
        let mut bindings = FxHashMap::default();
        if match_pattern(env, pattern, &item, &mut bindings) {
            env.push_scope();
            for (name, val) in bindings {
                env.bind(name, val);
            }
            let result = eval_block(env, body);
            env.pop_scope();
            result?;
        }
    }

    Ok(Value::None)
}

pub(super) fn eval_list_comprehension(
    env: &mut Env,
    element: &Spanned<ExprKind>,
    pattern: &Spanned<PatternKind>,
    iterable: &ForIterable,
    filter: Option<&Spanned<ExprKind>>,
) -> Result<Value, RuntimeError> {
    let items: Vec<Value> = match iterable {
        ForIterable::Collection(expr) => match eval_expr(env, expr)? {
            Value::List(items) => items,
            Value::Set(items) => items.into_iter().collect(),
            other => {
                return Err(RuntimeError::with_span(
                    format!("expected list or set, got {}", type_name(&other)),
                    expr.span,
                ));
            }
        },
        ForIterable::Range {
            start,
            end,
            inclusive,
        } => {
            let s = match eval_expr(env, start)? {
                Value::Int(n) => n,
                other => {
                    return Err(RuntimeError::with_span(
                        format!("range start must be int, got {}", type_name(&other)),
                        start.span,
                    ));
                }
            };
            let e = match eval_expr(env, end)? {
                Value::Int(n) => n,
                other => {
                    return Err(RuntimeError::with_span(
                        format!("range end must be int, got {}", type_name(&other)),
                        end.span,
                    ));
                }
            };
            if *inclusive {
                (s..=e).map(Value::Int).collect()
            } else {
                (s..e).map(Value::Int).collect()
            }
        }
    };

    let mut collected = Vec::new();
    for item in items {
        let mut bindings = FxHashMap::default();
        if match_pattern(env, pattern, &item, &mut bindings) {
            env.push_scope();
            for (name, val) in bindings {
                env.bind(name, val);
            }

            let include = if let Some(filter_expr) = filter {
                match eval_expr(env, filter_expr) {
                    Ok(Value::Bool(b)) => b,
                    Ok(_) => {
                        env.pop_scope();
                        return Err(RuntimeError::with_span(
                            "list comprehension filter must be bool",
                            filter_expr.span,
                        ));
                    }
                    Err(e) => {
                        env.pop_scope();
                        return Err(e);
                    }
                }
            } else {
                true
            };

            if include {
                match eval_expr(env, element) {
                    Ok(val) => collected.push(val),
                    Err(e) => {
                        env.pop_scope();
                        return Err(e);
                    }
                }
            }
            env.pop_scope();
        }
    }

    Ok(Value::List(collected))
}

// ── Block evaluation ───────────────────────────────────────────

/// Execute a block of statements. Returns the value of the last
/// expression-statement, or `Value::None` if the last statement
/// is a let/assign or the block is empty.
pub(crate) fn eval_block(
    env: &mut Env,
    block: &ttrpg_ast::ast::Block,
) -> Result<Value, RuntimeError> {
    env.push_scope();
    let mut result = Value::None;
    for stmt in &block.node {
        match eval_stmt(env, stmt) {
            Ok(val) => result = val,
            Err(e) => {
                env.pop_scope();
                return Err(e);
            }
        }
    }
    env.pop_scope();
    Ok(result)
}

// ── Statement evaluation ───────────────────────────────────────

pub(super) fn eval_stmt(
    env: &mut Env,
    stmt: &Spanned<ttrpg_ast::ast::StmtKind>,
) -> Result<Value, RuntimeError> {
    use ttrpg_ast::ast::StmtKind;

    match &stmt.node {
        StmtKind::Let { name, value, .. } => {
            let val = eval_expr(env, value)?;
            env.bind(name.clone(), val);
            Ok(Value::None)
        }
        StmtKind::Expr(expr) => eval_expr(env, expr),
        StmtKind::Assign { target, op, value } => {
            super::assign::eval_assign(env, target, *op, value, stmt.span)?;
            Ok(Value::None)
        }
        StmtKind::Grant {
            entity,
            group_name,
            fields: field_inits,
        } => {
            let entity_val = eval_expr(env, entity)?;
            let entity_ref = match entity_val {
                Value::Entity(r) => r,
                _ => {
                    return Err(RuntimeError::with_span(
                        "grant: expected entity value",
                        entity.span,
                    ))
                }
            };

            // Evaluate explicit field initializers
            let mut fields = BTreeMap::new();
            for init in field_inits {
                let val = eval_expr(env, &init.value)?;
                fields.insert(init.name.clone(), val);
            }

            // Collect defaults from the entity declaration's optional group.
            // Clone the data first to avoid borrow conflict with eval_expr.
            let entity_type = env.state.entity_type_name(&entity_ref);
            let defaults: Vec<_> =
                find_optional_group_fields(env, entity_type.as_deref(), group_name)
                    .into_iter()
                    .flatten()
                    .filter_map(|fd| {
                        if fields.contains_key(&fd.name) {
                            return None;
                        }
                        fd.default.clone().map(|d| (fd.name.clone(), d))
                    })
                    .collect();
            for (name, default_expr) in &defaults {
                let val = eval_expr(env, default_expr)?;
                fields.insert(name.clone(), val);
            }

            let struct_val = Value::Struct {
                name: group_name.clone(),
                fields,
            };

            let effect = Effect::GrantGroup {
                entity: entity_ref,
                group_name: group_name.clone(),
                fields: struct_val,
            };
            let response = env.handler.handle(effect);
            if let Response::Vetoed = response {
                return Err(RuntimeError::with_span(
                    format!("grant {group_name} was vetoed by host"),
                    stmt.span,
                ));
            }
            Ok(Value::None)
        }
        StmtKind::Revoke { entity, group_name } => {
            let entity_val = eval_expr(env, entity)?;
            let entity_ref = match entity_val {
                Value::Entity(r) => r,
                _ => {
                    return Err(RuntimeError::with_span(
                        "revoke: expected entity value",
                        entity.span,
                    ))
                }
            };

            let effect = Effect::RevokeGroup {
                entity: entity_ref,
                group_name: group_name.clone(),
            };
            let response = env.handler.handle(effect);
            if let Response::Vetoed = response {
                return Err(RuntimeError::with_span(
                    format!("revoke {group_name} was vetoed by host"),
                    stmt.span,
                ));
            }
            Ok(Value::None)
        }
        StmtKind::Emit {
            event_name,
            args,
            span,
        } => {
            super::emit::eval_emit(env, event_name, args, *span)?;
            Ok(Value::None)
        }
        StmtKind::WithBudget {
            entity,
            budget_fields,
            body,
            span,
        } => {
            let entity_val = eval_expr(env, entity)?;
            let actor = match entity_val {
                Value::Entity(r) => r,
                _ => {
                    return Err(RuntimeError::with_span(
                        "with_budget: expected entity value",
                        entity.span,
                    ))
                }
            };

            let mut budget = BTreeMap::new();
            for (name, expr) in budget_fields {
                let val = eval_expr(env, expr)?;
                budget.insert(name.node.clone(), val);
            }

            scoped_budget(env, actor, budget, *span, |env| eval_block(env, body))
        }
    }
}

// ── Scoped budget helper ────────────────────────────────────────

/// Execute `body` with a provisioned turn budget, restoring the previous
/// budget/turn_actor/cost_payer on exit (even on error).
fn scoped_budget<F>(
    env: &mut Env,
    actor: EntityRef,
    budget: BTreeMap<Name, Value>,
    span: Span,
    body: F,
) -> Result<Value, RuntimeError>
where
    F: FnOnce(&mut Env) -> Result<Value, RuntimeError>,
{
    // 1. Snapshot previous state
    let prev_budget = env.state.read_turn_budget(&actor);
    let prev_turn_actor = env.turn_actor;
    let prev_cost_payer = env.cost_payer;

    // 2. Emit ProvisionBudget
    let response = env.handler.handle(Effect::ProvisionBudget {
        actor,
        budget: budget.clone(),
    });
    if let Response::Vetoed = response {
        return Err(RuntimeError::with_span(
            "with_budget: ProvisionBudget was vetoed by host",
            span,
        ));
    }

    // 3. Set env context
    env.turn_actor = Some(actor);
    env.cost_payer = Some(actor);

    // 4. Execute body
    let body_result = body(env);

    // 5. Restore env context (always runs)
    env.turn_actor = prev_turn_actor;
    env.cost_payer = prev_cost_payer;

    // 6. Restore or clear budget (always runs)
    let cleanup_result = match prev_budget {
        Some(old_budget) => {
            let resp = env.handler.handle(Effect::ProvisionBudget {
                actor,
                budget: old_budget,
            });
            if let Response::Vetoed = resp {
                Err(RuntimeError::with_span(
                    "with_budget: budget restore was vetoed by host",
                    span,
                ))
            } else {
                Ok(())
            }
        }
        None => {
            let resp = env.handler.handle(Effect::ClearBudget { actor });
            if let Response::Vetoed = resp {
                Err(RuntimeError::with_span(
                    "with_budget: budget clear was vetoed by host",
                    span,
                ))
            } else {
                Ok(())
            }
        }
    };

    // 7. Body error takes precedence
    match body_result {
        Err(e) => Err(e),
        Ok(val) => {
            cleanup_result?;
            Ok(val)
        }
    }
}

// ── Arm body evaluation ────────────────────────────────────────

pub(super) fn eval_arm_body(env: &mut Env, body: &ArmBody) -> Result<Value, RuntimeError> {
    match body {
        ArmBody::Expr(expr) => eval_expr(env, expr),
        ArmBody::Block(block) => eval_block(env, block),
    }
}
