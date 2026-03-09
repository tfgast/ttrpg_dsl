use std::collections::BTreeMap;

use rustc_hash::FxHashMap;
use ttrpg_ast::ast::{ArmBody, ElseBranch, ExprKind, ForIterable, PatternKind};
use ttrpg_ast::{Span, Spanned};

use crate::coverage::{BranchKind, BranchPoint};
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
    parent_span: Span,
) -> Result<Value, RuntimeError> {
    let cond_val = eval_expr(env, condition)?;
    match cond_val {
        Value::Bool(true) => {
            env.record_branch(BranchPoint {
                parent_span,
                kind: BranchKind::IfThen,
                arm_span: then_block.span,
            });
            eval_block(env, then_block)
        }
        Value::Bool(false) => {
            env.record_branch(BranchPoint {
                parent_span,
                kind: BranchKind::IfElse,
                arm_span: else_branch.as_ref().map_or(parent_span, |eb| match eb {
                    ElseBranch::Block(b) => b.span,
                    ElseBranch::If(e) => e.span,
                }),
            });
            match else_branch {
                Some(ElseBranch::Block(block)) => eval_block(env, block),
                Some(ElseBranch::If(if_expr)) => eval_expr(env, if_expr),
                None => Ok(Value::Void),
            }
        }
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
    parent_span: Span,
) -> Result<Value, RuntimeError> {
    let scrutinee_val = eval_expr(env, scrutinee)?;
    let mut bindings = FxHashMap::default();

    if match_pattern(env, pattern, &scrutinee_val, &mut bindings) {
        env.record_branch(BranchPoint {
            parent_span,
            kind: BranchKind::IfThen,
            arm_span: then_block.span,
        });
        env.push_scope();
        for (name, val) in bindings {
            env.bind(name, val);
        }
        let result = eval_block(env, then_block);
        env.pop_scope();
        result
    } else {
        env.record_branch(BranchPoint {
            parent_span,
            kind: BranchKind::IfElse,
            arm_span: else_branch.as_ref().map_or(parent_span, |eb| match eb {
                ElseBranch::Block(b) => b.span,
                ElseBranch::If(e) => e.span,
            }),
        });
        match else_branch {
            Some(ElseBranch::Block(block)) => eval_block(env, block),
            Some(ElseBranch::If(if_expr)) => eval_expr(env, if_expr),
            None => Ok(Value::Void),
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
            if env.return_value.is_some() {
                return Ok(Value::Void);
            }
        }
    }

    Ok(Value::Void)
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
/// expression-statement, or `Value::Void` if the last statement
/// is a let/assign or the block is empty.
pub(crate) fn eval_block(
    env: &mut Env,
    block: &ttrpg_ast::ast::Block,
) -> Result<Value, RuntimeError> {
    env.push_scope();
    let mut result = Value::Void;
    for stmt in &block.node {
        match eval_stmt(env, stmt) {
            Ok(val) => {
                if let Some(ref ret) = env.return_value {
                    // Early return: use the return_value (not the statement value,
                    // which may be Void from an intermediate block like eval_for).
                    let ret = ret.clone();
                    env.pop_scope();
                    return Ok(ret);
                }
                result = val;
            }
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
    env.record_coverage(stmt.span);
    use ttrpg_ast::ast::StmtKind;

    match &stmt.node {
        StmtKind::Let { name, value, .. } => {
            let val = eval_expr(env, value)?;
            env.bind(name.clone(), val);
            Ok(Value::Void)
        }
        StmtKind::Expr(expr) => eval_expr(env, expr),
        StmtKind::Assign { target, op, value } => {
            super::assign::eval_assign(env, target, *op, value, stmt.span)?;
            Ok(Value::Void)
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
            Ok(Value::Void)
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
            Ok(Value::Void)
        }
        StmtKind::Emit {
            event_name,
            args,
            span,
        } => {
            super::emit::eval_emit(env, event_name, args, *span)?;
            Ok(Value::Void)
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
        StmtKind::WithBudgets {
            specs, body, span, ..
        } => {
            let specs_val = eval_expr(env, specs)?;
            let spec_list = match specs_val {
                Value::List(items) => items,
                _ => {
                    return Err(RuntimeError::with_span(
                        "with_budgets: expected list of BudgetSpec",
                        specs.span,
                    ))
                }
            };

            // Extract (actor, budget) pairs from each BudgetSpec struct
            let mut entries = Vec::with_capacity(spec_list.len());
            for item in &spec_list {
                match item {
                    Value::Struct { name, fields } if name == "BudgetSpec" => {
                        let actor = match fields.get("actor") {
                            Some(Value::Entity(r)) => *r,
                            _ => {
                                return Err(RuntimeError::with_span(
                                    "with_budgets: BudgetSpec missing entity `actor` field",
                                    specs.span,
                                ))
                            }
                        };
                        let budget = match fields.get("budget") {
                            Some(Value::Struct {
                                name: bn,
                                fields: bf,
                            }) if bn == "TurnBudget" => bf.clone(),
                            _ => {
                                return Err(RuntimeError::with_span(
                                    "with_budgets: BudgetSpec missing TurnBudget `budget` field",
                                    specs.span,
                                ))
                            }
                        };
                        entries.push((actor, budget));
                    }
                    _ => {
                        return Err(RuntimeError::with_span(
                            "with_budgets: list elements must be BudgetSpec structs",
                            specs.span,
                        ))
                    }
                }
            }

            scoped_budgets(env, entries, *span, |env| eval_block(env, body))
        }
        StmtKind::WithCostPayer {
            entity, body, ..
        } => {
            let entity_val = eval_expr(env, entity)?;
            let payer = match entity_val {
                Value::Entity(r) => r,
                _ => {
                    return Err(RuntimeError::with_span(
                        "with_cost_payer: expected entity value",
                        entity.span,
                    ))
                }
            };

            let prev = env.cost_payer;
            env.cost_payer = Some(payer);
            let result = eval_block(env, body);
            env.cost_payer = prev;
            result
        }
        StmtKind::Return(expr) => {
            let val = match expr {
                Some(e) => eval_expr(env, e)?,
                None => Value::Void,
            };
            env.return_value = Some(val.clone());
            Ok(val)
        }
    }
}

// ── Scoped budget helper ────────────────────────────────────────

/// Execute `body` with a provisioned turn budget, restoring the previous
/// budget on exit (even on error).  Does **not** set `turn_actor` or
/// `cost_payer` — action dispatch handles those per-action.
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
    // 1. Snapshot previous budget
    let prev_budget = env.state.read_turn_budget(&actor);

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

    // 3. Execute body
    let body_result = body(env);

    // 4. Restore or clear budget (always runs)
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

/// Execute `body` with budgets provisioned for multiple entities, restoring
/// all previous budgets on exit (even on error).
fn scoped_budgets<F>(
    env: &mut Env,
    entries: Vec<(EntityRef, BTreeMap<Name, Value>)>,
    span: Span,
    body: F,
) -> Result<Value, RuntimeError>
where
    F: FnOnce(&mut Env) -> Result<Value, RuntimeError>,
{
    // 1. Snapshot previous budgets and provision new ones
    let mut snapshots: Vec<(EntityRef, Option<BTreeMap<Name, Value>>)> =
        Vec::with_capacity(entries.len());

    for (actor, budget) in &entries {
        snapshots.push((*actor, env.state.read_turn_budget(actor)));
        let response = env.handler.handle(Effect::ProvisionBudget {
            actor: *actor,
            budget: budget.clone(),
        });
        if let Response::Vetoed = response {
            // Rollback already-provisioned budgets before returning
            for (prev_actor, prev_budget) in snapshots.into_iter().rev() {
                let _ = restore_budget(env, prev_actor, prev_budget, span);
            }
            return Err(RuntimeError::with_span(
                "with_budgets: ProvisionBudget was vetoed by host",
                span,
            ));
        }
    }

    // 2. Execute body
    let body_result = body(env);

    // 3. Restore all budgets (always runs, reverse order)
    let mut cleanup_err = None;
    for (actor, prev_budget) in snapshots.into_iter().rev() {
        if let Err(e) = restore_budget(env, actor, prev_budget, span) {
            if cleanup_err.is_none() {
                cleanup_err = Some(e);
            }
        }
    }

    // 4. Body error takes precedence
    match body_result {
        Err(e) => Err(e),
        Ok(val) => match cleanup_err {
            Some(e) => Err(e),
            None => Ok(val),
        },
    }
}

/// Restore a single entity's budget to its previous state, or clear it.
fn restore_budget(
    env: &mut Env,
    actor: EntityRef,
    prev: Option<BTreeMap<Name, Value>>,
    span: Span,
) -> Result<(), RuntimeError> {
    match prev {
        Some(old_budget) => {
            let resp = env.handler.handle(Effect::ProvisionBudget {
                actor,
                budget: old_budget,
            });
            if let Response::Vetoed = resp {
                Err(RuntimeError::with_span(
                    "with_budgets: budget restore was vetoed by host",
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
                    "with_budgets: budget clear was vetoed by host",
                    span,
                ))
            } else {
                Ok(())
            }
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
