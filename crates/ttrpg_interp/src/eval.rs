use std::collections::BTreeMap;

use ttrpg_ast::Spanned;
use ttrpg_ast::ast::{
    ArmBody, BinOp, ElseBranch, ExprKind, GuardKind, PatternKind, UnaryOp,
};
use ttrpg_checker::env::DeclInfo;

use crate::Env;
use crate::RuntimeError;
use crate::state::StateProvider;
use crate::value::{DiceExpr, Value};

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

        ExprKind::StructLit { name, fields } => {
            let mut field_map = BTreeMap::new();
            for f in fields {
                let val = eval_expr(env, &f.value)?;
                field_map.insert(f.name.clone(), val);
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

        ExprKind::Call { .. } => {
            // Stub — real dispatch in Phase 4
            Err(RuntimeError::with_span(
                "function calls are not yet implemented (Phase 4)",
                expr.span,
            ))
        }
    }
}

// ── Identifier evaluation ──────────────────────────────────────

fn eval_ident(
    env: &Env,
    name: &str,
    expr: &Spanned<ExprKind>,
) -> Result<Value, RuntimeError> {
    // 1. Check local scopes
    if let Some(val) = env.lookup(name) {
        return Ok(val.clone());
    }

    // 2. Check if it's an enum type name (for qualified access like `Duration.rounds`)
    //    Returns EnumNamespace so field access can resolve variants via eval_expr.
    if let Some(DeclInfo::Enum(_)) = env.interp.type_env.types.get(name) {
        return Ok(Value::EnumNamespace(name.to_string()));
    }

    // 3. Check if it's a bare enum variant name (unambiguous via variant_to_enum)
    if let Some(enum_name) = env.interp.type_env.variant_to_enum.get(name) {
        // Look up the variant info to check if it has fields
        if let Some(DeclInfo::Enum(enum_info)) = env.interp.type_env.types.get(enum_name.as_str())
        {
            if let Some(variant) = enum_info.variants.iter().find(|v| v.name == name) {
                if variant.fields.is_empty() {
                    // Fieldless variant — can be used as a value directly
                    return Ok(Value::EnumVariant {
                        enum_name: enum_name.clone(),
                        variant: name.to_string(),
                        fields: BTreeMap::new(),
                    });
                }
                // Variant with fields — this will be handled as a Call
                // Fall through to error
            }
        }
    }

    Err(RuntimeError::with_span(
        format!("undefined variable '{}'", name),
        expr.span,
    ))
}

// ── Unary operator evaluation ──────────────────────────────────

fn eval_unary(
    env: &mut Env,
    op: UnaryOp,
    operand: &Spanned<ExprKind>,
    expr: &Spanned<ExprKind>,
) -> Result<Value, RuntimeError> {
    let val = eval_expr(env, operand)?;
    match (op, &val) {
        (UnaryOp::Neg, Value::Int(n)) => n
            .checked_neg()
            .map(Value::Int)
            .ok_or_else(|| RuntimeError::with_span("integer overflow in negation", expr.span)),
        (UnaryOp::Neg, Value::Float(f)) => Ok(Value::Float(-f)),
        (UnaryOp::Not, Value::Bool(b)) => Ok(Value::Bool(!b)),
        _ => Err(RuntimeError::with_span(
            format!("invalid unary {:?} on {:?}", op, type_name(&val)),
            expr.span,
        )),
    }
}

// ── Binary operator evaluation ─────────────────────────────────

fn eval_binop(
    env: &mut Env,
    op: BinOp,
    lhs_expr: &Spanned<ExprKind>,
    rhs_expr: &Spanned<ExprKind>,
    expr: &Spanned<ExprKind>,
) -> Result<Value, RuntimeError> {
    // Short-circuit for logical operators
    if op == BinOp::And {
        let lhs = eval_expr(env, lhs_expr)?;
        return match lhs {
            Value::Bool(false) => Ok(Value::Bool(false)),
            Value::Bool(true) => {
                let rhs = eval_expr(env, rhs_expr)?;
                match rhs {
                    Value::Bool(b) => Ok(Value::Bool(b)),
                    _ => Err(RuntimeError::with_span("&& requires Bool operands", expr.span)),
                }
            }
            _ => Err(RuntimeError::with_span("&& requires Bool operands", expr.span)),
        };
    }
    if op == BinOp::Or {
        let lhs = eval_expr(env, lhs_expr)?;
        return match lhs {
            Value::Bool(true) => Ok(Value::Bool(true)),
            Value::Bool(false) => {
                let rhs = eval_expr(env, rhs_expr)?;
                match rhs {
                    Value::Bool(b) => Ok(Value::Bool(b)),
                    _ => Err(RuntimeError::with_span("|| requires Bool operands", expr.span)),
                }
            }
            _ => Err(RuntimeError::with_span("|| requires Bool operands", expr.span)),
        };
    }

    let lhs = eval_expr(env, lhs_expr)?;
    let rhs = eval_expr(env, rhs_expr)?;

    // RollResult coerces to Int (via .total) only for arithmetic and comparison.
    // Equality, membership, and logical ops use the raw values so that
    // e.g. `roll_result in list<RollResult>` compares structurally.
    match op {
        // Arithmetic — coerce
        BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div => {
            let lhs = coerce_roll_result(lhs);
            let rhs = coerce_roll_result(rhs);
            match op {
                BinOp::Add => eval_add(&lhs, &rhs, expr),
                BinOp::Sub => eval_sub(&lhs, &rhs, expr),
                BinOp::Mul => eval_mul(&lhs, &rhs, expr),
                BinOp::Div => eval_div(&lhs, &rhs, expr),
                _ => unreachable!(),
            }
        }

        // Comparison — coerce
        BinOp::Lt | BinOp::LtEq | BinOp::Gt | BinOp::GtEq => {
            let lhs = coerce_roll_result(lhs);
            let rhs = coerce_roll_result(rhs);
            match op {
                BinOp::Lt => eval_comparison(&lhs, &rhs, |o| o.is_lt(), env.interp.type_env, expr),
                BinOp::LtEq => eval_comparison(&lhs, &rhs, |o| o.is_le(), env.interp.type_env, expr),
                BinOp::Gt => eval_comparison(&lhs, &rhs, |o| o.is_gt(), env.interp.type_env, expr),
                BinOp::GtEq => eval_comparison(&lhs, &rhs, |o| o.is_ge(), env.interp.type_env, expr),
                _ => unreachable!(),
            }
        }

        // Equality — coerce RollResult to Int (spec: == / != coerce RollResult)
        BinOp::Eq => {
            let lhs = coerce_roll_result(lhs);
            let rhs = coerce_roll_result(rhs);
            Ok(Value::Bool(value_eq(env.state, &lhs, &rhs)))
        }
        BinOp::NotEq => {
            let lhs = coerce_roll_result(lhs);
            let rhs = coerce_roll_result(rhs);
            Ok(Value::Bool(!value_eq(env.state, &lhs, &rhs)))
        }

        // Membership — no coercion
        BinOp::In => eval_in(&lhs, &rhs, env.state, expr),

        // Logical handled above via short-circuit
        BinOp::And | BinOp::Or => unreachable!(),
    }
}

/// Coerce RollResult to Int via .total for arithmetic/comparison contexts.
fn coerce_roll_result(val: Value) -> Value {
    match val {
        Value::RollResult(r) => Value::Int(r.total),
        other => other,
    }
}

fn eval_add(lhs: &Value, rhs: &Value, expr: &Spanned<ExprKind>) -> Result<Value, RuntimeError> {
    match (lhs, rhs) {
        (Value::Int(a), Value::Int(b)) => a
            .checked_add(*b)
            .map(Value::Int)
            .ok_or_else(|| RuntimeError::with_span("integer overflow in addition", expr.span)),
        (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a + b)),
        (Value::Int(a), Value::Float(b)) => Ok(Value::Float(*a as f64 + b)),
        (Value::Float(a), Value::Int(b)) => Ok(Value::Float(a + *b as f64)),
        (Value::Str(a), Value::Str(b)) => Ok(Value::Str(format!("{}{}", a, b))),
        // DiceExpr algebra: DiceExpr + Int → adjust modifier
        (Value::DiceExpr(d), Value::Int(n)) => {
            let modifier = d.modifier.checked_add(*n)
                .ok_or_else(|| RuntimeError::with_span("dice modifier overflow in addition", expr.span))?;
            Ok(Value::DiceExpr(DiceExpr { modifier, ..d.clone() }))
        }
        (Value::Int(n), Value::DiceExpr(d)) => {
            let modifier = d.modifier.checked_add(*n)
                .ok_or_else(|| RuntimeError::with_span("dice modifier overflow in addition", expr.span))?;
            Ok(Value::DiceExpr(DiceExpr { modifier, ..d.clone() }))
        }
        // DiceExpr + DiceExpr → merge counts and modifiers (must have same dice spec)
        (Value::DiceExpr(a), Value::DiceExpr(b)) => {
            if a.sides != b.sides || a.filter != b.filter {
                return Err(RuntimeError::with_span(
                    format!(
                        "cannot add dice expressions with different specs ({}d{} vs {}d{})",
                        a.count, a.sides, b.count, b.sides
                    ),
                    expr.span,
                ));
            }
            let count = a.count.checked_add(b.count)
                .ok_or_else(|| RuntimeError::with_span("dice count overflow in addition", expr.span))?;
            let modifier = a.modifier.checked_add(b.modifier)
                .ok_or_else(|| RuntimeError::with_span("dice modifier overflow in addition", expr.span))?;
            Ok(Value::DiceExpr(DiceExpr {
                count,
                sides: a.sides,
                filter: a.filter,
                modifier,
            }))
        }
        _ => Err(RuntimeError::with_span(
            format!("cannot add {:?} and {:?}", type_name(lhs), type_name(rhs)),
            expr.span,
        )),
    }
}

fn eval_sub(lhs: &Value, rhs: &Value, expr: &Spanned<ExprKind>) -> Result<Value, RuntimeError> {
    match (lhs, rhs) {
        (Value::Int(a), Value::Int(b)) => a
            .checked_sub(*b)
            .map(Value::Int)
            .ok_or_else(|| RuntimeError::with_span("integer overflow in subtraction", expr.span)),
        (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a - b)),
        (Value::Int(a), Value::Float(b)) => Ok(Value::Float(*a as f64 - b)),
        (Value::Float(a), Value::Int(b)) => Ok(Value::Float(a - *b as f64)),
        // DiceExpr - Int → adjust modifier
        (Value::DiceExpr(d), Value::Int(n)) => {
            let modifier = d.modifier.checked_sub(*n)
                .ok_or_else(|| RuntimeError::with_span("dice modifier overflow in subtraction", expr.span))?;
            Ok(Value::DiceExpr(DiceExpr { modifier, ..d.clone() }))
        }
        _ => Err(RuntimeError::with_span(
            format!(
                "cannot subtract {:?} from {:?}",
                type_name(rhs),
                type_name(lhs)
            ),
            expr.span,
        )),
    }
}

fn eval_mul(lhs: &Value, rhs: &Value, expr: &Spanned<ExprKind>) -> Result<Value, RuntimeError> {
    match (lhs, rhs) {
        (Value::Int(a), Value::Int(b)) => a
            .checked_mul(*b)
            .map(Value::Int)
            .ok_or_else(|| {
                RuntimeError::with_span("integer overflow in multiplication", expr.span)
            }),
        (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a * b)),
        (Value::Int(a), Value::Float(b)) => Ok(Value::Float(*a as f64 * b)),
        (Value::Float(a), Value::Int(b)) => Ok(Value::Float(a * *b as f64)),
        _ => Err(RuntimeError::with_span(
            format!(
                "cannot multiply {:?} and {:?}",
                type_name(lhs),
                type_name(rhs)
            ),
            expr.span,
        )),
    }
}

fn eval_div(lhs: &Value, rhs: &Value, expr: &Spanned<ExprKind>) -> Result<Value, RuntimeError> {
    match (lhs, rhs) {
        // Int / Int → Float (not integer division)
        (Value::Int(a), Value::Int(b)) => {
            if *b == 0 {
                Err(RuntimeError::with_span("division by zero", expr.span))
            } else {
                Ok(Value::Float(*a as f64 / *b as f64))
            }
        }
        (Value::Float(a), Value::Float(b)) => {
            if *b == 0.0 {
                Err(RuntimeError::with_span("division by zero", expr.span))
            } else {
                Ok(Value::Float(a / b))
            }
        }
        (Value::Int(a), Value::Float(b)) => {
            if *b == 0.0 {
                Err(RuntimeError::with_span("division by zero", expr.span))
            } else {
                Ok(Value::Float(*a as f64 / b))
            }
        }
        (Value::Float(a), Value::Int(b)) => {
            if *b == 0 {
                Err(RuntimeError::with_span("division by zero", expr.span))
            } else {
                Ok(Value::Float(a / *b as f64))
            }
        }
        _ => Err(RuntimeError::with_span(
            format!(
                "cannot divide {:?} by {:?}",
                type_name(lhs),
                type_name(rhs)
            ),
            expr.span,
        )),
    }
}

fn eval_comparison(
    lhs: &Value,
    rhs: &Value,
    cmp_fn: fn(std::cmp::Ordering) -> bool,
    type_env: &ttrpg_checker::env::TypeEnv,
    expr: &Spanned<ExprKind>,
) -> Result<Value, RuntimeError> {
    let ordering = match (lhs, rhs) {
        (Value::Int(a), Value::Int(b)) => a.cmp(b),
        (Value::Float(a), Value::Float(b)) => a
            .partial_cmp(b)
            .ok_or_else(|| RuntimeError::with_span("cannot compare NaN", expr.span))?,
        (Value::Int(a), Value::Float(b)) => (*a as f64)
            .partial_cmp(b)
            .ok_or_else(|| RuntimeError::with_span("cannot compare NaN", expr.span))?,
        (Value::Float(a), Value::Int(b)) => a
            .partial_cmp(&(*b as f64))
            .ok_or_else(|| RuntimeError::with_span("cannot compare NaN", expr.span))?,
        (Value::Str(a), Value::Str(b)) => a.cmp(b),
        (
            Value::EnumVariant {
                enum_name: e1,
                variant: v1,
                ..
            },
            Value::EnumVariant {
                enum_name: e2,
                variant: v2,
                ..
            },
        ) if e1 == e2 => {
            let ord1 = variant_ordinal(type_env, e1, v1);
            let ord2 = variant_ordinal(type_env, e2, v2);
            ord1.cmp(&ord2)
        }
        _ => {
            return Err(RuntimeError::with_span(
                format!(
                    "cannot compare {:?} and {:?}",
                    type_name(lhs),
                    type_name(rhs)
                ),
                expr.span,
            ));
        }
    };
    Ok(Value::Bool(cmp_fn(ordering)))
}

/// Look up a variant's declaration-order index within its enum.
fn variant_ordinal(
    type_env: &ttrpg_checker::env::TypeEnv,
    enum_name: &str,
    variant_name: &str,
) -> Option<usize> {
    if let Some(DeclInfo::Enum(info)) = type_env.types.get(enum_name) {
        info.variants.iter().position(|v| v.name == variant_name)
    } else {
        None
    }
}

fn eval_in(
    lhs: &Value,
    rhs: &Value,
    state: &dyn StateProvider,
    expr: &Spanned<ExprKind>,
) -> Result<Value, RuntimeError> {
    match rhs {
        Value::List(items) => {
            let found = items.iter().any(|item| value_eq(state, lhs, item));
            Ok(Value::Bool(found))
        }
        Value::Set(items) => {
            let found = items.iter().any(|item| value_eq(state, lhs, item));
            Ok(Value::Bool(found))
        }
        Value::Map(map) => {
            let found = map.keys().any(|k| value_eq(state, lhs, k));
            Ok(Value::Bool(found))
        }
        _ => Err(RuntimeError::with_span(
            format!("'in' requires List, Set, or Map on right side, got {:?}", type_name(rhs)),
            expr.span,
        )),
    }
}

// ── Field access ───────────────────────────────────────────────

fn eval_field_access(
    env: &mut Env,
    object_expr: &Spanned<ExprKind>,
    field: &str,
    expr: &Spanned<ExprKind>,
) -> Result<Value, RuntimeError> {
    let object = eval_expr(env, object_expr)?;

    match &object {
        // Entity fields via StateProvider
        Value::Entity(entity_ref) => {
            env.state
                .read_field(entity_ref, field)
                .ok_or_else(|| {
                    RuntimeError::with_span(
                        format!("entity {} has no field '{}'", entity_ref.0, field),
                        expr.span,
                    )
                })
        }

        // Struct fields
        Value::Struct { fields, name, .. } => {
            fields.get(field).cloned().ok_or_else(|| {
                RuntimeError::with_span(
                    format!("struct '{}' has no field '{}'", name, field),
                    expr.span,
                )
            })
        }

        // Enum variant fields
        Value::EnumVariant {
            enum_name,
            variant,
            fields,
        } => fields.get(field).cloned().ok_or_else(|| {
            RuntimeError::with_span(
                format!("variant '{}.{}' has no field '{}'", enum_name, variant, field),
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
            _ => Err(RuntimeError::with_span(
                format!("RollResult has no field '{}'", field),
                expr.span,
            )),
        },

        // TurnBudget fields
        Value::TurnBudget(tb) => match field {
            "actions" => Ok(Value::Int(tb.actions)),
            "bonus_actions" => Ok(Value::Int(tb.bonus_actions)),
            "reactions" => Ok(Value::Int(tb.reactions)),
            "movement" => Ok(Value::Int(tb.movement)),
            "free_interactions" => Ok(Value::Int(tb.free_interactions)),
            _ => Err(RuntimeError::with_span(
                format!("TurnBudget has no field '{}'", field),
                expr.span,
            )),
        },

        // Qualified enum variant access: EnumType.variant
        Value::EnumNamespace(enum_name) => {
            if let Some(DeclInfo::Enum(enum_info)) =
                env.interp.type_env.types.get(enum_name.as_str())
            {
                if let Some(variant) = enum_info.variants.iter().find(|v| v.name == field) {
                    if variant.fields.is_empty() {
                        return Ok(Value::EnumVariant {
                            enum_name: enum_name.clone(),
                            variant: field.to_string(),
                            fields: BTreeMap::new(),
                        });
                    }
                    return Err(RuntimeError::with_span(
                        format!(
                            "enum variant '{}.{}' has fields and must be called as a function",
                            enum_name, field
                        ),
                        expr.span,
                    ));
                }
            }
            Err(RuntimeError::with_span(
                format!("enum '{}' has no variant '{}'", enum_name, field),
                expr.span,
            ))
        }

        _ => Err(RuntimeError::with_span(
            format!("cannot access field '{}' on {:?}", field, type_name(&object)),
            expr.span,
        )),
    }
}

// ── Index access ───────────────────────────────────────────────

fn eval_index(
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
                        format!(
                            "list index {} out of bounds, length {}",
                            i,
                            items.len()
                        ),
                        expr.span,
                    ));
                }
                positive as usize
            } else {
                *i as usize
            };
            items.get(idx).cloned().ok_or_else(|| {
                RuntimeError::with_span(
                    format!(
                        "list index {} out of bounds, length {}",
                        i,
                        items.len()
                    ),
                    expr.span,
                )
            })
        }
        (Value::Map(map), key) => map.get(key).cloned().ok_or_else(|| {
            RuntimeError::with_span(
                format!("map key {:?} not found", key),
                expr.span,
            )
        }),
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

// ── If expression evaluation ───────────────────────────────────

fn eval_if(
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

pub(crate) fn eval_stmt(
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
        StmtKind::Assign { .. } => {
            // Stub — full implementation in Phase 3
            Err(RuntimeError::with_span(
                "assignments are not yet implemented (Phase 3)",
                stmt.span,
            ))
        }
    }
}

// ── Arm body evaluation ────────────────────────────────────────

fn eval_arm_body(env: &mut Env, body: &ArmBody) -> Result<Value, RuntimeError> {
    match body {
        ArmBody::Expr(expr) => eval_expr(env, expr),
        ArmBody::Block(block) => eval_block(env, block),
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
        (Value::Int(a), Value::Float(b)) => (*a as f64) == *b,
        (Value::Float(a), Value::Int(b)) => *a == (*b as f64),
        (Value::Str(a), Value::Str(b)) => a == b,
        (Value::DiceExpr(a), Value::DiceExpr(b)) => a == b,
        (Value::RollResult(a), Value::RollResult(b)) => a == b,
        (Value::Entity(a), Value::Entity(b)) => a == b,
        (Value::Condition(a), Value::Condition(b)) => a == b,
        (Value::Duration(a), Value::Duration(b)) => a == b,
        (Value::TurnBudget(a), Value::TurnBudget(b)) => a == b,

        // Position: delegate to host
        (Value::Position(_), Value::Position(_)) => state.position_eq(a, b),

        // Composites: recursive
        (Value::List(a), Value::List(b)) => {
            a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| value_eq(state, x, y))
        }
        (Value::Set(a), Value::Set(b)) => {
            // Sets use structural equality since elements are ordered
            a.len() == b.len()
                && a.iter()
                    .zip(b.iter())
                    .all(|(x, y)| value_eq(state, x, y))
        }
        (Value::Map(a), Value::Map(b)) => {
            a.len() == b.len()
                && a.iter().zip(b.iter()).all(|((k1, v1), (k2, v2))| {
                    value_eq(state, k1, k2) && value_eq(state, v1, v2)
                })
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
                && f1.iter().zip(f2.iter()).all(|((k1, v1), (k2, v2))| {
                    k1 == k2 && value_eq(state, v1, v2)
                })
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
                && f1.iter().zip(f2.iter()).all(|((k1, v1), (k2, v2))| {
                    k1 == k2 && value_eq(state, v1, v2)
                })
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
pub(crate) fn match_pattern(
    env: &Env,
    pattern: &PatternKind,
    value: &Value,
    bindings: &mut std::collections::HashMap<String, Value>,
) -> bool {
    match pattern {
        PatternKind::Wildcard => true,

        PatternKind::IntLit(n) => matches!(value, Value::Int(v) if v == n),

        PatternKind::StringLit(s) => matches!(value, Value::Str(v) if v == s),

        PatternKind::BoolLit(b) => matches!(value, Value::Bool(v) if v == b),

        PatternKind::Ident(name) => {
            // Check if this ident is a bare enum variant (via variant_to_enum).
            // If so, match against the variant; otherwise bind as a variable.
            if let Some(enum_name) = env.interp.type_env.variant_to_enum.get(name.as_str()) {
                // It's a bare enum variant — match only if value is that variant
                matches!(
                    value,
                    Value::EnumVariant { enum_name: actual_enum, variant, fields }
                    if actual_enum == enum_name && variant == name && fields.is_empty()
                )
            } else {
                bindings.insert(name.clone(), value.clone());
                true
            }
        }

        PatternKind::QualifiedVariant { ty, variant } => {
            matches!(
                value,
                Value::EnumVariant { enum_name, variant: v, fields }
                if enum_name == ty && v == variant && fields.is_empty()
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
                if let Some(DeclInfo::Enum(enum_info)) =
                    env.interp.type_env.types.get(ty.as_str())
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
            // Check if this is an enum variant via variant_to_enum
            if let Some(enum_name) = env.interp.type_env.variant_to_enum.get(name.as_str()) {
                if let Value::EnumVariant {
                    enum_name: actual_enum,
                    variant,
                    fields,
                } = value
                {
                    if actual_enum != enum_name || variant != name {
                        return false;
                    }
                    // Match fields positionally using variant field info
                    if let Some(DeclInfo::Enum(enum_info)) =
                        env.interp.type_env.types.get(enum_name.as_str())
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
                        for (pat, field_info) in
                            patterns.iter().zip(struct_info.fields.iter())
                        {
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

// ── Helpers ────────────────────────────────────────────────────

/// Returns a human-readable type name for error messages.
fn type_name(val: &Value) -> &'static str {
    match val {
        Value::Int(_) => "Int",
        Value::Float(_) => "Float",
        Value::Bool(_) => "Bool",
        Value::Str(_) => "String",
        Value::None => "None",
        Value::DiceExpr(_) => "DiceExpr",
        Value::RollResult(_) => "RollResult",
        Value::List(_) => "List",
        Value::Set(_) => "Set",
        Value::Map(_) => "Map",
        Value::Option(_) => "Option",
        Value::Struct { .. } => "Struct",
        Value::Entity(_) => "Entity",
        Value::EnumVariant { .. } => "EnumVariant",
        Value::Position(_) => "Position",
        Value::TurnBudget(_) => "TurnBudget",
        Value::Duration(_) => "Duration",
        Value::Condition(_) => "Condition",
        Value::EnumNamespace(_) => "EnumNamespace",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::{BTreeMap, HashMap};
    use std::sync::Arc;

    use ttrpg_ast::Span;
    use ttrpg_ast::ast::*;
    use ttrpg_checker::env::{EnumInfo, TypeEnv, VariantInfo};

    use crate::effect::{Effect, EffectHandler, Response};
    use crate::state::{ActiveCondition, EntityRef, StateProvider};
    use crate::value::{DiceExpr, PositionValue, RollResult, TurnBudget};
    use crate::Interpreter;

    // ── Test infrastructure ────────────────────────────────────

    /// Records effects and replays scripted responses.
    struct ScriptedHandler {
        script: std::collections::VecDeque<Response>,
        log: Vec<Effect>,
    }

    impl ScriptedHandler {
        fn new() -> Self {
            ScriptedHandler {
                script: std::collections::VecDeque::new(),
                log: Vec::new(),
            }
        }
    }

    impl EffectHandler for ScriptedHandler {
        fn handle(&mut self, effect: Effect) -> Response {
            self.log.push(effect);
            self.script.pop_front().unwrap_or(Response::Acknowledged)
        }
    }

    /// Minimal StateProvider for tests.
    struct TestState {
        fields: HashMap<(u64, String), Value>,
        conditions: HashMap<u64, Vec<ActiveCondition>>,
        turn_budgets: HashMap<u64, TurnBudget>,
        enabled_options: Vec<String>,
    }

    impl TestState {
        fn new() -> Self {
            TestState {
                fields: HashMap::new(),
                conditions: HashMap::new(),
                turn_budgets: HashMap::new(),
                enabled_options: Vec::new(),
            }
        }
    }

    impl StateProvider for TestState {
        fn read_field(&self, entity: &EntityRef, field: &str) -> Option<Value> {
            self.fields.get(&(entity.0, field.to_string())).cloned()
        }

        fn read_conditions(&self, entity: &EntityRef) -> Option<Vec<ActiveCondition>> {
            self.conditions.get(&entity.0).cloned()
        }

        fn read_turn_budget(&self, entity: &EntityRef) -> Option<TurnBudget> {
            self.turn_budgets.get(&entity.0).cloned()
        }

        fn read_enabled_options(&self) -> Vec<String> {
            self.enabled_options.clone()
        }

        fn position_eq(&self, a: &Value, b: &Value) -> bool {
            // For testing: compare as (i64, i64) grid positions
            if let (Value::Position(pa), Value::Position(pb)) = (a, b) {
                if let (Some(a), Some(b)) = (
                    pa.0.downcast_ref::<(i64, i64)>(),
                    pb.0.downcast_ref::<(i64, i64)>(),
                ) {
                    return a == b;
                }
            }
            false
        }

        fn distance(&self, a: &Value, b: &Value) -> Option<i64> {
            if let (Value::Position(pa), Value::Position(pb)) = (a, b) {
                if let (Some(a), Some(b)) = (
                    pa.0.downcast_ref::<(i64, i64)>(),
                    pb.0.downcast_ref::<(i64, i64)>(),
                ) {
                    return Some(std::cmp::max((a.0 - b.0).abs(), (a.1 - b.1).abs()));
                }
            }
            None
        }
    }

    // Helpers to build test environments

    fn empty_program() -> Program {
        Program { items: vec![] }
    }

    fn empty_type_env() -> TypeEnv {
        TypeEnv::new()
    }

    fn dummy_span() -> Span {
        Span::dummy()
    }

    fn spanned<T>(node: T) -> Spanned<T> {
        Spanned::new(node, dummy_span())
    }

    fn make_env<'a, 'p>(
        state: &'a TestState,
        handler: &'a mut ScriptedHandler,
        interp: &'a Interpreter<'p>,
    ) -> Env<'a, 'p> {
        Env::new(state, handler, interp)
    }

    // ── Literal tests ──────────────────────────────────────────

    #[test]
    fn eval_int_lit() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::IntLit(42));
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(42));
    }

    #[test]
    fn eval_string_lit() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::StringLit("hello".to_string()));
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Str("hello".to_string()));
    }

    #[test]
    fn eval_bool_lit() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::BoolLit(true));
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));

        let expr = spanned(ExprKind::BoolLit(false));
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(false));
    }

    #[test]
    fn eval_none_lit() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::NoneLit);
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::None);
    }

    #[test]
    fn eval_dice_lit() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::DiceLit {
            count: 2,
            sides: 6,
            filter: None,
        });
        let result = eval_expr(&mut env, &expr).unwrap();
        match result {
            Value::DiceExpr(de) => {
                assert_eq!(de.count, 2);
                assert_eq!(de.sides, 6);
                assert_eq!(de.modifier, 0);
                assert!(de.filter.is_none());
            }
            _ => panic!("expected DiceExpr, got {:?}", result),
        }
    }

    #[test]
    fn eval_paren() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::Paren(Box::new(spanned(ExprKind::IntLit(99)))));
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(99));
    }

    // ── Ident tests ────────────────────────────────────────────

    #[test]
    fn eval_ident_from_scope() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("x".to_string(), Value::Int(10));

        let expr = spanned(ExprKind::Ident("x".to_string()));
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(10));
    }

    #[test]
    fn eval_ident_undefined() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::Ident("unknown".to_string()));
        let err = eval_expr(&mut env, &expr).unwrap_err();
        assert!(err.message.contains("undefined variable 'unknown'"));
    }

    // ── Unary operator tests ───────────────────────────────────

    #[test]
    fn eval_unary_neg_int() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::UnaryOp {
            op: UnaryOp::Neg,
            operand: Box::new(spanned(ExprKind::IntLit(5))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(-5));
    }

    #[test]
    fn eval_unary_neg_float() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::UnaryOp {
            op: UnaryOp::Neg,
            operand: Box::new(spanned(ExprKind::IntLit(0))),
        });
        // Test that -0 works for int
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(0));
    }

    #[test]
    fn eval_unary_not() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::UnaryOp {
            op: UnaryOp::Not,
            operand: Box::new(spanned(ExprKind::BoolLit(true))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(false));
    }

    // ── Arithmetic tests ───────────────────────────────────────

    #[test]
    fn eval_add_int() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::BinOp {
            op: BinOp::Add,
            lhs: Box::new(spanned(ExprKind::IntLit(3))),
            rhs: Box::new(spanned(ExprKind::IntLit(4))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(7));
    }

    #[test]
    fn eval_sub_int() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::BinOp {
            op: BinOp::Sub,
            lhs: Box::new(spanned(ExprKind::IntLit(10))),
            rhs: Box::new(spanned(ExprKind::IntLit(3))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(7));
    }

    #[test]
    fn eval_mul_int() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::BinOp {
            op: BinOp::Mul,
            lhs: Box::new(spanned(ExprKind::IntLit(6))),
            rhs: Box::new(spanned(ExprKind::IntLit(7))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(42));
    }

    #[test]
    fn eval_div_int_promotes_to_float() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::BinOp {
            op: BinOp::Div,
            lhs: Box::new(spanned(ExprKind::IntLit(7))),
            rhs: Box::new(spanned(ExprKind::IntLit(2))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Float(3.5));
    }

    #[test]
    fn eval_string_concatenation() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::BinOp {
            op: BinOp::Add,
            lhs: Box::new(spanned(ExprKind::StringLit("hello".to_string()))),
            rhs: Box::new(spanned(ExprKind::StringLit(" world".to_string()))),
        });
        assert_eq!(
            eval_expr(&mut env, &expr).unwrap(),
            Value::Str("hello world".to_string())
        );
    }

    #[test]
    fn eval_mixed_int_float_arithmetic() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // Int + Float promotes to Float
        env.bind("x".to_string(), Value::Int(3));
        env.bind("y".to_string(), Value::Float(1.5));

        let expr = spanned(ExprKind::BinOp {
            op: BinOp::Add,
            lhs: Box::new(spanned(ExprKind::Ident("x".to_string()))),
            rhs: Box::new(spanned(ExprKind::Ident("y".to_string()))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Float(4.5));
    }

    // ── Overflow tests ─────────────────────────────────────────

    #[test]
    fn eval_integer_overflow_add() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::BinOp {
            op: BinOp::Add,
            lhs: Box::new(spanned(ExprKind::IntLit(i64::MAX))),
            rhs: Box::new(spanned(ExprKind::IntLit(1))),
        });
        let err = eval_expr(&mut env, &expr).unwrap_err();
        assert!(err.message.contains("overflow"));
    }

    #[test]
    fn eval_integer_overflow_mul() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::BinOp {
            op: BinOp::Mul,
            lhs: Box::new(spanned(ExprKind::IntLit(i64::MAX))),
            rhs: Box::new(spanned(ExprKind::IntLit(2))),
        });
        let err = eval_expr(&mut env, &expr).unwrap_err();
        assert!(err.message.contains("overflow"));
    }

    #[test]
    fn eval_integer_overflow_sub() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::BinOp {
            op: BinOp::Sub,
            lhs: Box::new(spanned(ExprKind::IntLit(i64::MIN))),
            rhs: Box::new(spanned(ExprKind::IntLit(1))),
        });
        let err = eval_expr(&mut env, &expr).unwrap_err();
        assert!(err.message.contains("overflow"));
    }

    #[test]
    fn eval_integer_overflow_neg() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::UnaryOp {
            op: UnaryOp::Neg,
            operand: Box::new(spanned(ExprKind::IntLit(i64::MIN))),
        });
        let err = eval_expr(&mut env, &expr).unwrap_err();
        assert!(err.message.contains("overflow"));
    }

    // ── Division by zero tests ─────────────────────────────────

    #[test]
    fn eval_div_by_zero_int() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::BinOp {
            op: BinOp::Div,
            lhs: Box::new(spanned(ExprKind::IntLit(10))),
            rhs: Box::new(spanned(ExprKind::IntLit(0))),
        });
        let err = eval_expr(&mut env, &expr).unwrap_err();
        assert!(err.message.contains("division by zero"));
    }

    // ── Comparison tests ───────────────────────────────────────

    #[test]
    fn eval_comparisons() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // 3 < 5 = true
        let expr = spanned(ExprKind::BinOp {
            op: BinOp::Lt,
            lhs: Box::new(spanned(ExprKind::IntLit(3))),
            rhs: Box::new(spanned(ExprKind::IntLit(5))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));

        // 5 <= 5 = true
        let expr = spanned(ExprKind::BinOp {
            op: BinOp::LtEq,
            lhs: Box::new(spanned(ExprKind::IntLit(5))),
            rhs: Box::new(spanned(ExprKind::IntLit(5))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));

        // 5 > 3 = true
        let expr = spanned(ExprKind::BinOp {
            op: BinOp::Gt,
            lhs: Box::new(spanned(ExprKind::IntLit(5))),
            rhs: Box::new(spanned(ExprKind::IntLit(3))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));

        // 3 >= 5 = false
        let expr = spanned(ExprKind::BinOp {
            op: BinOp::GtEq,
            lhs: Box::new(spanned(ExprKind::IntLit(3))),
            rhs: Box::new(spanned(ExprKind::IntLit(5))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(false));
    }

    // ── Equality tests ─────────────────────────────────────────

    #[test]
    fn eval_equality_int() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::BinOp {
            op: BinOp::Eq,
            lhs: Box::new(spanned(ExprKind::IntLit(5))),
            rhs: Box::new(spanned(ExprKind::IntLit(5))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));

        let expr = spanned(ExprKind::BinOp {
            op: BinOp::NotEq,
            lhs: Box::new(spanned(ExprKind::IntLit(5))),
            rhs: Box::new(spanned(ExprKind::IntLit(3))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));
    }

    #[test]
    fn eval_equality_float_neg_zero() {
        // Semantic equality: -0.0 == +0.0 (standard f64)
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("a".to_string(), Value::Float(-0.0));
        env.bind("b".to_string(), Value::Float(0.0));

        let expr = spanned(ExprKind::BinOp {
            op: BinOp::Eq,
            lhs: Box::new(spanned(ExprKind::Ident("a".to_string()))),
            rhs: Box::new(spanned(ExprKind::Ident("b".to_string()))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));
    }

    #[test]
    fn eval_equality_position_delegation() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // Two different Arc allocations with same logical position
        let pos1 = Value::Position(PositionValue(Arc::new((1i64, 2i64))));
        let pos2 = Value::Position(PositionValue(Arc::new((1i64, 2i64))));

        env.bind("p1".to_string(), pos1);
        env.bind("p2".to_string(), pos2);

        let expr = spanned(ExprKind::BinOp {
            op: BinOp::Eq,
            lhs: Box::new(spanned(ExprKind::Ident("p1".to_string()))),
            rhs: Box::new(spanned(ExprKind::Ident("p2".to_string()))),
        });
        // TestState's position_eq compares the underlying (i64, i64)
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));
    }

    // ── Logical operator tests ─────────────────────────────────

    #[test]
    fn eval_logical_and_short_circuit() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // false && (error) should short-circuit — never evaluate RHS
        let expr = spanned(ExprKind::BinOp {
            op: BinOp::And,
            lhs: Box::new(spanned(ExprKind::BoolLit(false))),
            rhs: Box::new(spanned(ExprKind::Ident("undefined_var".to_string()))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(false));
    }

    #[test]
    fn eval_logical_or_short_circuit() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // true || (error) should short-circuit
        let expr = spanned(ExprKind::BinOp {
            op: BinOp::Or,
            lhs: Box::new(spanned(ExprKind::BoolLit(true))),
            rhs: Box::new(spanned(ExprKind::Ident("undefined_var".to_string()))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));
    }

    #[test]
    fn eval_logical_and_both_true() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::BinOp {
            op: BinOp::And,
            lhs: Box::new(spanned(ExprKind::BoolLit(true))),
            rhs: Box::new(spanned(ExprKind::BoolLit(true))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));
    }

    // ── In operator tests ──────────────────────────────────────

    #[test]
    fn eval_in_list() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind(
            "items".to_string(),
            Value::List(vec![Value::Int(1), Value::Int(2), Value::Int(3)]),
        );

        // 2 in items => true
        let expr = spanned(ExprKind::BinOp {
            op: BinOp::In,
            lhs: Box::new(spanned(ExprKind::IntLit(2))),
            rhs: Box::new(spanned(ExprKind::Ident("items".to_string()))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));

        // 5 in items => false
        let expr = spanned(ExprKind::BinOp {
            op: BinOp::In,
            lhs: Box::new(spanned(ExprKind::IntLit(5))),
            rhs: Box::new(spanned(ExprKind::Ident("items".to_string()))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(false));
    }

    #[test]
    fn eval_in_set() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let mut s = std::collections::BTreeSet::new();
        s.insert(Value::Str("a".into()));
        s.insert(Value::Str("b".into()));
        env.bind("my_set".to_string(), Value::Set(s));

        let expr = spanned(ExprKind::BinOp {
            op: BinOp::In,
            lhs: Box::new(spanned(ExprKind::StringLit("a".to_string()))),
            rhs: Box::new(spanned(ExprKind::Ident("my_set".to_string()))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));
    }

    #[test]
    fn eval_in_map() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let mut m = BTreeMap::new();
        m.insert(Value::Str("key".into()), Value::Int(1));
        env.bind("my_map".to_string(), Value::Map(m));

        // "key" in my_map => true
        let expr = spanned(ExprKind::BinOp {
            op: BinOp::In,
            lhs: Box::new(spanned(ExprKind::StringLit("key".to_string()))),
            rhs: Box::new(spanned(ExprKind::Ident("my_map".to_string()))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));
    }

    // ── RollResult coercion tests ──────────────────────────────

    #[test]
    fn eval_roll_result_coercion_in_arithmetic() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let rr = Value::RollResult(RollResult {
            expr: DiceExpr {
                count: 1,
                sides: 20,
                filter: None,
                modifier: 5,
            },
            dice: vec![15],
            kept: vec![15],
            modifier: 5,
            total: 20,
            unmodified: 15,
        });
        env.bind("roll".to_string(), rr);

        // roll + 2 should coerce RollResult to 20, then add 2
        let expr = spanned(ExprKind::BinOp {
            op: BinOp::Add,
            lhs: Box::new(spanned(ExprKind::Ident("roll".to_string()))),
            rhs: Box::new(spanned(ExprKind::IntLit(2))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(22));
    }

    #[test]
    fn eval_roll_result_coercion_in_comparison() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let rr = Value::RollResult(RollResult {
            expr: DiceExpr {
                count: 1,
                sides: 20,
                filter: None,
                modifier: 5,
            },
            dice: vec![15],
            kept: vec![15],
            modifier: 5,
            total: 20,
            unmodified: 15,
        });
        env.bind("roll".to_string(), rr);

        // roll >= 10 should be true (20 >= 10)
        let expr = spanned(ExprKind::BinOp {
            op: BinOp::GtEq,
            lhs: Box::new(spanned(ExprKind::Ident("roll".to_string()))),
            rhs: Box::new(spanned(ExprKind::IntLit(10))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));
    }

    // ── Field access tests ─────────────────────────────────────

    #[test]
    fn eval_field_access_entity() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let mut state = TestState::new();
        state.fields.insert((1, "HP".into()), Value::Int(30));

        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("target".to_string(), Value::Entity(EntityRef(1)));

        let expr = spanned(ExprKind::FieldAccess {
            object: Box::new(spanned(ExprKind::Ident("target".to_string()))),
            field: "HP".to_string(),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(30));
    }

    #[test]
    fn eval_field_access_struct() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let mut fields = BTreeMap::new();
        fields.insert("x".to_string(), Value::Int(10));
        fields.insert("y".to_string(), Value::Int(20));
        env.bind(
            "point".to_string(),
            Value::Struct {
                name: "Point".to_string(),
                fields,
            },
        );

        let expr = spanned(ExprKind::FieldAccess {
            object: Box::new(spanned(ExprKind::Ident("point".to_string()))),
            field: "x".to_string(),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(10));
    }

    #[test]
    fn eval_field_access_roll_result() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let rr = Value::RollResult(RollResult {
            expr: DiceExpr {
                count: 2,
                sides: 6,
                filter: None,
                modifier: 3,
            },
            dice: vec![4, 5],
            kept: vec![4, 5],
            modifier: 3,
            total: 12,
            unmodified: 9,
        });
        env.bind("result".to_string(), rr);

        // .total
        let expr = spanned(ExprKind::FieldAccess {
            object: Box::new(spanned(ExprKind::Ident("result".to_string()))),
            field: "total".to_string(),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(12));

        // .unmodified
        let expr = spanned(ExprKind::FieldAccess {
            object: Box::new(spanned(ExprKind::Ident("result".to_string()))),
            field: "unmodified".to_string(),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(9));

        // .dice
        let expr = spanned(ExprKind::FieldAccess {
            object: Box::new(spanned(ExprKind::Ident("result".to_string()))),
            field: "dice".to_string(),
        });
        assert_eq!(
            eval_expr(&mut env, &expr).unwrap(),
            Value::List(vec![Value::Int(4), Value::Int(5)])
        );
    }

    #[test]
    fn eval_field_access_turn_budget() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind(
            "budget".to_string(),
            Value::TurnBudget(TurnBudget::default()),
        );

        let expr = spanned(ExprKind::FieldAccess {
            object: Box::new(spanned(ExprKind::Ident("budget".to_string()))),
            field: "actions".to_string(),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(1));
    }

    // ── Index tests ────────────────────────────────────────────

    #[test]
    fn eval_index_list() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind(
            "items".to_string(),
            Value::List(vec![Value::Int(10), Value::Int(20), Value::Int(30)]),
        );

        let expr = spanned(ExprKind::Index {
            object: Box::new(spanned(ExprKind::Ident("items".to_string()))),
            index: Box::new(spanned(ExprKind::IntLit(1))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(20));
    }

    #[test]
    fn eval_index_list_out_of_bounds() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("items".to_string(), Value::List(vec![Value::Int(10)]));

        let expr = spanned(ExprKind::Index {
            object: Box::new(spanned(ExprKind::Ident("items".to_string()))),
            index: Box::new(spanned(ExprKind::IntLit(5))),
        });
        let err = eval_expr(&mut env, &expr).unwrap_err();
        assert!(err.message.contains("out of bounds"));
    }

    #[test]
    fn eval_index_map() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let mut m = BTreeMap::new();
        m.insert(Value::Str("STR".into()), Value::Int(18));
        env.bind("stats".to_string(), Value::Map(m));

        let expr = spanned(ExprKind::Index {
            object: Box::new(spanned(ExprKind::Ident("stats".to_string()))),
            index: Box::new(spanned(ExprKind::StringLit("STR".to_string()))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(18));
    }

    #[test]
    fn eval_index_map_missing_key() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let m = BTreeMap::new();
        env.bind("stats".to_string(), Value::Map(m));

        let expr = spanned(ExprKind::Index {
            object: Box::new(spanned(ExprKind::Ident("stats".to_string()))),
            index: Box::new(spanned(ExprKind::StringLit("DEX".to_string()))),
        });
        let err = eval_expr(&mut env, &expr).unwrap_err();
        assert!(err.message.contains("not found"));
    }

    // ── List literal tests ─────────────────────────────────────

    #[test]
    fn eval_list_lit() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::ListLit(vec![
            spanned(ExprKind::IntLit(1)),
            spanned(ExprKind::IntLit(2)),
            spanned(ExprKind::IntLit(3)),
        ]));
        assert_eq!(
            eval_expr(&mut env, &expr).unwrap(),
            Value::List(vec![Value::Int(1), Value::Int(2), Value::Int(3)])
        );
    }

    // ── Struct literal tests ───────────────────────────────────

    #[test]
    fn eval_struct_lit() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::StructLit {
            name: "Point".to_string(),
            fields: vec![
                StructFieldInit {
                    name: "x".to_string(),
                    value: spanned(ExprKind::IntLit(10)),
                    span: dummy_span(),
                },
                StructFieldInit {
                    name: "y".to_string(),
                    value: spanned(ExprKind::IntLit(20)),
                    span: dummy_span(),
                },
            ],
        });
        let result = eval_expr(&mut env, &expr).unwrap();
        match &result {
            Value::Struct { name, fields } => {
                assert_eq!(name, "Point");
                assert_eq!(fields.get("x"), Some(&Value::Int(10)));
                assert_eq!(fields.get("y"), Some(&Value::Int(20)));
            }
            _ => panic!("expected Struct, got {:?}", result),
        }
    }

    // ── If expression tests ────────────────────────────────────

    #[test]
    fn eval_if_true_branch() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::If {
            condition: Box::new(spanned(ExprKind::BoolLit(true))),
            then_block: spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::IntLit(1))))]),
            else_branch: Some(ElseBranch::Block(spanned(vec![spanned(
                StmtKind::Expr(spanned(ExprKind::IntLit(2))),
            )]))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(1));
    }

    #[test]
    fn eval_if_false_branch() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::If {
            condition: Box::new(spanned(ExprKind::BoolLit(false))),
            then_block: spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::IntLit(1))))]),
            else_branch: Some(ElseBranch::Block(spanned(vec![spanned(
                StmtKind::Expr(spanned(ExprKind::IntLit(2))),
            )]))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(2));
    }

    #[test]
    fn eval_if_no_else_returns_none() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::If {
            condition: Box::new(spanned(ExprKind::BoolLit(false))),
            then_block: spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::IntLit(1))))]),
            else_branch: None,
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::None);
    }

    // ── Guard match tests ──────────────────────────────────────

    #[test]
    fn eval_guard_match_first_matching() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("x".to_string(), Value::Int(15));

        let expr = spanned(ExprKind::GuardMatch {
            arms: vec![
                GuardArm {
                    guard: GuardKind::Expr(spanned(ExprKind::BinOp {
                        op: BinOp::GtEq,
                        lhs: Box::new(spanned(ExprKind::Ident("x".to_string()))),
                        rhs: Box::new(spanned(ExprKind::IntLit(10))),
                    })),
                    body: ArmBody::Expr(spanned(ExprKind::StringLit("high".to_string()))),
                    span: dummy_span(),
                },
                GuardArm {
                    guard: GuardKind::Expr(spanned(ExprKind::BinOp {
                        op: BinOp::GtEq,
                        lhs: Box::new(spanned(ExprKind::Ident("x".to_string()))),
                        rhs: Box::new(spanned(ExprKind::IntLit(7))),
                    })),
                    body: ArmBody::Expr(spanned(ExprKind::StringLit("medium".to_string()))),
                    span: dummy_span(),
                },
                GuardArm {
                    guard: GuardKind::Wildcard,
                    body: ArmBody::Expr(spanned(ExprKind::StringLit("low".to_string()))),
                    span: dummy_span(),
                },
            ],
        });
        assert_eq!(
            eval_expr(&mut env, &expr).unwrap(),
            Value::Str("high".to_string())
        );
    }

    #[test]
    fn eval_guard_match_wildcard_fallthrough() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("x".to_string(), Value::Int(3));

        let expr = spanned(ExprKind::GuardMatch {
            arms: vec![
                GuardArm {
                    guard: GuardKind::Expr(spanned(ExprKind::BinOp {
                        op: BinOp::GtEq,
                        lhs: Box::new(spanned(ExprKind::Ident("x".to_string()))),
                        rhs: Box::new(spanned(ExprKind::IntLit(10))),
                    })),
                    body: ArmBody::Expr(spanned(ExprKind::StringLit("high".to_string()))),
                    span: dummy_span(),
                },
                GuardArm {
                    guard: GuardKind::Wildcard,
                    body: ArmBody::Expr(spanned(ExprKind::StringLit("low".to_string()))),
                    span: dummy_span(),
                },
            ],
        });
        assert_eq!(
            eval_expr(&mut env, &expr).unwrap(),
            Value::Str("low".to_string())
        );
    }

    // ── Pattern match tests ────────────────────────────────────

    #[test]
    fn eval_pattern_match_int() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::PatternMatch {
            scrutinee: Box::new(spanned(ExprKind::IntLit(2))),
            arms: vec![
                PatternArm {
                    pattern: spanned(PatternKind::IntLit(1)),
                    body: ArmBody::Expr(spanned(ExprKind::StringLit("one".to_string()))),
                    span: dummy_span(),
                },
                PatternArm {
                    pattern: spanned(PatternKind::IntLit(2)),
                    body: ArmBody::Expr(spanned(ExprKind::StringLit("two".to_string()))),
                    span: dummy_span(),
                },
                PatternArm {
                    pattern: spanned(PatternKind::Wildcard),
                    body: ArmBody::Expr(spanned(ExprKind::StringLit("other".to_string()))),
                    span: dummy_span(),
                },
            ],
        });
        assert_eq!(
            eval_expr(&mut env, &expr).unwrap(),
            Value::Str("two".to_string())
        );
    }

    #[test]
    fn eval_pattern_match_binding() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // match 42 { x => x + 1 }
        let expr = spanned(ExprKind::PatternMatch {
            scrutinee: Box::new(spanned(ExprKind::IntLit(42))),
            arms: vec![PatternArm {
                pattern: spanned(PatternKind::Ident("x".to_string())),
                body: ArmBody::Expr(spanned(ExprKind::BinOp {
                    op: BinOp::Add,
                    lhs: Box::new(spanned(ExprKind::Ident("x".to_string()))),
                    rhs: Box::new(spanned(ExprKind::IntLit(1))),
                })),
                span: dummy_span(),
            }],
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(43));
    }

    #[test]
    fn eval_pattern_match_wildcard() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::PatternMatch {
            scrutinee: Box::new(spanned(ExprKind::IntLit(999))),
            arms: vec![PatternArm {
                pattern: spanned(PatternKind::Wildcard),
                body: ArmBody::Expr(spanned(ExprKind::StringLit("caught".to_string()))),
                span: dummy_span(),
            }],
        });
        assert_eq!(
            eval_expr(&mut env, &expr).unwrap(),
            Value::Str("caught".to_string())
        );
    }

    #[test]
    fn eval_pattern_match_qualified_variant() {
        let program = empty_program();
        let mut type_env = empty_type_env();

        // Register Duration enum with fieldless variants
        type_env.types.insert(
            "Duration".to_string(),
            DeclInfo::Enum(EnumInfo {
                name: "Duration".to_string(),
                variants: vec![
                    VariantInfo {
                        name: "end_of_turn".to_string(),
                        fields: vec![],
                    },
                    VariantInfo {
                        name: "indefinite".to_string(),
                        fields: vec![],
                    },
                ],
            }),
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let val = Value::EnumVariant {
            enum_name: "Duration".to_string(),
            variant: "end_of_turn".to_string(),
            fields: BTreeMap::new(),
        };
        env.bind("dur".to_string(), val);

        let expr = spanned(ExprKind::PatternMatch {
            scrutinee: Box::new(spanned(ExprKind::Ident("dur".to_string()))),
            arms: vec![
                PatternArm {
                    pattern: spanned(PatternKind::QualifiedVariant {
                        ty: "Duration".to_string(),
                        variant: "end_of_turn".to_string(),
                    }),
                    body: ArmBody::Expr(spanned(ExprKind::StringLit("eot".to_string()))),
                    span: dummy_span(),
                },
                PatternArm {
                    pattern: spanned(PatternKind::Wildcard),
                    body: ArmBody::Expr(spanned(ExprKind::StringLit("other".to_string()))),
                    span: dummy_span(),
                },
            ],
        });
        assert_eq!(
            eval_expr(&mut env, &expr).unwrap(),
            Value::Str("eot".to_string())
        );
    }

    #[test]
    fn eval_pattern_match_qualified_destructure() {
        let program = empty_program();
        let mut type_env = empty_type_env();

        type_env.types.insert(
            "Duration".to_string(),
            DeclInfo::Enum(EnumInfo {
                name: "Duration".to_string(),
                variants: vec![VariantInfo {
                    name: "rounds".to_string(),
                    fields: vec![("n".to_string(), ttrpg_checker::ty::Ty::Int)],
                }],
            }),
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let mut fields = BTreeMap::new();
        fields.insert("n".to_string(), Value::Int(3));
        let val = Value::EnumVariant {
            enum_name: "Duration".to_string(),
            variant: "rounds".to_string(),
            fields,
        };
        env.bind("dur".to_string(), val);

        // match dur { Duration.rounds(count) => count }
        let expr = spanned(ExprKind::PatternMatch {
            scrutinee: Box::new(spanned(ExprKind::Ident("dur".to_string()))),
            arms: vec![PatternArm {
                pattern: spanned(PatternKind::QualifiedDestructure {
                    ty: "Duration".to_string(),
                    variant: "rounds".to_string(),
                    fields: vec![spanned(PatternKind::Ident("count".to_string()))],
                }),
                body: ArmBody::Expr(spanned(ExprKind::Ident("count".to_string()))),
                span: dummy_span(),
            }],
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(3));
    }

    // ── Let statement tests ────────────────────────────────────

    #[test]
    fn eval_let_binding() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // Simulate: let x = 42; x + 1
        let block = spanned(vec![
            spanned(StmtKind::Let {
                name: "x".to_string(),
                ty: None,
                value: spanned(ExprKind::IntLit(42)),
            }),
            spanned(StmtKind::Expr(spanned(ExprKind::BinOp {
                op: BinOp::Add,
                lhs: Box::new(spanned(ExprKind::Ident("x".to_string()))),
                rhs: Box::new(spanned(ExprKind::IntLit(1))),
            }))),
        ]);
        assert_eq!(eval_block(&mut env, &block).unwrap(), Value::Int(43));
    }

    #[test]
    fn eval_nested_scopes() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // let x = 1; { let x = 2; x } + x should be 3
        // But we need to use two block evaluations to test scope isolation
        env.bind("x".to_string(), Value::Int(1));
        let inner_block = spanned(vec![
            spanned(StmtKind::Let {
                name: "x".to_string(),
                ty: None,
                value: spanned(ExprKind::IntLit(2)),
            }),
            spanned(StmtKind::Expr(spanned(ExprKind::Ident("x".to_string())))),
        ]);
        let inner_result = eval_block(&mut env, &inner_block).unwrap();
        assert_eq!(inner_result, Value::Int(2));

        // After inner block, x should still be 1
        let outer_x = env.lookup("x").unwrap().clone();
        assert_eq!(outer_x, Value::Int(1));
    }

    // ── Call stub test ─────────────────────────────────────────

    #[test]
    fn eval_call_returns_stub_error() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("foo".to_string()))),
            args: vec![],
        });
        let err = eval_expr(&mut env, &expr).unwrap_err();
        assert!(err.message.contains("not yet implemented"));
    }

    // ── value_eq unit tests ────────────────────────────────────

    #[test]
    fn value_eq_float_neg_zero() {
        let state = TestState::new();
        assert!(value_eq(&state, &Value::Float(-0.0), &Value::Float(0.0)));
    }

    #[test]
    fn value_eq_float_nan() {
        let state = TestState::new();
        assert!(!value_eq(&state, &Value::Float(f64::NAN), &Value::Float(f64::NAN)));
    }

    #[test]
    fn value_eq_position_delegates() {
        let state = TestState::new();
        let p1 = Value::Position(PositionValue(Arc::new((5i64, 10i64))));
        let p2 = Value::Position(PositionValue(Arc::new((5i64, 10i64))));
        assert!(value_eq(&state, &p1, &p2)); // same logical position

        let p3 = Value::Position(PositionValue(Arc::new((5i64, 11i64))));
        assert!(!value_eq(&state, &p1, &p3)); // different position
    }

    #[test]
    fn value_eq_composite_recursive() {
        let state = TestState::new();
        let a = Value::List(vec![Value::Float(-0.0), Value::Int(1)]);
        let b = Value::List(vec![Value::Float(0.0), Value::Int(1)]);
        assert!(value_eq(&state, &a, &b)); // -0.0 == +0.0 via value_eq
    }

    // ── Bare enum variant ident test ───────────────────────────

    #[test]
    fn eval_bare_fieldless_variant() {
        let program = empty_program();
        let mut type_env = empty_type_env();

        type_env.types.insert(
            "Color".to_string(),
            DeclInfo::Enum(EnumInfo {
                name: "Color".to_string(),
                variants: vec![
                    VariantInfo {
                        name: "red".to_string(),
                        fields: vec![],
                    },
                    VariantInfo {
                        name: "blue".to_string(),
                        fields: vec![],
                    },
                ],
            }),
        );
        type_env
            .variant_to_enum
            .insert("red".to_string(), "Color".to_string());
        type_env
            .variant_to_enum
            .insert("blue".to_string(), "Color".to_string());

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::Ident("red".to_string()));
        let result = eval_expr(&mut env, &expr).unwrap();
        assert_eq!(
            result,
            Value::EnumVariant {
                enum_name: "Color".to_string(),
                variant: "red".to_string(),
                fields: BTreeMap::new(),
            }
        );
    }

    // ── Qualified enum field access ────────────────────────────

    #[test]
    fn eval_qualified_enum_variant_via_field_access() {
        let program = empty_program();
        let mut type_env = empty_type_env();

        type_env.types.insert(
            "Color".to_string(),
            DeclInfo::Enum(EnumInfo {
                name: "Color".to_string(),
                variants: vec![VariantInfo {
                    name: "red".to_string(),
                    fields: vec![],
                }],
            }),
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // Color.red
        let expr = spanned(ExprKind::FieldAccess {
            object: Box::new(spanned(ExprKind::Ident("Color".to_string()))),
            field: "red".to_string(),
        });
        assert_eq!(
            eval_expr(&mut env, &expr).unwrap(),
            Value::EnumVariant {
                enum_name: "Color".to_string(),
                variant: "red".to_string(),
                fields: BTreeMap::new(),
            }
        );
    }

    // ── Interpreter construction ───────────────────────────────

    #[test]
    fn interpreter_rejects_surviving_move() {
        use ttrpg_ast::ast::{MoveDecl, TopLevel, SystemBlock};

        let program = Program {
            items: vec![spanned(TopLevel::System(SystemBlock {
                name: "Test".to_string(),
                decls: vec![spanned(DeclKind::Move(MoveDecl {
                    name: "TestMove".to_string(),
                    receiver_name: "actor".to_string(),
                    receiver_type: spanned(ttrpg_ast::ast::TypeExpr::Named("Character".to_string())),
                    params: vec![],
                    trigger_text: "test".to_string(),
                    roll_expr: spanned(ExprKind::IntLit(0)),
                    outcomes: vec![],
                }))],
            }))],
        };
        let type_env = empty_type_env();
        match Interpreter::new(&program, &type_env) {
            Err(err) => assert!(err.message.contains("must be lowered")),
            Ok(_) => panic!("expected error for surviving Move decl"),
        }
    }

    // ── Enum variant field access ──────────────────────────────

    #[test]
    fn eval_field_access_enum_variant() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let mut fields = BTreeMap::new();
        fields.insert("n".to_string(), Value::Int(5));
        env.bind(
            "d".to_string(),
            Value::EnumVariant {
                enum_name: "Duration".to_string(),
                variant: "rounds".to_string(),
                fields,
            },
        );

        let expr = spanned(ExprKind::FieldAccess {
            object: Box::new(spanned(ExprKind::Ident("d".to_string()))),
            field: "n".to_string(),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(5));
    }

    // ── Dice literal with filter ───────────────────────────────

    #[test]
    fn eval_dice_lit_with_filter() {
        use ttrpg_ast::DiceFilter;

        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::DiceLit {
            count: 4,
            sides: 6,
            filter: Some(DiceFilter::KeepHighest(3)),
        });
        let result = eval_expr(&mut env, &expr).unwrap();
        match result {
            Value::DiceExpr(de) => {
                assert_eq!(de.count, 4);
                assert_eq!(de.sides, 6);
                assert_eq!(de.filter, Some(DiceFilter::KeepHighest(3)));
            }
            _ => panic!("expected DiceExpr"),
        }
    }

    // ── If with else-if chain ──────────────────────────────────

    #[test]
    fn eval_if_else_if_chain() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // if false { 1 } else if true { 2 } else { 3 }
        // This is: If { cond: false, then: 1, else: If { cond: true, then: 2, else: 3 } }
        let expr = spanned(ExprKind::If {
            condition: Box::new(spanned(ExprKind::BoolLit(false))),
            then_block: spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::IntLit(1))))]),
            else_branch: Some(ElseBranch::If(Box::new(spanned(ExprKind::If {
                condition: Box::new(spanned(ExprKind::BoolLit(true))),
                then_block: spanned(vec![spanned(StmtKind::Expr(spanned(
                    ExprKind::IntLit(2),
                )))]),
                else_branch: Some(ElseBranch::Block(spanned(vec![spanned(
                    StmtKind::Expr(spanned(ExprKind::IntLit(3))),
                )]))),
            })))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(2));
    }

    // ── Bare enum variant pattern tests ────────────────────────

    #[test]
    fn eval_pattern_bare_variant_matches() {
        let program = empty_program();
        let mut type_env = empty_type_env();
        type_env.types.insert(
            "Color".to_string(),
            ttrpg_checker::env::DeclInfo::Enum(EnumInfo {
                name: "Color".to_string(),
                variants: vec![
                    VariantInfo { name: "red".to_string(), fields: vec![] },
                    VariantInfo { name: "blue".to_string(), fields: vec![] },
                ],
            }),
        );
        type_env.variant_to_enum.insert("red".to_string(), "Color".to_string());
        type_env.variant_to_enum.insert("blue".to_string(), "Color".to_string());

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // Pattern match with bare variant idents: match val { red => 1, blue => 2 }
        let val = Value::EnumVariant {
            enum_name: "Color".to_string(),
            variant: "blue".to_string(),
            fields: BTreeMap::new(),
        };
        env.bind("val".to_string(), val);

        let expr = spanned(ExprKind::PatternMatch {
            scrutinee: Box::new(spanned(ExprKind::Ident("val".to_string()))),
            arms: vec![
                PatternArm {
                    pattern: spanned(PatternKind::Ident("red".to_string())),
                    body: ArmBody::Expr(spanned(ExprKind::IntLit(1))),
                    span: dummy_span(),
                },
                PatternArm {
                    pattern: spanned(PatternKind::Ident("blue".to_string())),
                    body: ArmBody::Expr(spanned(ExprKind::IntLit(2))),
                    span: dummy_span(),
                },
            ],
        });
        // `blue` should match the second arm, NOT the first (red should NOT act as a binding)
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(2));
    }

    #[test]
    fn eval_pattern_bare_variant_no_match() {
        let program = empty_program();
        let mut type_env = empty_type_env();
        type_env.types.insert(
            "Color".to_string(),
            ttrpg_checker::env::DeclInfo::Enum(EnumInfo {
                name: "Color".to_string(),
                variants: vec![
                    VariantInfo { name: "red".to_string(), fields: vec![] },
                ],
            }),
        );
        type_env.variant_to_enum.insert("red".to_string(), "Color".to_string());

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let env = make_env(&state, &mut handler, &interp);

        // Try to match `red` against an Int — should not match
        let mut bindings = HashMap::new();
        let result = match_pattern(
            &env,
            &PatternKind::Ident("red".to_string()),
            &Value::Int(42),
            &mut bindings,
        );
        assert!(!result);
        assert!(bindings.is_empty());
    }

    #[test]
    fn eval_pattern_binding_still_works_for_non_variant() {
        let program = empty_program();
        let type_env = empty_type_env();
        // No variants registered — "x" is purely a binding
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let env = make_env(&state, &mut handler, &interp);

        let mut bindings = HashMap::new();
        let result = match_pattern(
            &env,
            &PatternKind::Ident("x".to_string()),
            &Value::Int(42),
            &mut bindings,
        );
        assert!(result);
        assert_eq!(bindings.get("x"), Some(&Value::Int(42)));
    }

    // ── DiceExpr arithmetic tests ──────────────────────────────

    #[test]
    fn eval_dice_add_int() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind(
            "d".to_string(),
            Value::DiceExpr(DiceExpr { count: 1, sides: 20, filter: None, modifier: 0 }),
        );

        // d + 5
        let expr = spanned(ExprKind::BinOp {
            op: BinOp::Add,
            lhs: Box::new(spanned(ExprKind::Ident("d".to_string()))),
            rhs: Box::new(spanned(ExprKind::IntLit(5))),
        });
        match eval_expr(&mut env, &expr).unwrap() {
            Value::DiceExpr(de) => {
                assert_eq!(de.count, 1);
                assert_eq!(de.sides, 20);
                assert_eq!(de.modifier, 5);
            }
            other => panic!("expected DiceExpr, got {:?}", other),
        }
    }

    #[test]
    fn eval_int_add_dice() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind(
            "d".to_string(),
            Value::DiceExpr(DiceExpr { count: 2, sides: 6, filter: None, modifier: 3 }),
        );

        // 10 + d
        let expr = spanned(ExprKind::BinOp {
            op: BinOp::Add,
            lhs: Box::new(spanned(ExprKind::IntLit(10))),
            rhs: Box::new(spanned(ExprKind::Ident("d".to_string()))),
        });
        match eval_expr(&mut env, &expr).unwrap() {
            Value::DiceExpr(de) => {
                assert_eq!(de.count, 2);
                assert_eq!(de.sides, 6);
                assert_eq!(de.modifier, 13);
            }
            other => panic!("expected DiceExpr, got {:?}", other),
        }
    }

    #[test]
    fn eval_dice_add_dice() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind(
            "a".to_string(),
            Value::DiceExpr(DiceExpr { count: 2, sides: 6, filter: None, modifier: 1 }),
        );
        env.bind(
            "b".to_string(),
            Value::DiceExpr(DiceExpr { count: 3, sides: 6, filter: None, modifier: 2 }),
        );

        // a + b → 5d6 with modifier 3
        let expr = spanned(ExprKind::BinOp {
            op: BinOp::Add,
            lhs: Box::new(spanned(ExprKind::Ident("a".to_string()))),
            rhs: Box::new(spanned(ExprKind::Ident("b".to_string()))),
        });
        match eval_expr(&mut env, &expr).unwrap() {
            Value::DiceExpr(de) => {
                assert_eq!(de.count, 5);
                assert_eq!(de.sides, 6);
                assert_eq!(de.modifier, 3);
            }
            other => panic!("expected DiceExpr, got {:?}", other),
        }
    }

    #[test]
    fn eval_dice_sub_int() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind(
            "d".to_string(),
            Value::DiceExpr(DiceExpr { count: 1, sides: 20, filter: None, modifier: 5 }),
        );

        // d - 3
        let expr = spanned(ExprKind::BinOp {
            op: BinOp::Sub,
            lhs: Box::new(spanned(ExprKind::Ident("d".to_string()))),
            rhs: Box::new(spanned(ExprKind::IntLit(3))),
        });
        match eval_expr(&mut env, &expr).unwrap() {
            Value::DiceExpr(de) => {
                assert_eq!(de.count, 1);
                assert_eq!(de.sides, 20);
                assert_eq!(de.modifier, 2);
            }
            other => panic!("expected DiceExpr, got {:?}", other),
        }
    }

    // ── GuardMatch non-bool guard error test ───────────────────

    #[test]
    fn eval_guard_match_non_bool_error() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // match { 42 => ... } — guard evaluates to Int, not Bool
        let expr = spanned(ExprKind::GuardMatch {
            arms: vec![GuardArm {
                guard: GuardKind::Expr(spanned(ExprKind::IntLit(42))),
                body: ArmBody::Expr(spanned(ExprKind::IntLit(1))),
                span: dummy_span(),
            }],
        });
        let err = eval_expr(&mut env, &expr).unwrap_err();
        assert!(err.message.contains("guard expression must be Bool"));
    }

    // ── Scope cleanup on error test ────────────────────────────

    #[test]
    fn eval_block_error_cleans_scope() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let scope_depth_before = env.scopes.len();

        // Block that contains an error (undefined variable)
        let block: ttrpg_ast::ast::Block = spanned(vec![
            spanned(StmtKind::Expr(spanned(ExprKind::Ident("undefined_var".to_string())))),
        ]);
        let result = eval_block(&mut env, &block);
        assert!(result.is_err());

        // Scope stack should be restored to its pre-block state
        assert_eq!(env.scopes.len(), scope_depth_before);
    }

    #[test]
    fn eval_pattern_match_error_in_arm_cleans_scope() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let scope_depth_before = env.scopes.len();

        // Pattern match where the matched arm body errors
        let expr = spanned(ExprKind::PatternMatch {
            scrutinee: Box::new(spanned(ExprKind::IntLit(1))),
            arms: vec![PatternArm {
                pattern: spanned(PatternKind::Wildcard),
                body: ArmBody::Expr(spanned(ExprKind::Ident("undefined_var".to_string()))),
                span: dummy_span(),
            }],
        });
        let result = eval_expr(&mut env, &expr);
        assert!(result.is_err());

        // Scope stack should be restored
        assert_eq!(env.scopes.len(), scope_depth_before);
    }

    // ── Issue fix: qualified enum access respects scoping ──────

    #[test]
    fn eval_qualified_enum_access_via_paren() {
        // (Color).red should work — parenthesized enum namespace access
        let program = empty_program();
        let mut type_env = empty_type_env();
        type_env.types.insert(
            "Color".to_string(),
            DeclInfo::Enum(EnumInfo {
                name: "Color".to_string(),
                variants: vec![
                    VariantInfo {
                        name: "red".to_string(),
                        fields: vec![],
                    },
                ],
            }),
        );
        type_env
            .variant_to_enum
            .insert("red".to_string(), "Color".to_string());

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // (Color).red — parenthesized
        let expr = spanned(ExprKind::FieldAccess {
            object: Box::new(spanned(ExprKind::Paren(Box::new(spanned(
                ExprKind::Ident("Color".to_string()),
            ))))),
            field: "red".to_string(),
        });
        let result = eval_expr(&mut env, &expr).unwrap();
        assert_eq!(
            result,
            Value::EnumVariant {
                enum_name: "Color".to_string(),
                variant: "red".to_string(),
                fields: BTreeMap::new(),
            }
        );
    }

    #[test]
    fn eval_qualified_enum_access_shadowed_by_local() {
        // If a local variable shadows an enum type name, field access
        // should resolve the local, not the enum namespace.
        let program = empty_program();
        let mut type_env = empty_type_env();
        type_env.types.insert(
            "Color".to_string(),
            DeclInfo::Enum(EnumInfo {
                name: "Color".to_string(),
                variants: vec![
                    VariantInfo {
                        name: "red".to_string(),
                        fields: vec![],
                    },
                ],
            }),
        );
        type_env
            .variant_to_enum
            .insert("red".to_string(), "Color".to_string());

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // Bind "Color" as a local struct value
        let mut struct_fields = BTreeMap::new();
        struct_fields.insert("name".to_string(), Value::Str("my_color".to_string()));
        env.bind(
            "Color".to_string(),
            Value::Struct {
                name: "MyStruct".to_string(),
                fields: struct_fields,
            },
        );

        // Color.name should resolve local struct, not enum namespace
        let expr = spanned(ExprKind::FieldAccess {
            object: Box::new(spanned(ExprKind::Ident("Color".to_string()))),
            field: "name".to_string(),
        });
        let result = eval_expr(&mut env, &expr).unwrap();
        assert_eq!(result, Value::Str("my_color".to_string()));
    }

    #[test]
    fn eval_enum_namespace_not_usable_as_value() {
        // Using an enum type name as a standalone expression (not in field access)
        // should produce an EnumNamespace value (which would fail in most contexts).
        let program = empty_program();
        let mut type_env = empty_type_env();
        type_env.types.insert(
            "Color".to_string(),
            DeclInfo::Enum(EnumInfo {
                name: "Color".to_string(),
                variants: vec![],
            }),
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::Ident("Color".to_string()));
        let result = eval_expr(&mut env, &expr).unwrap();
        assert!(matches!(result, Value::EnumNamespace(ref s) if s == "Color"));
    }

    // ── Issue fix: RollResult coercion not applied to `in` ────

    #[test]
    fn eval_in_roll_result_no_coercion() {
        // `roll_result in list<RollResult>` should match structurally,
        // not coerce to Int first.
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let roll = Value::RollResult(RollResult {
            expr: DiceExpr {
                count: 1,
                sides: 20,
                filter: None,
                modifier: 0,
            },
            dice: vec![15],
            kept: vec![15],
            modifier: 0,
            total: 15,
            unmodified: 15,
        });

        env.bind("r".to_string(), roll.clone());
        env.bind("rolls".to_string(), Value::List(vec![roll]));

        let expr = spanned(ExprKind::BinOp {
            op: BinOp::In,
            lhs: Box::new(spanned(ExprKind::Ident("r".to_string()))),
            rhs: Box::new(spanned(ExprKind::Ident("rolls".to_string()))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));
    }

    #[test]
    fn eval_in_roll_result_not_in_int_list() {
        // `roll_result in list<Int>` should be false (different types),
        // not coerced-true.
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let roll = Value::RollResult(RollResult {
            expr: DiceExpr {
                count: 1,
                sides: 20,
                filter: None,
                modifier: 0,
            },
            dice: vec![15],
            kept: vec![15],
            modifier: 0,
            total: 15,
            unmodified: 15,
        });

        env.bind("r".to_string(), roll);
        // List contains Int(15) — same total but different type
        env.bind("ints".to_string(), Value::List(vec![Value::Int(15)]));

        let expr = spanned(ExprKind::BinOp {
            op: BinOp::In,
            lhs: Box::new(spanned(ExprKind::Ident("r".to_string()))),
            rhs: Box::new(spanned(ExprKind::Ident("ints".to_string()))),
        });
        // Should be false — RollResult != Int even though total matches
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(false));
    }

    // ── Issue fix: dice arithmetic overflow and spec validation ──

    #[test]
    fn eval_dice_add_dice_different_sides_error() {
        // 2d6 + 3d8 should error — different dice specs
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind(
            "a".to_string(),
            Value::DiceExpr(DiceExpr {
                count: 2,
                sides: 6,
                filter: None,
                modifier: 0,
            }),
        );
        env.bind(
            "b".to_string(),
            Value::DiceExpr(DiceExpr {
                count: 3,
                sides: 8,
                filter: None,
                modifier: 0,
            }),
        );

        let expr = spanned(ExprKind::BinOp {
            op: BinOp::Add,
            lhs: Box::new(spanned(ExprKind::Ident("a".to_string()))),
            rhs: Box::new(spanned(ExprKind::Ident("b".to_string()))),
        });
        let result = eval_expr(&mut env, &expr);
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .message
            .contains("different specs"));
    }

    #[test]
    fn eval_dice_add_int_overflow() {
        // DiceExpr with modifier near i64::MAX + Int should overflow
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind(
            "d".to_string(),
            Value::DiceExpr(DiceExpr {
                count: 1,
                sides: 20,
                filter: None,
                modifier: i64::MAX,
            }),
        );

        let expr = spanned(ExprKind::BinOp {
            op: BinOp::Add,
            lhs: Box::new(spanned(ExprKind::Ident("d".to_string()))),
            rhs: Box::new(spanned(ExprKind::IntLit(1))),
        });
        let result = eval_expr(&mut env, &expr);
        assert!(result.is_err());
        assert!(result.unwrap_err().message.contains("overflow"));
    }

    #[test]
    fn eval_dice_sub_int_overflow() {
        // DiceExpr with modifier near i64::MIN - Int should overflow
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind(
            "d".to_string(),
            Value::DiceExpr(DiceExpr {
                count: 1,
                sides: 20,
                filter: None,
                modifier: i64::MIN,
            }),
        );

        let expr = spanned(ExprKind::BinOp {
            op: BinOp::Sub,
            lhs: Box::new(spanned(ExprKind::Ident("d".to_string()))),
            rhs: Box::new(spanned(ExprKind::IntLit(1))),
        });
        let result = eval_expr(&mut env, &expr);
        assert!(result.is_err());
        assert!(result.unwrap_err().message.contains("overflow"));
    }

    #[test]
    fn eval_dice_add_dice_count_overflow() {
        // Two DiceExpr with u32::MAX counts should overflow
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind(
            "a".to_string(),
            Value::DiceExpr(DiceExpr {
                count: u32::MAX,
                sides: 6,
                filter: None,
                modifier: 0,
            }),
        );
        env.bind(
            "b".to_string(),
            Value::DiceExpr(DiceExpr {
                count: 1,
                sides: 6,
                filter: None,
                modifier: 0,
            }),
        );

        let expr = spanned(ExprKind::BinOp {
            op: BinOp::Add,
            lhs: Box::new(spanned(ExprKind::Ident("a".to_string()))),
            rhs: Box::new(spanned(ExprKind::Ident("b".to_string()))),
        });
        let result = eval_expr(&mut env, &expr);
        assert!(result.is_err());
        assert!(result.unwrap_err().message.contains("overflow"));
    }

    #[test]
    fn eval_dice_add_dice_same_spec_succeeds() {
        // 2d6+1 + 3d6+2 = 5d6+3 — same spec, should merge
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind(
            "a".to_string(),
            Value::DiceExpr(DiceExpr {
                count: 2,
                sides: 6,
                filter: None,
                modifier: 1,
            }),
        );
        env.bind(
            "b".to_string(),
            Value::DiceExpr(DiceExpr {
                count: 3,
                sides: 6,
                filter: None,
                modifier: 2,
            }),
        );

        let expr = spanned(ExprKind::BinOp {
            op: BinOp::Add,
            lhs: Box::new(spanned(ExprKind::Ident("a".to_string()))),
            rhs: Box::new(spanned(ExprKind::Ident("b".to_string()))),
        });
        let result = eval_expr(&mut env, &expr).unwrap();
        assert_eq!(
            result,
            Value::DiceExpr(DiceExpr {
                count: 5,
                sides: 6,
                filter: None,
                modifier: 3,
            })
        );
    }

    // ── Issue 1: == / != coerce RollResult; Int↔Float equality ──

    #[test]
    fn eq_coerces_roll_result_to_int() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // Bind `r` to a RollResult with total=10
        env.bind(
            "r".to_string(),
            Value::RollResult(RollResult {
                expr: DiceExpr { count: 1, sides: 20, filter: None, modifier: 0 },
                dice: vec![10],
                kept: vec![10],
                modifier: 0,
                total: 10,
                unmodified: 10,
            }),
        );

        // r == 10 should be true (coerced)
        let expr = spanned(ExprKind::BinOp {
            op: BinOp::Eq,
            lhs: Box::new(spanned(ExprKind::Ident("r".to_string()))),
            rhs: Box::new(spanned(ExprKind::IntLit(10))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));

        // r != 10 should be false
        let expr = spanned(ExprKind::BinOp {
            op: BinOp::NotEq,
            lhs: Box::new(spanned(ExprKind::Ident("r".to_string()))),
            rhs: Box::new(spanned(ExprKind::IntLit(10))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(false));

        // r == 99 should be false
        let expr = spanned(ExprKind::BinOp {
            op: BinOp::Eq,
            lhs: Box::new(spanned(ExprKind::Ident("r".to_string()))),
            rhs: Box::new(spanned(ExprKind::IntLit(99))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(false));
    }

    #[test]
    fn value_eq_int_float_cross_type() {
        let state = TestState::new();
        assert!(value_eq(&state, &Value::Int(1), &Value::Float(1.0)));
        assert!(value_eq(&state, &Value::Float(1.0), &Value::Int(1)));
        assert!(!value_eq(&state, &Value::Int(1), &Value::Float(1.5)));
        assert!(!value_eq(&state, &Value::Float(1.5), &Value::Int(1)));
    }

    // ── Issue 2: Enum ordering uses declaration order ───────────

    #[test]
    fn enum_ordering_uses_declaration_order() {
        let program = empty_program();
        let mut type_env = empty_type_env();

        // Declare enum Size { small, medium, large }
        // Declaration order: small=0, medium=1, large=2
        // Alphabetical would be: large < medium < small — opposite!
        type_env.types.insert(
            "Size".to_string(),
            DeclInfo::Enum(EnumInfo {
                name: "Size".to_string(),
                variants: vec![
                    VariantInfo { name: "small".to_string(), fields: vec![] },
                    VariantInfo { name: "medium".to_string(), fields: vec![] },
                    VariantInfo { name: "large".to_string(), fields: vec![] },
                ],
            }),
        );
        type_env.variant_to_enum.insert("small".to_string(), "Size".to_string());
        type_env.variant_to_enum.insert("medium".to_string(), "Size".to_string());
        type_env.variant_to_enum.insert("large".to_string(), "Size".to_string());

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("a".to_string(), Value::EnumVariant {
            enum_name: "Size".to_string(),
            variant: "small".to_string(),
            fields: BTreeMap::new(),
        });
        env.bind("b".to_string(), Value::EnumVariant {
            enum_name: "Size".to_string(),
            variant: "large".to_string(),
            fields: BTreeMap::new(),
        });

        // small < large should be true (declaration order: 0 < 2)
        let expr = spanned(ExprKind::BinOp {
            op: BinOp::Lt,
            lhs: Box::new(spanned(ExprKind::Ident("a".to_string()))),
            rhs: Box::new(spanned(ExprKind::Ident("b".to_string()))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));

        // large > small should be true
        let expr = spanned(ExprKind::BinOp {
            op: BinOp::Gt,
            lhs: Box::new(spanned(ExprKind::Ident("b".to_string()))),
            rhs: Box::new(spanned(ExprKind::Ident("a".to_string()))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));

        // small >= large should be false
        let expr = spanned(ExprKind::BinOp {
            op: BinOp::GtEq,
            lhs: Box::new(spanned(ExprKind::Ident("a".to_string()))),
            rhs: Box::new(spanned(ExprKind::Ident("b".to_string()))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(false));
    }

    // ── Issue 3: none == Option(None) ───────────────────────────

    #[test]
    fn value_eq_none_vs_option_none() {
        let state = TestState::new();

        // Value::None == Value::Option(None)
        assert!(value_eq(&state, &Value::None, &Value::Option(None)));
        assert!(value_eq(&state, &Value::Option(None), &Value::None));

        // Value::None != Value::Option(Some(...))
        assert!(!value_eq(
            &state,
            &Value::None,
            &Value::Option(Some(Box::new(Value::Int(1))))
        ));
        assert!(!value_eq(
            &state,
            &Value::Option(Some(Box::new(Value::Int(1)))),
            &Value::None
        ));
    }

    #[test]
    fn binop_eq_none_vs_option_none() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("x".to_string(), Value::Option(None));

        // x == none should be true
        let expr = spanned(ExprKind::BinOp {
            op: BinOp::Eq,
            lhs: Box::new(spanned(ExprKind::Ident("x".to_string()))),
            rhs: Box::new(spanned(ExprKind::NoneLit)),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));

        // x != none should be false
        let expr = spanned(ExprKind::BinOp {
            op: BinOp::NotEq,
            lhs: Box::new(spanned(ExprKind::Ident("x".to_string()))),
            rhs: Box::new(spanned(ExprKind::NoneLit)),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(false));
    }
}
