use std::collections::BTreeMap;

use ttrpg_ast::Spanned;
use ttrpg_ast::ast::{
    ArmBody, AssignOp, BinOp, DeclKind, ElseBranch, ExprKind, ForIterable, GuardKind, LValue,
    LValueSegment, OptionalGroup, PatternKind, TopLevel, UnaryOp,
};
use ttrpg_checker::env::DeclInfo;

use crate::Env;
use crate::RuntimeError;
use crate::effect::{Effect, FieldPathSegment, Response};
use crate::state::{EntityRef, StateProvider};
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

        ExprKind::Call { callee, args } => {
            crate::call::eval_call(env, callee, args, expr.span)
        }

        ExprKind::For {
            pattern,
            iterable,
            body,
        } => eval_for(env, pattern, iterable, body),

        ExprKind::Has { entity, group_name } => {
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

    // 4. Check if it's a condition name
    if env.interp.program.conditions.contains_key(name) {
        return Ok(Value::Condition(name.to_string()));
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
        (Value::Int(a), Value::Float(b)) => int_float_cmp(*a, *b)
            .ok_or_else(|| RuntimeError::with_span("cannot compare NaN", expr.span))?,
        (Value::Float(a), Value::Int(b)) => int_float_cmp(*b, *a)
            .ok_or_else(|| RuntimeError::with_span("cannot compare NaN", expr.span))?
            .reverse(),
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
            "expr" => Ok(Value::DiceExpr(r.expr.clone())),
            _ => Err(RuntimeError::with_span(
                format!("RollResult has no field '{}'", field),
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
        (Value::Map(map), key) => {
            // Use semantic equality (value_eq) for lookup so that e.g. none
            // and option<T>.none are treated as the same key, consistent with `in`.
            map.iter()
                .find(|(k, _)| value_eq(env.state, k, key))
                .map(|(_, v)| v.clone())
                .ok_or_else(|| {
                    RuntimeError::with_span(
                        format!("map key {:?} not found", key),
                        expr.span,
                    )
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

fn eval_if_let(
    env: &mut Env,
    pattern: &Spanned<PatternKind>,
    scrutinee: &Spanned<ExprKind>,
    then_block: &ttrpg_ast::ast::Block,
    else_branch: &Option<ElseBranch>,
) -> Result<Value, RuntimeError> {
    let scrutinee_val = eval_expr(env, scrutinee)?;
    let mut bindings = std::collections::HashMap::new();

    if match_pattern(env, &pattern.node, &scrutinee_val, &mut bindings) {
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

fn eval_for(
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
        ForIterable::Range { start, end } => {
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
            (s..e).map(Value::Int).collect()
        }
    };

    for item in items {
        let mut bindings = std::collections::HashMap::new();
        if match_pattern(env, &pattern.node, &item, &mut bindings) {
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
        StmtKind::Assign { target, op, value } => {
            eval_assign(env, target, *op, value, stmt.span)?;
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
            let defaults: Vec<_> = find_optional_group(env, entity_type.as_deref(), group_name)
                .into_iter()
                .flat_map(|g| g.fields.iter())
                .filter(|fd| !fields.contains_key(&fd.name) && fd.default.is_some())
                .map(|fd| (fd.name.clone(), fd.default.clone().unwrap()))
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
            match response {
                Response::Vetoed => {
                    return Err(RuntimeError::with_span(
                        format!("grant {} was vetoed by host", group_name),
                        stmt.span,
                    ))
                }
                _ => {}
            }
            Ok(Value::None)
        }
        StmtKind::Revoke {
            entity,
            group_name,
        } => {
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
            match response {
                Response::Vetoed => {
                    return Err(RuntimeError::with_span(
                        format!("revoke {} was vetoed by host", group_name),
                        stmt.span,
                    ))
                }
                _ => {}
            }
            Ok(Value::None)
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

// ── Assignment ─────────────────────────────────────────────────

/// Execute an assignment statement.
///
/// Dispatches to one of three mutation paths:
/// - **Turn path**: root is `"turn"` → emit `MutateTurnField`
/// - **Entity path**: root resolves to Entity → emit `MutateField`
/// - **Local path**: root resolves to local value → mutate in-place
///
/// For nested paths (e.g. `trigger.entity.HP -= 5`), the local path
/// walks into the value until it encounters an Entity, then switches
/// to the entity mutation path for the remaining segments.
fn eval_assign(
    env: &mut Env,
    target: &LValue,
    op: AssignOp,
    value: &Spanned<ExprKind>,
    span: ttrpg_ast::Span,
) -> Result<(), RuntimeError> {
    let rhs = eval_expr(env, value)?;

    // ── Turn budget mutation path ───────────────────────────
    if target.root == "turn" {
        return eval_assign_turn(env, target, op, rhs, span);
    }

    // ── Direct variable reassignment (no segments) ──────────
    if target.segments.is_empty() {
        return eval_assign_direct(env, &target.root, op, rhs, span);
    }

    // ── Look up the root value ──────────────────────────────
    // We need to check if the root is an entity (entity mutation path)
    // or a local value (local mutation path).
    let root_val = env.lookup(&target.root).cloned();
    match root_val {
        Some(Value::Entity(entity_ref)) => {
            // Entity mutation: all segments become FieldPathSegments
            eval_assign_entity(env, entity_ref, &target.segments, op, rhs, span)
        }
        Some(_) => {
            // Local mutation path: walk segments, switching to entity
            // mutation if we encounter an Entity along the way
            eval_assign_local(env, &target.root, &target.segments, op, rhs, span)
        }
        None => Err(RuntimeError::with_span(
            format!("undefined variable `{}`", target.root),
            span,
        )),
    }
}

/// Turn budget mutation: `turn.actions -= 1`
fn eval_assign_turn(
    env: &mut Env,
    target: &LValue,
    op: AssignOp,
    rhs: Value,
    span: ttrpg_ast::Span,
) -> Result<(), RuntimeError> {
    let actor = env.turn_actor.ok_or_else(|| {
        RuntimeError::with_span(
            "cannot access `turn` outside of action/reaction context",
            span,
        )
    })?;

    // First segment must be a field name
    let field = match target.segments.first() {
        Some(LValueSegment::Field(name)) => name.clone(),
        Some(LValueSegment::Index(_)) => {
            return Err(RuntimeError::with_span(
                "turn budget fields must be accessed by name, not index",
                span,
            ));
        }
        None => {
            return Err(RuntimeError::with_span(
                "cannot reassign `turn` directly; mutate individual fields (e.g. turn.actions -= 1)",
                span,
            ));
        }
    };

    // Turn path only supports a single field segment
    if target.segments.len() > 1 {
        return Err(RuntimeError::with_span(
            "turn budget fields do not support nested access",
            span,
        ));
    }

    let effect = Effect::MutateTurnField {
        actor,
        field,
        op,
        value: rhs,
    };
    env.handler.handle(effect);

    Ok(())
}

/// Direct variable reassignment with no segments: `x = 5`, `x += 1`
fn eval_assign_direct(
    env: &mut Env,
    name: &str,
    op: AssignOp,
    rhs: Value,
    span: ttrpg_ast::Span,
) -> Result<(), RuntimeError> {
    let var = env.lookup_mut(name).ok_or_else(|| {
        RuntimeError::with_span(format!("undefined variable `{}`", name), span)
    })?;

    let new_val = apply_assign_op(op, var.clone(), rhs, span)?;
    *var = new_val;
    Ok(())
}

/// Entity field mutation: convert segments to FieldPathSegments and emit MutateField.
fn eval_assign_entity(
    env: &mut Env,
    entity: EntityRef,
    segments: &[LValueSegment],
    op: AssignOp,
    rhs: Value,
    span: ttrpg_ast::Span,
) -> Result<(), RuntimeError> {
    let path = lvalue_segments_to_field_path(env, segments, span)?;

    // Resource bounds: the plan calls for looking up bounds from TypeEnv,
    // but Ty::Resource doesn't carry bound values, and evaluating AST bound
    // expressions may require derive calls (Phase 4). Pass None for now;
    // the host/adapter is responsible for clamping independently.
    let bounds = None;

    let effect = Effect::MutateField {
        entity,
        path,
        op,
        value: rhs,
        bounds,
    };
    env.handler.handle(effect);

    Ok(())
}

/// Convert LValue segments to FieldPathSegments for entity mutation effects.
fn lvalue_segments_to_field_path(
    env: &mut Env,
    segments: &[LValueSegment],
    span: ttrpg_ast::Span,
) -> Result<Vec<FieldPathSegment>, RuntimeError> {
    let mut path = Vec::with_capacity(segments.len());
    for seg in segments {
        match seg {
            LValueSegment::Field(name) => {
                path.push(FieldPathSegment::Field(name.clone()));
            }
            LValueSegment::Index(idx_expr) => {
                let idx_val = eval_expr(env, idx_expr)?;
                path.push(FieldPathSegment::Index(idx_val));
            }
        }
    }
    if path.is_empty() {
        return Err(RuntimeError::with_span(
            "entity mutation requires at least one field segment",
            span,
        ));
    }
    Ok(path)
}

/// A pre-evaluated LValue segment (index expressions already resolved to Values).
enum EvalSegment {
    Field(String),
    Index(Value),
}

/// Local variable mutation path.
///
/// Pre-evaluates all index expressions, then walks the local value.
/// If an Entity is encountered along the way, the remaining segments
/// become an entity mutation via `eval_assign_entity_from_eval_segs`.
fn eval_assign_local(
    env: &mut Env,
    root_name: &str,
    segments: &[LValueSegment],
    op: AssignOp,
    rhs: Value,
    span: ttrpg_ast::Span,
) -> Result<(), RuntimeError> {
    // Pre-evaluate all index expressions so we don't need env during mutation walk
    let eval_segs = eval_segments(env, segments)?;

    // Walk the value (read-only) to check for entities in the path
    let entity_depth = find_entity_depth(env, root_name, &eval_segs, span, env.state)?;

    if let Some((depth, entity_ref)) = entity_depth {
        // Convert remaining EvalSegments to FieldPathSegments for entity mutation
        let path: Vec<FieldPathSegment> = eval_segs[depth..]
            .iter()
            .map(|s| match s {
                EvalSegment::Field(name) => FieldPathSegment::Field(name.clone()),
                EvalSegment::Index(val) => FieldPathSegment::Index(val.clone()),
            })
            .collect();

        if path.is_empty() {
            return Err(RuntimeError::with_span(
                "entity mutation requires at least one field segment",
                span,
            ));
        }

        let effect = Effect::MutateField {
            entity: entity_ref,
            path,
            op,
            value: rhs,
            bounds: None,
        };
        env.handler.handle(effect);
        return Ok(());
    }

    // Pure local mutation: navigate into the value and apply the op
    // Copy the shared state reference before taking &mut on env via lookup_mut.
    let state = env.state;
    let root = env.lookup_mut(root_name).ok_or_else(|| {
        RuntimeError::with_span(format!("undefined variable `{}`", root_name), span)
    })?;

    apply_local_mutation(root, &eval_segs, 0, op, rhs, span, state)
}

/// Pre-evaluate all index expressions in LValue segments.
fn eval_segments(
    env: &mut Env,
    segments: &[LValueSegment],
) -> Result<Vec<EvalSegment>, RuntimeError> {
    let mut result = Vec::with_capacity(segments.len());
    for seg in segments {
        match seg {
            LValueSegment::Field(name) => {
                result.push(EvalSegment::Field(name.clone()));
            }
            LValueSegment::Index(idx_expr) => {
                let val = eval_expr(env, idx_expr)?;
                result.push(EvalSegment::Index(val));
            }
        }
    }
    Ok(result)
}

/// Find the depth at which an Entity is encountered when walking segments.
/// Returns Some((depth, entity_ref)) if found, None if the path is pure local.
fn find_entity_depth(
    env: &Env,
    root_name: &str,
    segments: &[EvalSegment],
    span: ttrpg_ast::Span,
    state: &dyn StateProvider,
) -> Result<Option<(usize, EntityRef)>, RuntimeError> {
    let mut current = env.lookup(root_name).cloned().ok_or_else(|| {
        RuntimeError::with_span(format!("undefined variable `{}`", root_name), span)
    })?;

    for (i, seg) in segments.iter().enumerate() {
        match &current {
            Value::Entity(entity_ref) => {
                return Ok(Some((i, *entity_ref)));
            }
            Value::Struct { fields, .. } => {
                if let EvalSegment::Field(name) = seg {
                    current = fields.get(name.as_str()).cloned().ok_or_else(|| {
                        RuntimeError::with_span(
                            format!("struct has no field `{}`", name),
                            span,
                        )
                    })?;
                } else {
                    return Err(RuntimeError::with_span(
                        "cannot index into a struct",
                        span,
                    ));
                }
            }
            Value::List(list) => {
                if let EvalSegment::Index(idx_val) = seg {
                    let index = resolve_list_index(idx_val, list.len(), span)?;
                    current = list[index].clone();
                } else {
                    return Err(RuntimeError::with_span(
                        "cannot access field on a list; use index instead",
                        span,
                    ));
                }
            }
            Value::Map(map) => {
                if let EvalSegment::Index(key) = seg {
                    // Use semantic equality (value_eq) consistent with read indexing.
                    match map.iter().find(|(k, _)| value_eq(state, k, key)) {
                        Some((_, val)) => current = val.clone(),
                        // Key not in map — no entity can be deeper, so return None.
                        // The actual mutation code handles insert vs compound-assign errors.
                        None => return Ok(None),
                    }
                } else {
                    return Err(RuntimeError::with_span(
                        "cannot access field on a map; use index instead",
                        span,
                    ));
                }
            }
            _ => {
                return Err(RuntimeError::with_span(
                    format!("cannot navigate into {}", type_name(&current)),
                    span,
                ));
            }
        }
    }

    Ok(None)
}

/// Recursively navigate into a local value and apply the assignment at the final depth.
fn apply_local_mutation(
    current: &mut Value,
    segments: &[EvalSegment],
    depth: usize,
    op: AssignOp,
    rhs: Value,
    span: ttrpg_ast::Span,
    state: &dyn StateProvider,
) -> Result<(), RuntimeError> {
    if depth >= segments.len() {
        // We've reached the target — apply the op
        let new_val = apply_assign_op(op, current.clone(), rhs, span)?;
        *current = new_val;
        return Ok(());
    }

    match (&segments[depth], current) {
        (EvalSegment::Field(name), Value::Struct { fields, .. }) => {
            let field = fields.get_mut(name.as_str()).ok_or_else(|| {
                RuntimeError::with_span(
                    format!("struct has no field `{}`", name),
                    span,
                )
            })?;
            apply_local_mutation(field, segments, depth + 1, op, rhs, span, state)
        }
        (EvalSegment::Index(idx_val), Value::List(list)) => {
            let index = resolve_list_index(idx_val, list.len(), span)?;
            apply_local_mutation(&mut list[index], segments, depth + 1, op, rhs, span, state)
        }
        (EvalSegment::Index(key), Value::Map(map)) => {
            // Use semantic equality (value_eq) to find the existing key,
            // consistent with read indexing in eval_index.
            let existing_key = map.keys().find(|k| value_eq(state, k, key)).cloned();
            if depth + 1 >= segments.len() {
                // Final segment — apply the op to the map entry
                match op {
                    AssignOp::Eq => {
                        // Remove existing semantically-equal key (if any) and insert with the new key
                        if let Some(ref ek) = existing_key {
                            map.remove(ek);
                        }
                        map.insert(key.clone(), rhs);
                        Ok(())
                    }
                    AssignOp::PlusEq | AssignOp::MinusEq => {
                        // Entry must exist for compound assignment
                        let ek = existing_key.ok_or_else(|| {
                            RuntimeError::with_span(
                                format!(
                                    "cannot apply {} to absent map key {:?}",
                                    if op == AssignOp::PlusEq { "+=" } else { "-=" },
                                    key,
                                ),
                                span,
                            )
                        })?;
                        let entry = map.get_mut(&ek).unwrap();
                        let new_val = apply_assign_op(op, entry.clone(), rhs, span)?;
                        *entry = new_val;
                        Ok(())
                    }
                }
            } else {
                // Navigate deeper into the map value
                let ek = existing_key.ok_or_else(|| {
                    RuntimeError::with_span(
                        format!("map has no key {:?}", key),
                        span,
                    )
                })?;
                let entry = map.get_mut(&ek).unwrap();
                apply_local_mutation(entry, segments, depth + 1, op, rhs, span, state)
            }
        }
        (EvalSegment::Field(_), other) => {
            Err(RuntimeError::with_span(
                format!("cannot access field on {}", type_name(other)),
                span,
            ))
        }
        (EvalSegment::Index(_), other) => {
            Err(RuntimeError::with_span(
                format!("cannot index into {}", type_name(other)),
                span,
            ))
        }
    }
}

/// Apply an assignment operator to produce a new value.
///
/// - `Eq` → replace with rhs
/// - `PlusEq` → current + rhs (Int/Float, checked overflow)
/// - `MinusEq` → current - rhs (Int/Float, checked overflow)
pub(crate) fn apply_assign_op(
    op: AssignOp,
    current: Value,
    rhs: Value,
    span: ttrpg_ast::Span,
) -> Result<Value, RuntimeError> {
    match op {
        AssignOp::Eq => Ok(rhs),
        AssignOp::PlusEq => {
            // Coerce RollResult to Int for arithmetic
            let current = coerce_roll_result(current);
            let rhs = coerce_roll_result(rhs);
            match (&current, &rhs) {
                (Value::Int(a), Value::Int(b)) => a
                    .checked_add(*b)
                    .map(Value::Int)
                    .ok_or_else(|| RuntimeError::with_span("integer overflow in +=", span)),
                (Value::Float(a), Value::Float(b)) => {
                    let result = a + b;
                    if !result.is_finite() {
                        return Err(RuntimeError::with_span(
                            "float overflow in +=",
                            span,
                        ));
                    }
                    Ok(Value::Float(result))
                }
                (Value::Int(a), Value::Float(b)) | (Value::Float(b), Value::Int(a)) => {
                    let result = (*a as f64) + b;
                    if !result.is_finite() {
                        return Err(RuntimeError::with_span(
                            "float overflow in +=",
                            span,
                        ));
                    }
                    Ok(Value::Float(result))
                }
                _ => Err(RuntimeError::with_span(
                    format!(
                        "cannot apply += to {} and {}",
                        type_name(&current),
                        type_name(&rhs)
                    ),
                    span,
                )),
            }
        }
        AssignOp::MinusEq => {
            let current = coerce_roll_result(current);
            let rhs = coerce_roll_result(rhs);
            match (&current, &rhs) {
                (Value::Int(a), Value::Int(b)) => a
                    .checked_sub(*b)
                    .map(Value::Int)
                    .ok_or_else(|| RuntimeError::with_span("integer overflow in -=", span)),
                (Value::Float(a), Value::Float(b)) => {
                    let result = a - b;
                    if !result.is_finite() {
                        return Err(RuntimeError::with_span(
                            "float overflow in -=",
                            span,
                        ));
                    }
                    Ok(Value::Float(result))
                }
                (Value::Int(a), Value::Float(b)) => {
                    let result = (*a as f64) - b;
                    if !result.is_finite() {
                        return Err(RuntimeError::with_span(
                            "float overflow in -=",
                            span,
                        ));
                    }
                    Ok(Value::Float(result))
                }
                (Value::Float(a), Value::Int(b)) => {
                    let result = a - (*b as f64);
                    if !result.is_finite() {
                        return Err(RuntimeError::with_span(
                            "float overflow in -=",
                            span,
                        ));
                    }
                    Ok(Value::Float(result))
                }
                _ => Err(RuntimeError::with_span(
                    format!(
                        "cannot apply -= to {} and {}",
                        type_name(&current),
                        type_name(&rhs)
                    ),
                    span,
                )),
            }
        }
    }
}

/// Resolve a list index value to a usize, supporting negative indexing.
/// Negative indices count from the end: -1 is last, -len is first.
fn resolve_list_index(
    idx_val: &Value,
    len: usize,
    span: ttrpg_ast::Span,
) -> Result<usize, RuntimeError> {
    match idx_val {
        Value::Int(i) => {
            let i = *i;
            let index = if i >= 0 {
                i as usize
            } else {
                let positive = i.checked_neg().ok_or_else(|| {
                    RuntimeError::with_span(
                        format!("list index {} out of bounds, length {}", i, len),
                        span,
                    )
                })? as usize;
                if positive > len {
                    return Err(RuntimeError::with_span(
                        format!(
                            "list index {} out of bounds, length {}",
                            i, len
                        ),
                        span,
                    ));
                }
                len - positive
            };
            if index >= len {
                return Err(RuntimeError::with_span(
                    format!(
                        "list index {} out of bounds, length {}",
                        i, len
                    ),
                    span,
                ));
            }
            Ok(index)
        }
        _ => Err(RuntimeError::with_span(
            format!("list index must be int, found {}", type_name(idx_val)),
            span,
        )),
    }
}

// ── Exact cross-type int/float helpers ─────────────────────────

/// Exact equality between i64 and f64 without lossy `i64 as f64` cast.
/// Returns false when the float has a fractional part, is non-finite, or
/// falls outside the range exactly representable as i64.
fn int_float_eq(i: i64, f: f64) -> bool {
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
fn int_float_cmp(i: i64, f: f64) -> Option<std::cmp::Ordering> {
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
        (Value::Condition(a), Value::Condition(b)) => a == b,

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

        PatternKind::NoneLit => matches!(value, Value::None | Value::Option(None)),

        PatternKind::Some(inner_pattern) => {
            match value {
                Value::Option(Some(inner_val)) => {
                    match_pattern(env, &inner_pattern.node, inner_val, bindings)
                }
                _ => false,
            }
        }

        PatternKind::Ident(name) => {
            // Check if this ident is a bare enum variant (via variant_to_enum).
            // If so, match against the variant; otherwise bind as a variable.
            if let Some(enum_name) = env.interp.type_env.variant_to_enum.get(name.as_str()) {
                // It's a bare enum variant — match by variant name (checker rejects
                // bare patterns for payload variants, but we match by name as safety net)
                matches!(
                    value,
                    Value::EnumVariant { enum_name: actual_enum, variant, .. }
                    if actual_enum == enum_name && variant == name
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
pub(crate) fn type_name(val: &Value) -> &'static str {
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
        Value::Condition(_) => "Condition",
        Value::EnumNamespace(_) => "EnumNamespace",
    }
}

/// Walk `program.items` to find the `OptionalGroup` definition with the given name,
/// scoped to a specific entity type. Falls back to first global match if no entity
/// type is provided.
fn find_optional_group<'a>(
    env: &'a Env,
    entity_type: Option<&str>,
    group_name: &str,
) -> Option<&'a OptionalGroup> {
    let entity_type = entity_type?;
    for item in &env.interp.program.items {
        if let TopLevel::System(system) = &item.node {
            for decl in &system.decls {
                if let DeclKind::Entity(entity_decl) = &decl.node {
                    if entity_decl.name == entity_type {
                        for group in &entity_decl.optional_groups {
                            if group.name == group_name {
                                return Some(group);
                            }
                        }
                    }
                }
            }
        }
    }
    None
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
    use crate::value::{DiceExpr, PositionValue, RollResult, default_turn_budget};
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
        turn_budgets: HashMap<u64, BTreeMap<String, Value>>,
        enabled_options: Vec<String>,
        entity_type: Option<String>,
    }

    impl TestState {
        fn new() -> Self {
            TestState {
                fields: HashMap::new(),
                conditions: HashMap::new(),
                turn_budgets: HashMap::new(),
                enabled_options: Vec::new(),
                entity_type: None,
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

        fn read_turn_budget(&self, entity: &EntityRef) -> Option<BTreeMap<String, Value>> {
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

        fn entity_type_name(&self, _entity: &EntityRef) -> Option<String> {
            self.entity_type.clone()
        }
    }

    // Helpers to build test environments

    fn empty_program() -> Program {
        Program::default()
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

        env.bind("budget".to_string(), default_turn_budget());

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

    // ── Call dispatch test ──────────────────────────────────────

    #[test]
    fn eval_call_undefined_function_error() {
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
        assert!(err.message.contains("undefined function"));
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
            ..Default::default()
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

    #[test]
    fn value_eq_int_float_boundary() {
        let state = TestState::new();

        // i64::MAX as f64 rounds up to 2^63 — must NOT equal i64::MAX
        let max_f = i64::MAX as f64; // 9223372036854775808.0
        assert!(!value_eq(&state, &Value::Int(i64::MAX), &Value::Float(max_f)));
        assert!(!value_eq(&state, &Value::Float(max_f), &Value::Int(i64::MAX)));

        // i64::MIN as f64 is exactly -2^63 — SHOULD equal i64::MIN
        let min_f = i64::MIN as f64; // -9223372036854775808.0
        assert!(value_eq(&state, &Value::Int(i64::MIN), &Value::Float(min_f)));
        assert!(value_eq(&state, &Value::Float(min_f), &Value::Int(i64::MIN)));

        // Large float above i64 range
        assert!(!value_eq(&state, &Value::Int(i64::MAX), &Value::Float(1.0e19)));
        assert!(!value_eq(&state, &Value::Int(i64::MIN), &Value::Float(-1.0e19)));

        // Largest f64 below 2^63 (still in i64 range) should round-trip correctly
        let largest_below = 9223372036854774784.0_f64; // 2^63 - 1024
        assert!(value_eq(
            &state,
            &Value::Int(9223372036854774784),
            &Value::Float(largest_below),
        ));
        assert!(!value_eq(
            &state,
            &Value::Int(i64::MAX),
            &Value::Float(largest_below),
        ));
    }

    #[test]
    fn int_float_cmp_boundary() {
        use std::cmp::Ordering;

        // i64::MAX < (i64::MAX as f64) because the float rounds up to 2^63
        assert_eq!(int_float_cmp(i64::MAX, i64::MAX as f64), Some(Ordering::Less));

        // i64::MIN == (i64::MIN as f64) because -2^63 is exact
        assert_eq!(int_float_cmp(i64::MIN, i64::MIN as f64), Some(Ordering::Equal));

        // i64::MAX vs very large float
        assert_eq!(int_float_cmp(i64::MAX, 1.0e19), Some(Ordering::Less));

        // i64::MIN vs very negative float
        assert_eq!(int_float_cmp(i64::MIN, -1.0e19), Some(Ordering::Greater));

        // NaN → None
        assert_eq!(int_float_cmp(0, f64::NAN), None);

        // Infinity
        assert_eq!(int_float_cmp(i64::MAX, f64::INFINITY), Some(Ordering::Less));
        assert_eq!(int_float_cmp(i64::MIN, f64::NEG_INFINITY), Some(Ordering::Greater));

        // Largest f64 below 2^63
        let largest_below = 9223372036854774784.0_f64;
        assert_eq!(
            int_float_cmp(9223372036854774784, largest_below),
            Some(Ordering::Equal),
        );
        assert_eq!(
            int_float_cmp(i64::MAX, largest_below),
            Some(Ordering::Greater),
        );
    }

    #[test]
    fn int_float_eq_helper_edge_cases() {
        // Basic exact matches
        assert!(int_float_eq(0, 0.0));
        assert!(int_float_eq(0, -0.0)); // -0.0 == +0.0
        assert!(int_float_eq(-1, -1.0));

        // Fractional → never equal
        assert!(!int_float_eq(1, 1.5));
        assert!(!int_float_eq(0, 0.1));

        // Non-finite → never equal
        assert!(!int_float_eq(0, f64::NAN));
        assert!(!int_float_eq(0, f64::INFINITY));
        assert!(!int_float_eq(0, f64::NEG_INFINITY));

        // 2^53 boundary (largest exact integer in f64)
        let two_53: i64 = 1 << 53;
        assert!(int_float_eq(two_53, two_53 as f64));
        assert!(!int_float_eq(two_53 + 1, (two_53 + 1) as f64));
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

    // ── Condition identifier resolution ───────────────────────

    #[test]
    fn eval_ident_condition_name() {
        use ttrpg_ast::ast::{ConditionDecl, TopLevel, SystemBlock};

        let mut program = Program {
            items: vec![spanned(TopLevel::System(SystemBlock {
                name: "Test".to_string(),
                decls: vec![spanned(DeclKind::Condition(ConditionDecl {
                    name: "Stunned".to_string(),
                    receiver_name: "bearer".to_string(),
                    receiver_type: spanned(TypeExpr::Named("Character".to_string())),
                    receiver_with_groups: vec![],
                    clauses: vec![],
                }))],
            }))],
            ..Default::default()
        };
        program.build_index();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::Ident("Stunned".to_string()));
        assert_eq!(
            eval_expr(&mut env, &expr).unwrap(),
            Value::Condition("Stunned".to_string())
        );
    }

    #[test]
    fn eval_ident_condition_eq() {
        use ttrpg_ast::ast::{ConditionDecl, TopLevel, SystemBlock};

        let mut program = Program {
            items: vec![spanned(TopLevel::System(SystemBlock {
                name: "Test".to_string(),
                decls: vec![
                    spanned(DeclKind::Condition(ConditionDecl {
                        name: "Stunned".to_string(),
                        receiver_name: "bearer".to_string(),
                        receiver_type: spanned(TypeExpr::Named("Character".to_string())),
                        receiver_with_groups: vec![],
                        clauses: vec![],
                    })),
                    spanned(DeclKind::Condition(ConditionDecl {
                        name: "Prone".to_string(),
                        receiver_name: "bearer".to_string(),
                        receiver_type: spanned(TypeExpr::Named("Character".to_string())),
                        receiver_with_groups: vec![],
                        clauses: vec![],
                    })),
                ],
            }))],
            ..Default::default()
        };
        program.build_index();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // Same condition == itself
        let expr = spanned(ExprKind::BinOp {
            op: BinOp::Eq,
            lhs: Box::new(spanned(ExprKind::Ident("Stunned".to_string()))),
            rhs: Box::new(spanned(ExprKind::Ident("Stunned".to_string()))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));

        // Different conditions != each other
        let expr = spanned(ExprKind::BinOp {
            op: BinOp::Eq,
            lhs: Box::new(spanned(ExprKind::Ident("Stunned".to_string()))),
            rhs: Box::new(spanned(ExprKind::Ident("Prone".to_string()))),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(false));
    }

    // ── Phase 3: Statement Execution tests ─────────────────────

    // Helper to build an LValue
    fn make_lvalue(root: &str, segments: Vec<LValueSegment>) -> LValue {
        LValue {
            root: root.to_string(),
            segments,
            span: dummy_span(),
        }
    }

    // Helper to build an Assign statement
    fn make_assign(target: LValue, op: AssignOp, value: Spanned<ExprKind>) -> Spanned<StmtKind> {
        spanned(StmtKind::Assign { target, op, value })
    }

    // Helper to build a Let statement
    fn make_let(name: &str, value: Spanned<ExprKind>) -> Spanned<StmtKind> {
        spanned(StmtKind::Let {
            name: name.to_string(),
            ty: None,
            value,
        })
    }

    // ── Let binding tests ──────────────────────────────────────

    #[test]
    fn assign_let_bindings_visible_in_scope() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // let x = 42
        let stmt = make_let("x", spanned(ExprKind::IntLit(42)));
        eval_stmt(&mut env, &stmt).unwrap();
        assert_eq!(env.lookup("x"), Some(&Value::Int(42)));
    }

    #[test]
    fn assign_nested_scopes_shadowing_and_isolation() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // Bind x = 10 in outer scope
        env.bind("x".to_string(), Value::Int(10));

        // Enter a block: let x = 20 (shadows outer x)
        let block = spanned(vec![
            make_let("x", spanned(ExprKind::IntLit(20))),
            spanned(StmtKind::Expr(spanned(ExprKind::Ident("x".to_string())))),
        ]);
        let result = eval_block(&mut env, &block).unwrap();
        assert_eq!(result, Value::Int(20));

        // After block, outer x is still 10
        assert_eq!(env.lookup("x"), Some(&Value::Int(10)));
    }

    // ── Direct variable reassignment tests ─────────────────────

    #[test]
    fn assign_direct_variable_eq() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // let x = 10; x = 20
        env.bind("x".to_string(), Value::Int(10));
        let stmt = make_assign(
            make_lvalue("x", vec![]),
            AssignOp::Eq,
            spanned(ExprKind::IntLit(20)),
        );
        eval_stmt(&mut env, &stmt).unwrap();
        assert_eq!(env.lookup("x"), Some(&Value::Int(20)));
    }

    #[test]
    fn assign_direct_variable_plus_eq() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("x".to_string(), Value::Int(10));
        let stmt = make_assign(
            make_lvalue("x", vec![]),
            AssignOp::PlusEq,
            spanned(ExprKind::IntLit(5)),
        );
        eval_stmt(&mut env, &stmt).unwrap();
        assert_eq!(env.lookup("x"), Some(&Value::Int(15)));
    }

    #[test]
    fn assign_direct_variable_minus_eq() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("x".to_string(), Value::Int(10));
        let stmt = make_assign(
            make_lvalue("x", vec![]),
            AssignOp::MinusEq,
            spanned(ExprKind::IntLit(3)),
        );
        eval_stmt(&mut env, &stmt).unwrap();
        assert_eq!(env.lookup("x"), Some(&Value::Int(7)));
    }

    #[test]
    fn assign_direct_undefined_variable_error() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let stmt = make_assign(
            make_lvalue("nonexistent", vec![]),
            AssignOp::Eq,
            spanned(ExprKind::IntLit(1)),
        );
        let err = eval_stmt(&mut env, &stmt).unwrap_err();
        assert!(err.message.contains("undefined variable"), "got: {}", err.message);
    }

    // ── Entity field assignment tests ──────────────────────────

    #[test]
    fn assign_entity_field_emits_mutate_field() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let entity_ref = EntityRef(1);
        env.bind("target".to_string(), Value::Entity(entity_ref));

        // target.HP -= 5
        let stmt = make_assign(
            make_lvalue("target", vec![LValueSegment::Field("HP".to_string())]),
            AssignOp::MinusEq,
            spanned(ExprKind::IntLit(5)),
        );
        eval_stmt(&mut env, &stmt).unwrap();

        // Verify MutateField was emitted
        assert_eq!(handler.log.len(), 1);
        match &handler.log[0] {
            Effect::MutateField {
                entity,
                path,
                op,
                value,
                bounds,
            } => {
                assert_eq!(entity.0, 1);
                assert_eq!(path.len(), 1);
                match &path[0] {
                    FieldPathSegment::Field(name) => assert_eq!(name, "HP"),
                    _ => panic!("expected Field segment"),
                }
                assert_eq!(*op, AssignOp::MinusEq);
                assert_eq!(*value, Value::Int(5));
                assert!(bounds.is_none());
            }
            other => panic!("expected MutateField, got {:?}", other),
        }
    }

    #[test]
    fn assign_entity_nested_path_emits_mutate_field() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let entity_ref = EntityRef(42);
        env.bind("target".to_string(), Value::Entity(entity_ref));

        // target.stats[STR] = 18
        let stmt = make_assign(
            make_lvalue("target", vec![
                LValueSegment::Field("stats".to_string()),
                LValueSegment::Index(spanned(ExprKind::StringLit("STR".to_string()))),
            ]),
            AssignOp::Eq,
            spanned(ExprKind::IntLit(18)),
        );
        eval_stmt(&mut env, &stmt).unwrap();

        assert_eq!(handler.log.len(), 1);
        match &handler.log[0] {
            Effect::MutateField { entity, path, op, value, .. } => {
                assert_eq!(entity.0, 42);
                assert_eq!(path.len(), 2);
                match &path[0] {
                    FieldPathSegment::Field(name) => assert_eq!(name, "stats"),
                    _ => panic!("expected Field segment"),
                }
                match &path[1] {
                    FieldPathSegment::Index(val) => assert_eq!(*val, Value::Str("STR".to_string())),
                    _ => panic!("expected Index segment"),
                }
                assert_eq!(*op, AssignOp::Eq);
                assert_eq!(*value, Value::Int(18));
            }
            other => panic!("expected MutateField, got {:?}", other),
        }
    }

    #[test]
    fn assign_entity_through_struct_emits_mutate_field() {
        // trigger.entity.HP -= 5 where trigger is a struct containing an entity
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let entity_ref = EntityRef(7);
        let trigger_struct = Value::Struct {
            name: "__event_Attack".to_string(),
            fields: {
                let mut f = BTreeMap::new();
                f.insert("entity".to_string(), Value::Entity(entity_ref));
                f
            },
        };
        env.bind("trigger".to_string(), trigger_struct);

        // trigger.entity.HP -= 5
        let stmt = make_assign(
            make_lvalue("trigger", vec![
                LValueSegment::Field("entity".to_string()),
                LValueSegment::Field("HP".to_string()),
            ]),
            AssignOp::MinusEq,
            spanned(ExprKind::IntLit(5)),
        );
        eval_stmt(&mut env, &stmt).unwrap();

        // Should emit MutateField with entity=7, path=[Field("HP")]
        assert_eq!(handler.log.len(), 1);
        match &handler.log[0] {
            Effect::MutateField { entity, path, op, value, .. } => {
                assert_eq!(entity.0, 7);
                assert_eq!(path.len(), 1);
                match &path[0] {
                    FieldPathSegment::Field(name) => assert_eq!(name, "HP"),
                    _ => panic!("expected Field segment"),
                }
                assert_eq!(*op, AssignOp::MinusEq);
                assert_eq!(*value, Value::Int(5));
            }
            other => panic!("expected MutateField, got {:?}", other),
        }
    }

    // ── Turn budget mutation tests ─────────────────────────────

    #[test]
    fn assign_turn_field_emits_mutate_turn_field() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.turn_actor = Some(EntityRef(5));

        // turn.actions -= 1
        let stmt = make_assign(
            make_lvalue("turn", vec![LValueSegment::Field("actions".to_string())]),
            AssignOp::MinusEq,
            spanned(ExprKind::IntLit(1)),
        );
        eval_stmt(&mut env, &stmt).unwrap();

        assert_eq!(handler.log.len(), 1);
        match &handler.log[0] {
            Effect::MutateTurnField { actor, field, op, value } => {
                assert_eq!(actor.0, 5);
                assert_eq!(field, "actions");
                assert_eq!(*op, AssignOp::MinusEq);
                assert_eq!(*value, Value::Int(1));
            }
            other => panic!("expected MutateTurnField, got {:?}", other),
        }
    }

    #[test]
    fn assign_turn_without_actor_error() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // No turn_actor set
        let stmt = make_assign(
            make_lvalue("turn", vec![LValueSegment::Field("actions".to_string())]),
            AssignOp::MinusEq,
            spanned(ExprKind::IntLit(1)),
        );
        let err = eval_stmt(&mut env, &stmt).unwrap_err();
        assert!(err.message.contains("turn"), "got: {}", err.message);
    }

    #[test]
    fn assign_turn_no_segments_error() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.turn_actor = Some(EntityRef(1));

        // turn = 5 (no field segment)
        let stmt = make_assign(
            make_lvalue("turn", vec![]),
            AssignOp::Eq,
            spanned(ExprKind::IntLit(5)),
        );
        let err = eval_stmt(&mut env, &stmt).unwrap_err();
        assert!(err.message.contains("turn"), "got: {}", err.message);
    }

    // ── Local struct field mutation tests ──────────────────────

    #[test]
    fn assign_local_struct_field() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let my_struct = Value::Struct {
            name: "Point".to_string(),
            fields: {
                let mut f = BTreeMap::new();
                f.insert("x".to_string(), Value::Int(1));
                f.insert("y".to_string(), Value::Int(2));
                f
            },
        };
        env.bind("p".to_string(), my_struct);

        // p.x = 10
        let stmt = make_assign(
            make_lvalue("p", vec![LValueSegment::Field("x".to_string())]),
            AssignOp::Eq,
            spanned(ExprKind::IntLit(10)),
        );
        eval_stmt(&mut env, &stmt).unwrap();

        match env.lookup("p") {
            Some(Value::Struct { fields, .. }) => {
                assert_eq!(fields.get("x"), Some(&Value::Int(10)));
                assert_eq!(fields.get("y"), Some(&Value::Int(2)));
            }
            other => panic!("expected Struct, got {:?}", other),
        }
    }

    #[test]
    fn assign_local_struct_field_plus_eq() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let my_struct = Value::Struct {
            name: "Stats".to_string(),
            fields: {
                let mut f = BTreeMap::new();
                f.insert("strength".to_string(), Value::Int(10));
                f
            },
        };
        env.bind("s".to_string(), my_struct);

        // s.strength += 5
        let stmt = make_assign(
            make_lvalue("s", vec![LValueSegment::Field("strength".to_string())]),
            AssignOp::PlusEq,
            spanned(ExprKind::IntLit(5)),
        );
        eval_stmt(&mut env, &stmt).unwrap();

        match env.lookup("s") {
            Some(Value::Struct { fields, .. }) => {
                assert_eq!(fields.get("strength"), Some(&Value::Int(15)));
            }
            other => panic!("expected Struct, got {:?}", other),
        }
    }

    #[test]
    fn assign_local_struct_missing_field_error() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let my_struct = Value::Struct {
            name: "Point".to_string(),
            fields: {
                let mut f = BTreeMap::new();
                f.insert("x".to_string(), Value::Int(1));
                f
            },
        };
        env.bind("p".to_string(), my_struct);

        // p.z = 10 (no field z)
        let stmt = make_assign(
            make_lvalue("p", vec![LValueSegment::Field("z".to_string())]),
            AssignOp::Eq,
            spanned(ExprKind::IntLit(10)),
        );
        let err = eval_stmt(&mut env, &stmt).unwrap_err();
        assert!(err.message.contains("no field"), "got: {}", err.message);
    }

    // ── Local list index mutation tests ────────────────────────

    #[test]
    fn assign_local_list_index() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("nums".to_string(), Value::List(vec![
            Value::Int(10), Value::Int(20), Value::Int(30),
        ]));

        // nums[1] = 99
        let stmt = make_assign(
            make_lvalue("nums", vec![LValueSegment::Index(spanned(ExprKind::IntLit(1)))]),
            AssignOp::Eq,
            spanned(ExprKind::IntLit(99)),
        );
        eval_stmt(&mut env, &stmt).unwrap();

        match env.lookup("nums") {
            Some(Value::List(items)) => {
                assert_eq!(items, &vec![Value::Int(10), Value::Int(99), Value::Int(30)]);
            }
            other => panic!("expected List, got {:?}", other),
        }
    }

    #[test]
    fn assign_local_list_negative_index() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("nums".to_string(), Value::List(vec![
            Value::Int(1), Value::Int(2), Value::Int(3),
        ]));

        // nums[-1] = 99 (last element)
        let stmt = make_assign(
            make_lvalue("nums", vec![LValueSegment::Index(spanned(ExprKind::IntLit(-1)))]),
            AssignOp::Eq,
            spanned(ExprKind::IntLit(99)),
        );
        eval_stmt(&mut env, &stmt).unwrap();

        match env.lookup("nums") {
            Some(Value::List(items)) => {
                assert_eq!(items, &vec![Value::Int(1), Value::Int(2), Value::Int(99)]);
            }
            other => panic!("expected List, got {:?}", other),
        }
    }

    #[test]
    fn assign_local_list_index_out_of_bounds_error() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("nums".to_string(), Value::List(vec![
            Value::Int(1), Value::Int(2),
        ]));

        // nums[5] = 99 (out of bounds)
        let stmt = make_assign(
            make_lvalue("nums", vec![LValueSegment::Index(spanned(ExprKind::IntLit(5)))]),
            AssignOp::Eq,
            spanned(ExprKind::IntLit(99)),
        );
        let err = eval_stmt(&mut env, &stmt).unwrap_err();
        assert!(err.message.contains("out of bounds"), "got: {}", err.message);
    }

    #[test]
    fn assign_local_list_index_plus_eq() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("nums".to_string(), Value::List(vec![
            Value::Int(10), Value::Int(20),
        ]));

        // nums[0] += 5
        let stmt = make_assign(
            make_lvalue("nums", vec![LValueSegment::Index(spanned(ExprKind::IntLit(0)))]),
            AssignOp::PlusEq,
            spanned(ExprKind::IntLit(5)),
        );
        eval_stmt(&mut env, &stmt).unwrap();

        match env.lookup("nums") {
            Some(Value::List(items)) => {
                assert_eq!(items[0], Value::Int(15));
            }
            other => panic!("expected List, got {:?}", other),
        }
    }

    // ── Local map key mutation tests ───────────────────────────

    #[test]
    fn assign_local_map_key_insert() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let mut map = BTreeMap::new();
        map.insert(Value::Str("a".to_string()), Value::Int(1));
        env.bind("m".to_string(), Value::Map(map));

        // m["b"] = 2 (insert new entry)
        let stmt = make_assign(
            make_lvalue("m", vec![
                LValueSegment::Index(spanned(ExprKind::StringLit("b".to_string()))),
            ]),
            AssignOp::Eq,
            spanned(ExprKind::IntLit(2)),
        );
        eval_stmt(&mut env, &stmt).unwrap();

        match env.lookup("m") {
            Some(Value::Map(m)) => {
                assert_eq!(m.get(&Value::Str("a".to_string())), Some(&Value::Int(1)));
                assert_eq!(m.get(&Value::Str("b".to_string())), Some(&Value::Int(2)));
            }
            other => panic!("expected Map, got {:?}", other),
        }
    }

    #[test]
    fn assign_local_map_key_update() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let mut map = BTreeMap::new();
        map.insert(Value::Str("a".to_string()), Value::Int(1));
        env.bind("m".to_string(), Value::Map(map));

        // m["a"] = 99 (overwrite)
        let stmt = make_assign(
            make_lvalue("m", vec![
                LValueSegment::Index(spanned(ExprKind::StringLit("a".to_string()))),
            ]),
            AssignOp::Eq,
            spanned(ExprKind::IntLit(99)),
        );
        eval_stmt(&mut env, &stmt).unwrap();

        match env.lookup("m") {
            Some(Value::Map(m)) => {
                assert_eq!(m.get(&Value::Str("a".to_string())), Some(&Value::Int(99)));
            }
            other => panic!("expected Map, got {:?}", other),
        }
    }

    #[test]
    fn assign_local_map_key_plus_eq() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let mut map = BTreeMap::new();
        map.insert(Value::Str("score".to_string()), Value::Int(100));
        env.bind("m".to_string(), Value::Map(map));

        // m["score"] += 50
        let stmt = make_assign(
            make_lvalue("m", vec![
                LValueSegment::Index(spanned(ExprKind::StringLit("score".to_string()))),
            ]),
            AssignOp::PlusEq,
            spanned(ExprKind::IntLit(50)),
        );
        eval_stmt(&mut env, &stmt).unwrap();

        match env.lookup("m") {
            Some(Value::Map(m)) => {
                assert_eq!(m.get(&Value::Str("score".to_string())), Some(&Value::Int(150)));
            }
            other => panic!("expected Map, got {:?}", other),
        }
    }

    #[test]
    fn assign_local_map_missing_key_plus_eq_error() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let map = BTreeMap::new();
        env.bind("m".to_string(), Value::Map(map));

        // m["x"] += 1 (key doesn't exist)
        let stmt = make_assign(
            make_lvalue("m", vec![
                LValueSegment::Index(spanned(ExprKind::StringLit("x".to_string()))),
            ]),
            AssignOp::PlusEq,
            spanned(ExprKind::IntLit(1)),
        );
        let err = eval_stmt(&mut env, &stmt).unwrap_err();
        assert!(err.message.contains("absent map key"), "got: {}", err.message);
    }

    #[test]
    fn assign_local_map_missing_key_minus_eq_error() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let map = BTreeMap::new();
        env.bind("m".to_string(), Value::Map(map));

        // m["x"] -= 1 (key doesn't exist)
        let stmt = make_assign(
            make_lvalue("m", vec![
                LValueSegment::Index(spanned(ExprKind::StringLit("x".to_string()))),
            ]),
            AssignOp::MinusEq,
            spanned(ExprKind::IntLit(1)),
        );
        let err = eval_stmt(&mut env, &stmt).unwrap_err();
        assert!(err.message.contains("absent map key"), "got: {}", err.message);
    }

    // ── apply_assign_op error tests ────────────────────────────

    #[test]
    fn assign_plus_eq_incompatible_types_error() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("x".to_string(), Value::Str("hello".to_string()));

        // x += 5 (string += int)
        let stmt = make_assign(
            make_lvalue("x", vec![]),
            AssignOp::PlusEq,
            spanned(ExprKind::IntLit(5)),
        );
        let err = eval_stmt(&mut env, &stmt).unwrap_err();
        assert!(err.message.contains("cannot apply +="), "got: {}", err.message);
    }

    #[test]
    fn assign_integer_overflow_plus_eq_error() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("x".to_string(), Value::Int(i64::MAX));

        let stmt = make_assign(
            make_lvalue("x", vec![]),
            AssignOp::PlusEq,
            spanned(ExprKind::IntLit(1)),
        );
        let err = eval_stmt(&mut env, &stmt).unwrap_err();
        assert!(err.message.contains("overflow"), "got: {}", err.message);
    }

    #[test]
    fn assign_integer_overflow_minus_eq_error() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("x".to_string(), Value::Int(i64::MIN));

        let stmt = make_assign(
            make_lvalue("x", vec![]),
            AssignOp::MinusEq,
            spanned(ExprKind::IntLit(1)),
        );
        let err = eval_stmt(&mut env, &stmt).unwrap_err();
        assert!(err.message.contains("overflow"), "got: {}", err.message);
    }

    // ── Float assignment tests ─────────────────────────────────

    #[test]
    fn assign_float_plus_eq() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("x".to_string(), Value::Float(1.5));

        let block = spanned(vec![
            make_assign(
                make_lvalue("x", vec![]),
                AssignOp::PlusEq,
                spanned(ExprKind::IntLit(2)),  // Int + Float works via mixed type
            ),
            spanned(StmtKind::Expr(spanned(ExprKind::Ident("x".to_string())))),
        ]);
        let result = eval_block(&mut env, &block).unwrap();
        assert_eq!(result, Value::Float(3.5));
    }

    #[test]
    fn assign_float_minus_eq() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("x".to_string(), Value::Float(10.0));

        let stmt = make_assign(
            make_lvalue("x", vec![]),
            AssignOp::MinusEq,
            spanned(ExprKind::IntLit(3)),
        );
        eval_stmt(&mut env, &stmt).unwrap();
        assert_eq!(env.lookup("x"), Some(&Value::Float(7.0)));
    }

    // ── Block returning value after assignment ─────────────────

    #[test]
    fn assign_returns_none_as_stmt_value() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("x".to_string(), Value::Int(0));

        // Block: x = 42 (assign returns None as block value)
        let block = spanned(vec![
            make_assign(
                make_lvalue("x", vec![]),
                AssignOp::Eq,
                spanned(ExprKind::IntLit(42)),
            ),
        ]);
        let result = eval_block(&mut env, &block).unwrap();
        assert_eq!(result, Value::None);
        // But x was updated
        assert_eq!(env.lookup("x"), Some(&Value::Int(42)));
    }

    // ── RollResult coercion in assignment ──────────────────────

    #[test]
    fn assign_roll_result_coerced_in_plus_eq() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // RollResult with total=7
        let rr = Value::RollResult(RollResult {
            expr: DiceExpr { count: 2, sides: 6, filter: None, modifier: 0 },
            dice: vec![3, 4],
            kept: vec![3, 4],
            modifier: 0,
            total: 7,
            unmodified: 7,
        });
        env.bind("x".to_string(), rr);

        // x += 3 → RollResult coerced to Int(7), then 7 + 3 = 10
        let stmt = make_assign(
            make_lvalue("x", vec![]),
            AssignOp::PlusEq,
            spanned(ExprKind::IntLit(3)),
        );
        eval_stmt(&mut env, &stmt).unwrap();
        assert_eq!(env.lookup("x"), Some(&Value::Int(10)));
    }

    // ── No effects emitted for local mutations ─────────────────

    #[test]
    fn assign_local_mutation_emits_no_effects() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("x".to_string(), Value::Int(10));

        // x += 5 → purely local, no effects
        let stmt = make_assign(
            make_lvalue("x", vec![]),
            AssignOp::PlusEq,
            spanned(ExprKind::IntLit(5)),
        );
        eval_stmt(&mut env, &stmt).unwrap();

        assert!(handler.log.is_empty(), "expected no effects for local mutation");
    }

    // ── Regression: i64::MIN list index should not panic ────────

    #[test]
    fn assign_local_list_i64_min_index_error() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("nums".to_string(), Value::List(vec![Value::Int(1)]));

        // nums[i64::MIN] = 0 — should produce a RuntimeError, not panic
        let stmt = make_assign(
            make_lvalue("nums", vec![
                LValueSegment::Index(spanned(ExprKind::IntLit(i64::MIN))),
            ]),
            AssignOp::Eq,
            spanned(ExprKind::IntLit(0)),
        );
        let err = eval_stmt(&mut env, &stmt).unwrap_err();
        assert!(err.message.contains("out of bounds"), "got: {}", err.message);
    }

    // ── Regression: map assignment uses semantic key equality ────

    #[test]
    fn assign_local_map_semantic_key_overwrite() {
        // Writing with Option(None) key should overwrite an existing None key
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let mut map = BTreeMap::new();
        map.insert(Value::None, Value::Int(1));
        env.bind("m".to_string(), Value::Map(map));

        // m[option_none] = 99 — should overwrite the None entry, not create a duplicate
        let stmt = make_assign(
            make_lvalue("m", vec![
                LValueSegment::Index(spanned(ExprKind::NoneLit)),
            ]),
            AssignOp::Eq,
            spanned(ExprKind::IntLit(99)),
        );
        eval_stmt(&mut env, &stmt).unwrap();

        match env.lookup("m") {
            Some(Value::Map(m)) => {
                assert_eq!(m.len(), 1, "should have 1 entry, not a duplicate; got {:?}", m);
                // The value should be updated regardless of which structural key remains
                let val = m.values().next().unwrap();
                assert_eq!(val, &Value::Int(99));
            }
            other => panic!("expected Map, got {:?}", other),
        }
    }

    #[test]
    fn assign_local_map_semantic_key_plus_eq() {
        // Compound assignment should find an existing key via semantic equality
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let mut map = BTreeMap::new();
        map.insert(Value::None, Value::Int(10));
        env.bind("m".to_string(), Value::Map(map));

        // m[option_none] += 5 — should find the None key semantically
        let stmt = make_assign(
            make_lvalue("m", vec![
                LValueSegment::Index(spanned(ExprKind::NoneLit)),
            ]),
            AssignOp::PlusEq,
            spanned(ExprKind::IntLit(5)),
        );
        eval_stmt(&mut env, &stmt).unwrap();

        match env.lookup("m") {
            Some(Value::Map(m)) => {
                assert_eq!(m.len(), 1);
                let val = m.values().next().unwrap();
                assert_eq!(val, &Value::Int(15));
            }
            other => panic!("expected Map, got {:?}", other),
        }
    }

    // ── Has / Grant / Revoke tests ────────────────────────────

    #[test]
    fn has_returns_true_when_group_field_present() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let mut state = TestState::new();
        // Entity 1 has a "Spellcasting" field (simulating a granted group)
        state.fields.insert(
            (1, "Spellcasting".into()),
            Value::Struct {
                name: "Spellcasting".into(),
                fields: {
                    let mut f = BTreeMap::new();
                    f.insert("spell_slots".into(), Value::Int(3));
                    f
                },
            },
        );
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);
        env.bind("actor".into(), Value::Entity(EntityRef(1)));

        let expr = spanned(ExprKind::Has {
            entity: Box::new(spanned(ExprKind::Ident("actor".into()))),
            group_name: "Spellcasting".into(),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));
    }

    #[test]
    fn has_returns_false_when_group_field_absent() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new(); // Entity 1 has no fields
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);
        env.bind("actor".into(), Value::Entity(EntityRef(1)));

        let expr = spanned(ExprKind::Has {
            entity: Box::new(spanned(ExprKind::Ident("actor".into()))),
            group_name: "Spellcasting".into(),
        });
        assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(false));
    }

    #[test]
    fn has_on_non_entity_is_error() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);
        env.bind("x".into(), Value::Int(42));

        let expr = spanned(ExprKind::Has {
            entity: Box::new(spanned(ExprKind::Ident("x".into()))),
            group_name: "Spellcasting".into(),
        });
        let err = eval_expr(&mut env, &expr).unwrap_err();
        assert!(err.message.contains("expected entity"), "got: {}", err.message);
    }

    #[test]
    fn grant_emits_grant_group_effect_with_fields() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);
        env.bind("actor".into(), Value::Entity(EntityRef(1)));

        let stmt = spanned(StmtKind::Grant {
            entity: Box::new(spanned(ExprKind::Ident("actor".into()))),
            group_name: "Spellcasting".into(),
            fields: vec![
                StructFieldInit {
                    name: "spell_slots".into(),
                    value: spanned(ExprKind::IntLit(3)),
                    span: dummy_span(),
                },
                StructFieldInit {
                    name: "cantrips".into(),
                    value: spanned(ExprKind::IntLit(2)),
                    span: dummy_span(),
                },
            ],
        });
        eval_stmt(&mut env, &stmt).unwrap();

        // Should have emitted exactly one GrantGroup effect
        assert_eq!(handler.log.len(), 1);
        match &handler.log[0] {
            Effect::GrantGroup {
                entity,
                group_name,
                fields,
            } => {
                assert_eq!(entity.0, 1);
                assert_eq!(group_name, "Spellcasting");
                match fields {
                    Value::Struct { name, fields } => {
                        assert_eq!(name, "Spellcasting");
                        assert_eq!(fields.get("spell_slots"), Some(&Value::Int(3)));
                        assert_eq!(fields.get("cantrips"), Some(&Value::Int(2)));
                    }
                    _ => panic!("expected Struct value, got {:?}", fields),
                }
            }
            _ => panic!("expected GrantGroup effect, got {:?}", handler.log[0]),
        }
    }

    #[test]
    fn grant_with_no_fields_emits_empty_struct() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);
        env.bind("actor".into(), Value::Entity(EntityRef(1)));

        let stmt = spanned(StmtKind::Grant {
            entity: Box::new(spanned(ExprKind::Ident("actor".into()))),
            group_name: "Flight".into(),
            fields: vec![],
        });
        eval_stmt(&mut env, &stmt).unwrap();

        assert_eq!(handler.log.len(), 1);
        match &handler.log[0] {
            Effect::GrantGroup { fields, .. } => match fields {
                Value::Struct { fields, .. } => {
                    assert!(fields.is_empty());
                }
                _ => panic!("expected Struct"),
            },
            _ => panic!("expected GrantGroup"),
        }
    }

    #[test]
    fn grant_fills_defaults_from_entity_decl() {
        // Build a program with an entity that has an optional group with defaults
        let mut program = Program {
            items: vec![spanned(TopLevel::System(SystemBlock {
                name: "test".into(),
                decls: vec![spanned(DeclKind::Entity(EntityDecl {
                    name: "Character".into(),
                    fields: vec![],
                    optional_groups: vec![OptionalGroup {
                        name: "Spellcasting".into(),
                        fields: vec![
                            FieldDef {
                                name: "spell_slots".into(),
                                ty: spanned(TypeExpr::Int),
                                default: None, // no default
                                span: dummy_span(),
                            },
                            FieldDef {
                                name: "cantrips".into(),
                                ty: spanned(TypeExpr::Int),
                                default: Some(spanned(ExprKind::IntLit(4))), // default = 4
                                span: dummy_span(),
                            },
                        ],
                        span: dummy_span(),
                    }],
                }))],
            }))],
            ..Default::default()
        };
        program.build_index();

        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let mut state = TestState::new();
        state.entity_type = Some("Character".into());
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);
        env.bind("actor".into(), Value::Entity(EntityRef(1)));

        // Grant with only spell_slots provided; cantrips should get default 4
        let stmt = spanned(StmtKind::Grant {
            entity: Box::new(spanned(ExprKind::Ident("actor".into()))),
            group_name: "Spellcasting".into(),
            fields: vec![StructFieldInit {
                name: "spell_slots".into(),
                value: spanned(ExprKind::IntLit(3)),
                span: dummy_span(),
            }],
        });
        eval_stmt(&mut env, &stmt).unwrap();

        assert_eq!(handler.log.len(), 1);
        match &handler.log[0] {
            Effect::GrantGroup { fields, .. } => match fields {
                Value::Struct { fields, .. } => {
                    assert_eq!(fields.get("spell_slots"), Some(&Value::Int(3)));
                    assert_eq!(fields.get("cantrips"), Some(&Value::Int(4)));
                }
                _ => panic!("expected Struct"),
            },
            _ => panic!("expected GrantGroup"),
        }
    }

    #[test]
    fn grant_explicit_field_overrides_default() {
        // Build a program with an entity that has default=4 for cantrips
        let mut program = Program {
            items: vec![spanned(TopLevel::System(SystemBlock {
                name: "test".into(),
                decls: vec![spanned(DeclKind::Entity(EntityDecl {
                    name: "Character".into(),
                    fields: vec![],
                    optional_groups: vec![OptionalGroup {
                        name: "Spellcasting".into(),
                        fields: vec![FieldDef {
                            name: "cantrips".into(),
                            ty: spanned(TypeExpr::Int),
                            default: Some(spanned(ExprKind::IntLit(4))),
                            span: dummy_span(),
                        }],
                        span: dummy_span(),
                    }],
                }))],
            }))],
            ..Default::default()
        };
        program.build_index();

        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let mut state = TestState::new();
        state.entity_type = Some("Character".into());
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);
        env.bind("actor".into(), Value::Entity(EntityRef(1)));

        // Grant with cantrips=10 — should override the default of 4
        let stmt = spanned(StmtKind::Grant {
            entity: Box::new(spanned(ExprKind::Ident("actor".into()))),
            group_name: "Spellcasting".into(),
            fields: vec![StructFieldInit {
                name: "cantrips".into(),
                value: spanned(ExprKind::IntLit(10)),
                span: dummy_span(),
            }],
        });
        eval_stmt(&mut env, &stmt).unwrap();

        match &handler.log[0] {
            Effect::GrantGroup { fields, .. } => match fields {
                Value::Struct { fields, .. } => {
                    assert_eq!(fields.get("cantrips"), Some(&Value::Int(10)));
                }
                _ => panic!("expected Struct"),
            },
            _ => panic!("expected GrantGroup"),
        }
    }

    #[test]
    fn grant_on_non_entity_is_error() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);
        env.bind("x".into(), Value::Int(42));

        let stmt = spanned(StmtKind::Grant {
            entity: Box::new(spanned(ExprKind::Ident("x".into()))),
            group_name: "Spellcasting".into(),
            fields: vec![],
        });
        let err = eval_stmt(&mut env, &stmt).unwrap_err();
        assert!(err.message.contains("expected entity"), "got: {}", err.message);
    }

    #[test]
    fn grant_vetoed_by_host_is_error() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        handler.script.push_back(Response::Vetoed);
        let mut env = make_env(&state, &mut handler, &interp);
        env.bind("actor".into(), Value::Entity(EntityRef(1)));

        let stmt = spanned(StmtKind::Grant {
            entity: Box::new(spanned(ExprKind::Ident("actor".into()))),
            group_name: "Spellcasting".into(),
            fields: vec![],
        });
        let err = eval_stmt(&mut env, &stmt).unwrap_err();
        assert!(err.message.contains("vetoed"), "got: {}", err.message);
    }

    #[test]
    fn revoke_emits_revoke_group_effect() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);
        env.bind("actor".into(), Value::Entity(EntityRef(1)));

        let stmt = spanned(StmtKind::Revoke {
            entity: Box::new(spanned(ExprKind::Ident("actor".into()))),
            group_name: "Spellcasting".into(),
        });
        eval_stmt(&mut env, &stmt).unwrap();

        assert_eq!(handler.log.len(), 1);
        match &handler.log[0] {
            Effect::RevokeGroup {
                entity,
                group_name,
            } => {
                assert_eq!(entity.0, 1);
                assert_eq!(group_name, "Spellcasting");
            }
            _ => panic!("expected RevokeGroup effect, got {:?}", handler.log[0]),
        }
    }

    #[test]
    fn revoke_on_non_entity_is_error() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);
        env.bind("x".into(), Value::Str("not entity".into()));

        let stmt = spanned(StmtKind::Revoke {
            entity: Box::new(spanned(ExprKind::Ident("x".into()))),
            group_name: "Spellcasting".into(),
        });
        let err = eval_stmt(&mut env, &stmt).unwrap_err();
        assert!(err.message.contains("expected entity"), "got: {}", err.message);
    }

    #[test]
    fn revoke_vetoed_by_host_is_error() {
        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        handler.script.push_back(Response::Vetoed);
        let mut env = make_env(&state, &mut handler, &interp);
        env.bind("actor".into(), Value::Entity(EntityRef(1)));

        let stmt = spanned(StmtKind::Revoke {
            entity: Box::new(spanned(ExprKind::Ident("actor".into()))),
            group_name: "Spellcasting".into(),
        });
        let err = eval_stmt(&mut env, &stmt).unwrap_err();
        assert!(err.message.contains("vetoed"), "got: {}", err.message);
    }

    #[test]
    fn grant_defaults_scoped_to_entity_type() {
        // Two entity types share the same optional group name but with different defaults.
        // When granting on a Monster, `spell_slots` should default to 1 (Monster's), not 3.
        let mut program = Program {
            items: vec![spanned(TopLevel::System(SystemBlock {
                name: "test".into(),
                decls: vec![
                    spanned(DeclKind::Entity(EntityDecl {
                        name: "Character".into(),
                        fields: vec![FieldDef {
                            name: "HP".into(),
                            ty: spanned(TypeExpr::Int),
                            default: None,
                            span: dummy_span(),
                        }],
                        optional_groups: vec![OptionalGroup {
                            name: "Spellcasting".into(),
                            fields: vec![
                                FieldDef {
                                    name: "spell_slots".into(),
                                    ty: spanned(TypeExpr::Int),
                                    default: Some(spanned(ExprKind::IntLit(3))),
                                    span: dummy_span(),
                                },
                                FieldDef {
                                    name: "dc".into(),
                                    ty: spanned(TypeExpr::Int),
                                    default: None,
                                    span: dummy_span(),
                                },
                            ],
                            span: dummy_span(),
                        }],
                    })),
                    spanned(DeclKind::Entity(EntityDecl {
                        name: "Monster".into(),
                        fields: vec![FieldDef {
                            name: "HP".into(),
                            ty: spanned(TypeExpr::Int),
                            default: None,
                            span: dummy_span(),
                        }],
                        optional_groups: vec![OptionalGroup {
                            name: "Spellcasting".into(),
                            fields: vec![
                                FieldDef {
                                    name: "spell_slots".into(),
                                    ty: spanned(TypeExpr::Int),
                                    default: Some(spanned(ExprKind::IntLit(1))),
                                    span: dummy_span(),
                                },
                                FieldDef {
                                    name: "dc".into(),
                                    ty: spanned(TypeExpr::Int),
                                    default: None,
                                    span: dummy_span(),
                                },
                            ],
                            span: dummy_span(),
                        }],
                    })),
                ],
            }))],
            ..Default::default()
        };
        program.build_index();

        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let mut state = TestState::new();
        state.entity_type = Some("Monster".into());
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);
        env.bind("actor".into(), Value::Entity(EntityRef(1)));

        // Grant with only dc provided; spell_slots should use Monster's default (1)
        let stmt = spanned(StmtKind::Grant {
            entity: Box::new(spanned(ExprKind::Ident("actor".into()))),
            group_name: "Spellcasting".into(),
            fields: vec![StructFieldInit {
                name: "dc".into(),
                value: spanned(ExprKind::IntLit(15)),
                span: dummy_span(),
            }],
        });
        eval_stmt(&mut env, &stmt).unwrap();

        assert_eq!(handler.log.len(), 1);
        match &handler.log[0] {
            Effect::GrantGroup { fields, .. } => match fields {
                Value::Struct { fields, .. } => {
                    assert_eq!(fields.get("dc"), Some(&Value::Int(15)));
                    assert_eq!(
                        fields.get("spell_slots"),
                        Some(&Value::Int(1)),
                        "spell_slots should default to Monster's 1, not Character's 3"
                    );
                }
                _ => panic!("expected Struct"),
            },
            _ => panic!("expected GrantGroup"),
        }
    }

    #[test]
    fn grant_no_defaults_when_entity_type_unknown() {
        // When entity_type_name returns None, find_optional_group should NOT
        // fall back to a different entity's group — no defaults are filled.
        let mut program = Program {
            items: vec![spanned(TopLevel::System(SystemBlock {
                name: "test".into(),
                decls: vec![
                    spanned(DeclKind::Entity(EntityDecl {
                        name: "Character".into(),
                        fields: vec![FieldDef {
                            name: "HP".into(),
                            ty: spanned(TypeExpr::Int),
                            default: None,
                            span: dummy_span(),
                        }],
                        optional_groups: vec![OptionalGroup {
                            name: "Spellcasting".into(),
                            fields: vec![
                                FieldDef {
                                    name: "spell_slots".into(),
                                    ty: spanned(TypeExpr::Int),
                                    default: Some(spanned(ExprKind::IntLit(3))),
                                    span: dummy_span(),
                                },
                                FieldDef {
                                    name: "dc".into(),
                                    ty: spanned(TypeExpr::Int),
                                    default: None,
                                    span: dummy_span(),
                                },
                            ],
                            span: dummy_span(),
                        }],
                    })),
                    spanned(DeclKind::Entity(EntityDecl {
                        name: "Monster".into(),
                        fields: vec![FieldDef {
                            name: "HP".into(),
                            ty: spanned(TypeExpr::Int),
                            default: None,
                            span: dummy_span(),
                        }],
                        optional_groups: vec![OptionalGroup {
                            name: "Spellcasting".into(),
                            fields: vec![
                                FieldDef {
                                    name: "spell_slots".into(),
                                    ty: spanned(TypeExpr::Int),
                                    default: Some(spanned(ExprKind::IntLit(1))),
                                    span: dummy_span(),
                                },
                                FieldDef {
                                    name: "dc".into(),
                                    ty: spanned(TypeExpr::Int),
                                    default: None,
                                    span: dummy_span(),
                                },
                            ],
                            span: dummy_span(),
                        }],
                    })),
                ],
            }))],
            ..Default::default()
        };
        program.build_index();

        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        // entity_type is None — simulates unknown entity type
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);
        env.bind("actor".into(), Value::Entity(EntityRef(1)));

        // Grant with only dc provided; spell_slots should NOT be filled
        // because entity type is unknown and we don't fall back.
        let stmt = spanned(StmtKind::Grant {
            entity: Box::new(spanned(ExprKind::Ident("actor".into()))),
            group_name: "Spellcasting".into(),
            fields: vec![StructFieldInit {
                name: "dc".into(),
                value: spanned(ExprKind::IntLit(15)),
                span: dummy_span(),
            }],
        });
        eval_stmt(&mut env, &stmt).unwrap();

        assert_eq!(handler.log.len(), 1);
        match &handler.log[0] {
            Effect::GrantGroup { fields, .. } => match fields {
                Value::Struct { fields, .. } => {
                    assert_eq!(fields.get("dc"), Some(&Value::Int(15)));
                    assert_eq!(
                        fields.get("spell_slots"),
                        None,
                        "spell_slots should not be filled when entity type is unknown"
                    );
                }
                _ => panic!("expected Struct"),
            },
            _ => panic!("expected GrantGroup"),
        }
    }
}
