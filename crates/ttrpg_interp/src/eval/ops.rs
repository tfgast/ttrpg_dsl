use std::collections::BTreeMap;

use ttrpg_ast::ast::{BinOp, ExprKind, UnaryOp};
use ttrpg_ast::{Name, Spanned};
use ttrpg_checker::env::DeclInfo;

use crate::state::StateProvider;
use crate::value::{DiceExpr, Value};
use crate::Env;
use crate::RuntimeError;

use super::compare::{int_float_cmp, value_eq};
use super::dispatch::eval_expr;
use super::helpers::type_name;

// ── Unary operator evaluation ──────────────────────────────────

pub(super) fn eval_unary(
    env: &mut Env,
    op: UnaryOp,
    operand: &Spanned<ExprKind>,
    expr: &Spanned<ExprKind>,
) -> Result<Value, RuntimeError> {
    let val = eval_expr(env, operand)?;
    // Unit type negation
    if op == UnaryOp::Neg {
        if let Some((name, field, n)) = as_unit_value(&val, env.interp.type_env) {
            let result = n.checked_neg().ok_or_else(|| {
                RuntimeError::with_span("integer overflow in unit negation", expr.span)
            })?;
            return Ok(make_unit_value(name, field, result));
        }
    }
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

pub(super) fn eval_binop(
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
                    _ => Err(RuntimeError::with_span(
                        "&& requires Bool operands",
                        expr.span,
                    )),
                }
            }
            _ => Err(RuntimeError::with_span(
                "&& requires Bool operands",
                expr.span,
            )),
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
                    _ => Err(RuntimeError::with_span(
                        "|| requires Bool operands",
                        expr.span,
                    )),
                }
            }
            _ => Err(RuntimeError::with_span(
                "|| requires Bool operands",
                expr.span,
            )),
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
                BinOp::Add => eval_add(&lhs, &rhs, env.interp.type_env, expr),
                BinOp::Sub => eval_sub(&lhs, &rhs, env.interp.type_env, expr),
                BinOp::Mul => eval_mul(&lhs, &rhs, env.interp.type_env, expr),
                BinOp::Div => eval_div(&lhs, &rhs, env.interp.type_env, expr),
                _ => unreachable!(),
            }
        }

        // Comparison — coerce
        BinOp::Lt | BinOp::LtEq | BinOp::Gt | BinOp::GtEq => {
            let lhs = coerce_roll_result(lhs);
            let rhs = coerce_roll_result(rhs);
            match op {
                BinOp::Lt => eval_comparison(&lhs, &rhs, |o| o.is_lt(), env.interp.type_env, expr),
                BinOp::LtEq => {
                    eval_comparison(&lhs, &rhs, |o| o.is_le(), env.interp.type_env, expr)
                }
                BinOp::Gt => eval_comparison(&lhs, &rhs, |o| o.is_gt(), env.interp.type_env, expr),
                BinOp::GtEq => {
                    eval_comparison(&lhs, &rhs, |o| o.is_ge(), env.interp.type_env, expr)
                }
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
pub(super) fn coerce_roll_result(val: Value) -> Value {
    match val {
        Value::RollResult(r) => Value::Int(r.total),
        other => other,
    }
}

/// If `val` is a `Value::Struct` whose name is registered as a unit type in the
/// type environment, return `(unit_type_name, field_name, int_value)`.
fn as_unit_value(val: &Value, type_env: &ttrpg_checker::env::TypeEnv) -> Option<(Name, Name, i64)> {
    if let Value::Struct { name, fields } = val {
        if let Some(DeclInfo::Unit(info)) = type_env.types.get(name.as_str()) {
            let field_name = &info.fields[0].name;
            if let Some(Value::Int(n)) = fields.get(field_name.as_str()) {
                return Some((name.clone(), field_name.clone(), *n));
            }
        }
    }
    None
}

/// Construct a unit-type Value::Struct from its type name, field name, and int value.
fn make_unit_value(unit_name: Name, field_name: Name, int_val: i64) -> Value {
    let mut fields = BTreeMap::new();
    fields.insert(field_name, Value::Int(int_val));
    Value::Struct {
        name: unit_name,
        fields,
    }
}

fn eval_add(
    lhs: &Value,
    rhs: &Value,
    type_env: &ttrpg_checker::env::TypeEnv,
    expr: &Spanned<ExprKind>,
) -> Result<Value, RuntimeError> {
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
            let modifier = d.modifier.checked_add(*n).ok_or_else(|| {
                RuntimeError::with_span("dice modifier overflow in addition", expr.span)
            })?;
            Ok(Value::DiceExpr(DiceExpr {
                modifier,
                ..d.clone()
            }))
        }
        (Value::Int(n), Value::DiceExpr(d)) => {
            let modifier = d.modifier.checked_add(*n).ok_or_else(|| {
                RuntimeError::with_span("dice modifier overflow in addition", expr.span)
            })?;
            Ok(Value::DiceExpr(DiceExpr {
                modifier,
                ..d.clone()
            }))
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
            let count = a.count.checked_add(b.count).ok_or_else(|| {
                RuntimeError::with_span("dice count overflow in addition", expr.span)
            })?;
            let modifier = a.modifier.checked_add(b.modifier).ok_or_else(|| {
                RuntimeError::with_span("dice modifier overflow in addition", expr.span)
            })?;
            Ok(Value::DiceExpr(DiceExpr {
                count,
                sides: a.sides,
                filter: a.filter,
                modifier,
            }))
        }
        // Unit type addition: same-type → same-type
        _ => {
            if let (Some((n1, field, a)), Some((n2, _, b))) =
                (as_unit_value(lhs, type_env), as_unit_value(rhs, type_env))
            {
                if n1 != n2 {
                    return Err(RuntimeError::with_span(
                        format!("cannot add {:?} and {:?}", type_name(lhs), type_name(rhs)),
                        expr.span,
                    ));
                }
                let result = a.checked_add(b).ok_or_else(|| {
                    RuntimeError::with_span("integer overflow in unit addition", expr.span)
                })?;
                Ok(make_unit_value(n1, field, result))
            } else {
                Err(RuntimeError::with_span(
                    format!("cannot add {:?} and {:?}", type_name(lhs), type_name(rhs)),
                    expr.span,
                ))
            }
        }
    }
}

fn eval_sub(
    lhs: &Value,
    rhs: &Value,
    type_env: &ttrpg_checker::env::TypeEnv,
    expr: &Spanned<ExprKind>,
) -> Result<Value, RuntimeError> {
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
            let modifier = d.modifier.checked_sub(*n).ok_or_else(|| {
                RuntimeError::with_span("dice modifier overflow in subtraction", expr.span)
            })?;
            Ok(Value::DiceExpr(DiceExpr {
                modifier,
                ..d.clone()
            }))
        }
        // Unit type subtraction: same-type → same-type
        _ => {
            if let (Some((n1, field, a)), Some((n2, _, b))) =
                (as_unit_value(lhs, type_env), as_unit_value(rhs, type_env))
            {
                if n1 != n2 {
                    return Err(RuntimeError::with_span(
                        format!(
                            "cannot subtract {:?} from {:?}",
                            type_name(rhs),
                            type_name(lhs)
                        ),
                        expr.span,
                    ));
                }
                let result = a.checked_sub(b).ok_or_else(|| {
                    RuntimeError::with_span("integer overflow in unit subtraction", expr.span)
                })?;
                Ok(make_unit_value(n1, field, result))
            } else {
                Err(RuntimeError::with_span(
                    format!(
                        "cannot subtract {:?} from {:?}",
                        type_name(rhs),
                        type_name(lhs)
                    ),
                    expr.span,
                ))
            }
        }
    }
}

fn eval_mul(
    lhs: &Value,
    rhs: &Value,
    type_env: &ttrpg_checker::env::TypeEnv,
    expr: &Spanned<ExprKind>,
) -> Result<Value, RuntimeError> {
    // Unit type scaling: Int * unit or unit * Int
    if let Some((name, field, uval)) = as_unit_value(lhs, type_env) {
        if let Value::Int(n) = rhs {
            let result = uval.checked_mul(*n).ok_or_else(|| {
                RuntimeError::with_span("integer overflow in unit multiplication", expr.span)
            })?;
            return Ok(make_unit_value(name, field, result));
        }
    }
    if let Some((name, field, uval)) = as_unit_value(rhs, type_env) {
        if let Value::Int(n) = lhs {
            let result = n.checked_mul(uval).ok_or_else(|| {
                RuntimeError::with_span("integer overflow in unit multiplication", expr.span)
            })?;
            return Ok(make_unit_value(name, field, result));
        }
    }
    match (lhs, rhs) {
        (Value::Int(a), Value::Int(b)) => a.checked_mul(*b).map(Value::Int).ok_or_else(|| {
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

fn eval_div(
    lhs: &Value,
    rhs: &Value,
    type_env: &ttrpg_checker::env::TypeEnv,
    expr: &Spanned<ExprKind>,
) -> Result<Value, RuntimeError> {
    // Unit type division: same-type → Float
    if let (Some((n1, _, a)), Some((n2, _, b))) =
        (as_unit_value(lhs, type_env), as_unit_value(rhs, type_env))
    {
        if n1 == n2 {
            if b == 0 {
                return Err(RuntimeError::with_span("division by zero", expr.span));
            }
            return Ok(Value::Float(a as f64 / b as f64));
        }
    }
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
            format!("cannot divide {:?} by {:?}", type_name(lhs), type_name(rhs)),
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
            if let (Some((n1, _, a)), Some((n2, _, b))) =
                (as_unit_value(lhs, type_env), as_unit_value(rhs, type_env))
            {
                if n1 != n2 {
                    return Err(RuntimeError::with_span(
                        format!(
                            "cannot compare {:?} and {:?}",
                            type_name(lhs),
                            type_name(rhs)
                        ),
                        expr.span,
                    ));
                }
                a.cmp(&b)
            } else {
                return Err(RuntimeError::with_span(
                    format!(
                        "cannot compare {:?} and {:?}",
                        type_name(lhs),
                        type_name(rhs)
                    ),
                    expr.span,
                ));
            }
        }
    };
    Ok(Value::Bool(cmp_fn(ordering)))
}

/// Look up a variant's declaration-order index within its enum.
pub(crate) fn variant_ordinal(
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
            format!(
                "'in' requires List, Set, or Map on right side, got {:?}",
                type_name(rhs)
            ),
            expr.span,
        )),
    }
}
