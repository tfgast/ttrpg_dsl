use ttrpg_ast::ast::Arg;
use ttrpg_ast::Span;

use crate::eval::{eval_expr, type_name};
use crate::effect::{Effect, Response};
use crate::value::{DiceExpr, Value};
use crate::Env;
use crate::RuntimeError;

// ── Method dispatch ─────────────────────────────────────────────

pub(super) fn eval_method_call(
    env: &mut Env,
    object: Value,
    method: &str,
    args: &[Arg],
    span: Span,
) -> Result<Value, RuntimeError> {
    match &object {
        Value::Option(_) | Value::None => eval_option_method(env, object, method, args, span),
        Value::List(_) => eval_list_method(env, object, method, args, span),
        Value::Set(_) => eval_set_method(object, method, span),
        Value::Map(_) => eval_map_method(object, method, span),
        Value::DiceExpr(_) => eval_dice_method(env, object, method, args, span),
        Value::Str(_) => eval_string_method(env, object, method, args, span),
        _ => Err(RuntimeError::with_span(
            format!("type {} has no methods", type_name(&object)),
            span,
        )),
    }
}

fn eval_option_method(
    env: &mut Env,
    value: Value,
    method: &str,
    args: &[Arg],
    span: Span,
) -> Result<Value, RuntimeError> {
    match method {
        "unwrap" => {
            match value {
                Value::Option(Some(inner)) => Ok(*inner),
                Value::Option(None) | Value::None => Err(RuntimeError::with_span(
                    "called unwrap() on a none value",
                    span,
                )),
                _ => unreachable!(),
            }
        }
        "unwrap_or" => {
            if args.is_empty() {
                return Err(RuntimeError::with_span("unwrap_or() requires 1 argument", span));
            }
            let default_val = eval_expr(env, &args[0].value)?;
            match value {
                Value::Option(Some(inner)) => Ok(*inner),
                Value::Option(None) | Value::None => Ok(default_val),
                _ => unreachable!(),
            }
        }
        "is_some" => {
            match value {
                Value::Option(Some(_)) => Ok(Value::Bool(true)),
                Value::Option(None) | Value::None => Ok(Value::Bool(false)),
                _ => unreachable!(),
            }
        }
        "is_none" => {
            match value {
                Value::Option(None) | Value::None => Ok(Value::Bool(true)),
                Value::Option(Some(_)) => Ok(Value::Bool(false)),
                _ => unreachable!(),
            }
        }
        _ => Err(RuntimeError::with_span(
            format!(
                "option type has no method `{}`; available methods: unwrap, unwrap_or, is_some, is_none",
                method
            ),
            span,
        )),
    }
}

fn eval_list_method(
    env: &mut Env,
    object: Value,
    method: &str,
    args: &[Arg],
    span: Span,
) -> Result<Value, RuntimeError> {
    let Value::List(list) = object else {
        unreachable!()
    };
    match method {
        "len" => Ok(Value::Int(list.len() as i64)),
        "first" => Ok(list.into_iter().next()
            .map(|v| Value::Option(Some(Box::new(v))))
            .unwrap_or(Value::None)),
        "last" => Ok(list.into_iter().next_back()
            .map(|v| Value::Option(Some(Box::new(v))))
            .unwrap_or(Value::None)),
        "reverse" => {
            let mut v = list;
            v.reverse();
            Ok(Value::List(v))
        }
        "append" => {
            if args.is_empty() {
                return Err(RuntimeError::with_span("append() requires 1 argument", span));
            }
            let elem = eval_expr(env, &args[0].value)?;
            let mut v = list;
            v.push(elem);
            Ok(Value::List(v))
        }
        "concat" => {
            if args.is_empty() {
                return Err(RuntimeError::with_span("concat() requires 1 argument", span));
            }
            let other = eval_expr(env, &args[0].value)?;
            match other {
                Value::List(b) => {
                    let mut v = list;
                    v.extend(b);
                    Ok(Value::List(v))
                }
                _ => Err(RuntimeError::with_span(
                    format!("concat() argument must be a list, got {}", type_name(&other)),
                    span,
                )),
            }
        }
        "sum" => {
            if list.is_empty() {
                return Ok(Value::Int(0));
            }
            let mut int_sum: i64 = 0;
            let mut float_sum: f64 = 0.0;
            let mut is_float = false;
            for item in &list {
                match item {
                    Value::Int(n) => {
                        if is_float { float_sum += *n as f64; } else { int_sum += n; }
                    }
                    Value::Float(f) => {
                        if !is_float { is_float = true; float_sum = int_sum as f64; }
                        float_sum += f;
                    }
                    _ => {
                        return Err(RuntimeError::with_span(
                            format!("sum() requires list of int or float, got {}", type_name(item)),
                            span,
                        ));
                    }
                }
            }
            if is_float { Ok(Value::Float(float_sum)) } else { Ok(Value::Int(int_sum)) }
        }
        "any" => {
            for item in &list {
                match item {
                    Value::Bool(true) => return Ok(Value::Bool(true)),
                    Value::Bool(false) => {}
                    _ => {
                        return Err(RuntimeError::with_span(
                            format!("any() requires list of bool, got {}", type_name(item)),
                            span,
                        ));
                    }
                }
            }
            Ok(Value::Bool(false))
        }
        "all" => {
            for item in &list {
                match item {
                    Value::Bool(false) => return Ok(Value::Bool(false)),
                    Value::Bool(true) => {}
                    _ => {
                        return Err(RuntimeError::with_span(
                            format!("all() requires list of bool, got {}", type_name(item)),
                            span,
                        ));
                    }
                }
            }
            Ok(Value::Bool(true))
        }
        "sort" => {
            let mut v = list;
            v.sort();
            Ok(Value::List(v))
        }
        _ => Err(RuntimeError::with_span(
            format!(
                "list type has no method `{}`; available methods: len, first, last, reverse, append, concat, sum, any, all, sort",
                method
            ),
            span,
        )),
    }
}

fn eval_set_method(object: Value, method: &str, span: Span) -> Result<Value, RuntimeError> {
    let Value::Set(set) = object else {
        unreachable!()
    };
    match method {
        "len" => Ok(Value::Int(set.len() as i64)),
        _ => Err(RuntimeError::with_span(
            format!(
                "set type has no method `{}`; available methods: len",
                method
            ),
            span,
        )),
    }
}

fn eval_map_method(object: Value, method: &str, span: Span) -> Result<Value, RuntimeError> {
    let Value::Map(map) = object else {
        unreachable!()
    };
    match method {
        "len" => Ok(Value::Int(map.len() as i64)),
        "keys" => Ok(Value::List(map.into_keys().collect())),
        "values" => Ok(Value::List(map.into_values().collect())),
        _ => Err(RuntimeError::with_span(
            format!(
                "map type has no method `{}`; available methods: len, keys, values",
                method
            ),
            span,
        )),
    }
}

fn eval_dice_method(
    env: &mut Env,
    object: Value,
    method: &str,
    args: &[Arg],
    span: Span,
) -> Result<Value, RuntimeError> {
    let Value::DiceExpr(expr) = object else {
        unreachable!()
    };
    match method {
        "multiply" => {
            if args.is_empty() {
                return Err(RuntimeError::with_span(
                    "multiply() requires 1 argument",
                    span,
                ));
            }
            let factor_val = eval_expr(env, &args[0].value)?;
            match factor_val {
                Value::Int(factor) => {
                    if factor <= 0 {
                        return Err(RuntimeError::with_span(
                            format!("multiply() factor must be positive, got {}", factor),
                            span,
                        ));
                    }
                    let new_count = (expr.count as i64)
                        .checked_mul(factor)
                        .and_then(|n| u32::try_from(n).ok())
                        .ok_or_else(|| {
                            RuntimeError::with_span("dice count overflow in multiply()", span)
                        })?;
                    Ok(Value::DiceExpr(DiceExpr {
                        count: new_count,
                        sides: expr.sides,
                        filter: expr.filter,
                        modifier: expr.modifier,
                    }))
                }
                _ => Err(RuntimeError::with_span(
                    format!(
                        "multiply() factor must be int, got {}",
                        type_name(&factor_val)
                    ),
                    span,
                )),
            }
        }
        "roll" => {
            let effect = Effect::RollDice { expr };
            let response = env.handler.handle(effect);
            match response {
                Response::Rolled(rr) => Ok(Value::RollResult(rr)),
                Response::Override(Value::RollResult(rr)) => Ok(Value::RollResult(rr)),
                _ => Err(RuntimeError::with_span(
                    format!(
                        "protocol error: expected Rolled or Override(RollResult) for .roll(), got {:?}",
                        response
                    ),
                    span,
                )),
            }
        }
        _ => Err(RuntimeError::with_span(
            format!(
                "DiceExpr type has no method `{}`; available methods: multiply, roll",
                method
            ),
            span,
        )),
    }
}

fn eval_string_method(
    env: &mut Env,
    object: Value,
    method: &str,
    args: &[Arg],
    span: Span,
) -> Result<Value, RuntimeError> {
    let Value::Str(s) = object else {
        unreachable!()
    };
    match method {
        "len" => Ok(Value::Int(s.len() as i64)),
        "contains" | "starts_with" | "ends_with" => {
            if args.is_empty() {
                return Err(RuntimeError::with_span(
                    format!("{}() requires 1 argument", method),
                    span,
                ));
            }
            let arg_val = eval_expr(env, &args[0].value)?;
            let Value::Str(substr) = arg_val else {
                return Err(RuntimeError::with_span(
                    format!(
                        "{}() argument must be string, got {}",
                        method,
                        type_name(&arg_val)
                    ),
                    span,
                ));
            };
            let result = match method {
                "contains" => s.contains(substr.as_str()),
                "starts_with" => s.starts_with(substr.as_str()),
                "ends_with" => s.ends_with(substr.as_str()),
                _ => unreachable!(),
            };
            Ok(Value::Bool(result))
        }
        _ => Err(RuntimeError::with_span(
            format!(
                "string type has no method `{}`; available methods: len, contains, starts_with, ends_with",
                method
            ),
            span,
        )),
    }
}
