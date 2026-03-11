use ttrpg_ast::Span;
use ttrpg_ast::ast::Arg;

use crate::Env;
use crate::RuntimeError;
use crate::eval::{eval_expr, type_name};
use crate::value::Value;

// ── Collection builtins ─────────────────────────────────────────

pub(super) fn eval_len(
    env: &mut Env,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    if args.len() != 1 {
        return Err(RuntimeError::with_span(
            format!("len() requires 1 argument, got {}", args.len()),
            call_span,
        ));
    }
    let val = eval_expr(env, &args[0].value)?;
    match &val {
        Value::List(v) => Ok(Value::Int(v.len() as i64)),
        Value::Set(s) => Ok(Value::Int(s.len() as i64)),
        Value::Map(m) => Ok(Value::Int(m.len() as i64)),
        _ => Err(RuntimeError::with_span(
            format!("len() expects a list, set, or map, got {}", type_name(&val)),
            call_span,
        )),
    }
}

pub(super) fn eval_keys(
    env: &mut Env,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    if args.len() != 1 {
        return Err(RuntimeError::with_span(
            format!("keys() requires 1 argument, got {}", args.len()),
            call_span,
        ));
    }
    let val = eval_expr(env, &args[0].value)?;
    match val {
        Value::Map(m) => Ok(Value::List(m.into_keys().collect())),
        _ => Err(RuntimeError::with_span(
            format!("keys() expects a map, got {}", type_name(&val)),
            call_span,
        )),
    }
}

pub(super) fn eval_values(
    env: &mut Env,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    if args.len() != 1 {
        return Err(RuntimeError::with_span(
            format!("values() requires 1 argument, got {}", args.len()),
            call_span,
        ));
    }
    let val = eval_expr(env, &args[0].value)?;
    match val {
        Value::Map(m) => Ok(Value::List(m.into_values().collect())),
        _ => Err(RuntimeError::with_span(
            format!("values() expects a map, got {}", type_name(&val)),
            call_span,
        )),
    }
}

pub(super) fn eval_first(
    env: &mut Env,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    if args.len() != 1 {
        return Err(RuntimeError::with_span(
            format!("first() requires 1 argument, got {}", args.len()),
            call_span,
        ));
    }
    let val = eval_expr(env, &args[0].value)?;
    match val {
        Value::List(v) => Ok(v
            .into_iter()
            .next()
            .map_or(Value::Option(None), |v| Value::Option(Some(Box::new(v))))),
        _ => Err(RuntimeError::with_span(
            format!("first() expects a list, got {}", type_name(&val)),
            call_span,
        )),
    }
}

pub(super) fn eval_last(
    env: &mut Env,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    if args.len() != 1 {
        return Err(RuntimeError::with_span(
            format!("last() requires 1 argument, got {}", args.len()),
            call_span,
        ));
    }
    let val = eval_expr(env, &args[0].value)?;
    match val {
        Value::List(v) => Ok(v
            .into_iter()
            .next_back()
            .map_or(Value::Option(None), |v| Value::Option(Some(Box::new(v))))),
        _ => Err(RuntimeError::with_span(
            format!("last() expects a list, got {}", type_name(&val)),
            call_span,
        )),
    }
}

pub(super) fn eval_append(
    env: &mut Env,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    if args.len() != 2 {
        return Err(RuntimeError::with_span(
            format!("append() requires 2 arguments, got {}", args.len()),
            call_span,
        ));
    }
    let list_val = eval_expr(env, &args[0].value)?;
    let elem_val = eval_expr(env, &args[1].value)?;
    match list_val {
        Value::List(mut v) => {
            v.push(elem_val);
            Ok(Value::List(v))
        }
        _ => Err(RuntimeError::with_span(
            format!(
                "append() first argument must be a list, got {}",
                type_name(&list_val)
            ),
            call_span,
        )),
    }
}

pub(super) fn eval_concat(
    env: &mut Env,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    if args.len() != 2 {
        return Err(RuntimeError::with_span(
            format!("concat() requires 2 arguments, got {}", args.len()),
            call_span,
        ));
    }
    let first_val = eval_expr(env, &args[0].value)?;
    let second_val = eval_expr(env, &args[1].value)?;
    match (first_val, &second_val) {
        (Value::List(mut a), Value::List(b)) => {
            a.extend(b.iter().cloned());
            Ok(Value::List(a))
        }
        (Value::List(_), _) => Err(RuntimeError::with_span(
            format!(
                "concat() second argument must be a list, got {}",
                type_name(&second_val)
            ),
            call_span,
        )),
        (ref other, _) => Err(RuntimeError::with_span(
            format!(
                "concat() expects two lists, got {} and {}",
                type_name(other),
                type_name(&second_val)
            ),
            call_span,
        )),
    }
}

pub(super) fn eval_reverse(
    env: &mut Env,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    if args.len() != 1 {
        return Err(RuntimeError::with_span(
            format!("reverse() requires 1 argument, got {}", args.len()),
            call_span,
        ));
    }
    let val = eval_expr(env, &args[0].value)?;
    match val {
        Value::List(mut v) => {
            v.reverse();
            Ok(Value::List(v))
        }
        _ => Err(RuntimeError::with_span(
            format!("reverse() expects a list, got {}", type_name(&val)),
            call_span,
        )),
    }
}

pub(super) fn eval_sum(
    env: &mut Env,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    if args.len() != 1 {
        return Err(RuntimeError::with_span(
            format!("sum() requires 1 argument, got {}", args.len()),
            call_span,
        ));
    }
    let val = eval_expr(env, &args[0].value)?;
    match val {
        Value::List(v) => {
            if v.is_empty() {
                return Ok(Value::Int(0));
            }
            let mut int_sum: i64 = 0;
            let mut float_sum: f64 = 0.0;
            let mut is_float = false;
            for item in &v {
                match item {
                    Value::Int(n) => {
                        if is_float {
                            float_sum += *n as f64;
                        } else {
                            int_sum = int_sum.checked_add(*n).ok_or_else(|| {
                                RuntimeError::with_span("integer overflow in sum()", call_span)
                            })?;
                        }
                    }
                    Value::Float(f) => {
                        if !is_float {
                            is_float = true;
                            float_sum = int_sum as f64;
                        }
                        float_sum += f;
                    }
                    _ => {
                        return Err(RuntimeError::with_span(
                            format!(
                                "sum() requires list of int or float, got {}",
                                type_name(item)
                            ),
                            call_span,
                        ));
                    }
                }
            }
            if is_float {
                Ok(Value::Float(float_sum))
            } else {
                Ok(Value::Int(int_sum))
            }
        }
        _ => Err(RuntimeError::with_span(
            format!("sum() expects a list, got {}", type_name(&val)),
            call_span,
        )),
    }
}

pub(super) fn eval_any(
    env: &mut Env,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    if args.len() != 1 {
        return Err(RuntimeError::with_span(
            format!("any() requires 1 argument, got {}", args.len()),
            call_span,
        ));
    }
    let val = eval_expr(env, &args[0].value)?;
    match val {
        Value::List(v) => {
            for item in &v {
                match item {
                    Value::Bool(true) => return Ok(Value::Bool(true)),
                    Value::Bool(false) => {}
                    _ => {
                        return Err(RuntimeError::with_span(
                            format!("any() requires list of bool, got {}", type_name(item)),
                            call_span,
                        ));
                    }
                }
            }
            Ok(Value::Bool(false))
        }
        _ => Err(RuntimeError::with_span(
            format!("any() expects a list, got {}", type_name(&val)),
            call_span,
        )),
    }
}

pub(super) fn eval_all(
    env: &mut Env,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    if args.len() != 1 {
        return Err(RuntimeError::with_span(
            format!("all() requires 1 argument, got {}", args.len()),
            call_span,
        ));
    }
    let val = eval_expr(env, &args[0].value)?;
    match val {
        Value::List(v) => {
            for item in &v {
                match item {
                    Value::Bool(false) => return Ok(Value::Bool(false)),
                    Value::Bool(true) => {}
                    _ => {
                        return Err(RuntimeError::with_span(
                            format!("all() requires list of bool, got {}", type_name(item)),
                            call_span,
                        ));
                    }
                }
            }
            Ok(Value::Bool(true))
        }
        _ => Err(RuntimeError::with_span(
            format!("all() expects a list, got {}", type_name(&val)),
            call_span,
        )),
    }
}

pub(super) fn eval_sort(
    env: &mut Env,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    if args.len() != 1 {
        return Err(RuntimeError::with_span(
            format!("sort() requires 1 argument, got {}", args.len()),
            call_span,
        ));
    }
    let val = eval_expr(env, &args[0].value)?;
    match val {
        Value::List(mut v) => {
            v.sort();
            Ok(Value::List(v))
        }
        _ => Err(RuntimeError::with_span(
            format!("sort() expects a list, got {}", type_name(&val)),
            call_span,
        )),
    }
}

pub(super) fn eval_take(
    env: &mut Env,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    if args.len() != 2 {
        return Err(RuntimeError::with_span(
            format!("take() requires 2 arguments, got {}", args.len()),
            call_span,
        ));
    }
    let list_val = eval_expr(env, &args[0].value)?;
    let n_val = eval_expr(env, &args[1].value)?;
    let n = match &n_val {
        Value::Int(i) => *i,
        _ => {
            return Err(RuntimeError::with_span(
                format!(
                    "take() expects an int as second argument, got {}",
                    type_name(&n_val)
                ),
                call_span,
            ));
        }
    };
    match list_val {
        Value::List(v) => {
            let n = (n.max(0) as usize).min(v.len());
            Ok(Value::List(v.into_iter().take(n).collect()))
        }
        _ => Err(RuntimeError::with_span(
            format!(
                "take() expects a list as first argument, got {}",
                type_name(&list_val)
            ),
            call_span,
        )),
    }
}

pub(super) fn eval_some(
    env: &mut Env,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    if args.len() != 1 {
        return Err(RuntimeError::with_span(
            format!("some() requires 1 argument, got {}", args.len()),
            call_span,
        ));
    }
    let val = eval_expr(env, &args[0].value)?;
    Ok(Value::Option(Some(Box::new(val))))
}

/// `max(a, b)` or `max(list)` — returns the maximum int.
pub(super) fn eval_max(
    env: &mut Env,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    eval_min_max(env, args, call_span, "max", |a, b| a.max(b))
}

/// `min(a, b)` or `min(list)` — returns the minimum int.
pub(super) fn eval_min(
    env: &mut Env,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    eval_min_max(env, args, call_span, "min", |a, b| a.min(b))
}

fn eval_min_max(
    env: &mut Env,
    args: &[Arg],
    call_span: Span,
    name: &str,
    combine: fn(i64, i64) -> i64,
) -> Result<Value, RuntimeError> {
    match args.len() {
        2 => {
            let a = eval_expr(env, &args[0].value)?;
            let b = eval_expr(env, &args[1].value)?;
            match (&a, &b) {
                (Value::Int(x), Value::Int(y)) => Ok(Value::Int(combine(*x, *y))),
                _ => Err(RuntimeError::with_span(
                    format!(
                        "{name}() expects (int, int) or (list<int>), got ({}, {})",
                        type_name(&a),
                        type_name(&b)
                    ),
                    call_span,
                )),
            }
        }
        1 => {
            let val = eval_expr(env, &args[0].value)?;
            match val {
                Value::List(ref items) => {
                    let mut iter = items.iter();
                    let first = match iter.next() {
                        Some(Value::Int(n)) => *n,
                        Some(other) => {
                            return Err(RuntimeError::with_span(
                                format!("{name}() list contains non-int: {}", type_name(other)),
                                call_span,
                            ));
                        }
                        None => {
                            return Err(RuntimeError::with_span(
                                format!("{name}() called on empty list"),
                                call_span,
                            ));
                        }
                    };
                    let mut result = first;
                    for item in iter {
                        match item {
                            Value::Int(n) => result = combine(result, *n),
                            other => {
                                return Err(RuntimeError::with_span(
                                    format!("{name}() list contains non-int: {}", type_name(other)),
                                    call_span,
                                ));
                            }
                        }
                    }
                    Ok(Value::Int(result))
                }
                _ => Err(RuntimeError::with_span(
                    format!(
                        "{name}() expects (int, int) or (list<int>), got ({})",
                        type_name(&val)
                    ),
                    call_span,
                )),
            }
        }
        _ => Err(RuntimeError::with_span(
            format!("{name}() requires 1 or 2 arguments, got {}", args.len()),
            call_span,
        )),
    }
}
