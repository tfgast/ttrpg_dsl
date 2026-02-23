use std::collections::BTreeMap;
use ttrpg_ast::Span;

use crate::Env;
use crate::RuntimeError;
use crate::effect::{Effect, Response};
use crate::value::{DiceExpr, Value};

// ── Builtin dispatch ───────────────────────────────────────────

/// Dispatch a builtin function call by name.
///
/// Arguments have already been evaluated and bound positionally.
pub(crate) fn call_builtin(
    env: &mut Env,
    name: &str,
    args: Vec<Value>,
    span: Span,
) -> Result<Value, RuntimeError> {
    match name {
        "floor" => builtin_floor(&args, span),
        "ceil" => builtin_ceil(&args, span),
        "min" => builtin_min(&args, span),
        "max" => builtin_max(&args, span),
        "distance" => builtin_distance(env, &args, span),
        "dice" => builtin_dice(&args, span),
        "multiply_dice" => builtin_multiply_dice(&args, span),
        "roll" => builtin_roll(env, &args, span),
        "apply_condition" => builtin_apply_condition(env, &args, span),
        "remove_condition" => builtin_remove_condition(env, &args, span),
        _ => Err(RuntimeError::with_span(
            format!("unknown builtin function '{}'", name),
            span,
        )),
    }
}

// ── floor ──────────────────────────────────────────────────────

/// `floor(x: Float) -> Int`
fn builtin_floor(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    match args.first() {
        Some(Value::Float(f)) => Ok(Value::Int(f.floor() as i64)),
        Some(other) => Err(RuntimeError::with_span(
            format!("floor() expects Float, got {}", type_name(other)),
            span,
        )),
        None => Err(RuntimeError::with_span("floor() requires 1 argument", span)),
    }
}

// ── ceil ───────────────────────────────────────────────────────

/// `ceil(x: Float) -> Int`
fn builtin_ceil(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    match args.first() {
        Some(Value::Float(f)) => Ok(Value::Int(f.ceil() as i64)),
        Some(other) => Err(RuntimeError::with_span(
            format!("ceil() expects Float, got {}", type_name(other)),
            span,
        )),
        None => Err(RuntimeError::with_span("ceil() requires 1 argument", span)),
    }
}

// ── min ────────────────────────────────────────────────────────

/// `min(a: Int, b: Int) -> Int`
fn builtin_min(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    match (args.first(), args.get(1)) {
        (Some(Value::Int(a)), Some(Value::Int(b))) => Ok(Value::Int((*a).min(*b))),
        (Some(a), Some(b)) => Err(RuntimeError::with_span(
            format!(
                "min() expects (Int, Int), got ({}, {})",
                type_name(a),
                type_name(b)
            ),
            span,
        )),
        _ => Err(RuntimeError::with_span("min() requires 2 arguments", span)),
    }
}

// ── max ────────────────────────────────────────────────────────

/// `max(a: Int, b: Int) -> Int`
fn builtin_max(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    match (args.first(), args.get(1)) {
        (Some(Value::Int(a)), Some(Value::Int(b))) => Ok(Value::Int((*a).max(*b))),
        (Some(a), Some(b)) => Err(RuntimeError::with_span(
            format!(
                "max() expects (Int, Int), got ({}, {})",
                type_name(a),
                type_name(b)
            ),
            span,
        )),
        _ => Err(RuntimeError::with_span("max() requires 2 arguments", span)),
    }
}

// ── distance ───────────────────────────────────────────────────

/// `distance(a: Position, b: Position) -> Int`
///
/// Delegates to `StateProvider::distance()`.
fn builtin_distance(env: &Env, args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    match (args.first(), args.get(1)) {
        (Some(a @ Value::Position(_)), Some(b @ Value::Position(_))) => {
            env.state.distance(a, b).map(Value::Int).ok_or_else(|| {
                RuntimeError::with_span("distance() received invalid position values", span)
            })
        }
        (Some(a), Some(b)) => Err(RuntimeError::with_span(
            format!(
                "distance() expects (Position, Position), got ({}, {})",
                type_name(a),
                type_name(b)
            ),
            span,
        )),
        _ => Err(RuntimeError::with_span(
            "distance() requires 2 arguments",
            span,
        )),
    }
}

// ── dice ────────────────────────────────────────────────────────

/// `dice(count: Int, sides: Int) -> DiceExpr`
///
/// Constructs a DiceExpr from runtime integer values.
/// count must be >= 0, sides must be >= 1, both must fit in u32.
fn builtin_dice(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    match (args.first(), args.get(1)) {
        (Some(Value::Int(count)), Some(Value::Int(sides))) => {
            if *count < 0 {
                return Err(RuntimeError::with_span(
                    format!("dice() count must be non-negative, got {}", count),
                    span,
                ));
            }
            if *sides < 1 {
                return Err(RuntimeError::with_span(
                    format!("dice() sides must be at least 1, got {}", sides),
                    span,
                ));
            }
            let count_u32 = u32::try_from(*count).map_err(|_| {
                RuntimeError::with_span(
                    format!("dice() count {} overflows u32", count),
                    span,
                )
            })?;
            let sides_u32 = u32::try_from(*sides).map_err(|_| {
                RuntimeError::with_span(
                    format!("dice() sides {} overflows u32", sides),
                    span,
                )
            })?;
            Ok(Value::DiceExpr(DiceExpr {
                count: count_u32,
                sides: sides_u32,
                filter: None,
                modifier: 0,
            }))
        }
        (Some(a), Some(b)) => Err(RuntimeError::with_span(
            format!(
                "dice() expects (Int, Int), got ({}, {})",
                type_name(a),
                type_name(b)
            ),
            span,
        )),
        _ => Err(RuntimeError::with_span(
            "dice() requires 2 arguments",
            span,
        )),
    }
}

// ── multiply_dice ──────────────────────────────────────────────

/// `multiply_dice(expr: DiceExpr, factor: Int) -> DiceExpr`
///
/// Multiplies the dice count by factor. Factor must be positive.
fn builtin_multiply_dice(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    match (args.first(), args.get(1)) {
        (Some(Value::DiceExpr(expr)), Some(Value::Int(factor))) => {
            if *factor <= 0 {
                return Err(RuntimeError::with_span(
                    format!("multiply_dice() factor must be positive, got {}", factor),
                    span,
                ));
            }
            let new_count = (expr.count as i64)
                .checked_mul(*factor)
                .and_then(|n| u32::try_from(n).ok())
                .ok_or_else(|| {
                    RuntimeError::with_span("dice count overflow in multiply_dice()", span)
                })?;
            Ok(Value::DiceExpr(DiceExpr {
                count: new_count,
                sides: expr.sides,
                filter: expr.filter,
                modifier: expr.modifier,
            }))
        }
        (Some(a), Some(b)) => Err(RuntimeError::with_span(
            format!(
                "multiply_dice() expects (DiceExpr, Int), got ({}, {})",
                type_name(a),
                type_name(b)
            ),
            span,
        )),
        _ => Err(RuntimeError::with_span(
            "multiply_dice() requires 2 arguments",
            span,
        )),
    }
}

// ── roll ───────────────────────────────────────────────────────

/// `roll(expr: DiceExpr) -> RollResult`
///
/// Emits a `RollDice` effect and expects `Rolled(RollResult)` or
/// `Override(RollResult)` back from the host.
fn builtin_roll(env: &mut Env, args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    match args.first() {
        Some(Value::DiceExpr(expr)) => {
            let effect = Effect::RollDice { expr: expr.clone() };
            let response = env.handler.handle(effect);
            match response {
                Response::Rolled(rr) => Ok(Value::RollResult(rr)),
                Response::Override(Value::RollResult(rr)) => Ok(Value::RollResult(rr)),
                _ => Err(RuntimeError::with_span(
                    format!(
                        "protocol error: expected Rolled or Override(RollResult) for RollDice, got {:?}",
                        response
                    ),
                    span,
                )),
            }
        }
        Some(other) => Err(RuntimeError::with_span(
            format!("roll() expects DiceExpr, got {}", type_name(other)),
            span,
        )),
        None => Err(RuntimeError::with_span("roll() requires 1 argument", span)),
    }
}

// ── apply_condition ────────────────────────────────────────────

/// `apply_condition(target: Entity, condition: Condition, duration: Duration) -> None`
///
/// Emits an `ApplyCondition` effect.
fn builtin_apply_condition(
    env: &mut Env,
    args: &[Value],
    span: Span,
) -> Result<Value, RuntimeError> {
    match (args.first(), args.get(1), args.get(2)) {
        (Some(Value::Entity(target)), Some(Value::Condition { name: cond_name, args: cond_args }), Some(duration)) => {
            let effect = Effect::ApplyCondition {
                target: *target,
                condition: cond_name.clone(),
                params: cond_args.clone(),
                duration: duration.clone(),
            };
            validate_mutation_response(env.handler.handle(effect), "ApplyCondition", span)?;
            Ok(Value::None)
        }
        (Some(Value::Entity(target)), Some(Value::Str(cond_name)), Some(duration)) => {
            // Also accept String for condition name (common in DSL)
            let effect = Effect::ApplyCondition {
                target: *target,
                condition: cond_name.clone(),
                params: BTreeMap::new(),
                duration: duration.clone(),
            };
            validate_mutation_response(env.handler.handle(effect), "ApplyCondition", span)?;
            Ok(Value::None)
        }
        (Some(a), Some(b), Some(c)) => Err(RuntimeError::with_span(
            format!(
                "apply_condition() expects (Entity, Condition, Duration), got ({}, {}, {})",
                type_name(a),
                type_name(b),
                type_name(c)
            ),
            span,
        )),
        _ => Err(RuntimeError::with_span(
            "apply_condition() requires 3 arguments",
            span,
        )),
    }
}

// ── remove_condition ───────────────────────────────────────────

/// `remove_condition(target: Entity, condition: Condition) -> None`
///
/// Emits a `RemoveCondition` effect.
fn builtin_remove_condition(
    env: &mut Env,
    args: &[Value],
    span: Span,
) -> Result<Value, RuntimeError> {
    match (args.first(), args.get(1)) {
        (Some(Value::Entity(target)), Some(Value::Condition { name: cond_name, args: cond_args })) => {
            let effect = Effect::RemoveCondition {
                target: *target,
                condition: cond_name.clone(),
                params: if cond_args.is_empty() { None } else { Some(cond_args.clone()) },
            };
            validate_mutation_response(env.handler.handle(effect), "RemoveCondition", span)?;
            Ok(Value::None)
        }
        (Some(Value::Entity(target)), Some(Value::Str(cond_name))) => {
            let effect = Effect::RemoveCondition {
                target: *target,
                condition: cond_name.clone(),
                params: None,
            };
            validate_mutation_response(env.handler.handle(effect), "RemoveCondition", span)?;
            Ok(Value::None)
        }
        (Some(a), Some(b)) => Err(RuntimeError::with_span(
            format!(
                "remove_condition() expects (Entity, Condition), got ({}, {})",
                type_name(a),
                type_name(b)
            ),
            span,
        )),
        _ => Err(RuntimeError::with_span(
            "remove_condition() requires 2 arguments",
            span,
        )),
    }
}

// ── Helpers ────────────────────────────────────────────────────

/// Validate a response to a mutation effect (ApplyCondition, RemoveCondition).
///
/// Mutation effects accept `Acknowledged`, `Override(Value)`, and `Vetoed`.
/// Any other response (e.g., `Rolled`, `PromptResult`) is a protocol error.
fn validate_mutation_response(
    response: Response,
    effect_name: &str,
    span: Span,
) -> Result<(), RuntimeError> {
    match response {
        Response::Acknowledged | Response::Override(_) | Response::Vetoed => Ok(()),
        _ => Err(RuntimeError::with_span(
            format!(
                "protocol error: unsupported response for {}: {:?}",
                effect_name, response
            ),
            span,
        )),
    }
}

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
        Value::Condition { .. } => "Condition",
        Value::EnumNamespace(_) => "EnumNamespace",
    }
}
