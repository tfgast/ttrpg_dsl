use std::collections::{BTreeMap, BTreeSet};
use ttrpg_ast::Name;
use ttrpg_ast::Span;

use crate::effect::{Effect, Response};
use crate::value::{DiceExpr, Value};
use crate::Env;
use crate::RuntimeError;

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
        // min/max are handled in collection_builtins (support list overloads)
        "distance" => builtin_distance(env, &args, span),
        "conditions" => builtin_conditions(env, &args, span),
        "has_condition" => builtin_has_condition(env, &args, span),
        "dice" => builtin_dice(&args, span),
        "multiply_dice" => builtin_multiply_dice(&args, span),
        "max_value" => builtin_max_value(&args, span),
        "dice_count" => builtin_dice_count(&args, span),
        "dice_sides" => builtin_dice_sides(&args, span),
        "dice_modifier" => builtin_dice_modifier(&args, span),
        "error" => builtin_error(&args, span),
        "roll" => builtin_roll(env, &args, span),
        "apply_condition" => builtin_apply_condition(env, &args, span),
        "remove_condition" => builtin_remove_condition(env, &args, span),
        "invocation" => builtin_invocation(env, &args, span),
        "revoke" => builtin_revoke(env, &args, span),
        "game_time" => builtin_game_time(env, &args, span),
        "advance_time" => builtin_advance_time(env, &args, span),
        "budget_of" => builtin_budget_of(env, &args, span),
        "despawn" => builtin_despawn(env, &args, span),
        "suspend" => builtin_suspend(env, &args, span),
        "suspend_with_source" => builtin_suspend_with_source(env, &args, span),
        "remove_suspension_source" => builtin_remove_suspension_source(env, &args, span),
        "is_suspended" => builtin_is_suspended(env, &args, span),
        "is_off_board" => builtin_is_off_board(env, &args, span),
        "are_turns_frozen" => builtin_are_turns_frozen(env, &args, span),
        "are_durations_frozen" => builtin_are_durations_frozen(env, &args, span),
        "condition_token" => builtin_condition_token(env, &args, span),
        "process_periodic_conditions" => builtin_process_periodic_conditions(env, &args, span),
        _ => Err(RuntimeError::with_span(
            format!("unknown builtin function '{name}'"),
            span,
        )),
    }
}

// ── error ─────────────────────────────────────────────────────

/// `error(message: String) -> <never>`
///
/// Always aborts evaluation with the provided message.
fn builtin_error(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    match args.first() {
        Some(Value::Str(message)) => Err(RuntimeError::with_span(message.clone(), span)),
        Some(other) => Err(RuntimeError::with_span(
            format!("error() expects String, got {}", type_name(other)),
            span,
        )),
        None => Err(RuntimeError::with_span("error() requires 1 argument", span)),
    }
}

// ── floor ──────────────────────────────────────────────────────

/// `floor(x: Float) -> Int`
fn builtin_floor(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    match args.first() {
        Some(Value::Float(f)) => {
            if f.is_nan() {
                return Err(RuntimeError::with_span("floor() received NaN", span));
            }
            if f.is_infinite() {
                return Err(RuntimeError::with_span("floor() received infinity", span));
            }
            let floored = f.floor();
            if floored < (i64::MIN as f64) || floored > (i64::MAX as f64) {
                return Err(RuntimeError::with_span(
                    format!("floor({f}) overflows integer range"),
                    span,
                ));
            }
            Ok(Value::Int(floored as i64))
        }
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
        Some(Value::Float(f)) => {
            if f.is_nan() {
                return Err(RuntimeError::with_span("ceil() received NaN", span));
            }
            if f.is_infinite() {
                return Err(RuntimeError::with_span("ceil() received infinity", span));
            }
            let ceiled = f.ceil();
            if ceiled < (i64::MIN as f64) || ceiled > (i64::MAX as f64) {
                return Err(RuntimeError::with_span(
                    format!("ceil({f}) overflows integer range"),
                    span,
                ));
            }
            Ok(Value::Int(ceiled as i64))
        }
        Some(other) => Err(RuntimeError::with_span(
            format!("ceil() expects Float, got {}", type_name(other)),
            span,
        )),
        None => Err(RuntimeError::with_span("ceil() requires 1 argument", span)),
    }
}

// ── distance ───────────────────────────────────────────────────

/// `distance(a: Position, b: Position) -> Int`
///
/// Delegates to `StateProvider::distance()`.
fn builtin_distance(env: &Env, args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    match (args.first(), args.get(1)) {
        (Some(Value::Position(pa)), Some(Value::Position(pb))) => env
            .state
            .distance(pa.0, pb.0)
            .map(Value::Int)
            .ok_or_else(|| {
                RuntimeError::with_span("distance() received invalid position values", span)
            }),
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

// ── conditions ────────────────────────────────────────────────────

/// `conditions(entity: Entity) -> list<ActiveCondition>`
///
/// Returns the active conditions on an entity, ordered by `gained_at` (oldest first).
fn builtin_conditions(env: &Env, args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    match args.first() {
        Some(Value::Entity(entity)) => match env.state.read_conditions(entity) {
            Some(conditions) => {
                let values = conditions.iter().map(|c| c.to_value()).collect();
                Ok(Value::List(values))
            }
            None => Err(RuntimeError::with_span(
                format!("conditions() called on unknown entity: {entity:?}"),
                span,
            )),
        },
        Some(other) => Err(RuntimeError::with_span(
            format!("conditions() expects Entity, got {}", type_name(other)),
            span,
        )),
        None => Err(RuntimeError::with_span(
            "conditions() requires 1 argument",
            span,
        )),
    }
}

// ── has_condition ─────────────────────────────────────────────

/// `has_condition(entity: Entity, name: String) -> Bool`
///
/// Returns true if the entity currently has an active condition with the given name.
fn builtin_has_condition(env: &Env, args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    match (args.first(), args.get(1)) {
        (Some(Value::Entity(entity)), Some(Value::Str(cond_name))) => {
            match env.state.read_conditions(entity) {
                Some(conditions) => {
                    let has_it = conditions
                        .iter()
                        .any(|c| c.name.as_str() == cond_name.as_str());
                    Ok(Value::Bool(has_it))
                }
                None => Err(RuntimeError::with_span(
                    format!("has_condition() called on unknown entity: {entity:?}"),
                    span,
                )),
            }
        }
        (Some(Value::Entity(_)), Some(other)) => Err(RuntimeError::with_span(
            format!(
                "has_condition() expects String as second argument, got {}",
                type_name(other)
            ),
            span,
        )),
        (Some(other), _) => Err(RuntimeError::with_span(
            format!(
                "has_condition() expects Entity as first argument, got {}",
                type_name(other)
            ),
            span,
        )),
        _ => Err(RuntimeError::with_span(
            "has_condition() requires 2 arguments",
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
                    format!("dice() count must be non-negative, got {count}"),
                    span,
                ));
            }
            if *sides < 1 {
                return Err(RuntimeError::with_span(
                    format!("dice() sides must be at least 1, got {sides}"),
                    span,
                ));
            }
            let count_u32 = u32::try_from(*count).map_err(|_| {
                RuntimeError::with_span(format!("dice() count {count} overflows u32"), span)
            })?;
            let sides_u32 = u32::try_from(*sides).map_err(|_| {
                RuntimeError::with_span(format!("dice() sides {sides} overflows u32"), span)
            })?;
            Ok(Value::DiceExpr(DiceExpr::single(
                count_u32, sides_u32, None, 0,
            )))
        }
        (Some(a), Some(b)) => Err(RuntimeError::with_span(
            format!(
                "dice() expects (Int, Int), got ({}, {})",
                type_name(a),
                type_name(b)
            ),
            span,
        )),
        _ => Err(RuntimeError::with_span("dice() requires 2 arguments", span)),
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
                    format!("multiply_dice() factor must be positive, got {factor}"),
                    span,
                ));
            }
            let mut new_groups = Vec::with_capacity(expr.groups.len());
            for g in &expr.groups {
                let new_count = (g.count as i64)
                    .checked_mul(*factor)
                    .and_then(|n| u32::try_from(n).ok())
                    .ok_or_else(|| {
                        RuntimeError::with_span("dice count overflow in multiply_dice()", span)
                    })?;
                new_groups.push(crate::value::DiceGroup {
                    count: new_count,
                    sides: g.sides,
                    filter: g.filter,
                });
            }
            Ok(Value::DiceExpr(DiceExpr {
                groups: new_groups,
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

// ── max_value ─────────────────────────────────────────────────

/// `max_value(expr: DiceExpr) -> Int`
///
/// Returns the maximum possible value of a dice expression.
/// For each group, computes effective_count * sides, then adds the modifier.
/// Accounts for keep/drop filters.
fn builtin_max_value(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    match args.first() {
        Some(Value::DiceExpr(expr)) => {
            let max_dice: i64 = expr
                .groups
                .iter()
                .map(|g| {
                    let effective = match g.filter {
                        Some(
                            ttrpg_ast::DiceFilter::KeepHighest(n)
                            | ttrpg_ast::DiceFilter::KeepLowest(n),
                        ) => n,
                        Some(
                            ttrpg_ast::DiceFilter::DropHighest(n)
                            | ttrpg_ast::DiceFilter::DropLowest(n),
                        ) => g.count.saturating_sub(n),
                        None => g.count,
                    };
                    (effective as i64) * (g.sides as i64)
                })
                .sum();
            Ok(Value::Int(max_dice + expr.modifier))
        }
        Some(other) => Err(RuntimeError::with_span(
            format!("max_value() expects DiceExpr, got {}", type_name(other)),
            span,
        )),
        None => Err(RuntimeError::with_span(
            "max_value() requires 1 argument",
            span,
        )),
    }
}

// ── dice_count ────────────────────────────────────────────────

/// `dice_count(expr: DiceExpr) -> Int`
///
/// Returns the total number of dice across all groups.
fn builtin_dice_count(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    match args.first() {
        Some(Value::DiceExpr(expr)) => Ok(Value::Int(expr.total_dice_count() as i64)),
        Some(other) => Err(RuntimeError::with_span(
            format!("dice_count() expects DiceExpr, got {}", type_name(other)),
            span,
        )),
        None => Err(RuntimeError::with_span(
            "dice_count() requires 1 argument",
            span,
        )),
    }
}

// ── dice_sides ────────────────────────────────────────────────

/// `dice_sides(expr: DiceExpr) -> Int`
///
/// Returns the number of sides per die. All groups must have the
/// same die size; errors if the expression has mixed die sizes.
fn builtin_dice_sides(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    match args.first() {
        Some(Value::DiceExpr(expr)) => {
            if expr.groups.is_empty() {
                return Err(RuntimeError::with_span(
                    "dice_sides() called on dice expression with no dice groups",
                    span,
                ));
            }
            let sides = expr.groups[0].sides;
            for g in &expr.groups[1..] {
                if g.sides != sides {
                    return Err(RuntimeError::with_span(
                        format!(
                            "dice_sides() requires uniform die size, got d{} and d{}",
                            sides, g.sides
                        ),
                        span,
                    ));
                }
            }
            Ok(Value::Int(sides as i64))
        }
        Some(other) => Err(RuntimeError::with_span(
            format!("dice_sides() expects DiceExpr, got {}", type_name(other)),
            span,
        )),
        None => Err(RuntimeError::with_span(
            "dice_sides() requires 1 argument",
            span,
        )),
    }
}

// ── dice_modifier ─────────────────────────────────────────────

/// `dice_modifier(expr: DiceExpr) -> Int`
///
/// Returns the flat modifier of the dice expression.
fn builtin_dice_modifier(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    match args.first() {
        Some(Value::DiceExpr(expr)) => Ok(Value::Int(expr.modifier)),
        Some(other) => Err(RuntimeError::with_span(
            format!("dice_modifier() expects DiceExpr, got {}", type_name(other)),
            span,
        )),
        None => Err(RuntimeError::with_span(
            "dice_modifier() requires 1 argument",
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
                        "protocol error: expected Rolled or Override(RollResult) for RollDice, got {response:?}"
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
/// Two-phase lifecycle:
/// 1. Emit `ConditionApplyGate` — if host vetoes, return early (no condition)
/// 2. Execute `on_apply` lifecycle blocks
/// 3. If on_apply succeeds, emit `ApplyCondition` to activate
/// 4. If on_apply errors, propagate error (condition never activates)
fn builtin_apply_condition(
    env: &mut Env,
    args: &[Value],
    span: Span,
) -> Result<Value, RuntimeError> {
    if env.in_lifecycle_block > 0 {
        return Err(RuntimeError::with_span(
            "apply_condition() cannot be called inside on_apply/on_remove blocks",
            span,
        ));
    }

    // Extract arguments (3 required + 1 optional source)
    let (target, cond_name, cond_args, duration) = match (args.first(), args.get(1), args.get(2)) {
        (
            Some(Value::Entity(target)),
            Some(Value::Condition {
                name: cond_name,
                args: cond_args,
            }),
            Some(duration),
        ) => (
            *target,
            cond_name.clone(),
            cond_args.clone(),
            duration.clone(),
        ),
        (Some(Value::Entity(target)), Some(Value::Str(cond_name)), Some(duration)) => (
            *target,
            Name::from(cond_name.as_str()),
            BTreeMap::new(),
            duration.clone(),
        ),
        (Some(a), Some(b), Some(c)) => {
            return Err(RuntimeError::with_span(
                format!(
                    "apply_condition() expects (Entity, Condition, Duration[, EffectSource]), got ({}, {}, {})",
                    type_name(a),
                    type_name(b),
                    type_name(c)
                ),
                span,
            ));
        }
        _ => {
            return Err(RuntimeError::with_span(
                "apply_condition() requires 3-4 arguments",
                span,
            ));
        }
    };

    // Optional 4th argument: EffectSource (defaults to EffectSource.Unknown)
    let source = if let Some(s) = args.get(3) {
        s.clone()
    } else {
        crate::value::effect_source_unknown()
    };

    // Look up declaration tags for this condition
    let tags: BTreeSet<Name> = env
        .interp
        .type_env
        .conditions
        .get(&cond_name)
        .map(|info| info.tags.iter().cloned().collect())
        .unwrap_or_default();

    // Pre-allocate condition ID so lifecycle blocks can reference it
    let token = env.interp.alloc_condition_id()?;

    // Phase 1: Gate — host can veto
    let gate = Effect::ConditionApplyGate {
        target,
        condition: cond_name.clone(),
        params: cond_args.clone(),
        duration: duration.clone(),
        invocation: env.current_invocation_id,
        source: source.clone(),
        tags: tags.clone(),
    };
    match env.handler.handle(gate) {
        Response::Vetoed => return Ok(Value::Void),
        Response::Acknowledged => {}
        other => {
            return Err(RuntimeError::with_span(
                format!("protocol error: unexpected response for ConditionApplyGate: {other:?}"),
                span,
            ));
        }
    }

    // Phase 2: Execute on_apply lifecycle blocks (token available via env)
    let saved_token = env.current_condition_token;
    env.current_condition_token = Some(token);
    let lifecycle_result = crate::pipeline::execute_lifecycle_blocks(
        env,
        cond_name.as_str(),
        target,
        &cond_args,
        crate::pipeline::LifecycleKind::OnApply,
    );
    env.current_condition_token = saved_token;
    lifecycle_result?;

    // Phase 3: Activate the condition (using pre-allocated ID)
    let effect = Effect::ApplyCondition {
        target,
        condition: cond_name,
        params: cond_args,
        duration,
        invocation: env.current_invocation_id,
        source,
        tags,
        condition_id: token.0,
    };
    validate_mutation_response(env.handler.handle(effect), "ApplyCondition", span)?;
    Ok(Value::Void)
}

// ── remove_condition ───────────────────────────────────────────

/// `remove_condition(target: Entity, condition: Condition | ActiveCondition) -> None`
///
/// Two-phase lifecycle per instance:
/// 1. Emit `ConditionRemovalGate` — if host vetoes, skip (condition stays)
/// 2. Execute `on_remove` lifecycle blocks (condition still active)
/// 3. Emit `RemoveCondition` to strip it — always, even if on_remove errored
/// 4. Propagate first on_remove error after all instances processed
fn builtin_remove_condition(
    env: &mut Env,
    args: &[Value],
    span: Span,
) -> Result<Value, RuntimeError> {
    if env.in_lifecycle_block > 0 {
        return Err(RuntimeError::with_span(
            "remove_condition() cannot be called inside on_apply/on_remove blocks",
            span,
        ));
    }

    // Resolve the target entity and matching condition instances
    let (target, instances) = match (args.first(), args.get(1)) {
        (
            Some(Value::Entity(target)),
            Some(Value::Condition {
                name: cond_name,
                args: cond_args,
            }),
        ) => {
            let conditions = env.state.read_conditions(target).unwrap_or_default();
            let matching: Vec<_> = conditions
                .into_iter()
                .filter(|c| c.name == *cond_name && c.params == *cond_args)
                .collect();
            (*target, matching)
        }
        (Some(Value::Entity(target)), Some(Value::Str(cond_name))) => {
            let conditions = env.state.read_conditions(target).unwrap_or_default();
            let name = Name::from(cond_name.as_str());
            let matching: Vec<_> = conditions.into_iter().filter(|c| c.name == name).collect();
            (*target, matching)
        }
        (Some(Value::Entity(target)), Some(Value::Struct { name, fields }))
            if name == "ActiveCondition" =>
        {
            let cond_id = match fields.get("id") {
                Some(Value::Int(id)) if *id >= 0 => *id as u64,
                Some(Value::Int(_)) => {
                    return Err(RuntimeError::with_span(
                        "ActiveCondition id must be non-negative",
                        span,
                    ));
                }
                _ => {
                    return Err(RuntimeError::with_span(
                        "ActiveCondition missing 'id' field",
                        span,
                    ));
                }
            };
            let cond_name = match fields.get("name") {
                Some(Value::Str(s)) => Name::from(s.as_str()),
                _ => Name::from("?"),
            };
            let cond_params = match fields.get("params") {
                Some(Value::Map(m)) => {
                    let mut params = BTreeMap::new();
                    for (k, v) in m {
                        if let Value::Str(key) = k {
                            params.insert(Name::from(key.as_str()), v.clone());
                        }
                    }
                    params
                }
                _ => BTreeMap::new(),
            };
            let instance = crate::state::ActiveCondition {
                id: cond_id,
                name: cond_name,
                params: cond_params,
                bearer: *target,
                gained_at: 0,
                duration: Value::Void,
                invocation: None,
                applied_at: 0,
                source: crate::value::effect_source_unknown(),
                tags: BTreeSet::new(),
            };
            (*target, vec![instance])
        }
        (Some(a), Some(b)) => {
            return Err(RuntimeError::with_span(
                format!(
                    "remove_condition() expects (Entity, Condition), got ({}, {})",
                    type_name(a),
                    type_name(b)
                ),
                span,
            ));
        }
        _ => {
            return Err(RuntimeError::with_span(
                "remove_condition() requires 2 arguments",
                span,
            ));
        }
    };

    // Process each instance with lifecycle hooks
    remove_condition_instances(env, target, &instances, span)?;
    Ok(Value::Void)
}

/// Shared helper: per-instance gate → on_remove → remove flow.
///
/// For each instance (in `gained_at` order):
/// 1. Emit `ConditionRemovalGate` — if vetoed, skip
/// 2. Execute `on_remove` lifecycle blocks (condition still active during execution)
/// 3. Emit `RemoveCondition` to strip it — always, even if on_remove errored
/// 4. Collect first on_remove error; propagate after loop
fn remove_condition_instances(
    env: &mut Env,
    target: crate::state::EntityRef,
    instances: &[crate::state::ActiveCondition],
    span: Span,
) -> Result<(), RuntimeError> {
    let mut first_error: Option<RuntimeError> = None;

    // Sort by gained_at (instances should already be sorted, but be safe)
    let mut sorted: Vec<_> = instances.to_vec();
    sorted.sort_by_key(|c| c.gained_at);

    for instance in &sorted {
        // Phase 1: Gate
        let gate = Effect::ConditionRemovalGate {
            target,
            condition: instance.name.clone(),
            id: instance.id,
        };
        match env.handler.handle(gate) {
            Response::Vetoed => continue,
            Response::Acknowledged => {}
            _ => {} // Treat unexpected responses as acknowledged
        }

        // Phase 2: on_remove lifecycle blocks
        let lifecycle_result = crate::pipeline::execute_lifecycle_blocks(
            env,
            instance.name.as_str(),
            target,
            &instance.params,
            crate::pipeline::LifecycleKind::OnRemove,
        );
        if let Err(e) = lifecycle_result {
            if first_error.is_none() {
                first_error = Some(e);
            }
        }

        // Phase 3: Always remove the condition, even if on_remove errored
        let effect = Effect::RemoveCondition {
            target,
            condition: instance.name.clone(),
            params: None,
            id: Some(instance.id),
        };
        if let Err(e) =
            validate_mutation_response(env.handler.handle(effect), "RemoveCondition", span)
        {
            if first_error.is_none() {
                first_error = Some(e);
            }
        }

        // Phase 4: Auto-cleanup suspension records keyed to this condition
        // This happens after RemoveCondition succeeds, not during on_remove.
        let suspension_effect = Effect::RemoveSuspensionSource {
            entity: target,
            source_id: instance.id,
        };
        let _ = env.handler.handle(suspension_effect);
    }

    if let Some(err) = first_error {
        Err(err)
    } else {
        Ok(())
    }
}

// ── invocation ─────────────────────────────────────────────

/// `invocation() -> Invocation`
///
/// Returns the current invocation ID. Must be called inside an action,
/// reaction, or hook scope — errors otherwise.
fn builtin_invocation(env: &Env, args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    if !args.is_empty() {
        return Err(RuntimeError::with_span(
            "invocation() takes no arguments",
            span,
        ));
    }
    match env.current_invocation_id {
        Some(id) => Ok(Value::Invocation(id)),
        None => Err(RuntimeError::with_span(
            "invocation() called outside of action/reaction/hook scope",
            span,
        )),
    }
}

// ── revoke ─────────────────────────────────────────────────

/// `revoke(inv: Invocation | option<Invocation> | none) -> none`
///
/// Finds all conditions tagged with the given invocation across all entities,
/// runs their on_remove lifecycle blocks, and removes them.
/// Accepts `none` or `Option(None)` as a no-op (nothing to revoke).
fn builtin_revoke(env: &mut Env, args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    if env.in_lifecycle_block > 0 {
        return Err(RuntimeError::with_span(
            "revoke() cannot be called inside on_apply/on_remove blocks",
            span,
        ));
    }

    let arg = args
        .first()
        .ok_or_else(|| RuntimeError::with_span("revoke() requires 1 argument", span))?;

    let inv_id = match arg {
        Value::Invocation(id) => *id,
        Value::Option(Some(inner)) => match inner.as_ref() {
            Value::Invocation(id) => *id,
            other => {
                return Err(RuntimeError::with_span(
                    format!(
                        "revoke() expects Invocation inside Option, got {}",
                        type_name(other)
                    ),
                    span,
                ));
            }
        },
        Value::Option(None) | Value::Void => return Ok(Value::Void),
        other => {
            return Err(RuntimeError::with_span(
                format!(
                    "revoke() expects Invocation or option<Invocation>, got {}",
                    type_name(other)
                ),
                span,
            ));
        }
    };

    // Collect all conditions with this invocation across all entities
    let entities = env.state.all_entities();
    let mut matching: Vec<(crate::state::EntityRef, crate::state::ActiveCondition)> = Vec::new();
    for entity in &entities {
        if let Some(conditions) = env.state.read_conditions(entity) {
            for cond in conditions {
                if cond.invocation == Some(inv_id) {
                    matching.push((*entity, cond));
                }
            }
        }
    }

    // Sort by gained_at
    matching.sort_by_key(|(_, c)| c.gained_at);

    // Run lifecycle hooks + remove for each
    let mut first_error: Option<RuntimeError> = None;
    for (entity, instance) in &matching {
        // Gate
        let gate = Effect::ConditionRemovalGate {
            target: *entity,
            condition: instance.name.clone(),
            id: instance.id,
        };
        if let Response::Vetoed = env.handler.handle(gate) {
            continue;
        }

        // on_remove lifecycle
        let lifecycle_result = crate::pipeline::execute_lifecycle_blocks(
            env,
            instance.name.as_str(),
            *entity,
            &instance.params,
            crate::pipeline::LifecycleKind::OnRemove,
        );
        if let Err(e) = lifecycle_result {
            if first_error.is_none() {
                first_error = Some(e);
            }
        }

        // Always remove
        let effect = Effect::RemoveCondition {
            target: *entity,
            condition: instance.name.clone(),
            params: None,
            id: Some(instance.id),
        };
        let _ = validate_mutation_response(env.handler.handle(effect), "RemoveCondition", span);
    }

    // Also emit RevokeInvocation for the host to do any cleanup
    let effect = Effect::RevokeInvocation { invocation: inv_id };
    let _ = validate_mutation_response(env.handler.handle(effect), "RevokeInvocation", span);

    if let Some(err) = first_error {
        Err(err)
    } else {
        Ok(Value::Void)
    }
}

// ── game_time ──────────────────────────────────────────────────

/// `game_time() -> Int`
///
/// Returns the current game time counter. Pure read, no context restriction.
fn builtin_game_time(env: &Env, args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    if !args.is_empty() {
        return Err(RuntimeError::with_span(
            "game_time() takes no arguments",
            span,
        ));
    }
    Ok(Value::Int(env.state.read_game_time() as i64))
}

// ── advance_time ───────────────────────────────────────────────

/// `advance_time(amount: Int) -> None`
///
/// Advances the game time counter by `amount`. Must be positive.
/// Cannot be called during action/reaction/hook execution.
fn builtin_advance_time(env: &mut Env, args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    if env.current_invocation_id.is_some() {
        return Err(RuntimeError::with_span(
            "advance_time() cannot be called during action/reaction/hook execution",
            span,
        ));
    }
    match args.first() {
        Some(Value::Int(amount)) if *amount > 0 => {
            let effect = Effect::AdvanceTime {
                amount: *amount as u64,
            };
            validate_mutation_response(env.handler.handle(effect), "AdvanceTime", span)?;
            Ok(Value::Void)
        }
        Some(Value::Int(amount)) if *amount == 0 => Err(RuntimeError::with_span(
            "advance_time() amount must be positive, got 0",
            span,
        )),
        Some(Value::Int(amount)) => Err(RuntimeError::with_span(
            format!("advance_time() amount must be positive, got {amount}"),
            span,
        )),
        Some(other) => Err(RuntimeError::with_span(
            format!("advance_time() expects Int, got {}", type_name(other)),
            span,
        )),
        None => Err(RuntimeError::with_span(
            "advance_time() requires 1 argument",
            span,
        )),
    }
}

// ── budget_of ─────────────────────────────────────────────────

/// `budget_of(entity: Entity) -> TurnBudget`
///
/// Returns the currently provisioned turn budget for an entity,
/// without requiring `turn_actor` context.  Useful for querying
/// remaining budget from within `with_budget` / `with_budgets`
/// bodies (outside of an action dispatch).
fn builtin_budget_of(env: &mut Env, args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    let entity = match args.first() {
        Some(Value::Entity(r)) => r,
        Some(other) => {
            return Err(RuntimeError::with_span(
                format!("budget_of() expects entity, got {}", type_name(other)),
                span,
            ))
        }
        None => {
            return Err(RuntimeError::with_span(
                "budget_of() requires 1 argument",
                span,
            ))
        }
    };
    let budget = env
        .state
        .read_turn_budget(entity)
        .ok_or_else(|| RuntimeError::with_span("no turn budget provisioned for entity", span))?;
    Ok(Value::Struct {
        name: Name::from("TurnBudget"),
        fields: budget,
    })
}

// ── despawn ────────────────────────────────────────────────────

/// `despawn(entity: Entity) -> None`
///
/// Removes an entity from the game state, including all associated
/// conditions and turn budgets.
fn builtin_despawn(env: &mut Env, args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    match args.first() {
        Some(Value::Entity(entity)) => {
            let effect = Effect::RemoveEntity { entity: *entity };
            validate_mutation_response(env.handler.handle(effect), "RemoveEntity", span)?;
            Ok(Value::Void)
        }
        Some(other) => Err(RuntimeError::with_span(
            format!("despawn() expects entity, got {}", type_name(other)),
            span,
        )),
        None => Err(RuntimeError::with_span(
            "despawn() requires 1 argument",
            span,
        )),
    }
}

// ── suspend / suspension queries ──────────────────────────────

/// Parse a DSL `Presence` enum variant into the Rust `Presence` type.
fn parse_presence(val: &Value, span: Span) -> Result<crate::state::Presence, RuntimeError> {
    match val {
        Value::EnumVariant {
            enum_name, variant, ..
        } if enum_name == "Presence" => match variant.as_str() {
            "OnMap" => Ok(crate::state::Presence::OnMap),
            "OffBoard" => Ok(crate::state::Presence::OffBoard),
            _ => Err(RuntimeError::with_span(
                format!("unknown Presence variant '{variant}'"),
                span,
            )),
        },
        _ => Err(RuntimeError::with_span(
            format!("expected Presence enum, got {}", type_name(val)),
            span,
        )),
    }
}

/// `suspend(entity, presence: Presence, freeze_turns: bool, freeze_durations: bool) -> unit`
///
/// Only legal inside lifecycle blocks (on_apply/on_remove). Auto-keyed to
/// the current condition token.
fn builtin_suspend(env: &mut Env, args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    if env.in_lifecycle_block == 0 {
        return Err(RuntimeError::with_span(
            "suspend() can only be called inside on_apply/on_remove blocks. \
             Use suspend_with_source() for explicit source keying outside lifecycle blocks.",
            span,
        ));
    }

    let token = env.current_condition_token.ok_or_else(|| {
        RuntimeError::with_span(
            "suspend() requires a condition token (no condition being applied/removed)",
            span,
        )
    })?;

    match (args.first(), args.get(1), args.get(2), args.get(3)) {
        (
            Some(Value::Entity(entity)),
            Some(presence_val),
            Some(Value::Bool(freeze_turns)),
            Some(Value::Bool(freeze_durations)),
        ) => {
            let presence = parse_presence(presence_val, span)?;
            let effect = Effect::AddSuspension {
                entity: *entity,
                source_id: token.0,
                presence,
                freeze_turns: *freeze_turns,
                freeze_durations: *freeze_durations,
            };
            validate_mutation_response(env.handler.handle(effect), "AddSuspension", span)?;
            Ok(Value::Void)
        }
        _ => Err(RuntimeError::with_span(
            "suspend() requires 4 arguments: (entity, Presence, bool, bool)",
            span,
        )),
    }
}

/// `suspend_with_source(entity, source_id: int, presence: Presence, freeze_turns: bool, freeze_durations: bool) -> unit`
///
/// Escape hatch for explicit source keying. Legal anywhere.
fn builtin_suspend_with_source(
    env: &mut Env,
    args: &[Value],
    span: Span,
) -> Result<Value, RuntimeError> {
    match (
        args.first(),
        args.get(1),
        args.get(2),
        args.get(3),
        args.get(4),
    ) {
        (
            Some(Value::Entity(entity)),
            Some(Value::Int(source_id)),
            Some(presence_val),
            Some(Value::Bool(freeze_turns)),
            Some(Value::Bool(freeze_durations)),
        ) if *source_id >= 0 => {
            let presence = parse_presence(presence_val, span)?;
            let effect = Effect::AddSuspension {
                entity: *entity,
                source_id: *source_id as u64,
                presence,
                freeze_turns: *freeze_turns,
                freeze_durations: *freeze_durations,
            };
            validate_mutation_response(env.handler.handle(effect), "AddSuspension", span)?;
            Ok(Value::Void)
        }
        _ => Err(RuntimeError::with_span(
            "suspend_with_source() requires 5 arguments: (entity, int, Presence, bool, bool)",
            span,
        )),
    }
}

/// `remove_suspension_source(entity, source_id: int) -> unit`
fn builtin_remove_suspension_source(
    env: &mut Env,
    args: &[Value],
    span: Span,
) -> Result<Value, RuntimeError> {
    match (args.first(), args.get(1)) {
        (Some(Value::Entity(entity)), Some(Value::Int(source_id))) if *source_id >= 0 => {
            let effect = Effect::RemoveSuspensionSource {
                entity: *entity,
                source_id: *source_id as u64,
            };
            validate_mutation_response(env.handler.handle(effect), "RemoveSuspensionSource", span)?;
            Ok(Value::Void)
        }
        _ => Err(RuntimeError::with_span(
            "remove_suspension_source() requires 2 arguments: (entity, int)",
            span,
        )),
    }
}

/// `is_suspended(entity) -> bool`
fn builtin_is_suspended(env: &Env, args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    match args.first() {
        Some(Value::Entity(entity)) => Ok(Value::Bool(env.state.is_suspended(entity))),
        _ => Err(RuntimeError::with_span(
            "is_suspended() requires 1 entity argument",
            span,
        )),
    }
}

/// `is_off_board(entity) -> bool`
fn builtin_is_off_board(env: &Env, args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    match args.first() {
        Some(Value::Entity(entity)) => Ok(Value::Bool(env.state.is_off_board(entity))),
        _ => Err(RuntimeError::with_span(
            "is_off_board() requires 1 entity argument",
            span,
        )),
    }
}

/// `are_turns_frozen(entity) -> bool`
fn builtin_are_turns_frozen(env: &Env, args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    match args.first() {
        Some(Value::Entity(entity)) => Ok(Value::Bool(env.state.are_turns_frozen(entity))),
        _ => Err(RuntimeError::with_span(
            "are_turns_frozen() requires 1 entity argument",
            span,
        )),
    }
}

/// `are_durations_frozen(entity) -> bool`
fn builtin_are_durations_frozen(
    env: &Env,
    args: &[Value],
    span: Span,
) -> Result<Value, RuntimeError> {
    match args.first() {
        Some(Value::Entity(entity)) => Ok(Value::Bool(env.state.are_durations_frozen(entity))),
        _ => Err(RuntimeError::with_span(
            "are_durations_frozen() requires 1 entity argument",
            span,
        )),
    }
}

/// `condition_token() -> int`
///
/// Returns the current condition token ID. Only valid inside lifecycle blocks.
fn builtin_condition_token(env: &Env, args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    if !args.is_empty() {
        return Err(RuntimeError::with_span(
            "condition_token() takes no arguments",
            span,
        ));
    }
    match env.current_condition_token {
        Some(token) => Ok(Value::Int(token.0 as i64)),
        None => Err(RuntimeError::with_span(
            "condition_token() requires an active condition token (only valid in lifecycle blocks)",
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
            format!("protocol error: unsupported response for {effect_name}: {response:?}"),
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
        Value::Void => "Void",
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
        Value::Direction(_) => "Direction",
        Value::Condition { .. } => "Condition",
        Value::Invocation(_) => "Invocation",
        Value::FnRef(_) => "FnRef",
        Value::EnumNamespace(_) => "EnumNamespace",
        Value::ModuleAlias(_) => "ModuleAlias",
    }
}

// ── process_periodic_conditions ──────────────────────────────────

fn builtin_process_periodic_conditions(
    env: &mut Env,
    args: &[Value],
    span: Span,
) -> Result<Value, RuntimeError> {
    use crate::state::EntityRef;
    use ttrpg_ast::ast::ConditionClause;

    let (combatants, tag) = match (args.first(), args.get(1)) {
        (Some(Value::List(combatants)), Some(Value::Str(tag))) => (combatants.clone(), tag.clone()),
        _ => {
            return Err(RuntimeError::with_span(
                "process_periodic_conditions() requires (list<entity>, string)",
                span,
            ))
        }
    };

    // Runtime tag validation: ensure the tag is declared
    if !env.interp.program.tags.contains(tag.as_str()) {
        return Err(RuntimeError::with_span(
            format!(
                "process_periodic_conditions: unknown tag `{tag}` — \
                 no `tag {tag}` declaration found in the program"
            ),
            span,
        ));
    }

    for combatant_val in combatants.iter() {
        let bearer: EntityRef = match combatant_val {
            Value::Entity(e) => *e,
            _ => continue,
        };

        // Snapshot: read conditions and compute stacking winners for this combatant
        let snapshot = env.state.read_conditions(&bearer).unwrap_or_default();
        let winners = crate::pipeline::compute_stacking_winners(&snapshot, env.interp.program);

        for cond_instance in &snapshot {
            // Only stacking winners execute periodic blocks
            if !winners.contains(&cond_instance.id) {
                continue;
            }

            // Check if the condition still exists (may have been removed by a previous block)
            let still_exists = env
                .state
                .read_conditions(&bearer)
                .unwrap_or_default()
                .iter()
                .any(|c| c.id == cond_instance.id);
            if !still_exists {
                continue;
            }

            // Walk ancestor chain (parent-first), looking for periodic blocks with matching tag
            let chain = crate::pipeline::collect_ancestor_order(
                env.interp.program,
                cond_instance.name.as_str(),
            );

            for decl in &chain {
                for clause in &decl.clauses {
                    let pc = match clause {
                        ConditionClause::Periodic(pc) if pc.tag == tag.as_str() => pc,
                        _ => continue,
                    };

                    // Execute the periodic block
                    env.push_scope();
                    env.bind(decl.receiver_name.clone(), Value::Entity(bearer));
                    // Bind `self` as the active condition instance
                    env.bind("self".into(), cond_instance.to_value());
                    // Bind condition parameters
                    for (pname, pval) in &cond_instance.params {
                        env.bind(pname.clone(), pval.clone());
                    }
                    let result = crate::eval::eval_block(env, &pc.body);
                    env.pop_scope();
                    env.return_value = None; // clear early-return flag
                    result?;
                }
            }
        }
    }

    Ok(Value::Void)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn dummy_span() -> Span {
        Span::dummy()
    }

    // ── Regression: tdsl-0s0y — floor/ceil with NaN, infinity, out-of-range ──

    #[test]
    fn floor_nan_returns_error() {
        let result = builtin_floor(&[Value::Float(f64::NAN)], dummy_span());
        assert!(result.is_err());
        assert!(result.unwrap_err().message.contains("NaN"));
    }

    #[test]
    fn floor_infinity_returns_error() {
        let result = builtin_floor(&[Value::Float(f64::INFINITY)], dummy_span());
        assert!(result.is_err());
        assert!(result.unwrap_err().message.contains("infinity"));
    }

    #[test]
    fn floor_neg_infinity_returns_error() {
        let result = builtin_floor(&[Value::Float(f64::NEG_INFINITY)], dummy_span());
        assert!(result.is_err());
        assert!(result.unwrap_err().message.contains("infinity"));
    }

    #[test]
    fn floor_out_of_range_returns_error() {
        let result = builtin_floor(&[Value::Float(1e19)], dummy_span());
        assert!(result.is_err());
        assert!(result.unwrap_err().message.contains("overflow"));
    }

    #[test]
    fn ceil_nan_returns_error() {
        let result = builtin_ceil(&[Value::Float(f64::NAN)], dummy_span());
        assert!(result.is_err());
        assert!(result.unwrap_err().message.contains("NaN"));
    }

    #[test]
    fn ceil_infinity_returns_error() {
        let result = builtin_ceil(&[Value::Float(f64::INFINITY)], dummy_span());
        assert!(result.is_err());
        assert!(result.unwrap_err().message.contains("infinity"));
    }

    #[test]
    fn floor_normal_value_works() {
        let result = builtin_floor(&[Value::Float(3.7)], dummy_span());
        assert_eq!(result.unwrap(), Value::Int(3));
    }

    #[test]
    fn ceil_normal_value_works() {
        let result = builtin_ceil(&[Value::Float(3.2)], dummy_span());
        assert_eq!(result.unwrap(), Value::Int(4));
    }

    #[test]
    fn error_builtin_returns_runtime_error_with_message() {
        let result = builtin_error(&[Value::Str("boom".into())], dummy_span());
        let err = result.unwrap_err();
        assert!(err.message.contains("boom"));
    }

    #[test]
    fn error_builtin_rejects_non_string_argument() {
        let result = builtin_error(&[Value::Int(42)], dummy_span());
        let err = result.unwrap_err();
        assert!(err.message.contains("expects String"));
    }

    // ── invocation() / revoke() unit tests ──────────────────

    use crate::effect::EffectHandler;
    use crate::state::{ActiveCondition, EntityRef, InvocationId, StateProvider};
    use crate::Interpreter;
    use std::collections::VecDeque;

    struct TestHandler {
        script: VecDeque<Response>,
        log: Vec<Effect>,
    }

    impl TestHandler {
        fn new() -> Self {
            TestHandler {
                script: VecDeque::new(),
                log: Vec::new(),
            }
        }
    }

    impl EffectHandler for TestHandler {
        fn handle(&mut self, effect: Effect) -> Response {
            self.log.push(effect);
            self.script.pop_front().unwrap_or(Response::Acknowledged)
        }
    }

    struct EmptyState;

    impl StateProvider for EmptyState {
        fn read_field(&self, _: &EntityRef, _: &str) -> Option<Value> {
            None
        }
        fn read_conditions(&self, _: &EntityRef) -> Option<Vec<ActiveCondition>> {
            None
        }
        fn read_turn_budget(&self, _: &EntityRef) -> Option<BTreeMap<Name, Value>> {
            None
        }
        fn read_enabled_options(&self) -> Vec<Name> {
            vec![]
        }
        fn position_eq(&self, _: u64, _: u64) -> bool {
            false
        }
        fn distance(&self, _: u64, _: u64) -> Option<i64> {
            None
        }
    }

    fn make_env<'a, 'p>(
        state: &'a EmptyState,
        handler: &'a mut TestHandler,
        interp: &'a Interpreter<'p>,
    ) -> crate::Env<'a, 'p> {
        crate::Env::new(state, handler, interp)
    }

    fn empty_program_and_env() -> (ttrpg_ast::ast::Program, ttrpg_checker::env::TypeEnv) {
        let program = ttrpg_ast::ast::Program::default();
        let env = ttrpg_checker::env::TypeEnv::default();
        (program, env)
    }

    #[test]
    fn invocation_returns_value_when_set() {
        let (program, type_env) = empty_program_and_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = EmptyState;
        let mut handler = TestHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);
        env.current_invocation_id = Some(InvocationId(42));

        let result = builtin_invocation(&env, &[], dummy_span()).unwrap();
        assert_eq!(result, Value::Invocation(InvocationId(42)));
    }

    #[test]
    fn invocation_errors_when_none() {
        let (program, type_env) = empty_program_and_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = EmptyState;
        let mut handler = TestHandler::new();
        let env = make_env(&state, &mut handler, &interp);

        let err = builtin_invocation(&env, &[], dummy_span()).unwrap_err();
        assert!(err.message.contains("outside of action"));
    }

    #[test]
    fn revoke_with_invocation_emits_effect() {
        let (program, type_env) = empty_program_and_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = EmptyState;
        let mut handler = TestHandler::new();
        {
            let mut env = make_env(&state, &mut handler, &interp);
            env.current_invocation_id = Some(InvocationId(1));

            let result = builtin_revoke(
                &mut env,
                &[Value::Invocation(InvocationId(7))],
                dummy_span(),
            )
            .unwrap();
            assert_eq!(result, Value::Void);
        }
        assert_eq!(handler.log.len(), 1);
        assert!(matches!(
            &handler.log[0],
            Effect::RevokeInvocation { invocation }
            if *invocation == InvocationId(7)
        ));
    }

    #[test]
    fn revoke_none_is_noop() {
        let (program, type_env) = empty_program_and_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = EmptyState;
        let mut handler = TestHandler::new();
        {
            let mut env = make_env(&state, &mut handler, &interp);
            let result = builtin_revoke(&mut env, &[Value::Void], dummy_span()).unwrap();
            assert_eq!(result, Value::Void);
        }
        assert!(handler.log.is_empty());
    }

    #[test]
    fn revoke_option_some_invocation_emits_effect() {
        let (program, type_env) = empty_program_and_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = EmptyState;
        let mut handler = TestHandler::new();
        {
            let mut env = make_env(&state, &mut handler, &interp);
            let arg = Value::Option(Some(Box::new(Value::Invocation(InvocationId(5)))));
            let result = builtin_revoke(&mut env, &[arg], dummy_span()).unwrap();
            assert_eq!(result, Value::Void);
        }
        assert_eq!(handler.log.len(), 1);
        assert!(matches!(
            &handler.log[0],
            Effect::RevokeInvocation { invocation }
            if *invocation == InvocationId(5)
        ));
    }

    #[test]
    fn revoke_option_none_is_noop() {
        let (program, type_env) = empty_program_and_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = EmptyState;
        let mut handler = TestHandler::new();
        {
            let mut env = make_env(&state, &mut handler, &interp);
            let arg = Value::Option(None);
            let result = builtin_revoke(&mut env, &[arg], dummy_span()).unwrap();
            assert_eq!(result, Value::Void);
        }
        assert!(handler.log.is_empty());
    }

    // ── conditions() unit tests ──────────────────────────────

    struct ConditionsState {
        /// Entity ID that has conditions; all others return None.
        known_entity: u64,
        conditions: Vec<ActiveCondition>,
    }

    impl StateProvider for ConditionsState {
        fn read_field(&self, _: &EntityRef, _: &str) -> Option<Value> {
            None
        }
        fn read_conditions(&self, entity: &EntityRef) -> Option<Vec<ActiveCondition>> {
            if entity.0 == self.known_entity {
                Some(self.conditions.clone())
            } else {
                None
            }
        }
        fn read_turn_budget(&self, _: &EntityRef) -> Option<BTreeMap<Name, Value>> {
            None
        }
        fn read_enabled_options(&self) -> Vec<Name> {
            vec![]
        }
        fn position_eq(&self, _: u64, _: u64) -> bool {
            false
        }
        fn distance(&self, _: u64, _: u64) -> Option<i64> {
            None
        }
    }

    fn make_env_with_state<'a, 'p>(
        state: &'a ConditionsState,
        handler: &'a mut TestHandler,
        interp: &'a Interpreter<'p>,
    ) -> crate::Env<'a, 'p> {
        crate::Env::new(state, handler, interp)
    }

    #[test]
    fn conditions_returns_empty_list_for_entity_with_no_conditions() {
        let (program, type_env) = empty_program_and_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = ConditionsState {
            known_entity: 1,
            conditions: vec![],
        };
        let mut handler = TestHandler::new();
        let env = make_env_with_state(&state, &mut handler, &interp);

        let entity = EntityRef(1);
        let result = builtin_conditions(&env, &[Value::Entity(entity)], dummy_span()).unwrap();
        assert_eq!(result, Value::List(vec![]));
    }

    #[test]
    fn conditions_returns_active_conditions_as_list() {
        use crate::value::{duration_variant, effect_source_unknown};

        let (program, type_env) = empty_program_and_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let cond = ActiveCondition {
            id: 1,
            name: "Prone".into(),
            params: BTreeMap::new(),
            bearer: EntityRef(1),
            gained_at: 0,
            duration: duration_variant("Indefinite"),
            invocation: None,
            applied_at: 0,
            source: effect_source_unknown(),
            tags: BTreeSet::new(),
        };
        let state = ConditionsState {
            known_entity: 1,
            conditions: vec![cond.clone()],
        };
        let mut handler = TestHandler::new();
        let env = make_env_with_state(&state, &mut handler, &interp);

        let entity = EntityRef(1);
        let result = builtin_conditions(&env, &[Value::Entity(entity)], dummy_span()).unwrap();
        match result {
            Value::List(items) => {
                assert_eq!(items.len(), 1);
                assert_eq!(items[0], cond.to_value());
            }
            other => panic!("expected List, got {other:?}"),
        }
    }

    #[test]
    fn conditions_errors_on_unknown_entity() {
        let (program, type_env) = empty_program_and_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = ConditionsState {
            known_entity: 1,
            conditions: vec![],
        };
        let mut handler = TestHandler::new();
        let env = make_env_with_state(&state, &mut handler, &interp);

        // Entity 99 is not the known_entity, so read_conditions returns None
        let entity = EntityRef(99);
        let err = builtin_conditions(&env, &[Value::Entity(entity)], dummy_span()).unwrap_err();
        assert!(err.message.contains("unknown entity"));
    }

    #[test]
    fn conditions_errors_on_non_entity_arg() {
        let (program, type_env) = empty_program_and_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = ConditionsState {
            known_entity: 1,
            conditions: vec![],
        };
        let mut handler = TestHandler::new();
        let env = make_env_with_state(&state, &mut handler, &interp);

        let err = builtin_conditions(&env, &[Value::Int(42)], dummy_span()).unwrap_err();
        assert!(err.message.contains("expects Entity"));
    }
}
