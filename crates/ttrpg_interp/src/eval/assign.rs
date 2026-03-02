use ttrpg_ast::ast::{AssignOp, ExprKind, LValue, LValueSegment};
use ttrpg_ast::{Name, Spanned};

use crate::effect::{Effect, FieldPathSegment};
use crate::state::{EntityRef, StateProvider};
use crate::value::Value;
use crate::Env;
use crate::RuntimeError;

use super::compare::value_eq;
use super::dispatch::eval_expr;
use super::helpers::{resolve_resource_bounds, type_name};
use super::ops::coerce_roll_result;

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
pub(super) fn eval_assign(
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
            eval_assign_entity(env, entity_ref, &target.segments, op, rhs, target.span)
        }
        Some(_) => {
            // Local mutation path: walk segments, switching to entity
            // mutation if we encounter an Entity along the way
            eval_assign_local(env, &target.root, &target.segments, op, rhs, target.span)
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
            "cannot access `turn` outside of action/reaction/hook context",
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
    let var = env
        .lookup_mut(name)
        .ok_or_else(|| RuntimeError::with_span(format!("undefined variable `{}`", name), span))?;

    let new_val = apply_assign_op(op, var.clone(), rhs, span)?;
    *var = new_val;
    Ok(())
}

/// If the first path segment is a flattened included-group field, insert the
/// group name as a prefix so the mutation targets the correct nested struct.
fn expand_flattened_path(env: &Env, entity: &EntityRef, path: &mut Vec<FieldPathSegment>) {
    if let Some(FieldPathSegment::Field(ref field_name)) = path.first() {
        if let Some(entity_type) = env.state.entity_type_name(entity) {
            if let Some(group_name) =
                env.interp.type_env.lookup_flattened_field(&entity_type, field_name)
            {
                path.insert(0, FieldPathSegment::Field(group_name.clone()));
            }
        }
    }
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
    let mut path = lvalue_segments_to_field_path(env, segments, span)?;

    // Apply group alias resolution from the checker
    if let Some((seg_idx, real_name)) = env.interp.type_env.resolved_lvalue_aliases.get(&span) {
        if *seg_idx < path.len() {
            path[*seg_idx] = FieldPathSegment::Field(real_name.clone());
        }
    }

    expand_flattened_path(env, &entity, &mut path);

    // Look up resource bounds from the entity's field declaration.
    // Handles direct resource fields (e.g. HP: resource(0..=max_HP)) and
    // resource-valued maps (e.g. spell_slots: map<int, resource(0..=9)>).
    let bounds = resolve_resource_bounds(env, &entity, &path);

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
    Field(Name),
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
        let mut path: Vec<FieldPathSegment> = eval_segs[depth..]
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

        // Apply group alias resolution, adjusting index for entity depth
        if let Some((seg_idx, real_name)) = env.interp.type_env.resolved_lvalue_aliases.get(&span)
        {
            let adjusted = seg_idx.saturating_sub(depth);
            if adjusted < path.len() {
                path[adjusted] = FieldPathSegment::Field(real_name.clone());
            }
        }

        expand_flattened_path(env, &entity_ref, &mut path);
        let bounds = resolve_resource_bounds(env, &entity_ref, &path);

        let effect = Effect::MutateField {
            entity: entity_ref,
            path,
            op,
            value: rhs,
            bounds,
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
                        RuntimeError::with_span(format!("struct has no field `{}`", name), span)
                    })?;
                } else {
                    return Err(RuntimeError::with_span("cannot index into a struct", span));
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
                RuntimeError::with_span(format!("struct has no field `{}`", name), span)
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
                        let entry = map.get_mut(&ek).ok_or_else(|| {
                            RuntimeError::with_span("internal: validated map key missing", span)
                        })?;
                        let new_val = apply_assign_op(op, entry.clone(), rhs, span)?;
                        *entry = new_val;
                        Ok(())
                    }
                }
            } else {
                // Navigate deeper into the map value
                let ek = existing_key.ok_or_else(|| {
                    RuntimeError::with_span(format!("map has no key {:?}", key), span)
                })?;
                let entry = map.get_mut(&ek).ok_or_else(|| {
                    RuntimeError::with_span("internal: validated map key missing", span)
                })?;
                apply_local_mutation(entry, segments, depth + 1, op, rhs, span, state)
            }
        }
        (EvalSegment::Field(_), other) => Err(RuntimeError::with_span(
            format!("cannot access field on {}", type_name(other)),
            span,
        )),
        (EvalSegment::Index(_), other) => Err(RuntimeError::with_span(
            format!("cannot index into {}", type_name(other)),
            span,
        )),
    }
}

/// Apply an assignment operator to produce a new value.
///
/// - `Eq` → replace with rhs
/// - `PlusEq` → current + rhs (Int/Float, checked overflow)
/// - `MinusEq` → current - rhs (Int/Float, checked overflow)
pub(super) fn apply_assign_op(
    op: AssignOp,
    current: Value,
    rhs: Value,
    span: ttrpg_ast::Span,
) -> Result<Value, RuntimeError> {
    match op {
        AssignOp::Eq => Ok(rhs),
        AssignOp::PlusEq => {
            // Set += elem: add element to set
            if let Value::Set(mut set) = current {
                set.insert(rhs);
                return Ok(Value::Set(set));
            }
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
                        return Err(RuntimeError::with_span("float overflow in +=", span));
                    }
                    Ok(Value::Float(result))
                }
                (Value::Int(a), Value::Float(b)) | (Value::Float(b), Value::Int(a)) => {
                    let result = (*a as f64) + b;
                    if !result.is_finite() {
                        return Err(RuntimeError::with_span("float overflow in +=", span));
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
            // Set -= elem: remove element from set
            if let Value::Set(mut set) = current {
                set.remove(&rhs);
                return Ok(Value::Set(set));
            }
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
                        return Err(RuntimeError::with_span("float overflow in -=", span));
                    }
                    Ok(Value::Float(result))
                }
                (Value::Int(a), Value::Float(b)) => {
                    let result = (*a as f64) - b;
                    if !result.is_finite() {
                        return Err(RuntimeError::with_span("float overflow in -=", span));
                    }
                    Ok(Value::Float(result))
                }
                (Value::Float(a), Value::Int(b)) => {
                    let result = a - (*b as f64);
                    if !result.is_finite() {
                        return Err(RuntimeError::with_span("float overflow in -=", span));
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
                        format!("list index {} out of bounds, length {}", i, len),
                        span,
                    ));
                }
                len - positive
            };
            if index >= len {
                return Err(RuntimeError::with_span(
                    format!("list index {} out of bounds, length {}", i, len),
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
