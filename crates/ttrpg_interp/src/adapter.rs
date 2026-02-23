use std::cell::RefCell;
use std::collections::HashSet;

use ttrpg_ast::ast::AssignOp;

use crate::effect::{Effect, EffectHandler, EffectKind, Response};
use crate::state::{ActiveCondition, EntityRef, StateProvider, WritableState};
use crate::value::Value;
use crate::effect::FieldPathSegment;

// ── StateAdapter ───────────────────────────────────────────────

/// Layer 2 adapter that wraps a `WritableState` and auto-applies
/// mutation effects locally.
///
/// The interpreter's public API takes `&dyn StateProvider` and
/// `&mut dyn EffectHandler` as separate parameters. `StateAdapter`
/// wraps the `WritableState` in a `RefCell` and implements
/// `StateProvider` directly. Each method does a short-lived borrow
/// that is dropped before the method returns.
///
/// **Mutation handling rules:**
///
/// 1. **Intercepted mutation** (not in `pass_through` set): applied
///    locally, returns `Acknowledged` without forwarding.
/// 2. **Pass-through mutation** (in `pass_through` set): forwarded
///    to the inner handler; adapter syncs locally based on response.
/// 3. **Non-mutation effects**: always forwarded to the inner handler.
/// 4. **`DeductCost`**: always passed through (decision effect);
///    adapter applies the mutation based on the host's response.
pub struct StateAdapter<S: WritableState> {
    state: RefCell<S>,
    pass_through: HashSet<EffectKind>,
}

impl<S: WritableState> StateAdapter<S> {
    /// Create a new adapter wrapping the given writable state.
    pub fn new(state: S) -> Self {
        StateAdapter {
            state: RefCell::new(state),
            pass_through: HashSet::new(),
        }
    }

    /// Mark an effect kind as pass-through. Mutation effects of this
    /// kind will be forwarded to the inner handler before being applied
    /// locally.
    pub fn pass_through(mut self, kind: EffectKind) -> Self {
        self.pass_through.insert(kind);
        self
    }

    /// Execute a closure providing read and write access to the adapted state.
    ///
    /// `&self` serves as `&dyn StateProvider` (per-call borrows via RefCell).
    /// An `AdaptedHandler` serves as `&mut dyn EffectHandler`.
    pub fn run<H: EffectHandler, R>(
        &self,
        inner: &mut H,
        f: impl FnOnce(&dyn StateProvider, &mut dyn EffectHandler) -> R,
    ) -> R {
        let mut handler = AdaptedHandler {
            adapter: self,
            inner,
        };
        f(self, &mut handler)
    }

    /// Consume the adapter and return the inner state.
    pub fn into_inner(self) -> S {
        self.state.into_inner()
    }
}

// ── StateProvider impl ─────────────────────────────────────────

impl<S: WritableState> StateProvider for StateAdapter<S> {
    fn read_field(&self, entity: &EntityRef, field: &str) -> Option<Value> {
        self.state.borrow().read_field(entity, field)
    }

    fn read_conditions(&self, entity: &EntityRef) -> Option<Vec<ActiveCondition>> {
        self.state.borrow().read_conditions(entity)
    }

    fn read_turn_budget(
        &self,
        entity: &EntityRef,
    ) -> Option<std::collections::BTreeMap<String, Value>> {
        self.state.borrow().read_turn_budget(entity)
    }

    fn read_enabled_options(&self) -> Vec<String> {
        self.state.borrow().read_enabled_options()
    }

    fn position_eq(&self, a: &Value, b: &Value) -> bool {
        self.state.borrow().position_eq(a, b)
    }

    fn distance(&self, a: &Value, b: &Value) -> Option<i64> {
        self.state.borrow().distance(a, b)
    }
}

// ── AdaptedHandler ─────────────────────────────────────────────

/// The handler that intercepts mutation effects and applies them locally.
///
/// Holds a shared `&StateAdapter<S>` reference for mutations via
/// `borrow_mut()`. Each mutation does one short-lived mutable borrow.
pub struct AdaptedHandler<'a, S: WritableState, H: EffectHandler> {
    adapter: &'a StateAdapter<S>,
    inner: &'a mut H,
}

/// The six mutation effect kinds.
const MUTATION_KINDS: [EffectKind; 6] = [
    EffectKind::MutateField,
    EffectKind::ApplyCondition,
    EffectKind::RemoveCondition,
    EffectKind::MutateTurnField,
    EffectKind::GrantGroup,
    EffectKind::RevokeGroup,
];

fn is_mutation(kind: EffectKind) -> bool {
    MUTATION_KINDS.contains(&kind)
}

impl<S: WritableState, H: EffectHandler> EffectHandler for AdaptedHandler<'_, S, H> {
    fn handle(&mut self, effect: Effect) -> Response {
        let kind = EffectKind::of(&effect);

        // DeductCost: always passed through, adapter applies mutation based on response
        if kind == EffectKind::DeductCost {
            return self.handle_deduct_cost(effect);
        }

        if is_mutation(kind) {
            if self.adapter.pass_through.contains(&kind) {
                // Pass-through: forward to inner, then sync locally
                let response = self.inner.handle(effect.clone());
                match &response {
                    Response::Acknowledged => {
                        apply_mutation(&mut *self.adapter.state.borrow_mut(), &effect);
                    }
                    Response::Override(override_val) => {
                        apply_mutation_with_override(
                            &mut *self.adapter.state.borrow_mut(),
                            &effect,
                            override_val,
                        );
                    }
                    Response::Vetoed => {
                        // No local mutation
                    }
                    _ => {
                        // Unexpected response type — do not mutate state.
                        // The interpreter will surface a protocol error for this response,
                        // so state must remain unchanged to preserve consistency.
                    }
                }
                response
            } else {
                // Intercepted: apply locally, return Acknowledged
                apply_mutation(&mut *self.adapter.state.borrow_mut(), &effect);
                Response::Acknowledged
            }
        } else {
            // Non-mutation: always forward
            self.inner.handle(effect)
        }
    }
}

impl<S: WritableState, H: EffectHandler> AdaptedHandler<'_, S, H> {
    /// Handle DeductCost: always passed through; adapter applies
    /// the state mutation based on the host's response.
    fn handle_deduct_cost(&mut self, effect: Effect) -> Response {
        let (actor, budget_field) = match &effect {
            Effect::DeductCost {
                actor,
                budget_field,
                ..
            } => (*actor, budget_field.clone()),
            _ => unreachable!(),
        };

        let response = self.inner.handle(effect);

        match &response {
            Response::Acknowledged => {
                // Decrement the original budget field by 1
                deduct_budget_field(&mut *self.adapter.state.borrow_mut(), &actor, &budget_field);
            }
            Response::Override(Value::Str(replacement)) => {
                // Map replacement token to budget field and decrement
                if let Some(replacement_field) = token_to_budget_field(replacement) {
                    deduct_budget_field(
                        &mut *self.adapter.state.borrow_mut(),
                        &actor,
                        replacement_field,
                    );
                }
                // If mapping fails, the interpreter's action.rs already validated this,
                // so it shouldn't happen. The adapter doesn't duplicate the validation.
            }
            Response::Vetoed => {
                // Cost waived — no mutation
            }
            _ => {
                // Unexpected response — do not mutate state.
                // The interpreter will surface a protocol error for this response,
                // so state must remain unchanged to preserve consistency.
            }
        }

        response
    }
}

// ── Mutation application helpers ───────────────────────────────

/// Apply a mutation effect to the writable state.
fn apply_mutation<S: WritableState>(state: &mut S, effect: &Effect) {
    match effect {
        Effect::MutateField {
            entity,
            path,
            op,
            value,
            bounds,
        } => {
            let final_value = compute_field_value(state, entity, path, *op, value, bounds);
            state.write_field(entity, path, final_value);
        }
        Effect::ApplyCondition {
            target,
            condition,
            duration,
        } => {
            // The adapter creates an ActiveCondition. The host assigns a unique id
            // via the WritableState implementation (e.g., GameState auto-assigns).
            state.add_condition(
                target,
                ActiveCondition {
                    id: 0, // WritableState impl is responsible for assigning a unique id
                    name: condition.clone(),
                    bearer: *target,
                    gained_at: 0, // WritableState impl assigns ordering timestamp
                    duration: duration.clone(),
                },
            );
        }
        Effect::RemoveCondition { target, condition } => {
            state.remove_condition(target, condition);
        }
        Effect::MutateTurnField {
            actor,
            field,
            op,
            value,
        } => {
            let final_value = compute_turn_field_value(state, actor, field, *op, value);
            state.write_turn_field(actor, field, final_value);
        }
        Effect::GrantGroup {
            entity,
            group_name,
            fields,
        } => {
            state.write_field(
                entity,
                &[FieldPathSegment::Field(group_name.clone())],
                fields.clone(),
            );
        }
        Effect::RevokeGroup {
            entity,
            group_name,
        } => {
            state.remove_field(entity, group_name);
        }
        _ => {} // Not a mutation effect
    }
}

/// Apply a mutation effect with an overridden value.
///
/// Override is a *replacement RHS* — the original operator is preserved.
/// For MutateField/MutateTurnField, the override value replaces the RHS
/// in the computation. For ApplyCondition, it replaces the duration.
/// For RemoveCondition, a `Str` override replaces the condition name.
fn apply_mutation_with_override<S: WritableState>(
    state: &mut S,
    effect: &Effect,
    override_val: &Value,
) {
    match effect {
        Effect::MutateField {
            entity,
            path,
            op,
            bounds,
            ..
        } => {
            let final_value = compute_field_value(state, entity, path, *op, override_val, bounds);
            state.write_field(entity, path, final_value);
        }
        Effect::MutateTurnField {
            actor, field, op, ..
        } => {
            let final_value = compute_turn_field_value(state, actor, field, *op, override_val);
            state.write_turn_field(actor, field, final_value);
        }
        Effect::ApplyCondition {
            target, condition, ..
        } => {
            state.add_condition(
                target,
                ActiveCondition {
                    id: 0,
                    name: condition.clone(),
                    bearer: *target,
                    gained_at: 0,
                    duration: override_val.clone(),
                },
            );
        }
        Effect::RemoveCondition { target, condition } => {
            if let Value::Str(name) = override_val {
                state.remove_condition(target, name);
            } else {
                // Non-string override: fall back to original condition name
                state.remove_condition(target, condition);
            }
        }
        Effect::GrantGroup {
            entity,
            group_name,
            ..
        } => {
            // Override replaces the entire struct value
            state.write_field(
                entity,
                &[FieldPathSegment::Field(group_name.clone())],
                override_val.clone(),
            );
        }
        Effect::RevokeGroup { .. } => {
            // No meaningful override for revoke; fall through to normal
            apply_mutation(state, effect);
        }
        _ => apply_mutation(state, effect),
    }
}

/// Compute the final field value after applying op + bounds clamping.
pub fn compute_field_value<S: StateProvider>(
    state: &S,
    entity: &EntityRef,
    path: &[FieldPathSegment],
    op: AssignOp,
    rhs: &Value,
    bounds: &Option<(Value, Value)>,
) -> Value {
    let new_val = match op {
        AssignOp::Eq => rhs.clone(),
        AssignOp::PlusEq | AssignOp::MinusEq => {
            let current = read_at_path(state, entity, path).unwrap_or(Value::Int(0));
            apply_op(op, &current, rhs)
        }
    };
    match bounds {
        Some((lo, hi)) => clamp_value(new_val, lo, hi),
        None => new_val,
    }
}

/// Compute the final turn field value after applying op.
pub fn compute_turn_field_value<S: StateProvider>(
    state: &S,
    actor: &EntityRef,
    field: &str,
    op: AssignOp,
    rhs: &Value,
) -> Value {
    match op {
        AssignOp::Eq => rhs.clone(),
        AssignOp::PlusEq | AssignOp::MinusEq => {
            let current = state
                .read_turn_budget(actor)
                .and_then(|b| b.get(field).cloned())
                .unwrap_or(Value::Int(0));
            apply_op(op, &current, rhs)
        }
    }
}

/// Read a value at a nested path from an entity.
pub fn read_at_path<S: StateProvider>(
    state: &S,
    entity: &EntityRef,
    path: &[FieldPathSegment],
) -> Option<Value> {
    if path.is_empty() {
        return None;
    }
    let root_field = match &path[0] {
        FieldPathSegment::Field(f) => f,
        _ => return None,
    };
    let mut current = state.read_field(entity, root_field)?;
    for seg in &path[1..] {
        current = match seg {
            FieldPathSegment::Field(f) => match current {
                Value::Struct { ref fields, .. } => fields.get(f.as_str())?.clone(),
                _ => return None,
            },
            FieldPathSegment::Index(key) => match current {
                Value::Map(ref map) => map.get(key)?.clone(),
                Value::List(ref list) => {
                    if let Value::Int(i) = key {
                        let idx = if *i < 0 {
                            (list.len() as i64 + i) as usize
                        } else {
                            *i as usize
                        };
                        list.get(idx)?.clone()
                    } else {
                        return None;
                    }
                }
                _ => return None,
            },
        };
    }
    Some(current)
}

/// Apply an assign op to two values. Panics on type mismatch or overflow
/// (mutations from the interpreter are already type-checked and overflow-checked,
/// so these conditions should be unreachable).
pub fn apply_op(op: AssignOp, current: &Value, rhs: &Value) -> Value {
    match op {
        AssignOp::Eq => rhs.clone(),
        AssignOp::PlusEq => match (current, rhs) {
            (Value::Int(a), Value::Int(b)) => Value::Int(
                a.checked_add(*b)
                    .expect("integer overflow in adapter += (interpreter should have caught this)"),
            ),
            (Value::Float(a), Value::Float(b)) => {
                let result = a + b;
                assert!(
                    result.is_finite(),
                    "non-finite float in adapter += (interpreter should have caught this)"
                );
                Value::Float(result)
            }
            _ => rhs.clone(), // Fallback for type-checked programs
        },
        AssignOp::MinusEq => match (current, rhs) {
            (Value::Int(a), Value::Int(b)) => Value::Int(
                a.checked_sub(*b)
                    .expect("integer overflow in adapter -= (interpreter should have caught this)"),
            ),
            (Value::Float(a), Value::Float(b)) => {
                let result = a - b;
                assert!(
                    result.is_finite(),
                    "non-finite float in adapter -= (interpreter should have caught this)"
                );
                Value::Float(result)
            }
            _ => rhs.clone(), // Fallback for type-checked programs
        },
    }
}

/// Clamp a value between lo and hi (inclusive). Only applies to Int and Float.
pub fn clamp_value(val: Value, lo: &Value, hi: &Value) -> Value {
    match (&val, lo, hi) {
        (Value::Int(v), Value::Int(l), Value::Int(h)) => Value::Int((*v).clamp(*l, *h)),
        (Value::Float(v), Value::Float(l), Value::Float(h)) => Value::Float(v.clamp(*l, *h)),
        _ => val,
    }
}

/// Decrement a turn budget field by 1.
pub fn deduct_budget_field<S: WritableState>(state: &mut S, actor: &EntityRef, field: &str) {
    let current = state
        .read_turn_budget(actor)
        .and_then(|b| b.get(field).cloned())
        .unwrap_or(Value::Int(0));
    let new_val = match current {
        Value::Int(v) => Value::Int(v.saturating_sub(1)),
        other => other,
    };
    state.write_turn_field(actor, field, new_val);
}

/// Maps a cost token to its budget field name.
pub fn token_to_budget_field(token: &str) -> Option<&'static str> {
    match token {
        "action" => Some("actions"),
        "bonus_action" => Some("bonus_actions"),
        "reaction" => Some("reactions"),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::effect::{Effect, Response};
    use crate::state::ActiveCondition;
    use crate::value::DurationValue;
    use std::collections::{BTreeMap, HashMap};

    // ── Test WritableState impl ────────────────────────────────

    struct TestWritableState {
        fields: HashMap<(u64, String), Value>,
        conditions: HashMap<u64, Vec<ActiveCondition>>,
        turn_budgets: HashMap<u64, BTreeMap<String, Value>>,
        enabled_options: Vec<String>,
        next_condition_id: u64,
    }

    impl TestWritableState {
        fn new() -> Self {
            TestWritableState {
                fields: HashMap::new(),
                conditions: HashMap::new(),
                turn_budgets: HashMap::new(),
                enabled_options: Vec::new(),
                next_condition_id: 1,
            }
        }
    }

    impl StateProvider for TestWritableState {
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

        fn position_eq(&self, _a: &Value, _b: &Value) -> bool {
            false
        }

        fn distance(&self, _a: &Value, _b: &Value) -> Option<i64> {
            None
        }
    }

    impl WritableState for TestWritableState {
        fn write_field(&mut self, entity: &EntityRef, path: &[FieldPathSegment], value: Value) {
            if let Some(FieldPathSegment::Field(f)) = path.first() {
                if path.len() == 1 {
                    self.fields.insert((entity.0, f.clone()), value);
                }
                // Nested paths: simplified for tests
            }
        }

        fn add_condition(&mut self, entity: &EntityRef, mut cond: ActiveCondition) {
            cond.id = self.next_condition_id;
            self.next_condition_id += 1;
            cond.gained_at = cond.id; // Use id as timestamp for simplicity
            self.conditions.entry(entity.0).or_default().push(cond);
        }

        fn remove_condition(&mut self, entity: &EntityRef, name: &str) {
            if let Some(conds) = self.conditions.get_mut(&entity.0) {
                conds.retain(|c| c.name != name);
            }
        }

        fn write_turn_field(&mut self, entity: &EntityRef, field: &str, value: Value) {
            self.turn_budgets
                .entry(entity.0)
                .or_default()
                .insert(field.to_string(), value);
        }

        fn remove_field(&mut self, entity: &EntityRef, field: &str) {
            self.fields.remove(&(entity.0, field.to_string()));
        }
    }

    // ── Recording handler ──────────────────────────────────────

    struct RecordingHandler {
        responses: Vec<Response>,
        log: Vec<Effect>,
        call_idx: usize,
    }

    impl RecordingHandler {
        fn new(responses: Vec<Response>) -> Self {
            RecordingHandler {
                responses,
                log: Vec::new(),
                call_idx: 0,
            }
        }

        fn acknowledged() -> Self {
            RecordingHandler::new(vec![])
        }
    }

    impl EffectHandler for RecordingHandler {
        fn handle(&mut self, effect: Effect) -> Response {
            self.log.push(effect);
            let resp = if self.call_idx < self.responses.len() {
                self.responses[self.call_idx].clone()
            } else {
                Response::Acknowledged
            };
            self.call_idx += 1;
            resp
        }
    }

    // ── Adapter: intercepted mutation applies locally ───────────

    #[test]
    fn intercepted_mutation_applies_locally() {
        let mut state = TestWritableState::new();
        state.fields.insert((1, "HP".into()), Value::Int(30));
        let adapter = StateAdapter::new(state);
        let mut handler = RecordingHandler::acknowledged();

        let response = adapter.run(&mut handler, |_state, handler| {
            handler.handle(Effect::MutateField {
                entity: EntityRef(1),
                path: vec![FieldPathSegment::Field("HP".into())],
                op: AssignOp::MinusEq,
                value: Value::Int(10),
                bounds: None,
            })
        });

        assert!(matches!(response, Response::Acknowledged));
        // Inner handler should NOT have received the effect
        assert_eq!(handler.log.len(), 0);
        // State should be updated
        let final_state = adapter.into_inner();
        assert_eq!(
            final_state.fields.get(&(1, "HP".into())),
            Some(&Value::Int(20))
        );
    }

    // ── Adapter: pass-through mutation forwards + syncs ─────────

    #[test]
    fn pass_through_mutation_forwards_and_syncs() {
        let mut state = TestWritableState::new();
        state.fields.insert((1, "HP".into()), Value::Int(30));
        let adapter = StateAdapter::new(state).pass_through(EffectKind::MutateField);
        let mut handler = RecordingHandler::new(vec![Response::Acknowledged]);

        let response = adapter.run(&mut handler, |_state, handler| {
            handler.handle(Effect::MutateField {
                entity: EntityRef(1),
                path: vec![FieldPathSegment::Field("HP".into())],
                op: AssignOp::MinusEq,
                value: Value::Int(10),
                bounds: None,
            })
        });

        assert!(matches!(response, Response::Acknowledged));
        // Inner handler SHOULD have received the effect
        assert_eq!(handler.log.len(), 1);
        assert!(matches!(handler.log[0], Effect::MutateField { .. }));
        // State should also be updated
        let final_state = adapter.into_inner();
        assert_eq!(
            final_state.fields.get(&(1, "HP".into())),
            Some(&Value::Int(20))
        );
    }

    // ── Adapter: pass-through vetoed → no local change ──────────

    #[test]
    fn pass_through_vetoed_no_local_change() {
        let mut state = TestWritableState::new();
        state.fields.insert((1, "HP".into()), Value::Int(30));
        let adapter = StateAdapter::new(state).pass_through(EffectKind::MutateField);
        let mut handler = RecordingHandler::new(vec![Response::Vetoed]);

        let response = adapter.run(&mut handler, |_state, handler| {
            handler.handle(Effect::MutateField {
                entity: EntityRef(1),
                path: vec![FieldPathSegment::Field("HP".into())],
                op: AssignOp::MinusEq,
                value: Value::Int(10),
                bounds: None,
            })
        });

        assert!(matches!(response, Response::Vetoed));
        // State should NOT be changed
        let final_state = adapter.into_inner();
        assert_eq!(
            final_state.fields.get(&(1, "HP".into())),
            Some(&Value::Int(30))
        );
    }

    // ── Adapter: non-mutation effects forwarded ─────────────────

    #[test]
    fn non_mutation_effects_forwarded() {
        let state = TestWritableState::new();
        let adapter = StateAdapter::new(state);
        let mut handler = RecordingHandler::new(vec![Response::Acknowledged]);

        let response = adapter.run(&mut handler, |_state, handler| {
            handler.handle(Effect::ActionCompleted {
                name: "Attack".into(),
                actor: EntityRef(1),
            })
        });

        assert!(matches!(response, Response::Acknowledged));
        assert_eq!(handler.log.len(), 1);
        assert!(matches!(handler.log[0], Effect::ActionCompleted { .. }));
    }

    // ── Adapter: DeductCost decision + mutation ─────────────────

    #[test]
    fn deduct_cost_acknowledged() {
        let mut state = TestWritableState::new();
        state
            .turn_budgets
            .entry(1)
            .or_default()
            .insert("actions".into(), Value::Int(1));
        let adapter = StateAdapter::new(state);
        let mut handler = RecordingHandler::new(vec![Response::Acknowledged]);

        adapter.run(&mut handler, |_state, handler| {
            handler.handle(Effect::DeductCost {
                actor: EntityRef(1),
                token: "action".into(),
                budget_field: "actions".into(),
            })
        });

        // Inner handler should see the effect
        assert_eq!(handler.log.len(), 1);
        // Budget should be decremented
        let final_state = adapter.into_inner();
        assert_eq!(
            final_state.turn_budgets.get(&1).and_then(|b| b.get("actions")),
            Some(&Value::Int(0))
        );
    }

    #[test]
    fn deduct_cost_overridden() {
        let mut state = TestWritableState::new();
        state
            .turn_budgets
            .entry(1)
            .or_default()
            .insert("actions".into(), Value::Int(1));
        state
            .turn_budgets
            .entry(1)
            .or_default()
            .insert("bonus_actions".into(), Value::Int(1));
        let adapter = StateAdapter::new(state);
        // Host says: use bonus_action instead
        let mut handler =
            RecordingHandler::new(vec![Response::Override(Value::Str("bonus_action".into()))]);

        adapter.run(&mut handler, |_state, handler| {
            handler.handle(Effect::DeductCost {
                actor: EntityRef(1),
                token: "action".into(),
                budget_field: "actions".into(),
            })
        });

        let final_state = adapter.into_inner();
        // actions should be unchanged (original not deducted)
        assert_eq!(
            final_state.turn_budgets.get(&1).and_then(|b| b.get("actions")),
            Some(&Value::Int(1))
        );
        // bonus_actions should be decremented
        assert_eq!(
            final_state
                .turn_budgets
                .get(&1)
                .and_then(|b| b.get("bonus_actions")),
            Some(&Value::Int(0))
        );
    }

    #[test]
    fn deduct_cost_vetoed() {
        let mut state = TestWritableState::new();
        state
            .turn_budgets
            .entry(1)
            .or_default()
            .insert("actions".into(), Value::Int(1));
        let adapter = StateAdapter::new(state);
        let mut handler = RecordingHandler::new(vec![Response::Vetoed]);

        adapter.run(&mut handler, |_state, handler| {
            handler.handle(Effect::DeductCost {
                actor: EntityRef(1),
                token: "action".into(),
                budget_field: "actions".into(),
            })
        });

        // Budget should be unchanged
        let final_state = adapter.into_inner();
        assert_eq!(
            final_state.turn_budgets.get(&1).and_then(|b| b.get("actions")),
            Some(&Value::Int(1))
        );
    }

    // ── Adapter: apply_condition intercepted ─────────────────────

    #[test]
    fn intercepted_apply_condition() {
        let state = TestWritableState::new();
        let adapter = StateAdapter::new(state);
        let mut handler = RecordingHandler::acknowledged();

        adapter.run(&mut handler, |_state, handler| {
            handler.handle(Effect::ApplyCondition {
                target: EntityRef(1),
                condition: "Prone".into(),
                duration: Value::Duration(DurationValue::EndOfTurn),
            })
        });

        assert_eq!(handler.log.len(), 0); // Intercepted
        let final_state = adapter.into_inner();
        let conds = final_state.conditions.get(&1).unwrap();
        assert_eq!(conds.len(), 1);
        assert_eq!(conds[0].name, "Prone");
    }

    // ── Adapter: remove_condition intercepted ────────────────────

    #[test]
    fn intercepted_remove_condition() {
        let mut state = TestWritableState::new();
        state.conditions.insert(
            1,
            vec![ActiveCondition {
                id: 1,
                name: "Prone".into(),
                bearer: EntityRef(1),
                gained_at: 1,
                duration: Value::Duration(DurationValue::EndOfTurn),
            }],
        );
        let adapter = StateAdapter::new(state);
        let mut handler = RecordingHandler::acknowledged();

        adapter.run(&mut handler, |_state, handler| {
            handler.handle(Effect::RemoveCondition {
                target: EntityRef(1),
                condition: "Prone".into(),
            })
        });

        let final_state = adapter.into_inner();
        let conds = final_state.conditions.get(&1).unwrap();
        assert_eq!(conds.len(), 0);
    }

    // ── Adapter: MutateTurnField intercepted ─────────────────────

    #[test]
    fn intercepted_mutate_turn_field() {
        let mut state = TestWritableState::new();
        state
            .turn_budgets
            .entry(1)
            .or_default()
            .insert("movement".into(), Value::Int(0));
        let adapter = StateAdapter::new(state);
        let mut handler = RecordingHandler::acknowledged();

        adapter.run(&mut handler, |_state, handler| {
            handler.handle(Effect::MutateTurnField {
                actor: EntityRef(1),
                field: "movement".into(),
                op: AssignOp::PlusEq,
                value: Value::Int(30),
            })
        });

        let final_state = adapter.into_inner();
        assert_eq!(
            final_state
                .turn_budgets
                .get(&1)
                .and_then(|b| b.get("movement")),
            Some(&Value::Int(30))
        );
    }

    // ── Adapter: bounds clamping ─────────────────────────────────

    #[test]
    fn mutation_with_bounds_clamping() {
        let mut state = TestWritableState::new();
        state.fields.insert((1, "HP".into()), Value::Int(5));
        let adapter = StateAdapter::new(state);
        let mut handler = RecordingHandler::acknowledged();

        adapter.run(&mut handler, |_state, handler| {
            handler.handle(Effect::MutateField {
                entity: EntityRef(1),
                path: vec![FieldPathSegment::Field("HP".into())],
                op: AssignOp::MinusEq,
                value: Value::Int(20),
                bounds: Some((Value::Int(0), Value::Int(100))),
            })
        });

        // 5 - 20 = -15, clamped to 0
        let final_state = adapter.into_inner();
        assert_eq!(
            final_state.fields.get(&(1, "HP".into())),
            Some(&Value::Int(0))
        );
    }

    // ── Adapter: pass-through override syncs overridden value ────

    #[test]
    fn pass_through_override_syncs_overridden_value() {
        let mut state = TestWritableState::new();
        state.fields.insert((1, "HP".into()), Value::Int(30));
        let adapter = StateAdapter::new(state).pass_through(EffectKind::MutateField);
        // Host overrides the RHS to 42; operator (-=) is preserved
        let mut handler = RecordingHandler::new(vec![Response::Override(Value::Int(42))]);

        adapter.run(&mut handler, |_state, handler| {
            handler.handle(Effect::MutateField {
                entity: EntityRef(1),
                path: vec![FieldPathSegment::Field("HP".into())],
                op: AssignOp::MinusEq,
                value: Value::Int(10),
                bounds: None,
            })
        });

        let final_state = adapter.into_inner();
        // Override is replacement RHS: 30 - 42 = -12
        assert_eq!(
            final_state.fields.get(&(1, "HP".into())),
            Some(&Value::Int(-12))
        );
    }

    // ── Adapter: eq assignment ───────────────────────────────────

    #[test]
    fn intercepted_eq_assignment() {
        let mut state = TestWritableState::new();
        state.fields.insert((1, "name".into()), Value::Str("old".into()));
        let adapter = StateAdapter::new(state);
        let mut handler = RecordingHandler::acknowledged();

        adapter.run(&mut handler, |_state, handler| {
            handler.handle(Effect::MutateField {
                entity: EntityRef(1),
                path: vec![FieldPathSegment::Field("name".into())],
                op: AssignOp::Eq,
                value: Value::Str("new".into()),
                bounds: None,
            })
        });

        let final_state = adapter.into_inner();
        assert_eq!(
            final_state.fields.get(&(1, "name".into())),
            Some(&Value::Str("new".into()))
        );
    }

    // ── Integration: full action via GameState + StateAdapter ────

    #[test]
    fn integration_full_action_via_gamestate_and_adapter() {
        use crate::action::execute_action;
        use crate::reference_state::GameState;
        use crate::Interpreter;
        use ttrpg_ast::Span;
        use ttrpg_ast::Spanned;
        use ttrpg_ast::ast::*;
        use ttrpg_checker::env::TypeEnv;

        fn span() -> Span {
            Span { start: 0, end: 0 }
        }
        fn spanned<T>(node: T) -> Spanned<T> {
            Spanned { node, span: span() }
        }

        // Build a simple action that:
        // 1. Costs one action
        // 2. Has a resolve block returning the literal 42
        let action = ActionDecl {
            name: "SimpleAttack".to_string(),
            receiver_name: "actor".to_string(),
            receiver_type: spanned(TypeExpr::Named("Character".to_string())),
            receiver_with_groups: vec![],
            params: vec![],
            cost: Some(CostClause {
                tokens: vec![spanned("action".to_string())],
                span: span(),
            }),
            requires: None,
            resolve: spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::IntLit(
                42,
            ))))]),
            trigger_text: None,
            synthetic: false,
        };

        // Set up GameState with an entity that has a turn budget
        let mut game_state = GameState::new();
        let actor = game_state.add_entity("Fighter", HashMap::new());
        let mut budget = BTreeMap::new();
        budget.insert("actions".into(), Value::Int(1));
        budget.insert("bonus_actions".into(), Value::Int(1));
        budget.insert("reactions".into(), Value::Int(1));
        game_state.set_turn_budget(&actor, budget);

        // Wrap in StateAdapter (Layer 2)
        let adapter = StateAdapter::new(game_state);
        let program = Program::default();
        let type_env = TypeEnv::new();
        let interp = Interpreter::new(&program, &type_env).unwrap();

        // Use a recording handler that acknowledges everything
        let mut host_handler = RecordingHandler::acknowledged();

        // Execute the action through the adapter
        let result = adapter.run(&mut host_handler, |state, handler| {
            let mut env = crate::Env::new(state, handler, &interp);
            execute_action(&mut env, &action, actor, vec![], span())
        });

        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Value::Int(42));

        // Verify the adapter applied the cost deduction:
        // - The host handler should have seen ActionStarted, DeductCost, ActionCompleted
        //   (DeductCost is always passed through)
        assert!(host_handler.log.len() >= 2);
        // ActionStarted is non-mutation → forwarded
        assert!(matches!(
            &host_handler.log[0],
            Effect::ActionStarted { .. }
        ));
        // DeductCost is always passed through
        assert!(matches!(&host_handler.log[1], Effect::DeductCost { .. }));

        // Verify the state was mutated: actions budget decremented from 1 to 0
        let final_state = adapter.into_inner();
        let budget = final_state.read_turn_budget(&actor).unwrap();
        assert_eq!(budget.get("actions"), Some(&Value::Int(0)));
        // Other budget fields unchanged
        assert_eq!(budget.get("bonus_actions"), Some(&Value::Int(1)));
        assert_eq!(budget.get("reactions"), Some(&Value::Int(1)));
    }

    // ── Override: condition duration ──────────────────────────────

    #[test]
    fn pass_through_apply_condition_override_duration() {
        let state = TestWritableState::new();
        let adapter = StateAdapter::new(state).pass_through(EffectKind::ApplyCondition);
        // Host overrides the duration to Rounds(3)
        let mut handler = RecordingHandler::new(vec![Response::Override(Value::Duration(
            DurationValue::Rounds(3),
        ))]);

        adapter.run(&mut handler, |_state, handler| {
            handler.handle(Effect::ApplyCondition {
                target: EntityRef(1),
                condition: "Prone".into(),
                duration: Value::Duration(DurationValue::EndOfTurn),
            })
        });

        let final_state = adapter.into_inner();
        let conds = final_state.conditions.get(&1).unwrap();
        assert_eq!(conds.len(), 1);
        assert_eq!(conds[0].name, "Prone");
        // Duration should be the overridden value, not the original
        assert_eq!(
            conds[0].duration,
            Value::Duration(DurationValue::Rounds(3))
        );
    }

    // ── Override: condition name for removal ──────────────────────

    #[test]
    fn pass_through_remove_condition_override_name() {
        let mut state = TestWritableState::new();
        // Set up entity with two conditions
        state.conditions.insert(
            1,
            vec![
                ActiveCondition {
                    id: 1,
                    name: "Prone".into(),
                    bearer: EntityRef(1),
                    gained_at: 1,
                    duration: Value::Duration(DurationValue::EndOfTurn),
                },
                ActiveCondition {
                    id: 2,
                    name: "Frightened".into(),
                    bearer: EntityRef(1),
                    gained_at: 2,
                    duration: Value::Duration(DurationValue::Rounds(1)),
                },
            ],
        );
        let adapter = StateAdapter::new(state).pass_through(EffectKind::RemoveCondition);
        // Host overrides: remove "Frightened" instead of "Prone"
        let mut handler =
            RecordingHandler::new(vec![Response::Override(Value::Str("Frightened".into()))]);

        adapter.run(&mut handler, |_state, handler| {
            handler.handle(Effect::RemoveCondition {
                target: EntityRef(1),
                condition: "Prone".into(),
            })
        });

        let final_state = adapter.into_inner();
        let conds = final_state.conditions.get(&1).unwrap();
        // "Frightened" removed, "Prone" remains
        assert_eq!(conds.len(), 1);
        assert_eq!(conds[0].name, "Prone");
    }

    // ── Override: MutateField preserves operator ──────────────────

    #[test]
    fn pass_through_override_mutate_field_preserves_op() {
        let mut state = TestWritableState::new();
        state.fields.insert((1, "HP".into()), Value::Int(30));
        let adapter = StateAdapter::new(state).pass_through(EffectKind::MutateField);
        // Override RHS to 10; original op is -=
        let mut handler = RecordingHandler::new(vec![Response::Override(Value::Int(10))]);

        adapter.run(&mut handler, |_state, handler| {
            handler.handle(Effect::MutateField {
                entity: EntityRef(1),
                path: vec![FieldPathSegment::Field("HP".into())],
                op: AssignOp::MinusEq,
                value: Value::Int(15),
                bounds: None,
            })
        });

        let final_state = adapter.into_inner();
        // 30 - 10 = 20 (operator preserved, override replaces RHS)
        assert_eq!(
            final_state.fields.get(&(1, "HP".into())),
            Some(&Value::Int(20))
        );
    }

    // ── Override: MutateTurnField preserves operator ──────────────

    #[test]
    fn pass_through_override_turn_field_preserves_op() {
        let mut state = TestWritableState::new();
        state
            .turn_budgets
            .entry(1)
            .or_default()
            .insert("movement".into(), Value::Int(10));
        let adapter = StateAdapter::new(state).pass_through(EffectKind::MutateTurnField);
        // Override RHS to 5; original op is +=
        let mut handler = RecordingHandler::new(vec![Response::Override(Value::Int(5))]);

        adapter.run(&mut handler, |_state, handler| {
            handler.handle(Effect::MutateTurnField {
                actor: EntityRef(1),
                field: "movement".into(),
                op: AssignOp::PlusEq,
                value: Value::Int(30),
            })
        });

        let final_state = adapter.into_inner();
        // 10 + 5 = 15 (operator preserved, override replaces RHS)
        assert_eq!(
            final_state
                .turn_budgets
                .get(&1)
                .and_then(|b| b.get("movement")),
            Some(&Value::Int(15))
        );
    }
}
