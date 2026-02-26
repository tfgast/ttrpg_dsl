use crate::effect::FieldPathSegment;
use std::collections::BTreeMap;

use ttrpg_ast::Name;

use crate::value::Value;

// ── EntityRef ───────────────────────────────────────────────────

/// An opaque handle to an entity in the host's state.
///
/// The interpreter never constructs `EntityRef`s — they come from
/// function parameters or `StateProvider` reads. The host maps
/// these to its own entity representation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EntityRef(pub u64);

// ── ActiveCondition ─────────────────────────────────────────────

/// An active condition on an entity.
///
/// The interpreter uses `gained_at` for modifier ordering (oldest first).
/// The host is responsible for removing expired conditions based on
/// duration semantics.
#[derive(Debug, Clone)]
pub struct ActiveCondition {
    /// Unique identifier for this condition instance.
    /// Assigned by the host (or by `GameState` in Layer 3).
    /// Used for deduplication when the same condition is collected
    /// through multiple entity-typed parameters.
    pub id: u64,
    /// Condition name (e.g., "Prone").
    pub name: Name,
    /// Condition parameters (e.g., `source: Entity(1)` for `Frightened(source: attacker)`).
    /// Empty map for conditions with no parameters.
    pub params: BTreeMap<Name, Value>,
    /// Entity bearing this condition.
    pub bearer: EntityRef,
    /// Ordering timestamp (oldest first).
    pub gained_at: u64,
    /// Duration value (e.g., `duration_variant("rounds")` or any ruleset-defined Duration variant).
    pub duration: Value,
}

// ── StateProvider trait ─────────────────────────────────────────

/// The host implements this trait to give the interpreter synchronous
/// read access to game state.
///
/// Reads are synchronous and do not yield effects. Writes go through
/// effects (`MutateField`, `ApplyCondition`, etc.).
///
/// If a read returns `None`, the interpreter returns `RuntimeError` —
/// since the program has passed type-checking, `None` indicates the
/// host's state is out of sync with the DSL program.
pub trait StateProvider {
    /// Read a single field from an entity.
    /// Returns `None` if the entity doesn't exist or the field is missing.
    fn read_field(&self, entity: &EntityRef, field: &str) -> Option<Value>;

    /// Active conditions on an entity, ordered by `gained_at` (oldest first).
    /// Returns `None` if the entity doesn't exist.
    fn read_conditions(&self, entity: &EntityRef) -> Option<Vec<ActiveCondition>>;

    /// Current turn budget for an entity as a dynamic field map.
    /// Returns `None` if the entity doesn't exist.
    fn read_turn_budget(&self, entity: &EntityRef) -> Option<BTreeMap<Name, Value>>;

    /// Names of currently enabled options.
    fn read_enabled_options(&self) -> Vec<Name>;

    /// Test equality of two opaque Position values.
    /// The interpreter calls this when evaluating `==` or `!=` on Positions.
    fn position_eq(&self, a: &Value, b: &Value) -> bool;

    /// Compute the distance between two opaque Position values.
    /// Returns `None` if the inputs are not valid positions.
    fn distance(&self, a: &Value, b: &Value) -> Option<i64>;

    /// Get the entity's declared type name (e.g. "Character", "Monster").
    /// Returns `None` if unknown. Used by `grant` to resolve group defaults.
    fn entity_type_name(&self, _entity: &EntityRef) -> Option<Name> {
        None
    }
}

// ── WritableState trait ─────────────────────────────────────────

/// Extension of `StateProvider` that supports writes.
///
/// Used by `StateAdapter` (Layer 2) to auto-apply mutation effects.
pub trait WritableState: StateProvider {
    /// Write a value to an entity field at the given path.
    fn write_field(&mut self, entity: &EntityRef, path: &[FieldPathSegment], value: Value);

    /// Add a condition to an entity.
    fn add_condition(&mut self, entity: &EntityRef, cond: ActiveCondition);

    /// Remove a condition from an entity by name.
    /// If `params` is `Some`, only remove conditions whose params match.
    /// If `params` is `None`, remove all conditions with the given name.
    fn remove_condition(
        &mut self,
        entity: &EntityRef,
        name: &str,
        params: Option<&BTreeMap<Name, Value>>,
    );

    /// Write a value to a turn budget field.
    fn write_turn_field(&mut self, entity: &EntityRef, field: &str, value: Value);

    /// Remove a field from an entity (used by `RevokeGroup`).
    fn remove_field(&mut self, entity: &EntityRef, field: &str);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::{default_turn_budget, duration_variant};
    use std::collections::HashMap;

    // A minimal test implementation of StateProvider.
    struct TestState {
        fields: HashMap<(u64, String), Value>,
        conditions: HashMap<u64, Vec<ActiveCondition>>,
        turn_budgets: HashMap<u64, BTreeMap<Name, Value>>,
        enabled_options: Vec<Name>,
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

        fn read_turn_budget(&self, entity: &EntityRef) -> Option<BTreeMap<Name, Value>> {
            self.turn_budgets.get(&entity.0).cloned()
        }

        fn read_enabled_options(&self) -> Vec<Name> {
            self.enabled_options.clone()
        }

        fn position_eq(&self, _a: &Value, _b: &Value) -> bool {
            false
        }

        fn distance(&self, _a: &Value, _b: &Value) -> Option<i64> {
            None
        }
    }

    #[test]
    fn entity_ref_equality() {
        assert_eq!(EntityRef(1), EntityRef(1));
        assert_ne!(EntityRef(1), EntityRef(2));
    }

    #[test]
    fn entity_ref_ordering() {
        assert!(EntityRef(1) < EntityRef(2));
    }

    #[test]
    fn test_state_read_field() {
        let mut state = TestState::new();
        let entity = EntityRef(1);
        state.fields.insert((1, "HP".into()), Value::Int(30));

        assert_eq!(state.read_field(&entity, "HP"), Some(Value::Int(30)));
        assert_eq!(state.read_field(&entity, "AC"), None);
        assert_eq!(state.read_field(&EntityRef(99), "HP"), None);
    }

    #[test]
    fn test_state_read_conditions() {
        let mut state = TestState::new();
        let entity = EntityRef(1);
        state.conditions.insert(
            1,
            vec![ActiveCondition {
                id: 100,
                name: "Prone".into(),
                params: BTreeMap::new(),
                bearer: entity,
                gained_at: 5,
                duration: duration_variant("end_of_turn"),
            }],
        );

        let conds = state.read_conditions(&entity).unwrap();
        assert_eq!(conds.len(), 1);
        assert_eq!(conds[0].name, "Prone");
        assert_eq!(conds[0].id, 100);
        assert_eq!(conds[0].gained_at, 5);
    }

    #[test]
    fn test_state_read_turn_budget() {
        let mut state = TestState::new();
        let entity = EntityRef(1);
        // Extract the fields from the default turn budget Value::Struct
        let fields = match default_turn_budget() {
            Value::Struct { fields, .. } => fields,
            _ => unreachable!(),
        };
        state.turn_budgets.insert(1, fields);

        let budget = state.read_turn_budget(&entity).unwrap();
        assert_eq!(budget.get("actions"), Some(&Value::Int(1)));
        assert_eq!(budget.get("bonus_actions"), Some(&Value::Int(1)));
        assert_eq!(budget.get("reactions"), Some(&Value::Int(1)));
    }

    #[test]
    fn test_state_read_enabled_options() {
        let mut state = TestState::new();
        state.enabled_options.push("flanking".into());
        state.enabled_options.push("critical_fumbles".into());

        let opts = state.read_enabled_options();
        assert_eq!(opts.len(), 2);
        assert!(opts.contains(&Name::from("flanking")));
    }

    #[test]
    fn active_condition_construction() {
        let cond = ActiveCondition {
            id: 42,
            name: "Stunned".into(),
            params: BTreeMap::new(),
            bearer: EntityRef(1),
            gained_at: 10,
            duration: duration_variant("rounds"),
        };
        assert_eq!(cond.id, 42);
        assert_eq!(cond.name, "Stunned");
        assert_eq!(cond.bearer, EntityRef(1));
        assert_eq!(cond.gained_at, 10);
    }
}
