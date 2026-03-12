use crate::effect::FieldPathSegment;
use std::collections::{BTreeMap, BTreeSet};

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

// ── InvocationId ────────────────────────────────────────────────

/// Unique identifier for an action/reaction/hook execution.
/// All conditions applied during that execution share this ID.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct InvocationId(pub u64);

// ── ConditionToken ──────────────────────────────────────────────

/// Pre-allocated unique ID for a condition instance.
///
/// Allocated *before* `on_apply` runs so that lifecycle blocks can
/// reference the upcoming condition (e.g. to create suspension records
/// keyed to this condition). Becomes `ActiveCondition.id` when the
/// condition is activated.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ConditionToken(pub u64);

// ── Suspension ─────────────────────────────────────────────────

/// Whether a suspended entity remains on the map or is off-board.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Presence {
    /// Entity stays on the map (e.g. Temporal Stasis — inert but visible).
    OnMap,
    /// Entity is removed from ordinary play (e.g. Imprisonment, Trap the Soul).
    /// Off-board entities are excluded from `entities_in_play()` scans.
    OffBoard,
}

/// A single suspension record tied to a source (typically a condition instance).
///
/// Multiple records can coexist on one entity. Resolution uses worst-case-wins:
/// off-board if ANY record says OffBoard, turns frozen if ANY says so, etc.
/// Records are keyed by `source_id` (usually a `ConditionToken` value) so that
/// overlapping effects don't restore too early.
#[derive(Debug, Clone)]
pub struct SuspensionRecord {
    /// Identifier of the source that created this suspension.
    /// Typically the `ConditionToken` / `ActiveCondition.id` value.
    pub source_id: u64,
    /// Whether the entity remains on the map or is off-board.
    pub presence: Presence,
    /// Whether the entity's turns are frozen (skipped by initiative).
    pub freeze_turns: bool,
    /// Whether condition durations on this entity are frozen.
    pub freeze_durations: bool,
    /// Game time when this suspension started. Used to compute
    /// `applied_at` adjustments on unfreeze.
    pub suspended_at: u64,
}

// ── ConditionArgs ───────────────────────────────────────────────

/// Arguments for applying a condition, with sensible defaults.
///
/// Most callers only need the condition name and target entity (passed
/// separately to `apply_condition`). This struct bundles the optional
/// fields so that new additions (like `source`) don't force every
/// callsite to update.
///
/// ```ignore
/// // Minimal: all defaults
/// state.apply_condition(&entity, "Prone", ConditionArgs::default());
///
/// // With overrides:
/// state.apply_condition(&entity, "Prone", ConditionArgs {
///     duration: duration_variant("Rounds"),
///     ..Default::default()
/// });
/// ```
#[derive(Debug, Clone)]
pub struct ConditionArgs {
    /// Condition parameters (e.g., `source: Entity(1)` for `Frightened(source: attacker)`).
    pub params: BTreeMap<Name, Value>,
    /// Duration value (e.g., `duration_variant("Rounds")`). Default: `Value::Void`.
    pub duration: Value,
    /// The invocation that applied this condition, if any. Default: `None`.
    pub invocation: Option<InvocationId>,
    /// Effect source metadata. Default: `EffectSource.Unknown`.
    pub source: Value,
    /// Tags from the condition declaration. Default: empty.
    pub tags: BTreeSet<Name>,
}

impl Default for ConditionArgs {
    fn default() -> Self {
        Self {
            params: BTreeMap::new(),
            duration: Value::Void,
            invocation: None,
            source: crate::value::effect_source_unknown(),
            tags: BTreeSet::new(),
        }
    }
}

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
    /// Duration value (e.g., `duration_variant("Rounds")` or any ruleset-defined Duration variant).
    pub duration: Value,
    /// The invocation that applied this condition, if any.
    /// `None` for conditions applied outside action scope (CLI grant, host-injected).
    pub invocation: Option<InvocationId>,
    /// Game time when this condition was applied.
    /// Set from `read_game_time()` by the adapter at application time.
    pub applied_at: u64,
    /// Effect source metadata (e.g., `EffectSource.Spell(...)` or `EffectSource.Unknown`).
    /// Ruleset-defined enum; defaults to `EffectSource.Unknown` when not specified.
    pub source: Value,
    /// Tags from the condition declaration (e.g., `#curse`, `#disease`).
    /// Static categorical properties of the condition type.
    pub tags: BTreeSet<Name>,
    /// Per-instance mutable state fields declared in `state { ... }`.
    /// Private to the condition hierarchy — not exposed in `to_value()`.
    pub state_fields: BTreeMap<Name, Value>,
}

impl ActiveCondition {
    /// Convert this active condition to a `Value::Struct` for DSL-level access.
    pub fn to_value(&self) -> Value {
        let mut fields = BTreeMap::new();
        fields.insert(Name::from("name"), Value::Str(self.name.to_string()));
        fields.insert(Name::from("duration"), self.duration.clone());
        fields.insert(
            Name::from("id"),
            Value::Int(self.id.min(i64::MAX as u64) as i64),
        );
        fields.insert(
            Name::from("applied_at"),
            Value::Int(self.applied_at.min(i64::MAX as u64) as i64),
        );
        fields.insert(Name::from("source"), self.source.clone());
        fields.insert(
            Name::from("tags"),
            Value::Set(
                self.tags
                    .iter()
                    .map(|t| Value::Str(t.to_string()))
                    .collect(),
            ),
        );
        Value::Struct {
            name: Name::from("ActiveCondition"),
            fields,
        }
    }

    /// Convert to a typed `Value::Struct` that includes params and state.
    ///
    /// Used by the 2-arg `conditions(entity, CondName)` overload.
    /// Includes base ActiveCondition fields, condition parameters, and
    /// a `state` sub-struct containing the per-instance mutable state.
    pub fn to_typed_value(&self) -> Value {
        let mut fields = BTreeMap::new();
        // Base fields
        fields.insert(Name::from("name"), Value::Str(self.name.to_string()));
        fields.insert(Name::from("duration"), self.duration.clone());
        fields.insert(
            Name::from("id"),
            Value::Int(self.id.min(i64::MAX as u64) as i64),
        );
        fields.insert(
            Name::from("applied_at"),
            Value::Int(self.applied_at.min(i64::MAX as u64) as i64),
        );
        fields.insert(Name::from("source"), self.source.clone());
        fields.insert(
            Name::from("tags"),
            Value::Set(
                self.tags
                    .iter()
                    .map(|t| Value::Str(t.to_string()))
                    .collect(),
            ),
        );
        // Condition parameters
        for (name, value) in &self.params {
            fields.insert(name.clone(), value.clone());
        }
        // State sub-struct (read-only snapshot)
        if !self.state_fields.is_empty() {
            fields.insert(
                Name::from("state"),
                Value::Struct {
                    name: Name::from("state"),
                    fields: self.state_fields.clone(),
                },
            );
        }
        Value::Struct {
            name: Name::from("ActiveCondition"),
            fields,
        }
    }
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

    /// Test equality of two opaque position handles.
    /// The interpreter calls this when evaluating `==` or `!=` on Positions.
    fn position_eq(&self, a: u64, b: u64) -> bool;

    /// Test equality of two opaque direction handles.
    /// The interpreter calls this when evaluating `==` or `!=` on Directions.
    fn direction_eq(&self, _a: u64, _b: u64) -> bool {
        false
    }

    /// Compute the distance between two opaque position handles.
    /// Returns `None` if a handle is unknown.
    fn distance(&self, a: u64, b: u64) -> Option<i64>;

    /// Read the current game time counter.
    /// Returns `0` by default (no time tracking).
    fn read_game_time(&self) -> u64 {
        0
    }

    /// Get the entity's declared type name (e.g. "Character", "Monster").
    /// Returns `None` if unknown. Used by `grant` to resolve group defaults.
    fn entity_type_name(&self, _entity: &EntityRef) -> Option<Name> {
        None
    }

    /// Resolve an opaque position handle to its (x, y) coordinates.
    /// Returns `None` if the handle is unknown.
    fn resolve_position(&self, _handle: u64) -> Option<(i64, i64)> {
        None
    }

    /// Return all entity refs known to the state.
    /// Used by `emit` to find hook candidates.
    fn all_entities(&self) -> Vec<EntityRef> {
        Vec::new()
    }

    // ── Suspension queries ──────────────────────────────────────

    /// Return entities that are in ordinary play (excludes off-board suspended).
    ///
    /// Use for event/hook/reaction candidate scans. Direct-ref access
    /// (e.g. Freedom targeting an imprisoned entity) should use `all_entities()`.
    fn entities_in_play(&self) -> Vec<EntityRef> {
        self.all_entities()
    }

    /// Whether the entity has any suspension records.
    fn is_suspended(&self, _entity: &EntityRef) -> bool {
        false
    }

    /// Whether the entity is off-board (excluded from `entities_in_play()`).
    fn is_off_board(&self, _entity: &EntityRef) -> bool {
        false
    }

    /// Whether the entity's turns should be skipped.
    fn are_turns_frozen(&self, _entity: &EntityRef) -> bool {
        false
    }

    /// Whether the entity's condition durations are frozen.
    fn are_durations_frozen(&self, _entity: &EntityRef) -> bool {
        false
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

    /// Remove a condition by its unique instance id.
    fn remove_condition_by_id(&mut self, entity: &EntityRef, id: u64);

    /// Write a value to a turn budget field.
    fn write_turn_field(&mut self, entity: &EntityRef, field: &str, value: Value);

    /// Remove a field from an entity (used by `RevokeGroup`).
    fn remove_field(&mut self, entity: &EntityRef, field: &str);

    /// Remove all conditions tagged with the given invocation, across all entities.
    fn remove_conditions_by_invocation(&mut self, invocation: InvocationId);

    /// Set the turn budget for an entity, replacing any existing budget.
    fn set_turn_budget(&mut self, entity: &EntityRef, budget: BTreeMap<Name, Value>);

    /// Remove the turn budget for an entity entirely.
    fn clear_turn_budget(&mut self, entity: &EntityRef);

    /// Set the game time counter.
    fn set_game_time(&mut self, time: u64);

    /// Add a new entity with the given type name and fields.
    /// Returns a reference to the new entity.
    fn add_entity(
        &mut self,
        type_name: &str,
        fields: rustc_hash::FxHashMap<Name, Value>,
    ) -> EntityRef;

    /// Remove an entity and all associated data (conditions, turn budgets).
    fn remove_entity(&mut self, entity: &EntityRef);

    /// Pre-allocate a condition ID for use as a `ConditionToken`.
    ///
    /// The returned ID will become `ActiveCondition.id` when the condition
    /// is activated via `add_condition`. This allows lifecycle blocks to
    /// reference the upcoming condition before it exists in state.
    fn allocate_condition_id(&mut self) -> ConditionToken;

    // ── Suspension methods ──────────────────────────────────────

    /// Add a suspension record to an entity.
    fn add_suspension(&mut self, entity: &EntityRef, record: SuspensionRecord);

    /// Update the state fields of a condition instance by id.
    /// No-op if the condition id does not exist on any entity.
    fn set_condition_state(
        &mut self,
        entity: &EntityRef,
        condition_id: u64,
        fields: BTreeMap<Name, Value>,
    );

    /// Remove the suspension record with the given `source_id` from an entity.
    ///
    /// If this was the last `freeze_durations` record, adjusts `applied_at`
    /// on all the entity's conditions using the per-condition rule:
    /// `applied_at += now - max(applied_at, freeze_start)`
    fn remove_suspension_source(&mut self, entity: &EntityRef, source_id: u64);

    /// Get all suspension records for an entity.
    fn suspension_records(&self, entity: &EntityRef) -> Vec<SuspensionRecord>;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::{default_turn_budget, duration_variant, effect_source_unknown};
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

        fn position_eq(&self, _a: u64, _b: u64) -> bool {
            false
        }

        fn distance(&self, _a: u64, _b: u64) -> Option<i64> {
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
                duration: duration_variant("EndOfTurn"),
                invocation: None,
                applied_at: 0,
                source: effect_source_unknown(),
                tags: BTreeSet::new(),
                state_fields: BTreeMap::new(),
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
            duration: duration_variant("Rounds"),
            invocation: None,
            applied_at: 0,
            source: effect_source_unknown(),
            tags: BTreeSet::new(),
            state_fields: BTreeMap::new(),
        };
        assert_eq!(cond.id, 42);
        assert_eq!(cond.name, "Stunned");
        assert_eq!(cond.bearer, EntityRef(1));
        assert_eq!(cond.gained_at, 10);
    }

    #[test]
    fn active_condition_to_value_no_params() {
        let cond = ActiveCondition {
            id: 7,
            name: "Prone".into(),
            params: BTreeMap::new(),
            bearer: EntityRef(1),
            gained_at: 3,
            duration: duration_variant("EndOfTurn"),
            invocation: None,
            applied_at: 42,
            source: effect_source_unknown(),
            tags: BTreeSet::new(),
            state_fields: BTreeMap::new(),
        };
        let val = cond.to_value();
        match &val {
            Value::Struct { name, fields } => {
                assert_eq!(name, "ActiveCondition");
                assert_eq!(fields.get("name"), Some(&Value::Str("Prone".into())));
                assert_eq!(fields.get("id"), Some(&Value::Int(7)));
                assert_eq!(fields.get("duration"), Some(&duration_variant("EndOfTurn")));
                assert_eq!(fields.get("applied_at"), Some(&Value::Int(42)));
            }
            _ => panic!("expected Value::Struct"),
        }
    }

    #[test]
    fn active_condition_to_value_with_params() {
        let mut params = BTreeMap::new();
        params.insert(Name::from("source"), Value::Entity(EntityRef(2)));
        let cond = ActiveCondition {
            id: 99,
            name: "Frightened".into(),
            params,
            bearer: EntityRef(1),
            gained_at: 5,
            duration: duration_variant("Rounds"),
            invocation: None,
            applied_at: 0,
            source: effect_source_unknown(),
            tags: BTreeSet::new(),
            state_fields: BTreeMap::new(),
        };
        let val = cond.to_value();
        match &val {
            Value::Struct { name, fields } => {
                assert_eq!(name, "ActiveCondition");
                assert_eq!(fields.get("name"), Some(&Value::Str("Frightened".into())));
                assert_eq!(fields.get("id"), Some(&Value::Int(99)));
                // params are not exposed in the value (deferred)
                assert!(!fields.contains_key("params"));
            }
            _ => panic!("expected Value::Struct"),
        }
    }

    #[test]
    fn active_condition_to_value_includes_tags() {
        let mut tags = BTreeSet::new();
        tags.insert(Name::from("curse"));
        tags.insert(Name::from("disease"));
        let cond = ActiveCondition {
            id: 1,
            name: "MummyRot".into(),
            params: BTreeMap::new(),
            bearer: EntityRef(1),
            gained_at: 0,
            duration: Value::Void,
            invocation: None,
            applied_at: 0,
            source: effect_source_unknown(),
            tags,
            state_fields: BTreeMap::new(),
        };
        let val = cond.to_value();
        match &val {
            Value::Struct { fields, .. } => {
                let expected_tags = Value::Set(
                    [Value::Str("curse".into()), Value::Str("disease".into())]
                        .into_iter()
                        .collect(),
                );
                assert_eq!(fields.get("tags"), Some(&expected_tags));
            }
            _ => panic!("expected Value::Struct"),
        }
    }
}
