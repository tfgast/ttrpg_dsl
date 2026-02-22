use std::any::Any;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::Arc;

use crate::effect::FieldPathSegment;
use crate::state::{ActiveCondition, EntityRef, StateProvider, WritableState};
use crate::value::{PositionValue, Value};

// ── Grid position ──────────────────────────────────────────────

/// A simple 2D grid position used by `GameState`.
///
/// Chebyshev distance (`max(|dx|, |dy|)`) matches D&D 5e's standard
/// movement rules where diagonal movement costs the same as orthogonal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GridPosition(pub i64, pub i64);

impl GridPosition {
    /// Create a `Value::Position` wrapping this grid position.
    pub fn to_value(self) -> Value {
        Value::Position(PositionValue(Arc::new(self) as Arc<dyn Any + Send + Sync>))
    }
}

// ── EntityState ────────────────────────────────────────────────

struct EntityState {
    name: String,
    fields: HashMap<String, Value>,
}

// ── GameState ──────────────────────────────────────────────────

/// A reference implementation of `WritableState` for testing
/// and simple host integrations.
///
/// Provides entity management, condition tracking, turn budgets,
/// option toggling, and grid-based position operations.
pub struct GameState {
    entities: HashMap<u64, EntityState>,
    conditions: HashMap<u64, Vec<ActiveCondition>>,
    turn_budgets: HashMap<u64, BTreeMap<String, Value>>,
    enabled_options: HashSet<String>,
    next_entity_id: u64,
    next_condition_id: u64,
}

impl GameState {
    /// Create a new empty game state.
    pub fn new() -> Self {
        GameState {
            entities: HashMap::new(),
            conditions: HashMap::new(),
            turn_budgets: HashMap::new(),
            enabled_options: HashSet::new(),
            next_entity_id: 1,
            next_condition_id: 1,
        }
    }

    /// Add a new entity with the given name and fields.
    /// Returns a reference to the new entity.
    pub fn add_entity(&mut self, name: &str, fields: HashMap<String, Value>) -> EntityRef {
        let id = self.next_entity_id;
        self.next_entity_id += 1;
        self.entities.insert(
            id,
            EntityState {
                name: name.to_string(),
                fields,
            },
        );
        EntityRef(id)
    }

    /// Set the turn budget for an entity.
    ///
    /// Silently does nothing if the entity doesn't exist, consistent
    /// with read paths that reject unknown entities.
    pub fn set_turn_budget(&mut self, entity: &EntityRef, budget: BTreeMap<String, Value>) {
        if !self.entities.contains_key(&entity.0) {
            return;
        }
        self.turn_budgets.insert(entity.0, budget);
    }

    /// Apply a condition to an entity with auto-assigned id and timestamp.
    ///
    /// Silently does nothing if the entity doesn't exist, consistent
    /// with read paths that reject unknown entities.
    pub fn apply_condition(&mut self, entity: &EntityRef, name: &str, duration: Value) {
        if !self.entities.contains_key(&entity.0) {
            return;
        }
        let id = self.next_condition_id;
        self.next_condition_id += 1;
        let cond = ActiveCondition {
            id,
            name: name.to_string(),
            bearer: *entity,
            gained_at: id, // Use id as ordering timestamp for simplicity
            duration,
        };
        self.conditions.entry(entity.0).or_default().push(cond);
    }

    /// Get the type name (as passed to `add_entity`) for an entity.
    pub fn entity_type_name(&self, entity: &EntityRef) -> Option<&str> {
        self.entities.get(&entity.0).map(|e| e.name.as_str())
    }

    /// Remove an entity and all associated data (conditions, turn budgets).
    /// Returns `true` if the entity existed and was removed.
    pub fn remove_entity(&mut self, entity: &EntityRef) -> bool {
        let existed = self.entities.remove(&entity.0).is_some();
        if existed {
            self.conditions.remove(&entity.0);
            self.turn_budgets.remove(&entity.0);
        }
        existed
    }

    /// Enable an option by name.
    pub fn enable_option(&mut self, name: &str) {
        self.enabled_options.insert(name.to_string());
    }

    /// Disable an option by name.
    pub fn disable_option(&mut self, name: &str) {
        self.enabled_options.remove(name);
    }
}

impl Default for GameState {
    fn default() -> Self {
        Self::new()
    }
}

// ── StateProvider impl ─────────────────────────────────────────

impl StateProvider for GameState {
    fn read_field(&self, entity: &EntityRef, field: &str) -> Option<Value> {
        self.entities
            .get(&entity.0)?
            .fields
            .get(field)
            .cloned()
    }

    fn read_conditions(&self, entity: &EntityRef) -> Option<Vec<ActiveCondition>> {
        if !self.entities.contains_key(&entity.0) {
            return None;
        }
        Some(
            self.conditions
                .get(&entity.0)
                .cloned()
                .unwrap_or_default(),
        )
    }

    fn read_turn_budget(&self, entity: &EntityRef) -> Option<BTreeMap<String, Value>> {
        if !self.entities.contains_key(&entity.0) {
            return None;
        }
        self.turn_budgets.get(&entity.0).cloned()
    }

    fn read_enabled_options(&self) -> Vec<String> {
        self.enabled_options.iter().cloned().collect()
    }

    fn position_eq(&self, a: &Value, b: &Value) -> bool {
        match (a, b) {
            (Value::Position(pa), Value::Position(pb)) => {
                let a_grid = pa.0.downcast_ref::<GridPosition>();
                let b_grid = pb.0.downcast_ref::<GridPosition>();
                match (a_grid, b_grid) {
                    (Some(a), Some(b)) => a == b,
                    _ => false,
                }
            }
            _ => false,
        }
    }

    fn distance(&self, a: &Value, b: &Value) -> Option<i64> {
        match (a, b) {
            (Value::Position(pa), Value::Position(pb)) => {
                let a_grid = pa.0.downcast_ref::<GridPosition>()?;
                let b_grid = pb.0.downcast_ref::<GridPosition>()?;
                // Chebyshev distance: max(|dx|, |dy|)
                // Use saturating arithmetic to avoid overflow/panic on extreme coordinates.
                let dx = a_grid.0.saturating_sub(b_grid.0).saturating_abs();
                let dy = a_grid.1.saturating_sub(b_grid.1).saturating_abs();
                Some(dx.max(dy))
            }
            _ => None,
        }
    }
}

// ── WritableState impl ─────────────────────────────────────────

impl WritableState for GameState {
    fn write_field(&mut self, entity: &EntityRef, path: &[FieldPathSegment], value: Value) {
        let Some(entity_state) = self.entities.get_mut(&entity.0) else {
            return;
        };
        if path.is_empty() {
            return;
        }

        let root_field = match &path[0] {
            FieldPathSegment::Field(f) => f.clone(),
            _ => return,
        };

        if path.len() == 1 {
            // Simple field write
            entity_state.fields.insert(root_field, value);
            return;
        }

        // Nested path: navigate and set the leaf
        let Some(root_val) = entity_state.fields.get_mut(&root_field) else {
            return;
        };
        write_nested(root_val, &path[1..], value);
    }

    fn add_condition(&mut self, entity: &EntityRef, mut cond: ActiveCondition) {
        if !self.entities.contains_key(&entity.0) {
            return;
        }
        // Auto-assign id and timestamp if not set (id == 0 indicates adapter-created)
        if cond.id == 0 {
            cond.id = self.next_condition_id;
            self.next_condition_id += 1;
            cond.gained_at = cond.id;
        }
        self.conditions.entry(entity.0).or_default().push(cond);
    }

    fn remove_condition(&mut self, entity: &EntityRef, name: &str) {
        if let Some(conds) = self.conditions.get_mut(&entity.0) {
            conds.retain(|c| c.name != name);
        }
    }

    fn write_turn_field(&mut self, entity: &EntityRef, field: &str, value: Value) {
        if !self.entities.contains_key(&entity.0) {
            return;
        }
        self.turn_budgets
            .entry(entity.0)
            .or_default()
            .insert(field.to_string(), value);
    }
}

/// Navigate a nested path and write the value at the leaf.
fn write_nested(current: &mut Value, path: &[FieldPathSegment], value: Value) {
    if path.is_empty() {
        *current = value;
        return;
    }

    match &path[0] {
        FieldPathSegment::Field(f) => {
            if let Value::Struct { fields, .. } = current {
                if path.len() == 1 {
                    fields.insert(f.clone(), value);
                } else if let Some(inner) = fields.get_mut(f.as_str()) {
                    write_nested(inner, &path[1..], value);
                }
            }
        }
        FieldPathSegment::Index(key) => match current {
            Value::Map(map) => {
                if path.len() == 1 {
                    map.insert(key.clone(), value);
                } else if let Some(inner) = map.get_mut(key) {
                    write_nested(inner, &path[1..], value);
                }
            }
            Value::List(list) => {
                if let Value::Int(i) = key {
                    let idx = if *i < 0 {
                        (list.len() as i64 + i) as usize
                    } else {
                        *i as usize
                    };
                    if idx < list.len() {
                        if path.len() == 1 {
                            list[idx] = value;
                        } else {
                            write_nested(&mut list[idx], &path[1..], value);
                        }
                    }
                }
            }
            _ => {}
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::DurationValue;

    // ── GameState: add entity, read fields ─────────────────────

    #[test]
    fn add_entity_and_read_fields() {
        let mut state = GameState::new();
        let mut fields = HashMap::new();
        fields.insert("HP".into(), Value::Int(30));
        fields.insert("AC".into(), Value::Int(15));
        let entity = state.add_entity("Fighter", fields);

        assert_eq!(state.read_field(&entity, "HP"), Some(Value::Int(30)));
        assert_eq!(state.read_field(&entity, "AC"), Some(Value::Int(15)));
        assert_eq!(state.read_field(&entity, "STR"), None);
    }

    #[test]
    fn read_field_nonexistent_entity() {
        let state = GameState::new();
        assert_eq!(state.read_field(&EntityRef(999), "HP"), None);
    }

    // ── GameState: write field, read back ──────────────────────

    #[test]
    fn write_field_simple() {
        let mut state = GameState::new();
        let mut fields = HashMap::new();
        fields.insert("HP".into(), Value::Int(30));
        let entity = state.add_entity("Fighter", fields);

        state.write_field(
            &entity,
            &[FieldPathSegment::Field("HP".into())],
            Value::Int(20),
        );
        assert_eq!(state.read_field(&entity, "HP"), Some(Value::Int(20)));
    }

    #[test]
    fn write_field_nested_map() {
        let mut state = GameState::new();
        let mut stats = BTreeMap::new();
        stats.insert(Value::Str("STR".into()), Value::Int(16));
        stats.insert(Value::Str("DEX".into()), Value::Int(14));

        let mut fields = HashMap::new();
        fields.insert("stats".into(), Value::Map(stats));
        let entity = state.add_entity("Fighter", fields);

        state.write_field(
            &entity,
            &[
                FieldPathSegment::Field("stats".into()),
                FieldPathSegment::Index(Value::Str("STR".into())),
            ],
            Value::Int(18),
        );

        let stats = state.read_field(&entity, "stats").unwrap();
        if let Value::Map(m) = stats {
            assert_eq!(m.get(&Value::Str("STR".into())), Some(&Value::Int(18)));
            assert_eq!(m.get(&Value::Str("DEX".into())), Some(&Value::Int(14)));
        } else {
            panic!("expected Map");
        }
    }

    // ── GameState: condition add/remove/query ──────────────────

    #[test]
    fn condition_add_and_query() {
        let mut state = GameState::new();
        let entity = state.add_entity("Fighter", HashMap::new());

        state.apply_condition(
            &entity,
            "Prone",
            Value::Duration(DurationValue::EndOfTurn),
        );

        let conds = state.read_conditions(&entity).unwrap();
        assert_eq!(conds.len(), 1);
        assert_eq!(conds[0].name, "Prone");
        assert_eq!(conds[0].bearer, entity);
        assert!(conds[0].id > 0);
    }

    #[test]
    fn condition_remove() {
        let mut state = GameState::new();
        let entity = state.add_entity("Fighter", HashMap::new());

        state.apply_condition(
            &entity,
            "Prone",
            Value::Duration(DurationValue::EndOfTurn),
        );
        state.apply_condition(
            &entity,
            "Stunned",
            Value::Duration(DurationValue::Rounds(1)),
        );

        state.remove_condition(&entity, "Prone");

        let conds = state.read_conditions(&entity).unwrap();
        assert_eq!(conds.len(), 1);
        assert_eq!(conds[0].name, "Stunned");
    }

    #[test]
    fn conditions_empty_for_new_entity() {
        let mut state = GameState::new();
        let entity = state.add_entity("Fighter", HashMap::new());
        let conds = state.read_conditions(&entity).unwrap();
        assert!(conds.is_empty());
    }

    #[test]
    fn conditions_none_for_nonexistent_entity() {
        let state = GameState::new();
        assert!(state.read_conditions(&EntityRef(999)).is_none());
    }

    // ── GameState: turn budget set/read/write ──────────────────

    #[test]
    fn turn_budget_set_and_read() {
        let mut state = GameState::new();
        let entity = state.add_entity("Fighter", HashMap::new());

        let mut budget = BTreeMap::new();
        budget.insert("actions".into(), Value::Int(1));
        budget.insert("bonus_actions".into(), Value::Int(1));
        state.set_turn_budget(&entity, budget);

        let read = state.read_turn_budget(&entity).unwrap();
        assert_eq!(read.get("actions"), Some(&Value::Int(1)));
        assert_eq!(read.get("bonus_actions"), Some(&Value::Int(1)));
    }

    #[test]
    fn turn_budget_write_field() {
        let mut state = GameState::new();
        let entity = state.add_entity("Fighter", HashMap::new());

        let mut budget = BTreeMap::new();
        budget.insert("actions".into(), Value::Int(1));
        state.set_turn_budget(&entity, budget);

        state.write_turn_field(&entity, "actions", Value::Int(0));

        let read = state.read_turn_budget(&entity).unwrap();
        assert_eq!(read.get("actions"), Some(&Value::Int(0)));
    }

    #[test]
    fn turn_budget_none_for_no_budget() {
        let mut state = GameState::new();
        let entity = state.add_entity("Fighter", HashMap::new());
        assert!(state.read_turn_budget(&entity).is_none());
    }

    // ── GameState: option enable/disable/query ─────────────────

    #[test]
    fn option_enable_and_query() {
        let mut state = GameState::new();
        state.enable_option("flanking");
        state.enable_option("critical_fumbles");

        let opts = state.read_enabled_options();
        assert_eq!(opts.len(), 2);
        assert!(opts.contains(&"flanking".to_string()));
        assert!(opts.contains(&"critical_fumbles".to_string()));
    }

    #[test]
    fn option_disable() {
        let mut state = GameState::new();
        state.enable_option("flanking");
        state.enable_option("critical_fumbles");

        state.disable_option("flanking");

        let opts = state.read_enabled_options();
        assert_eq!(opts.len(), 1);
        assert!(opts.contains(&"critical_fumbles".to_string()));
    }

    // ── GameState: position equality and Chebyshev distance ────

    #[test]
    fn position_equality_same_coords() {
        let state = GameState::new();
        let p1 = GridPosition(3, 4).to_value();
        let p2 = GridPosition(3, 4).to_value();
        assert!(state.position_eq(&p1, &p2));
    }

    #[test]
    fn position_equality_different_coords() {
        let state = GameState::new();
        let p1 = GridPosition(3, 4).to_value();
        let p2 = GridPosition(5, 4).to_value();
        assert!(!state.position_eq(&p1, &p2));
    }

    #[test]
    fn position_equality_non_position_values() {
        let state = GameState::new();
        assert!(!state.position_eq(&Value::Int(1), &Value::Int(1)));
    }

    #[test]
    fn chebyshev_distance_orthogonal() {
        let state = GameState::new();
        let p1 = GridPosition(0, 0).to_value();
        let p2 = GridPosition(3, 0).to_value();
        assert_eq!(state.distance(&p1, &p2), Some(3));
    }

    #[test]
    fn chebyshev_distance_diagonal() {
        let state = GameState::new();
        let p1 = GridPosition(0, 0).to_value();
        let p2 = GridPosition(3, 4).to_value();
        // max(3, 4) = 4
        assert_eq!(state.distance(&p1, &p2), Some(4));
    }

    #[test]
    fn chebyshev_distance_same_point() {
        let state = GameState::new();
        let p1 = GridPosition(5, 5).to_value();
        let p2 = GridPosition(5, 5).to_value();
        assert_eq!(state.distance(&p1, &p2), Some(0));
    }

    #[test]
    fn chebyshev_distance_negative_coords() {
        let state = GameState::new();
        let p1 = GridPosition(-2, -3).to_value();
        let p2 = GridPosition(1, 2).to_value();
        // max(|3|, |5|) = 5
        assert_eq!(state.distance(&p1, &p2), Some(5));
    }

    #[test]
    fn distance_non_position_values() {
        let state = GameState::new();
        assert_eq!(state.distance(&Value::Int(1), &Value::Int(2)), None);
    }

    // ── GameState: entity ids are unique ───────────────────────

    #[test]
    fn entity_ids_are_unique() {
        let mut state = GameState::new();
        let e1 = state.add_entity("A", HashMap::new());
        let e2 = state.add_entity("B", HashMap::new());
        assert_ne!(e1, e2);
    }

    // ── GameState: condition via WritableState (adapter path) ──

    #[test]
    fn writable_state_add_condition_auto_assigns_id() {
        let mut state = GameState::new();
        let entity = state.add_entity("Fighter", HashMap::new());

        // Simulate adapter-created condition (id = 0)
        let cond = ActiveCondition {
            id: 0,
            name: "Prone".into(),
            bearer: entity,
            gained_at: 0,
            duration: Value::Duration(DurationValue::EndOfTurn),
        };
        state.add_condition(&entity, cond);

        let conds = state.read_conditions(&entity).unwrap();
        assert_eq!(conds.len(), 1);
        assert!(conds[0].id > 0); // Auto-assigned
    }

    // ── GameState: write_field creates new fields ──────────────

    #[test]
    fn write_field_creates_new_field() {
        let mut state = GameState::new();
        let entity = state.add_entity("Fighter", HashMap::new());

        state.write_field(
            &entity,
            &[FieldPathSegment::Field("HP".into())],
            Value::Int(30),
        );
        assert_eq!(state.read_field(&entity, "HP"), Some(Value::Int(30)));
    }

    // ── Distance: extreme coordinates don't panic ────────────

    #[test]
    fn distance_extreme_coordinates_no_panic() {
        let state = GameState::new();
        let p1 = GridPosition(i64::MIN, 0).to_value();
        let p2 = GridPosition(i64::MAX, 0).to_value();
        // Should not panic; saturating arithmetic clamps the result
        let d = state.distance(&p1, &p2);
        assert!(d.is_some());
        assert!(d.unwrap() > 0);
    }

    #[test]
    fn distance_i64_min_abs_no_panic() {
        let state = GameState::new();
        let p1 = GridPosition(i64::MIN, i64::MIN).to_value();
        let p2 = GridPosition(0, 0).to_value();
        let d = state.distance(&p1, &p2);
        assert!(d.is_some());
    }

    // ── Orphan data: writes to nonexistent entities are rejected ─

    #[test]
    fn set_turn_budget_nonexistent_entity_noop() {
        let mut state = GameState::new();
        let ghost = EntityRef(999);
        let mut budget = BTreeMap::new();
        budget.insert("actions".into(), Value::Int(1));
        state.set_turn_budget(&ghost, budget);
        // No orphan data: read returns None
        assert!(state.read_turn_budget(&ghost).is_none());
    }

    #[test]
    fn apply_condition_nonexistent_entity_noop() {
        let mut state = GameState::new();
        let ghost = EntityRef(999);
        state.apply_condition(
            &ghost,
            "Prone",
            Value::Duration(DurationValue::EndOfTurn),
        );
        assert!(state.read_conditions(&ghost).is_none());
    }

    // ── GameState: remove_entity ──────────────────────────────

    #[test]
    fn remove_entity_cleans_all_maps() {
        let mut state = GameState::new();
        let mut fields = HashMap::new();
        fields.insert("HP".into(), Value::Int(30));
        let entity = state.add_entity("Fighter", fields);

        state.apply_condition(
            &entity,
            "Prone",
            Value::Duration(DurationValue::EndOfTurn),
        );
        let mut budget = BTreeMap::new();
        budget.insert("actions".into(), Value::Int(1));
        state.set_turn_budget(&entity, budget);

        assert!(state.remove_entity(&entity));

        // All reads should return None
        assert_eq!(state.read_field(&entity, "HP"), None);
        assert!(state.read_conditions(&entity).is_none());
        assert!(state.read_turn_budget(&entity).is_none());
    }

    #[test]
    fn remove_entity_nonexistent_returns_false() {
        let mut state = GameState::new();
        assert!(!state.remove_entity(&EntityRef(999)));
    }

    #[test]
    fn add_condition_nonexistent_entity_noop() {
        let mut state = GameState::new();
        let ghost = EntityRef(999);
        let cond = ActiveCondition {
            id: 0,
            name: "Prone".into(),
            bearer: ghost,
            gained_at: 0,
            duration: Value::Duration(DurationValue::EndOfTurn),
        };
        state.add_condition(&ghost, cond);
        assert!(state.read_conditions(&ghost).is_none());
    }
}
