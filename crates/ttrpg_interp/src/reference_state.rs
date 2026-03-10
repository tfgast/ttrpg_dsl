use std::collections::{BTreeMap, HashMap, HashSet};

use rustc_hash::FxHashMap;
use ttrpg_ast::Name;

use crate::effect::FieldPathSegment;
use crate::state::{
    ActiveCondition, ConditionArgs, ConditionToken, EntityRef, InvocationId, Presence,
    StateProvider, SuspensionRecord, WritableState,
};
use crate::value::{DirectionValue, PositionValue, Value};

// ── Grid position ──────────────────────────────────────────────

/// A simple 2D grid position used by `GameState`.
///
/// Chebyshev distance (`max(|dx|, |dy|)`) matches D&D 5e's standard
/// movement rules where diagonal movement costs the same as orthogonal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GridPosition(pub i64, pub i64);

// ── EntityState ────────────────────────────────────────────────

struct EntityState {
    name: Name,
    fields: FxHashMap<Name, Value>,
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
    turn_budgets: HashMap<u64, BTreeMap<Name, Value>>,
    enabled_options: HashSet<Name>,
    next_entity_id: u64,
    next_condition_id: u64,
    next_invocation_id: u64,
    game_time: u64,
    /// Maps opaque position handles to grid coordinates.
    positions: HashMap<u64, GridPosition>,
    next_position_id: u64,
    /// Maps opaque direction handles to (from, to) grid coordinate pairs.
    directions: HashMap<u64, (GridPosition, GridPosition)>,
    next_direction_id: u64,
    /// Suspension records per entity. Multiple sources can suspend one entity.
    suspensions: HashMap<u64, Vec<SuspensionRecord>>,
    /// Game time when duration-freezing started, per entity.
    /// Set when the first `freeze_durations` record is added, cleared on last removal.
    duration_freeze_start: HashMap<u64, u64>,
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
            next_invocation_id: 1,
            game_time: 0,
            suspensions: HashMap::new(),
            duration_freeze_start: HashMap::new(),
            positions: HashMap::new(),
            next_position_id: 1,
            directions: HashMap::new(),
            next_direction_id: 1,
        }
    }

    /// Register a grid position and return its opaque handle as a `Value::Position`.
    pub fn register_position(&mut self, pos: GridPosition) -> Value {
        let handle = self.next_position_id;
        self.next_position_id += 1;
        self.positions.insert(handle, pos);
        Value::Position(PositionValue(handle))
    }

    /// Resolve an opaque handle back to its `GridPosition`, if known.
    pub fn resolve_position(&self, handle: u64) -> Option<GridPosition> {
        self.positions.get(&handle).copied()
    }

    /// Register a direction and return its opaque handle as a `Value::Direction`.
    pub fn register_direction(&mut self, from: GridPosition, to: GridPosition) -> Value {
        let handle = self.next_direction_id;
        self.next_direction_id += 1;
        self.directions.insert(handle, (from, to));
        Value::Direction(DirectionValue(handle))
    }

    /// Resolve an opaque direction handle back to its (from, to) pair, if known.
    pub fn resolve_direction(&self, handle: u64) -> Option<(GridPosition, GridPosition)> {
        self.directions.get(&handle).copied()
    }

    /// Add a new entity with the given name and fields.
    /// Returns a reference to the new entity.
    pub fn add_entity(&mut self, name: &str, fields: FxHashMap<Name, Value>) -> EntityRef {
        let id = self.next_entity_id;
        self.next_entity_id += 1;
        self.entities.insert(
            id,
            EntityState {
                name: Name::from(name),
                fields,
            },
        );
        EntityRef(id)
    }

    /// Set the turn budget for an entity.
    ///
    /// Silently does nothing if the entity doesn't exist, consistent
    /// with read paths that reject unknown entities.
    pub fn set_turn_budget(&mut self, entity: &EntityRef, budget: BTreeMap<Name, Value>) {
        if !self.entities.contains_key(&entity.0) {
            return;
        }
        self.turn_budgets.insert(entity.0, budget);
    }

    /// Apply a condition to an entity with auto-assigned id and timestamp.
    ///
    /// Silently does nothing if the entity doesn't exist, consistent
    /// with read paths that reject unknown entities.
    /// Get the current invocation id counter.
    pub fn next_invocation_id(&self) -> u64 {
        self.next_invocation_id
    }

    /// Set the invocation id counter (for persistence round-trips).
    pub fn set_next_invocation_id(&mut self, id: u64) {
        self.next_invocation_id = id;
    }

    pub fn apply_condition(&mut self, entity: &EntityRef, name: &str, args: ConditionArgs) {
        if !self.entities.contains_key(&entity.0) {
            return;
        }
        let id = self.next_condition_id;
        self.next_condition_id += 1;
        let applied_at = self.game_time;
        let cond = ActiveCondition {
            id,
            name: Name::from(name),
            params: args.params,
            bearer: *entity,
            gained_at: id, // Use id as ordering timestamp for simplicity
            duration: args.duration,
            invocation: args.invocation,
            applied_at,
            source: args.source,
            tags: args.tags,
        };
        self.conditions.entry(entity.0).or_default().push(cond);
    }

    /// Get the type name (as passed to `add_entity`) for an entity.
    pub fn entity_type_name(&self, entity: &EntityRef) -> Option<&Name> {
        self.entities.get(&entity.0).map(|e| &e.name)
    }

    /// Remove an entity and all associated data (conditions, turn budgets, suspensions).
    /// Returns `true` if the entity existed and was removed.
    pub fn remove_entity(&mut self, entity: &EntityRef) -> bool {
        let existed = self.entities.remove(&entity.0).is_some();
        if existed {
            self.conditions.remove(&entity.0);
            self.turn_budgets.remove(&entity.0);
            self.suspensions.remove(&entity.0);
            self.duration_freeze_start.remove(&entity.0);
        }
        existed
    }

    /// Enable an option by name.
    pub fn enable_option(&mut self, name: &str) {
        self.enabled_options.insert(Name::from(name));
    }

    /// Disable an option by name.
    pub fn disable_option(&mut self, name: &str) {
        self.enabled_options.remove(name);
    }

    /// Get the current game time counter.
    pub fn game_time(&self) -> u64 {
        self.game_time
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
        self.entities.get(&entity.0)?.fields.get(field).cloned()
    }

    fn read_conditions(&self, entity: &EntityRef) -> Option<Vec<ActiveCondition>> {
        if !self.entities.contains_key(&entity.0) {
            return None;
        }
        Some(self.conditions.get(&entity.0).cloned().unwrap_or_default())
    }

    fn read_turn_budget(&self, entity: &EntityRef) -> Option<BTreeMap<Name, Value>> {
        if !self.entities.contains_key(&entity.0) {
            return None;
        }
        self.turn_budgets.get(&entity.0).cloned()
    }

    fn read_enabled_options(&self) -> Vec<Name> {
        let mut opts: Vec<Name> = self.enabled_options.iter().cloned().collect();
        opts.sort();
        opts
    }

    fn position_eq(&self, a: u64, b: u64) -> bool {
        match (self.positions.get(&a), self.positions.get(&b)) {
            (Some(a), Some(b)) => a == b,
            _ => false,
        }
    }

    fn direction_eq(&self, a: u64, b: u64) -> bool {
        match (self.directions.get(&a), self.directions.get(&b)) {
            (Some(a), Some(b)) => a == b,
            _ => false,
        }
    }

    fn distance(&self, a: u64, b: u64) -> Option<i64> {
        let a_grid = self.positions.get(&a)?;
        let b_grid = self.positions.get(&b)?;
        // Chebyshev distance: max(|dx|, |dy|)
        // Use saturating arithmetic to avoid overflow/panic on extreme coordinates.
        let dx = a_grid.0.saturating_sub(b_grid.0).saturating_abs();
        let dy = a_grid.1.saturating_sub(b_grid.1).saturating_abs();
        Some(dx.max(dy))
    }

    fn read_game_time(&self) -> u64 {
        self.game_time
    }

    fn entity_type_name(&self, entity: &EntityRef) -> Option<Name> {
        self.entities.get(&entity.0).map(|e| e.name.clone())
    }

    fn all_entities(&self) -> Vec<EntityRef> {
        self.entities.keys().map(|&id| EntityRef(id)).collect()
    }

    fn resolve_position(&self, handle: u64) -> Option<(i64, i64)> {
        let gp = self.positions.get(&handle)?;
        Some((gp.0, gp.1))
    }

    fn entities_in_play(&self) -> Vec<EntityRef> {
        self.entities
            .keys()
            .filter(|id| {
                !self
                    .suspensions
                    .get(id)
                    .is_some_and(|recs| recs.iter().any(|r| r.presence == Presence::OffBoard))
            })
            .map(|&id| EntityRef(id))
            .collect()
    }

    fn is_suspended(&self, entity: &EntityRef) -> bool {
        self.suspensions
            .get(&entity.0)
            .is_some_and(|recs| !recs.is_empty())
    }

    fn is_off_board(&self, entity: &EntityRef) -> bool {
        self.suspensions
            .get(&entity.0)
            .is_some_and(|recs| recs.iter().any(|r| r.presence == Presence::OffBoard))
    }

    fn are_turns_frozen(&self, entity: &EntityRef) -> bool {
        self.suspensions
            .get(&entity.0)
            .is_some_and(|recs| recs.iter().any(|r| r.freeze_turns))
    }

    fn are_durations_frozen(&self, entity: &EntityRef) -> bool {
        self.duration_freeze_start.contains_key(&entity.0)
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
        } else {
            // Keep counter above any externally-assigned id.
            if cond.id >= self.next_condition_id {
                self.next_condition_id = cond.id.saturating_add(1);
            }
        }
        self.conditions.entry(entity.0).or_default().push(cond);
    }

    fn remove_condition(
        &mut self,
        entity: &EntityRef,
        name: &str,
        params: Option<&BTreeMap<Name, Value>>,
    ) {
        if let Some(conds) = self.conditions.get_mut(&entity.0) {
            conds.retain(|c| {
                if c.name != name {
                    return true; // different condition, keep
                }
                match params {
                    None => false,             // remove all with this name
                    Some(p) => &c.params != p, // keep if params don't match
                }
            });
        }
    }

    fn remove_condition_by_id(&mut self, entity: &EntityRef, id: u64) {
        if let Some(conds) = self.conditions.get_mut(&entity.0) {
            conds.retain(|c| c.id != id);
        }
    }

    fn write_turn_field(&mut self, entity: &EntityRef, field: &str, value: Value) {
        if !self.entities.contains_key(&entity.0) {
            return;
        }
        self.turn_budgets
            .entry(entity.0)
            .or_default()
            .insert(Name::from(field), value);
    }

    fn remove_field(&mut self, entity: &EntityRef, field: &str) {
        if let Some(entity_state) = self.entities.get_mut(&entity.0) {
            entity_state.fields.remove(field);
        }
    }

    fn remove_conditions_by_invocation(&mut self, invocation: InvocationId) {
        for conds in self.conditions.values_mut() {
            conds.retain(|c| c.invocation != Some(invocation));
        }
    }

    fn set_turn_budget(&mut self, entity: &EntityRef, budget: BTreeMap<Name, Value>) {
        if !self.entities.contains_key(&entity.0) {
            return;
        }
        self.turn_budgets.insert(entity.0, budget);
    }

    fn clear_turn_budget(&mut self, entity: &EntityRef) {
        self.turn_budgets.remove(&entity.0);
    }

    fn set_game_time(&mut self, time: u64) {
        self.game_time = time;
    }

    fn add_entity(
        &mut self,
        type_name: &str,
        fields: rustc_hash::FxHashMap<Name, Value>,
    ) -> EntityRef {
        // Delegate to the inherent method
        GameState::add_entity(self, type_name, fields)
    }

    fn remove_entity(&mut self, entity: &EntityRef) {
        // Delegate to the inherent method
        GameState::remove_entity(self, entity);
    }

    fn allocate_condition_id(&mut self) -> ConditionToken {
        let id = self.next_condition_id;
        self.next_condition_id = id.saturating_add(1);
        ConditionToken(id)
    }

    fn add_suspension(&mut self, entity: &EntityRef, record: SuspensionRecord) {
        if !self.entities.contains_key(&entity.0) {
            return;
        }
        // If this is the first freeze_durations record, record the freeze start time
        if record.freeze_durations && !self.duration_freeze_start.contains_key(&entity.0) {
            self.duration_freeze_start.insert(entity.0, self.game_time);
        }
        self.suspensions.entry(entity.0).or_default().push(record);
    }

    fn remove_suspension_source(&mut self, entity: &EntityRef, source_id: u64) {
        let Some(records) = self.suspensions.get_mut(&entity.0) else {
            return;
        };

        // Check if we're about to lose the last freeze_durations record
        let had_freeze = records.iter().any(|r| r.freeze_durations);

        records.retain(|r| r.source_id != source_id);

        let still_has_freeze = records.iter().any(|r| r.freeze_durations);

        // If durations were frozen and this removal ends that, bump applied_at
        if had_freeze && !still_has_freeze {
            if let Some(freeze_start) = self.duration_freeze_start.remove(&entity.0) {
                let now = self.game_time;
                if let Some(conds) = self.conditions.get_mut(&entity.0) {
                    for cond in conds.iter_mut() {
                        // Per-condition rule: applied_at += now - max(applied_at, freeze_start)
                        let effective_start = cond.applied_at.max(freeze_start);
                        if now > effective_start {
                            cond.applied_at += now - effective_start;
                        }
                    }
                }
            }
        }

        // Clean up empty records
        if records.is_empty() {
            self.suspensions.remove(&entity.0);
        }
    }

    fn suspension_records(&self, entity: &EntityRef) -> Vec<SuspensionRecord> {
        self.suspensions.get(&entity.0).cloned().unwrap_or_default()
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
    use crate::value::{duration_variant, effect_source_unknown};
    use std::collections::BTreeSet;

    // ── GameState: add entity, read fields ─────────────────────

    #[test]
    fn add_entity_and_read_fields() {
        let mut state = GameState::new();
        let mut fields = FxHashMap::default();
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
        let mut fields = FxHashMap::default();
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

        let mut fields = FxHashMap::default();
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
        let entity = state.add_entity("Fighter", FxHashMap::default());

        state.apply_condition(
            &entity,
            "Prone",
            ConditionArgs {
                duration: duration_variant("EndOfTurn"),
                ..Default::default()
            },
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
        let entity = state.add_entity("Fighter", FxHashMap::default());

        state.apply_condition(
            &entity,
            "Prone",
            ConditionArgs {
                duration: duration_variant("EndOfTurn"),
                ..Default::default()
            },
        );
        state.apply_condition(
            &entity,
            "Stunned",
            ConditionArgs {
                duration: duration_variant("Rounds"),
                ..Default::default()
            },
        );

        state.remove_condition(&entity, "Prone", None);

        let conds = state.read_conditions(&entity).unwrap();
        assert_eq!(conds.len(), 1);
        assert_eq!(conds[0].name, "Stunned");
    }

    #[test]
    fn condition_remove_by_id() {
        let mut state = GameState::new();
        let entity = state.add_entity("Fighter", FxHashMap::default());

        state.apply_condition(
            &entity,
            "Prone",
            ConditionArgs {
                duration: duration_variant("EndOfTurn"),
                ..Default::default()
            },
        );
        state.apply_condition(
            &entity,
            "Prone",
            ConditionArgs {
                duration: duration_variant("Rounds"),
                ..Default::default()
            },
        );

        let conds = state.read_conditions(&entity).unwrap();
        assert_eq!(conds.len(), 2);
        let first_id = conds[0].id;
        let second_id = conds[1].id;
        assert_ne!(first_id, second_id);

        // Remove only the first instance by id
        state.remove_condition_by_id(&entity, first_id);

        let conds = state.read_conditions(&entity).unwrap();
        assert_eq!(conds.len(), 1);
        assert_eq!(conds[0].id, second_id);
    }

    #[test]
    fn conditions_empty_for_new_entity() {
        let mut state = GameState::new();
        let entity = state.add_entity("Fighter", FxHashMap::default());
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
        let entity = state.add_entity("Fighter", FxHashMap::default());

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
        let entity = state.add_entity("Fighter", FxHashMap::default());

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
        let entity = state.add_entity("Fighter", FxHashMap::default());
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
        assert!(opts.contains(&Name::from("flanking")));
        assert!(opts.contains(&Name::from("critical_fumbles")));
    }

    #[test]
    fn option_disable() {
        let mut state = GameState::new();
        state.enable_option("flanking");
        state.enable_option("critical_fumbles");

        state.disable_option("flanking");

        let opts = state.read_enabled_options();
        assert_eq!(opts.len(), 1);
        assert!(opts.contains(&Name::from("critical_fumbles")));
    }

    #[test]
    fn read_enabled_options_returns_sorted() {
        let mut state = GameState::new();
        state.enable_option("flanking");
        state.enable_option("critical_fumbles");
        state.enable_option("advanced_cover");

        let opts = state.read_enabled_options();
        assert_eq!(
            opts,
            vec![
                Name::from("advanced_cover"),
                Name::from("critical_fumbles"),
                Name::from("flanking")
            ]
        );
    }

    // ── GameState: position equality and Chebyshev distance ────

    /// Extract the opaque handle from a `Value::Position`.
    fn pos_handle(v: &Value) -> u64 {
        match v {
            Value::Position(pv) => pv.0,
            _ => panic!("expected Position value"),
        }
    }

    #[test]
    fn position_equality_same_coords() {
        let mut state = GameState::new();
        let p1 = state.register_position(GridPosition(3, 4));
        let p2 = state.register_position(GridPosition(3, 4));
        assert!(state.position_eq(pos_handle(&p1), pos_handle(&p2)));
    }

    #[test]
    fn position_equality_different_coords() {
        let mut state = GameState::new();
        let p1 = state.register_position(GridPosition(3, 4));
        let p2 = state.register_position(GridPosition(5, 4));
        assert!(!state.position_eq(pos_handle(&p1), pos_handle(&p2)));
    }

    #[test]
    fn position_equality_unknown_handles() {
        let state = GameState::new();
        // Unknown handles should not be equal
        assert!(!state.position_eq(999, 1000));
    }

    #[test]
    fn chebyshev_distance_orthogonal() {
        let mut state = GameState::new();
        let p1 = state.register_position(GridPosition(0, 0));
        let p2 = state.register_position(GridPosition(3, 0));
        assert_eq!(state.distance(pos_handle(&p1), pos_handle(&p2)), Some(3));
    }

    #[test]
    fn chebyshev_distance_diagonal() {
        let mut state = GameState::new();
        let p1 = state.register_position(GridPosition(0, 0));
        let p2 = state.register_position(GridPosition(3, 4));
        // max(3, 4) = 4
        assert_eq!(state.distance(pos_handle(&p1), pos_handle(&p2)), Some(4));
    }

    #[test]
    fn chebyshev_distance_same_point() {
        let mut state = GameState::new();
        let p1 = state.register_position(GridPosition(5, 5));
        let p2 = state.register_position(GridPosition(5, 5));
        assert_eq!(state.distance(pos_handle(&p1), pos_handle(&p2)), Some(0));
    }

    #[test]
    fn chebyshev_distance_negative_coords() {
        let mut state = GameState::new();
        let p1 = state.register_position(GridPosition(-2, -3));
        let p2 = state.register_position(GridPosition(1, 2));
        // max(|3|, |5|) = 5
        assert_eq!(state.distance(pos_handle(&p1), pos_handle(&p2)), Some(5));
    }

    #[test]
    fn distance_unknown_handles() {
        let state = GameState::new();
        assert_eq!(state.distance(999, 1000), None);
    }

    // ── GameState: entity ids are unique ───────────────────────

    #[test]
    fn entity_ids_are_unique() {
        let mut state = GameState::new();
        let e1 = state.add_entity("A", FxHashMap::default());
        let e2 = state.add_entity("B", FxHashMap::default());
        assert_ne!(e1, e2);
    }

    // ── GameState: condition via WritableState (adapter path) ──

    #[test]
    fn writable_state_add_condition_auto_assigns_id() {
        let mut state = GameState::new();
        let entity = state.add_entity("Fighter", FxHashMap::default());

        // Simulate adapter-created condition (id = 0)
        let cond = ActiveCondition {
            id: 0,
            name: "Prone".into(),
            params: BTreeMap::new(),
            bearer: entity,
            gained_at: 0,
            duration: duration_variant("EndOfTurn"),
            invocation: None,
            applied_at: 0,
            source: effect_source_unknown(),
            tags: BTreeSet::new(),
        };
        state.add_condition(&entity, cond);

        let conds = state.read_conditions(&entity).unwrap();
        assert_eq!(conds.len(), 1);
        assert!(conds[0].id > 0); // Auto-assigned
    }

    #[test]
    fn add_condition_preassigned_id_bumps_counter() {
        let mut state = GameState::new();
        let entity = state.add_entity("Fighter", FxHashMap::default());

        // Simulate externally-assigned condition with id = 50
        let cond = ActiveCondition {
            id: 50,
            name: "Prone".into(),
            params: BTreeMap::new(),
            bearer: entity,
            gained_at: 50,
            duration: duration_variant("EndOfTurn"),
            invocation: None,
            applied_at: 0,
            source: effect_source_unknown(),
            tags: BTreeSet::new(),
        };
        state.add_condition(&entity, cond);

        // Now add a condition with auto-assigned id (id = 0)
        let cond2 = ActiveCondition {
            id: 0,
            name: "Stunned".into(),
            params: BTreeMap::new(),
            bearer: entity,
            gained_at: 0,
            duration: duration_variant("Rounds"),
            invocation: None,
            applied_at: 0,
            source: effect_source_unknown(),
            tags: BTreeSet::new(),
        };
        state.add_condition(&entity, cond2);

        let conds = state.read_conditions(&entity).unwrap();
        assert_eq!(conds.len(), 2);
        assert_eq!(conds[0].id, 50);
        // Auto-assigned id must be > 50, not collide
        assert!(conds[1].id > 50);
    }

    // ── GameState: write_field creates new fields ──────────────

    #[test]
    fn write_field_creates_new_field() {
        let mut state = GameState::new();
        let entity = state.add_entity("Fighter", FxHashMap::default());

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
        let mut state = GameState::new();
        let p1 = state.register_position(GridPosition(i64::MIN, 0));
        let p2 = state.register_position(GridPosition(i64::MAX, 0));
        // Should not panic; saturating arithmetic clamps the result
        let d = state.distance(pos_handle(&p1), pos_handle(&p2));
        assert!(d.is_some());
        assert!(d.unwrap() > 0);
    }

    #[test]
    fn distance_i64_min_abs_no_panic() {
        let mut state = GameState::new();
        let p1 = state.register_position(GridPosition(i64::MIN, i64::MIN));
        let p2 = state.register_position(GridPosition(0, 0));
        let d = state.distance(pos_handle(&p1), pos_handle(&p2));
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
            ConditionArgs {
                duration: duration_variant("EndOfTurn"),
                ..Default::default()
            },
        );
        assert!(state.read_conditions(&ghost).is_none());
    }

    // ── GameState: remove_entity ──────────────────────────────

    #[test]
    fn remove_entity_cleans_all_maps() {
        let mut state = GameState::new();
        let mut fields = FxHashMap::default();
        fields.insert("HP".into(), Value::Int(30));
        let entity = state.add_entity("Fighter", fields);

        state.apply_condition(
            &entity,
            "Prone",
            ConditionArgs {
                duration: duration_variant("EndOfTurn"),
                ..Default::default()
            },
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
            params: BTreeMap::new(),
            bearer: ghost,
            gained_at: 0,
            duration: duration_variant("EndOfTurn"),
            invocation: None,
            applied_at: 0,
            source: effect_source_unknown(),
            tags: BTreeSet::new(),
        };
        state.add_condition(&ghost, cond);
        assert!(state.read_conditions(&ghost).is_none());
    }

    // ── GameState: remove_field ──────────────────────────────

    #[test]
    fn remove_field_removes_existing() {
        let mut state = GameState::new();
        let mut fields = FxHashMap::default();
        fields.insert("HP".into(), Value::Int(30));
        fields.insert(
            "Spellcasting".into(),
            Value::Struct {
                name: "Spellcasting".into(),
                fields: {
                    let mut f = BTreeMap::new();
                    f.insert("spell_slots".into(), Value::Int(3));
                    f
                },
            },
        );
        let entity = state.add_entity("Character", fields);

        state.remove_field(&entity, "Spellcasting");

        assert_eq!(state.read_field(&entity, "Spellcasting"), None);
        // Other fields are untouched
        assert_eq!(state.read_field(&entity, "HP"), Some(Value::Int(30)));
    }

    #[test]
    fn remove_field_nonexistent_field_noop() {
        let mut state = GameState::new();
        let entity = state.add_entity("Character", FxHashMap::default());
        // Should not panic
        state.remove_field(&entity, "DoesNotExist");
        assert_eq!(state.read_field(&entity, "DoesNotExist"), None);
    }

    #[test]
    fn remove_field_nonexistent_entity_noop() {
        let mut state = GameState::new();
        // Should not panic
        state.remove_field(&EntityRef(999), "HP");
    }

    // ── Invocation tracking ─────────────────────────────────────

    #[test]
    fn invocation_round_trip() {
        let mut state = GameState::new();
        let entity = state.add_entity("Fighter", FxHashMap::default());

        state.apply_condition(
            &entity,
            "Blessed",
            ConditionArgs {
                duration: duration_variant("Rounds"),
                invocation: Some(InvocationId(42)),
                ..Default::default()
            },
        );

        let conds = state.read_conditions(&entity).unwrap();
        assert_eq!(conds.len(), 1);
        assert_eq!(conds[0].invocation, Some(InvocationId(42)));
    }

    #[test]
    fn invocation_removal() {
        let mut state = GameState::new();
        let entity = state.add_entity("Fighter", FxHashMap::default());

        // 2 from invocation 1
        state.apply_condition(
            &entity,
            "Blessed",
            ConditionArgs {
                duration: duration_variant("Rounds"),
                invocation: Some(InvocationId(1)),
                ..Default::default()
            },
        );
        state.apply_condition(
            &entity,
            "Shielded",
            ConditionArgs {
                duration: duration_variant("Rounds"),
                invocation: Some(InvocationId(1)),
                ..Default::default()
            },
        );
        // 1 from invocation 2
        state.apply_condition(
            &entity,
            "Hasted",
            ConditionArgs {
                duration: duration_variant("Rounds"),
                invocation: Some(InvocationId(2)),
                ..Default::default()
            },
        );
        // 1 with no invocation
        state.apply_condition(
            &entity,
            "Prone",
            ConditionArgs {
                duration: duration_variant("Indefinite"),
                ..Default::default()
            },
        );

        assert_eq!(state.read_conditions(&entity).unwrap().len(), 4);

        state.remove_conditions_by_invocation(InvocationId(1));

        let conds = state.read_conditions(&entity).unwrap();
        assert_eq!(conds.len(), 2);
        assert_eq!(conds[0].name, "Hasted");
        assert_eq!(conds[1].name, "Prone");
    }

    #[test]
    fn invocation_removal_cross_entity() {
        let mut state = GameState::new();
        let e1 = state.add_entity("Fighter", FxHashMap::default());
        let e2 = state.add_entity("Rogue", FxHashMap::default());
        let e3 = state.add_entity("Wizard", FxHashMap::default());

        let inv = Some(InvocationId(7));
        state.apply_condition(
            &e1,
            "Blessed",
            ConditionArgs {
                duration: duration_variant("Rounds"),
                invocation: inv,
                ..Default::default()
            },
        );
        state.apply_condition(
            &e2,
            "Blessed",
            ConditionArgs {
                duration: duration_variant("Rounds"),
                invocation: inv,
                ..Default::default()
            },
        );
        state.apply_condition(
            &e3,
            "Blessed",
            ConditionArgs {
                duration: duration_variant("Rounds"),
                invocation: inv,
                ..Default::default()
            },
        );

        state.remove_conditions_by_invocation(InvocationId(7));

        assert!(state.read_conditions(&e1).unwrap().is_empty());
        assert!(state.read_conditions(&e2).unwrap().is_empty());
        assert!(state.read_conditions(&e3).unwrap().is_empty());
    }

    #[test]
    fn next_invocation_id_counter() {
        let mut state = GameState::new();
        assert_eq!(state.next_invocation_id(), 1);

        state.set_next_invocation_id(100);
        assert_eq!(state.next_invocation_id(), 100);
    }

    // ── Suspension tests ──────────────────────────────────────────

    #[test]
    fn suspension_basic_add_remove() {
        let mut state = GameState::new();
        let e1 = state.add_entity("Character", FxHashMap::default());

        assert!(!state.is_suspended(&e1));
        assert!(!state.is_off_board(&e1));

        state.add_suspension(
            &e1,
            SuspensionRecord {
                source_id: 100,
                presence: Presence::OffBoard,
                freeze_turns: true,
                freeze_durations: true,
                suspended_at: 0,
            },
        );

        assert!(state.is_suspended(&e1));
        assert!(state.is_off_board(&e1));
        assert!(state.are_turns_frozen(&e1));
        assert!(state.are_durations_frozen(&e1));

        // entities_in_play excludes off-board
        let in_play = state.entities_in_play();
        assert!(!in_play.contains(&e1));

        // all_entities still includes it
        let all = state.all_entities();
        assert!(all.contains(&e1));

        state.remove_suspension_source(&e1, 100);

        assert!(!state.is_suspended(&e1));
        assert!(!state.is_off_board(&e1));
        assert!(state.entities_in_play().contains(&e1));
    }

    #[test]
    fn suspension_on_map_stays_in_play() {
        let mut state = GameState::new();
        let e1 = state.add_entity("Character", FxHashMap::default());

        state.add_suspension(
            &e1,
            SuspensionRecord {
                source_id: 200,
                presence: Presence::OnMap,
                freeze_turns: true,
                freeze_durations: true,
                suspended_at: 0,
            },
        );

        assert!(state.is_suspended(&e1));
        assert!(!state.is_off_board(&e1));
        // OnMap entities stay in entities_in_play
        assert!(state.entities_in_play().contains(&e1));
    }

    #[test]
    fn suspension_worst_case_wins() {
        let mut state = GameState::new();
        let e1 = state.add_entity("Character", FxHashMap::default());

        // First record: on-map, no duration freeze
        state.add_suspension(
            &e1,
            SuspensionRecord {
                source_id: 1,
                presence: Presence::OnMap,
                freeze_turns: false,
                freeze_durations: false,
                suspended_at: 0,
            },
        );

        assert!(!state.is_off_board(&e1));
        assert!(!state.are_turns_frozen(&e1));

        // Second record: off-board, freeze turns
        state.add_suspension(
            &e1,
            SuspensionRecord {
                source_id: 2,
                presence: Presence::OffBoard,
                freeze_turns: true,
                freeze_durations: true,
                suspended_at: 0,
            },
        );

        // Worst-case-wins: off-board and frozen
        assert!(state.is_off_board(&e1));
        assert!(state.are_turns_frozen(&e1));
        assert!(state.are_durations_frozen(&e1));
        assert!(!state.entities_in_play().contains(&e1));

        // Remove the OffBoard record
        state.remove_suspension_source(&e1, 2);

        // Back to OnMap, unfrozen
        assert!(!state.is_off_board(&e1));
        assert!(!state.are_turns_frozen(&e1));
        assert!(state.is_suspended(&e1)); // still has record 1
        assert!(state.entities_in_play().contains(&e1));
    }

    #[test]
    fn suspension_duration_freeze_bumps_applied_at() {
        let mut state = GameState::new();
        let e1 = state.add_entity("Character", FxHashMap::default());

        // Apply condition at game_time 5
        state.set_game_time(5);
        state.add_condition(
            &e1,
            ActiveCondition {
                id: 0,
                name: "Stunned".into(),
                params: BTreeMap::new(),
                bearer: e1,
                gained_at: 0,
                duration: Value::Void,
                invocation: None,
                applied_at: 5,
                source: effect_source_unknown(),
                tags: BTreeSet::new(),
            },
        );

        // Suspend at game_time 7 with duration freeze
        state.set_game_time(7);
        state.add_suspension(
            &e1,
            SuspensionRecord {
                source_id: 10,
                presence: Presence::OnMap,
                freeze_turns: true,
                freeze_durations: true,
                suspended_at: 7,
            },
        );

        // Restore at game_time 12
        state.set_game_time(12);
        state.remove_suspension_source(&e1, 10);

        // applied_at should be bumped: 5 + (12 - max(5, 7)) = 5 + 5 = 10
        let conds = state.read_conditions(&e1).unwrap();
        assert_eq!(conds[0].applied_at, 10);
    }

    #[test]
    fn suspension_mid_freeze_condition_applied_at_adjusted_correctly() {
        let mut state = GameState::new();
        let e1 = state.add_entity("Character", FxHashMap::default());

        // Suspend at game_time 5
        state.set_game_time(5);
        state.add_suspension(
            &e1,
            SuspensionRecord {
                source_id: 10,
                presence: Presence::OnMap,
                freeze_turns: true,
                freeze_durations: true,
                suspended_at: 5,
            },
        );

        // Apply condition mid-freeze at game_time 8
        state.set_game_time(8);
        state.add_condition(
            &e1,
            ActiveCondition {
                id: 0,
                name: "Poisoned".into(),
                params: BTreeMap::new(),
                bearer: e1,
                gained_at: 0,
                duration: Value::Void,
                invocation: None,
                applied_at: 8,
                source: effect_source_unknown(),
                tags: BTreeSet::new(),
            },
        );

        // Restore at game_time 12
        state.set_game_time(12);
        state.remove_suspension_source(&e1, 10);

        // applied_at for mid-freeze condition: 8 + (12 - max(8, 5)) = 8 + 4 = 12
        let conds = state.read_conditions(&e1).unwrap();
        assert_eq!(conds[0].applied_at, 12);
    }

    #[test]
    fn suspension_allocate_condition_id() {
        let mut state = GameState::new();
        let t1 = state.allocate_condition_id();
        let t2 = state.allocate_condition_id();
        assert_ne!(t1, t2);
        assert_eq!(t1.0 + 1, t2.0);
    }

    #[test]
    fn remove_entity_cleans_up_suspensions() {
        let mut state = GameState::new();
        let e1 = state.add_entity("Character", FxHashMap::default());

        state.add_suspension(
            &e1,
            SuspensionRecord {
                source_id: 1,
                presence: Presence::OffBoard,
                freeze_turns: true,
                freeze_durations: true,
                suspended_at: 0,
            },
        );

        state.remove_entity(&e1);
        assert!(!state.is_suspended(&e1));
        assert!(state.suspension_records(&e1).is_empty());
    }
}
