//! Bidirectional `String ↔ EntityRef` mapping for human-readable entity names.
//!
//! Every user-facing host needs to map opaque [`EntityRef`]s to friendly names
//! (e.g. "hero", "goblin_1"). `HandleRegistry` provides this utility so hosts
//! don't have to maintain two `HashMap`s in lockstep.

use std::collections::HashMap;

use crate::state::EntityRef;

/// A bidirectional mapping between human-readable handle names and [`EntityRef`]s.
///
/// Both directions are kept in sync automatically — every insert/remove operates
/// on both internal maps atomically.
#[derive(Debug, Clone)]
pub struct HandleRegistry {
    by_name: HashMap<String, EntityRef>,
    by_entity: HashMap<EntityRef, String>,
}

impl HandleRegistry {
    /// Create an empty registry.
    pub fn new() -> Self {
        HandleRegistry {
            by_name: HashMap::new(),
            by_entity: HashMap::new(),
        }
    }

    /// Insert a handle ↔ entity mapping. Returns the previous entity bound to
    /// `name`, if any (and removes the stale reverse entry).
    pub fn insert(&mut self, name: String, entity: EntityRef) -> Option<EntityRef> {
        // Remove any prior reverse mapping for the *new* entity (it might have
        // a different name already).
        if let Some(old_name) = self.by_entity.insert(entity, name.clone())
            && old_name != name
        {
            self.by_name.remove(&old_name);
        }
        // Insert forward mapping and clean up stale reverse entry.
        let prev = self.by_name.insert(name, entity);
        if let Some(prev_entity) = prev
            && prev_entity != entity
        {
            self.by_entity.remove(&prev_entity);
        }
        prev
    }

    /// Look up an entity by handle name.
    pub fn get(&self, name: &str) -> Option<EntityRef> {
        self.by_name.get(name).copied()
    }

    /// Look up the handle name for an entity.
    pub fn name_of(&self, entity: &EntityRef) -> Option<&str> {
        self.by_entity.get(entity).map(|s| s.as_str())
    }

    /// Human-readable display name for an entity. Falls back to `Entity(<id>)`
    /// when the entity has no registered handle.
    pub fn display_name(&self, entity: &EntityRef) -> String {
        self.by_entity
            .get(entity)
            .cloned()
            .unwrap_or_else(|| format!("Entity({})", entity.0))
    }

    /// Returns `true` if `name` is already registered.
    pub fn contains(&self, name: &str) -> bool {
        self.by_name.contains_key(name)
    }

    /// Returns `true` if the registry has no entries.
    pub fn is_empty(&self) -> bool {
        self.by_name.is_empty()
    }

    /// Number of registered handles.
    pub fn len(&self) -> usize {
        self.by_name.len()
    }

    /// Remove a mapping by handle name. Returns the entity that was bound.
    pub fn remove_by_name(&mut self, name: &str) -> Option<EntityRef> {
        if let Some(entity) = self.by_name.remove(name) {
            self.by_entity.remove(&entity);
            Some(entity)
        } else {
            None
        }
    }

    /// Remove a mapping by entity ref. Returns the name that was bound.
    pub fn remove_by_entity(&mut self, entity: &EntityRef) -> Option<String> {
        if let Some(name) = self.by_entity.remove(entity) {
            self.by_name.remove(&name);
            Some(name)
        } else {
            None
        }
    }

    /// Remove all entries.
    pub fn clear(&mut self) {
        self.by_name.clear();
        self.by_entity.clear();
    }

    /// Iterate over all `(name, entity)` pairs.
    pub fn iter(&self) -> impl Iterator<Item = (&str, &EntityRef)> {
        self.by_name.iter().map(|(k, v)| (k.as_str(), v))
    }

    /// Iterate over all handle names.
    pub fn names(&self) -> impl Iterator<Item = &str> {
        self.by_name.keys().map(|k| k.as_str())
    }

    /// Borrow the name→entity map directly (e.g. for building expression bindings).
    pub fn by_name(&self) -> &HashMap<String, EntityRef> {
        &self.by_name
    }

    /// Borrow the entity→name map directly (e.g. for passing to an effect handler).
    pub fn by_entity(&self) -> &HashMap<EntityRef, String> {
        &self.by_entity
    }
}

impl Default for HandleRegistry {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insert_and_lookup() {
        let mut reg = HandleRegistry::new();
        reg.insert("hero".into(), EntityRef(1));

        assert_eq!(reg.get("hero"), Some(EntityRef(1)));
        assert_eq!(reg.name_of(&EntityRef(1)), Some("hero"));
        assert!(reg.contains("hero"));
        assert_eq!(reg.len(), 1);
    }

    #[test]
    fn remove_by_name() {
        let mut reg = HandleRegistry::new();
        reg.insert("hero".into(), EntityRef(1));
        let removed = reg.remove_by_name("hero");

        assert_eq!(removed, Some(EntityRef(1)));
        assert!(reg.is_empty());
        assert_eq!(reg.name_of(&EntityRef(1)), None);
    }

    #[test]
    fn remove_by_entity() {
        let mut reg = HandleRegistry::new();
        reg.insert("hero".into(), EntityRef(1));
        let removed = reg.remove_by_entity(&EntityRef(1));

        assert_eq!(removed, Some("hero".into()));
        assert!(reg.is_empty());
        assert_eq!(reg.get("hero"), None);
    }

    #[test]
    fn display_name_fallback() {
        let reg = HandleRegistry::new();
        assert_eq!(reg.display_name(&EntityRef(42)), "Entity(42)");
    }

    #[test]
    fn reassign_name_to_different_entity() {
        let mut reg = HandleRegistry::new();
        reg.insert("hero".into(), EntityRef(1));
        let prev = reg.insert("hero".into(), EntityRef(2));

        assert_eq!(prev, Some(EntityRef(1)));
        assert_eq!(reg.get("hero"), Some(EntityRef(2)));
        // Old entity should no longer have a name
        assert_eq!(reg.name_of(&EntityRef(1)), None);
        assert_eq!(reg.name_of(&EntityRef(2)), Some("hero"));
        assert_eq!(reg.len(), 1);
    }

    #[test]
    fn reassign_entity_to_different_name() {
        let mut reg = HandleRegistry::new();
        reg.insert("hero".into(), EntityRef(1));
        reg.insert("champion".into(), EntityRef(1));

        assert_eq!(reg.get("champion"), Some(EntityRef(1)));
        // Old name should no longer resolve
        assert_eq!(reg.get("hero"), None);
        assert_eq!(reg.name_of(&EntityRef(1)), Some("champion"));
        assert_eq!(reg.len(), 1);
    }

    #[test]
    fn clear() {
        let mut reg = HandleRegistry::new();
        reg.insert("a".into(), EntityRef(1));
        reg.insert("b".into(), EntityRef(2));
        reg.clear();

        assert!(reg.is_empty());
        assert_eq!(reg.len(), 0);
    }

    #[test]
    fn iter_and_names() {
        let mut reg = HandleRegistry::new();
        reg.insert("b".into(), EntityRef(2));
        reg.insert("a".into(), EntityRef(1));

        let mut names: Vec<_> = reg.names().collect();
        names.sort_unstable();
        assert_eq!(names, vec!["a", "b"]);

        let mut pairs: Vec<_> = reg.iter().map(|(n, e)| (n.to_string(), *e)).collect();
        pairs.sort();
        assert_eq!(
            pairs,
            vec![("a".into(), EntityRef(1)), ("b".into(), EntityRef(2))]
        );
    }
}
