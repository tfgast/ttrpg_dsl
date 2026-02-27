use std::collections::{HashMap, HashSet};

use crate::name::Name;
use crate::Span;

/// Maps system names to their declaration metadata and import relationships.
#[derive(Clone, Debug, Default)]
pub struct ModuleMap {
    pub systems: HashMap<Name, SystemInfo>,
}

/// Per-system declaration ownership and import list.
#[derive(Clone, Debug, Default)]
pub struct SystemInfo {
    /// Top-level group names defined in this system.
    pub groups: HashSet<Name>,
    /// Type names (enums, structs, entities) defined in this system.
    pub types: HashSet<Name>,
    /// Function names (derives, mechanics, actions, reactions, hooks, prompts) defined in this system.
    pub functions: HashSet<Name>,
    /// Condition names defined in this system.
    pub conditions: HashSet<Name>,
    /// Event names defined in this system.
    pub events: HashSet<Name>,
    /// Option names defined in this system.
    pub options: HashSet<Name>,
    /// Enum variant names defined in this system (via owning enum).
    pub variants: HashSet<Name>,
    /// Tag names defined in this system.
    pub tags: HashSet<Name>,

    /// Imports declared for this system (union of `use` decls across all files containing it).
    pub imports: Vec<ImportInfo>,
}

/// A single `use "system_name" as Alias` import.
#[derive(Clone, Debug)]
pub struct ImportInfo {
    pub system_name: Name,
    pub alias: Option<Name>,
    pub span: Span,
}
