use std::collections::{HashMap, HashSet};

use crate::Span;

/// Maps system names to their declaration metadata and import relationships.
#[derive(Clone, Debug, Default)]
pub struct ModuleMap {
    pub systems: HashMap<String, SystemInfo>,
}

/// Per-system declaration ownership and import list.
#[derive(Clone, Debug, Default)]
pub struct SystemInfo {
    /// Type names (enums, structs, entities) defined in this system.
    pub types: HashSet<String>,
    /// Function names (derives, mechanics, actions, reactions, hooks, prompts) defined in this system.
    pub functions: HashSet<String>,
    /// Condition names defined in this system.
    pub conditions: HashSet<String>,
    /// Event names defined in this system.
    pub events: HashSet<String>,
    /// Option names defined in this system.
    pub options: HashSet<String>,
    /// Enum variant names defined in this system (via owning enum).
    pub variants: HashSet<String>,

    /// Imports declared for this system (union of `use` decls across all files containing it).
    pub imports: Vec<ImportInfo>,
}

/// A single `use "system_name" as Alias` import.
#[derive(Clone, Debug)]
pub struct ImportInfo {
    pub system_name: String,
    pub alias: Option<String>,
    pub span: Span,
}
