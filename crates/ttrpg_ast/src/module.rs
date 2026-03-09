use rustc_hash::{FxHashMap, FxHashSet};

use crate::name::Name;
use crate::span::FileId;
use crate::Span;

/// Maps system names to their declaration metadata and import relationships.
#[derive(Clone, Debug, Default)]
pub struct ModuleMap {
    pub systems: FxHashMap<Name, SystemInfo>,
}

/// Per-system declaration ownership and import list.
#[derive(Clone, Debug, Default)]
pub struct SystemInfo {
    /// Files that contain `system` blocks for this system (by FileId).
    pub source_files: Vec<FileId>,

    /// Top-level group names defined in this system.
    pub groups: FxHashSet<Name>,
    /// Type names (enums, structs, entities) defined in this system.
    pub types: FxHashSet<Name>,
    /// Function names (derives, mechanics, actions, reactions, hooks, prompts) defined in this system.
    pub functions: FxHashSet<Name>,
    /// Condition names defined in this system.
    pub conditions: FxHashSet<Name>,
    /// Event names defined in this system.
    pub events: FxHashSet<Name>,
    /// Option names defined in this system.
    pub options: FxHashSet<Name>,
    /// Enum variant names defined in this system (via owning enum).
    pub variants: FxHashSet<Name>,
    /// Tag names defined in this system.
    pub tags: FxHashSet<Name>,

    /// Span of the first definition for each declaration name (any namespace).
    /// Used for diagnostic provenance in cross-system collision errors.
    pub decl_spans: FxHashMap<Name, Span>,

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
