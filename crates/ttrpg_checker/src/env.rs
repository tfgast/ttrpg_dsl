use std::collections::{HashMap, HashSet};

use crate::ty::Ty;
use ttrpg_ast::ast::{ModifyClauseId, TypeExpr};
use ttrpg_ast::diagnostic::Diagnostic;
use ttrpg_ast::Name;
use ttrpg_ast::Span;
use ttrpg_ast::Spanned;

/// What kind of declaration a type name refers to.
#[derive(Debug, Clone)]
pub enum DeclInfo {
    Enum(EnumInfo),
    Struct(StructInfo),
    Entity(EntityInfo),
    Unit(UnitInfo),
}

#[derive(Debug, Clone)]
pub struct EnumInfo {
    pub name: Name,
    pub ordered: bool,
    pub variants: Vec<VariantInfo>,
}

#[derive(Debug, Clone)]
pub struct VariantInfo {
    pub name: Name,
    pub fields: Vec<(Name, Ty)>,
}

#[derive(Debug, Clone)]
pub struct FieldInfo {
    pub name: Name,
    pub ty: Ty,
    pub has_default: bool,
}

#[derive(Debug, Clone)]
pub struct StructInfo {
    pub name: Name,
    pub fields: Vec<FieldInfo>,
}

#[derive(Debug, Clone)]
pub struct EntityInfo {
    pub name: Name,
    pub fields: Vec<FieldInfo>,
    pub optional_groups: Vec<OptionalGroupInfo>,
}

#[derive(Debug, Clone)]
pub struct UnitInfo {
    pub name: Name,
    pub fields: Vec<FieldInfo>,
    pub suffix: Option<String>,
}

#[derive(Debug, Clone)]
pub struct OptionalGroupInfo {
    pub name: Name,
    pub fields: Vec<FieldInfo>,
    pub required: bool,
}

/// What kind of callable a function name refers to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FnKind {
    Derive,
    Mechanic,
    Action,
    Reaction,
    Hook,
    Prompt,
    Builtin,
    Table,
}

#[derive(Debug, Clone)]
pub struct FnInfo {
    pub name: Name,
    pub kind: FnKind,
    pub params: Vec<ParamInfo>,
    pub return_type: Ty,
    /// For action/reaction: the receiver parameter info.
    pub receiver: Option<ParamInfo>,
    /// Tags applied to this function.
    pub tags: HashSet<Name>,
    /// True for declarations synthesized by `lower_moves`.
    pub synthetic: bool,
}

#[derive(Debug, Clone)]
pub struct ParamInfo {
    pub name: Name,
    pub ty: Ty,
    pub has_default: bool,
    /// Optional group constraints from `with` clauses, enforced at call sites.
    pub with_groups: Vec<Name>,
    /// True when the `with` clause is disjunctive (`with A | B`).
    /// Disjunctive constraints skip call-site group proof and body narrowing.
    pub with_disjunctive: bool,
}

#[derive(Debug, Clone)]
pub struct ConditionInfo {
    pub name: Name,
    pub params: Vec<ParamInfo>,
    pub extends: Vec<Name>,
    pub receiver_name: Name,
    pub receiver_type: Ty,
}

#[derive(Debug, Clone)]
pub struct EventInfo {
    pub name: Name,
    pub params: Vec<ParamInfo>,
    pub fields: Vec<(Name, Ty)>,
    /// True for auto-registered events (e.g., `modify_applied`). User-defined
    /// events with the same name are allowed to override builtins.
    pub builtin: bool,
}

/// The populated symbol table — built by Pass 1, consumed by Pass 2.
#[derive(Debug, Clone)]
pub struct TypeEnv {
    pub groups: HashMap<Name, OptionalGroupInfo>,
    pub types: HashMap<Name, DeclInfo>,
    pub functions: HashMap<Name, FnInfo>,
    pub conditions: HashMap<Name, ConditionInfo>,
    pub events: HashMap<Name, EventInfo>,
    pub variant_to_enums: HashMap<Name, Vec<Name>>,
    pub resolved_variants: HashMap<Span, Name>,
    pub flattened_group_fields: HashMap<(Name, Name), Name>,
    pub builtins: HashMap<Name, FnInfo>,
    pub suffix_to_unit: HashMap<String, Name>,
    pub options: HashSet<Name>,

    /// Maps FieldAccess spans where a group alias was used → real group name.
    pub resolved_group_aliases: HashMap<Span, Name>,
    /// Maps LValue spans where a group alias was used → (segment_index, real_group_name).
    pub resolved_lvalue_aliases: HashMap<Span, (usize, Name)>,

    // ── Module awareness (populated when ModuleMap is provided) ───
    /// Declaration name → owning system name, per namespace.
    pub type_owner: HashMap<Name, Name>,
    pub group_owner: HashMap<Name, Name>,
    pub function_owner: HashMap<Name, Name>,
    pub condition_owner: HashMap<Name, Name>,
    pub event_owner: HashMap<Name, Name>,
    pub option_owner: HashMap<Name, Name>,

    /// Per-system: which names are visible (own + imported).
    pub system_visibility: HashMap<Name, VisibleNames>,
    /// Per-system: alias → target system name.
    pub system_aliases: HashMap<Name, HashMap<Name, Name>>,

    // ── Tag / selector data ─────────────────────────────────────────
    /// Declared tag names.
    pub tags: HashSet<Name>,
    /// Tag → owning system name.
    pub tag_owner: HashMap<Name, Name>,
    /// Precomputed selector match sets, keyed by ModifyClauseId.
    pub selector_matches: HashMap<ModifyClauseId, HashSet<Name>>,
}

/// Names visible to a system (own declarations + imported declarations).
#[derive(Debug, Clone, Default)]
pub struct VisibleNames {
    pub groups: HashSet<Name>,
    pub types: HashSet<Name>,
    pub functions: HashSet<Name>,
    pub conditions: HashSet<Name>,
    pub events: HashSet<Name>,
    pub variants: HashSet<Name>,
    pub options: HashSet<Name>,
    pub tags: HashSet<Name>,
}

impl Default for TypeEnv {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeEnv {
    pub fn new() -> Self {
        Self {
            groups: HashMap::new(),
            types: HashMap::new(),
            functions: HashMap::new(),
            conditions: HashMap::new(),
            events: HashMap::new(),
            variant_to_enums: HashMap::new(),
            resolved_variants: HashMap::new(),
            flattened_group_fields: HashMap::new(),
            builtins: HashMap::new(),
            suffix_to_unit: HashMap::new(),
            options: HashSet::new(),
            resolved_group_aliases: HashMap::new(),
            resolved_lvalue_aliases: HashMap::new(),
            type_owner: HashMap::new(),
            group_owner: HashMap::new(),
            function_owner: HashMap::new(),
            condition_owner: HashMap::new(),
            event_owner: HashMap::new(),
            option_owner: HashMap::new(),
            system_visibility: HashMap::new(),
            system_aliases: HashMap::new(),
            tags: HashSet::new(),
            tag_owner: HashMap::new(),
            selector_matches: HashMap::new(),
        }
    }

    /// Look up a flattened included-group field on an entity.
    /// Returns the group name if `field` is a field in an included group on `entity_type`.
    pub fn lookup_flattened_field(&self, entity_type: &str, field: &str) -> Option<&Name> {
        self.flattened_group_fields
            .get(&(Name::from(entity_type), Name::from(field)))
    }

    /// If exactly one enum owns this variant, return that enum's name.
    pub fn unique_variant_owner(&self, variant: &str) -> Option<&Name> {
        match self.variant_to_enums.get(variant) {
            Some(owners) if owners.len() == 1 => Some(&owners[0]),
            _ => None,
        }
    }

    /// If a user-defined type with `name` exists, resolve to it; otherwise use the fallback.
    fn resolve_named_or(&self, name: &str, fallback: Ty) -> Ty {
        if let Some(decl) = self.types.get(name) {
            let n = Name::from(name);
            match decl {
                DeclInfo::Enum(_) => Ty::Enum(n),
                DeclInfo::Struct(_) => Ty::Struct(n),
                DeclInfo::Entity(_) => Ty::Entity(n),
                DeclInfo::Unit(_) => Ty::UnitType(n),
            }
        } else {
            fallback
        }
    }

    /// Resolve a syntactic TypeExpr to a semantic Ty.
    ///
    /// Precondition: `validate_type_names` (or `resolve_type_validated`) must
    /// have been called on this type expression previously. Unknown names
    /// resolve to `Ty::Error` without emitting diagnostics.
    pub fn resolve_type(&self, texpr: &Spanned<TypeExpr>) -> Ty {
        self.resolve_type_inner(&texpr.node)
    }

    /// Validate and resolve a type expression in one step.
    /// Emits diagnostics for unknown types, then resolves to a semantic Ty.
    pub fn resolve_type_validated(
        &self,
        texpr: &Spanned<TypeExpr>,
        diagnostics: &mut Vec<Diagnostic>,
    ) -> Ty {
        self.validate_type_names(texpr, diagnostics);
        self.resolve_type_inner(&texpr.node)
    }

    fn resolve_type_inner(&self, texpr: &TypeExpr) -> Ty {
        match texpr {
            TypeExpr::Int => Ty::Int,
            TypeExpr::Float => Ty::Float,
            TypeExpr::Bool => Ty::Bool,
            TypeExpr::String => Ty::String,
            TypeExpr::DiceExpr => Ty::DiceExpr,
            TypeExpr::RollResult => Ty::RollResult,
            // For TurnBudget and Duration: prefer user-defined types if they exist
            TypeExpr::TurnBudget => self.resolve_named_or("TurnBudget", Ty::TurnBudget),
            TypeExpr::Duration => self.resolve_named_or("Duration", Ty::Duration),
            TypeExpr::Position => self.resolve_named_or("Position", Ty::Position),
            TypeExpr::Condition => self.resolve_named_or("Condition", Ty::Condition),
            TypeExpr::ActiveCondition => Ty::ActiveCondition,
            TypeExpr::Invocation => Ty::Invocation,
            TypeExpr::Named(name) => {
                if name == "entity" {
                    return Ty::AnyEntity;
                }
                if let Some(decl) = self.types.get(name) {
                    match decl {
                        DeclInfo::Enum(_) => Ty::Enum(name.clone()),
                        DeclInfo::Struct(_) => Ty::Struct(name.clone()),
                        DeclInfo::Entity(_) => Ty::Entity(name.clone()),
                        DeclInfo::Unit(_) => Ty::UnitType(name.clone()),
                    }
                } else {
                    Ty::Error
                }
            }
            // Qualified types are desugared to Named by module resolution before checking.
            // If one reaches the checker, it's an internal error — resolve to Error.
            TypeExpr::Qualified { .. } => Ty::Error,
            TypeExpr::List(inner) => Ty::List(Box::new(self.resolve_type(inner))),
            TypeExpr::Set(inner) => Ty::Set(Box::new(self.resolve_type(inner))),
            TypeExpr::Map(k, v) => Ty::Map(
                Box::new(self.resolve_type(k)),
                Box::new(self.resolve_type(v)),
            ),
            TypeExpr::OptionType(inner) => Ty::Option(Box::new(self.resolve_type(inner))),
            TypeExpr::Resource(_, _) => Ty::Resource,
        }
    }

    /// Emit diagnostics for any unknown Named types in a type expression.
    pub fn validate_type_names(
        &self,
        texpr: &Spanned<TypeExpr>,
        diagnostics: &mut Vec<Diagnostic>,
    ) {
        match &texpr.node {
            TypeExpr::Named(name) => {
                if name == "entity" {
                    return;
                }
                if !self.types.contains_key(name) {
                    diagnostics.push(Diagnostic::error(
                        format!("unknown type `{}`", name),
                        texpr.span,
                    ));
                }
            }
            TypeExpr::List(inner) | TypeExpr::OptionType(inner) => {
                self.validate_type_names(inner, diagnostics);
            }
            TypeExpr::Set(inner) => {
                if matches!(inner.node, TypeExpr::Position) {
                    diagnostics.push(Diagnostic::error(
                        "Position cannot be used as a set element type",
                        inner.span,
                    ));
                }
                self.validate_type_names(inner, diagnostics);
            }
            TypeExpr::Map(k, v) => {
                if matches!(k.node, TypeExpr::Position) {
                    diagnostics.push(Diagnostic::error(
                        "Position cannot be used as a map key type",
                        k.span,
                    ));
                }
                self.validate_type_names(k, diagnostics);
                self.validate_type_names(v, diagnostics);
            }
            TypeExpr::Qualified { qualifier, name } => {
                diagnostics.push(Diagnostic::error(
                    format!(
                        "qualified type `{}.{}` requires module resolution",
                        qualifier, name
                    ),
                    texpr.span,
                ));
            }
            _ => {}
        }
    }

    /// Look up an enum by name.
    pub fn get_enum(&self, name: &str) -> Option<&EnumInfo> {
        match self.types.get(name)? {
            DeclInfo::Enum(info) => Some(info),
            _ => None,
        }
    }

    /// Return the variant names for a given enum type.
    ///
    /// Returns `None` if `enum_name` doesn't refer to a defined enum.
    pub fn enum_variants(&self, enum_name: &str) -> Option<Vec<&str>> {
        self.get_enum(enum_name)
            .map(|info| info.variants.iter().map(|v| v.name.as_ref()).collect())
    }

    /// Look up a function by name (user-defined or builtin).
    ///
    /// By design, user-defined functions shadow builtins. This is consistent
    /// with most languages (Rust, Python, JS) and lets users override default
    /// behavior when needed. A future lint pass could warn on shadowing if
    /// desired, but it is not an error.
    pub fn lookup_fn(&self, name: &str) -> Option<&FnInfo> {
        self.functions.get(name).or_else(|| self.builtins.get(name))
    }

    /// Look up fields of a struct/entity by name.
    pub fn lookup_fields(&self, name: &str) -> Option<&[FieldInfo]> {
        match self.types.get(name)? {
            DeclInfo::Struct(info) => Some(&info.fields),
            DeclInfo::Entity(info) => Some(&info.fields),
            DeclInfo::Unit(info) => Some(&info.fields),
            DeclInfo::Enum(_) => None,
        }
    }

    /// Look up an optional group on an entity by name.
    pub fn lookup_optional_group(
        &self,
        entity_name: &str,
        group_name: &str,
    ) -> Option<&OptionalGroupInfo> {
        match self.types.get(entity_name)? {
            DeclInfo::Entity(info) => info.optional_groups.iter().find(|g| g.name == group_name),
            _ => None,
        }
    }

    /// Return whether a group attached to an entity is required (`include`) vs optional.
    pub fn is_group_required(&self, entity_name: &str, group_name: &str) -> bool {
        self.lookup_optional_group(entity_name, group_name)
            .map(|g| g.required)
            .unwrap_or(false)
    }

    /// Look up a top-level group declaration by name.
    pub fn lookup_group(&self, group_name: &str) -> Option<&OptionalGroupInfo> {
        self.groups.get(group_name)
    }

    /// Return true if any entity declares an optional group with this name.
    pub fn has_optional_group_named(&self, group_name: &str) -> bool {
        if self.groups.contains_key(group_name) {
            return true;
        }
        self.types.values().any(|decl| match decl {
            DeclInfo::Entity(info) => info.optional_groups.iter().any(|g| g.name == group_name),
            _ => false,
        })
    }

    /// If exactly one entity declares `group_name`, return that owner and group.
    pub fn unique_optional_group_owner(
        &self,
        group_name: &str,
    ) -> Option<(Name, &OptionalGroupInfo)> {
        if let Some(group) = self.groups.get(group_name) {
            return Some((Name::from("entity"), group));
        }
        let mut found: Option<(Name, &OptionalGroupInfo)> = None;
        for decl in self.types.values() {
            let DeclInfo::Entity(info) = decl else {
                continue;
            };
            if let Some(group) = info.optional_groups.iter().find(|g| g.name == group_name) {
                if found.is_some() {
                    return None;
                }
                found = Some((info.name.clone(), group));
            }
        }
        found
    }

    /// Return true if any entity declares `group_name` as required (`include`).
    pub fn is_group_required_somewhere(&self, group_name: &str) -> bool {
        self.types.values().any(|decl| match decl {
            DeclInfo::Entity(info) => info
                .optional_groups
                .iter()
                .any(|g| g.name == group_name && g.required),
            _ => false,
        })
    }

    /// Get the RollResult struct fields.
    pub fn roll_result_fields() -> Vec<(&'static str, Ty)> {
        vec![
            ("expr", Ty::DiceExpr),
            ("dice", Ty::List(Box::new(Ty::Int))),
            ("kept", Ty::List(Box::new(Ty::Int))),
            ("modifier", Ty::Int),
            ("total", Ty::Int),
            ("unmodified", Ty::Int),
        ]
    }

    /// Get the ActiveCondition struct fields.
    pub fn active_condition_fields() -> Vec<(&'static str, Ty)> {
        vec![
            ("name", Ty::String),
            ("duration", Ty::Duration),
            ("id", Ty::Int),
        ]
    }

    /// Get the TurnBudget struct fields.
    pub fn turn_budget_fields() -> Vec<(&'static str, Ty)> {
        vec![
            ("actions", Ty::Int),
            ("bonus_actions", Ty::Int),
            ("reactions", Ty::Int),
            ("movement", Ty::Int),
            ("free_interactions", Ty::Int),
        ]
    }

    /// Return the active TurnBudget field names.
    ///
    /// If the program defines `struct TurnBudget`, those fields are used.
    /// Otherwise, the built-in fallback schema is returned.
    pub fn turn_budget_field_names(&self) -> Vec<Name> {
        if let Some(fields) = self.lookup_fields("TurnBudget") {
            fields.iter().map(|f| f.name.clone()).collect()
        } else {
            Self::turn_budget_fields()
                .into_iter()
                .map(|(name, _)| Name::from(name))
                .collect()
        }
    }

    /// Resolve a DSL cost token (from `cost { ... }`) to a TurnBudget field name.
    ///
    /// Supports:
    /// - Legacy aliases: `action`, `bonus_action`, `reaction`
    /// - Direct field-name tokens for any TurnBudget field (e.g. `movement`, `attack`)
    pub fn resolve_cost_token(&self, token: &str) -> Option<Name> {
        let fields: HashSet<Name> = self.turn_budget_field_names().into_iter().collect();

        let alias_field = match token {
            "action" => Some("actions"),
            "bonus_action" => Some("bonus_actions"),
            "reaction" => Some("reactions"),
            _ => None,
        };

        if let Some(field) = alias_field {
            if fields.contains(field) {
                return Some(Name::from(field));
            }
        }

        if fields.contains(token) {
            return Some(Name::from(token));
        }

        None
    }

    /// Return valid cost tokens for diagnostics and tooling.
    pub fn valid_cost_tokens(&self) -> Vec<Name> {
        let fields: HashSet<Name> = self.turn_budget_field_names().into_iter().collect();
        let mut tokens = fields.clone();

        if fields.contains("actions") {
            tokens.insert(Name::from("action"));
        }
        if fields.contains("bonus_actions") {
            tokens.insert(Name::from("bonus_action"));
        }
        if fields.contains("reactions") {
            tokens.insert(Name::from("reaction"));
        }

        let mut out: Vec<Name> = tokens.into_iter().collect();
        out.sort_by(|a, b| a.as_str().cmp(b.as_str()));
        out
    }
}
