use std::collections::{HashMap, HashSet};

use rustc_hash::{FxHashMap, FxHashSet};

use crate::ty::Ty;
use ttrpg_ast::Name;
use ttrpg_ast::Span;
use ttrpg_ast::Spanned;
use ttrpg_ast::ast::{ModifyClauseId, TypeExpr};
use ttrpg_ast::diagnostic::Diagnostic;

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
    pub has_defaults: Vec<bool>,
}

#[derive(Debug, Clone)]
pub struct FieldInfo {
    pub name: Name,
    pub ty: Ty,
    pub has_default: bool,
    pub restricted: bool,
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
    Function,
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
    /// For reactions/hooks: the trigger event name.
    pub trigger: Option<TriggerInfo>,
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
pub struct TriggerInfo {
    pub event_name: Name,
}

#[derive(Debug, Clone)]
pub struct ConditionInfo {
    pub name: Name,
    pub params: Vec<ParamInfo>,
    pub extends: Vec<Name>,
    pub receiver_name: Name,
    pub receiver_type: Ty,
    /// Tags declared on this condition (e.g., `#curse #disease`).
    pub tags: HashSet<Name>,
    /// State fields declared directly on this condition (own only, not inherited).
    pub own_state_fields: Vec<(Name, Ty)>,
    /// Merged state fields: inherited ancestor fields + own fields, in ancestor-first order.
    /// Populated by the post-collect `merge_condition_state_fields` pass.
    pub merged_state_fields: Vec<(Name, Ty)>,
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
    pub groups: FxHashMap<Name, OptionalGroupInfo>,
    pub types: FxHashMap<Name, DeclInfo>,
    pub functions: FxHashMap<Name, FnInfo>,
    pub conditions: FxHashMap<Name, ConditionInfo>,
    pub events: FxHashMap<Name, EventInfo>,
    pub variant_to_enums: FxHashMap<Name, Vec<Name>>,
    pub resolved_variants: HashMap<Span, Name>,
    pub flattened_group_fields: FxHashMap<(Name, Name), Name>,
    pub builtins: FxHashMap<Name, FnInfo>,
    pub suffix_to_unit: FxHashMap<String, Name>,
    pub options: FxHashSet<Name>,

    /// Maps each bare function-reference expression span to the function name.
    pub resolved_fn_refs: HashMap<Span, Name>,
    /// Maps FieldAccess spans where a group alias was used → real group name.
    pub resolved_group_aliases: HashMap<Span, Name>,
    /// Maps LValue spans where a group alias was used → (segment_index, real_group_name).
    pub resolved_lvalue_aliases: HashMap<Span, (usize, Name)>,

    // ── Module awareness (populated when ModuleMap is provided) ───
    /// Declaration name → owning system name, per namespace.
    pub type_owner: FxHashMap<Name, Name>,
    pub group_owner: FxHashMap<Name, Name>,
    pub function_owner: FxHashMap<Name, Name>,
    pub condition_owner: FxHashMap<Name, Name>,
    pub event_owner: FxHashMap<Name, Name>,
    pub option_owner: FxHashMap<Name, Name>,

    /// Per-system: which names are visible (own + imported).
    pub system_visibility: FxHashMap<Name, VisibleNames>,
    /// Per-system: alias → target system name.
    pub system_aliases: FxHashMap<Name, FxHashMap<Name, Name>>,

    // ── Action overload index ────────────────────────────────────
    /// Action name → all overloads (one per receiver type). Used for
    /// type-based dispatch when multiple actions share the same name.
    pub action_overloads: FxHashMap<Name, Vec<FnInfo>>,

    // ── Trigger index ─────────────────────────────────────────────
    /// Event name → reaction/hook function names that trigger on it (declaration order).
    pub trigger_index: FxHashMap<Name, Vec<Name>>,

    // ── Tag / selector data ─────────────────────────────────────────
    // ── Const data ────────────────────────────────────────────────
    /// Const name → resolved type.
    pub consts: FxHashMap<Name, Ty>,
    /// Const name → owning system.
    pub const_owner: FxHashMap<Name, Name>,

    /// Declared tag names.
    pub tags: FxHashSet<Name>,
    /// Tag → owning system name.
    pub tag_owner: FxHashMap<Name, Name>,
    /// Precomputed selector match sets, keyed by ModifyClauseId.
    pub selector_matches: HashMap<ModifyClauseId, HashSet<Name>>,
}

/// Names visible to a system (own declarations + imported declarations).
#[derive(Debug, Clone, Default)]
pub struct VisibleNames {
    pub groups: FxHashSet<Name>,
    pub types: FxHashSet<Name>,
    pub functions: FxHashSet<Name>,
    pub conditions: FxHashSet<Name>,
    pub events: FxHashSet<Name>,
    pub variants: FxHashSet<Name>,
    pub options: FxHashSet<Name>,
    pub tags: FxHashSet<Name>,
}

impl Default for TypeEnv {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeEnv {
    pub fn new() -> Self {
        Self {
            groups: FxHashMap::default(),
            types: FxHashMap::default(),
            functions: FxHashMap::default(),
            conditions: FxHashMap::default(),
            events: FxHashMap::default(),
            variant_to_enums: FxHashMap::default(),
            resolved_variants: HashMap::new(),
            flattened_group_fields: FxHashMap::default(),
            builtins: FxHashMap::default(),
            suffix_to_unit: FxHashMap::default(),
            options: FxHashSet::default(),
            resolved_fn_refs: HashMap::new(),
            resolved_group_aliases: HashMap::new(),
            resolved_lvalue_aliases: HashMap::new(),
            type_owner: FxHashMap::default(),
            group_owner: FxHashMap::default(),
            function_owner: FxHashMap::default(),
            condition_owner: FxHashMap::default(),
            event_owner: FxHashMap::default(),
            option_owner: FxHashMap::default(),
            system_visibility: FxHashMap::default(),
            system_aliases: FxHashMap::default(),
            action_overloads: FxHashMap::default(),
            trigger_index: FxHashMap::default(),
            consts: FxHashMap::default(),
            const_owner: FxHashMap::default(),
            tags: FxHashSet::default(),
            tag_owner: FxHashMap::default(),
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
    /// Maximum nesting depth for type resolution.
    const MAX_TYPE_DEPTH: usize = 128;

    pub fn resolve_type(&self, texpr: &Spanned<TypeExpr>) -> Ty {
        self.resolve_type_depth(&texpr.node, 0)
    }

    /// Validate and resolve a type expression in one step.
    /// Emits diagnostics for unknown types, then resolves to a semantic Ty.
    pub fn resolve_type_validated(
        &self,
        texpr: &Spanned<TypeExpr>,
        diagnostics: &mut Vec<Diagnostic>,
    ) -> Ty {
        self.validate_type_names(texpr, diagnostics);
        self.resolve_type_depth(&texpr.node, 0)
    }

    fn resolve_type_depth(&self, texpr: &TypeExpr, depth: usize) -> Ty {
        if depth > Self::MAX_TYPE_DEPTH {
            return Ty::Error;
        }
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
            TypeExpr::EffectSource => self.resolve_named_or("EffectSource", Ty::EffectSource),
            TypeExpr::Position => self.resolve_named_or("Position", Ty::Position),
            TypeExpr::Direction => self.resolve_named_or("Direction", Ty::Direction),
            TypeExpr::Condition => self.resolve_named_or("Condition", Ty::Condition),
            TypeExpr::ActiveCondition => Ty::ActiveCondition,
            TypeExpr::TypedActiveCondition(name) => Ty::TypedActiveCondition(name.clone()),
            TypeExpr::Invocation => Ty::Invocation,
            TypeExpr::Unit => Ty::Unit,
            TypeExpr::Any => Ty::Any,
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
            TypeExpr::List(inner) => {
                Ty::List(Box::new(self.resolve_type_depth(&inner.node, depth + 1)))
            }
            TypeExpr::Set(inner) => {
                Ty::Set(Box::new(self.resolve_type_depth(&inner.node, depth + 1)))
            }
            TypeExpr::Map(k, v) => Ty::Map(
                Box::new(self.resolve_type_depth(&k.node, depth + 1)),
                Box::new(self.resolve_type_depth(&v.node, depth + 1)),
            ),
            TypeExpr::OptionType(inner) => {
                Ty::Option(Box::new(self.resolve_type_depth(&inner.node, depth + 1)))
            }
            TypeExpr::Resource(_, _) => Ty::Resource,
            TypeExpr::Fn {
                params,
                return_type,
            } => {
                let param_tys: Vec<Ty> = params
                    .iter()
                    .map(|p| self.resolve_type_depth(&p.node, depth + 1))
                    .collect();
                let ret_ty = match return_type {
                    Some(r) => self.resolve_type_depth(&r.node, depth + 1),
                    None => Ty::Unit,
                };
                Ty::Fn(param_tys, Box::new(ret_ty))
            }
        }
    }

    /// Emit diagnostics for any unknown Named types in a type expression.
    pub fn validate_type_names(
        &self,
        texpr: &Spanned<TypeExpr>,
        diagnostics: &mut Vec<Diagnostic>,
    ) {
        self.validate_type_names_depth(texpr, diagnostics, 0);
    }

    fn validate_type_names_depth(
        &self,
        texpr: &Spanned<TypeExpr>,
        diagnostics: &mut Vec<Diagnostic>,
        depth: usize,
    ) {
        if depth > Self::MAX_TYPE_DEPTH {
            return;
        }
        match &texpr.node {
            TypeExpr::Named(name) => {
                if name == "entity" {
                    return;
                }
                if !self.types.contains_key(name) {
                    diagnostics.push(
                        Diagnostic::error(format!("unknown type `{name}`"), texpr.span)
                            .with_help(format!(
                                "declare it with: enum {name} {{ ... }}, struct {name} {{ ... }}, or entity {name} {{ ... }}"
                            )),
                    );
                }
            }
            TypeExpr::List(inner) | TypeExpr::OptionType(inner) => {
                self.validate_type_names_depth(inner, diagnostics, depth + 1);
            }
            TypeExpr::Set(inner) => {
                if matches!(inner.node, TypeExpr::Position) {
                    diagnostics.push(Diagnostic::error(
                        "Position cannot be used as a set element type",
                        inner.span,
                    ));
                }
                if matches!(inner.node, TypeExpr::Direction) {
                    diagnostics.push(Diagnostic::error(
                        "Direction cannot be used as a set element type",
                        inner.span,
                    ));
                }
                self.validate_type_names_depth(inner, diagnostics, depth + 1);
            }
            TypeExpr::Map(k, v) => {
                if matches!(k.node, TypeExpr::Position) {
                    diagnostics.push(Diagnostic::error(
                        "Position cannot be used as a map key type",
                        k.span,
                    ));
                }
                if matches!(k.node, TypeExpr::Direction) {
                    diagnostics.push(Diagnostic::error(
                        "Direction cannot be used as a map key type",
                        k.span,
                    ));
                }
                self.validate_type_names_depth(k, diagnostics, depth + 1);
                self.validate_type_names_depth(v, diagnostics, depth + 1);
            }
            TypeExpr::Fn {
                params,
                return_type,
            } => {
                for p in params {
                    self.validate_type_names_depth(p, diagnostics, depth + 1);
                }
                if let Some(ret) = return_type {
                    self.validate_type_names_depth(ret, diagnostics, depth + 1);
                }
            }
            TypeExpr::Qualified { qualifier, name } => {
                diagnostics.push(Diagnostic::error(
                    format!("qualified type `{qualifier}.{name}` requires module resolution"),
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

    /// Look up the best action overload for a given receiver type.
    ///
    /// Returns the overload whose receiver matches `receiver_ty`, falling back
    /// to an `AnyEntity` overload, or `None` if no overload matches.
    pub fn lookup_action_overload(&self, name: &str, receiver_ty: &Ty) -> Option<&FnInfo> {
        let overloads = self.action_overloads.get(name)?;
        if overloads.len() == 1 {
            return Some(&overloads[0]);
        }

        // Exact match on receiver type
        if let Some(info) = overloads
            .iter()
            .find(|fi| fi.receiver.as_ref().is_some_and(|r| r.ty == *receiver_ty))
        {
            return Some(info);
        }

        // AnyEntity fallback
        overloads
            .iter()
            .find(|fi| fi.receiver.as_ref().is_some_and(|r| r.ty == Ty::AnyEntity))
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
            .is_some_and(|g| g.required)
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
            ("source", Ty::EffectSource),
            ("id", Ty::Int),
            ("applied_at", Ty::Int),
            ("tags", Ty::Set(Box::new(Ty::String))),
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

        // Exact field match first
        if fields.contains(token) {
            return Some(Name::from(token));
        }

        // Legacy alias fallback
        let alias_field = match token {
            "action" => Some("actions"),
            "bonus_action" => Some("bonus_actions"),
            "reaction" => Some("reactions"),
            _ => None,
        };

        if let Some(field) = alias_field
            && fields.contains(field)
        {
            return Some(Name::from(field));
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
