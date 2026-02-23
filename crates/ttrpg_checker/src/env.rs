use std::collections::{HashMap, HashSet};

use crate::ty::Ty;
use ttrpg_ast::ast::TypeExpr;
use ttrpg_ast::diagnostic::Diagnostic;
use ttrpg_ast::Spanned;

/// What kind of declaration a type name refers to.
#[derive(Debug, Clone)]
pub enum DeclInfo {
    Enum(EnumInfo),
    Struct(StructInfo),
    Entity(EntityInfo),
}

#[derive(Debug, Clone)]
pub struct EnumInfo {
    pub name: String,
    pub variants: Vec<VariantInfo>,
}

#[derive(Debug, Clone)]
pub struct VariantInfo {
    pub name: String,
    pub fields: Vec<(String, Ty)>,
}

#[derive(Debug, Clone)]
pub struct FieldInfo {
    pub name: String,
    pub ty: Ty,
    pub has_default: bool,
}

#[derive(Debug, Clone)]
pub struct StructInfo {
    pub name: String,
    pub fields: Vec<FieldInfo>,
}

#[derive(Debug, Clone)]
pub struct EntityInfo {
    pub name: String,
    pub fields: Vec<FieldInfo>,
    pub optional_groups: Vec<OptionalGroupInfo>,
}

#[derive(Debug, Clone)]
pub struct OptionalGroupInfo {
    pub name: String,
    pub fields: Vec<FieldInfo>,
}

/// What kind of callable a function name refers to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FnKind {
    Derive,
    Mechanic,
    Action,
    Reaction,
    Prompt,
    Builtin,
}

#[derive(Debug, Clone)]
pub struct FnInfo {
    pub name: String,
    pub kind: FnKind,
    pub params: Vec<ParamInfo>,
    pub return_type: Ty,
    /// For action/reaction: the receiver parameter info.
    pub receiver: Option<ParamInfo>,
}

#[derive(Debug, Clone)]
pub struct ParamInfo {
    pub name: String,
    pub ty: Ty,
    pub has_default: bool,
}

#[derive(Debug, Clone)]
pub struct ConditionInfo {
    pub name: String,
    pub receiver_name: String,
    pub receiver_type: Ty,
}

#[derive(Debug, Clone)]
pub struct EventInfo {
    pub name: String,
    pub params: Vec<ParamInfo>,
    pub fields: Vec<(String, Ty)>,
}

/// The populated symbol table — built by Pass 1, consumed by Pass 2.
#[derive(Debug, Clone)]
pub struct TypeEnv {
    pub types: HashMap<String, DeclInfo>,
    pub functions: HashMap<String, FnInfo>,
    pub conditions: HashMap<String, ConditionInfo>,
    pub events: HashMap<String, EventInfo>,
    pub variant_to_enum: HashMap<String, String>,
    pub builtins: HashMap<String, FnInfo>,
    pub options: HashSet<String>,
}

impl Default for TypeEnv {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeEnv {
    pub fn new() -> Self {
        Self {
            types: HashMap::new(),
            functions: HashMap::new(),
            conditions: HashMap::new(),
            events: HashMap::new(),
            variant_to_enum: HashMap::new(),
            builtins: HashMap::new(),
            options: HashSet::new(),
        }
    }

    /// If a user-defined type with `name` exists, resolve to it; otherwise use the fallback.
    fn resolve_named_or(&self, name: &str, fallback: Ty) -> Ty {
        if let Some(decl) = self.types.get(name) {
            match decl {
                DeclInfo::Enum(_) => Ty::Enum(name.to_string()),
                DeclInfo::Struct(_) => Ty::Struct(name.to_string()),
                DeclInfo::Entity(_) => Ty::Entity(name.to_string()),
            }
        } else {
            fallback
        }
    }

    /// Resolve a syntactic TypeExpr to a semantic Ty.
    pub fn resolve_type(&self, texpr: &Spanned<TypeExpr>) -> Ty {
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
            TypeExpr::Position => Ty::Position,
            TypeExpr::Condition => Ty::Condition,
            TypeExpr::Named(name) => {
                if let Some(decl) = self.types.get(name) {
                    match decl {
                        DeclInfo::Enum(_) => Ty::Enum(name.clone()),
                        DeclInfo::Struct(_) => Ty::Struct(name.clone()),
                        DeclInfo::Entity(_) => Ty::Entity(name.clone()),
                    }
                } else {
                    Ty::Error
                }
            }
            TypeExpr::List(inner) => Ty::List(Box::new(self.resolve_type(inner))),
            TypeExpr::Set(inner) => Ty::Set(Box::new(self.resolve_type(inner))),
            TypeExpr::Map(k, v) => {
                Ty::Map(Box::new(self.resolve_type(k)), Box::new(self.resolve_type(v)))
            }
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
            _ => {}
        }
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
            DeclInfo::Enum(_) => None,
        }
    }

    /// Look up an optional group on an entity by name.
    pub fn lookup_optional_group(&self, entity_name: &str, group_name: &str) -> Option<&OptionalGroupInfo> {
        match self.types.get(entity_name)? {
            DeclInfo::Entity(info) => info.optional_groups.iter().find(|g| g.name == group_name),
            _ => None,
        }
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
}
