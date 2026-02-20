/// Resolved types, distinct from the syntactic `TypeExpr` in the AST.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ty {
    // Primitives
    Int,
    Float,
    Bool,
    String,

    // Dice pipeline
    DiceExpr,
    RollResult,

    // Built-in opaque types
    TurnBudget,
    Duration,
    Position,
    Condition,

    // Nominal (user-defined)
    Enum(std::string::String),
    Struct(std::string::String),
    Entity(std::string::String),

    // Wildcard: matches any Entity(_) — used for entity-generic builtins
    AnyEntity,

    // Generic containers
    List(Box<Ty>),
    Set(Box<Ty>),
    Map(Box<Ty>, Box<Ty>),
    Option(Box<Ty>),

    // Bounded int: behaves as int for reads, clamped on writes
    Resource,

    // Unit: for action/reaction return, if-without-else
    Unit,

    // Sentinel: suppresses cascading errors
    Error,
}

impl Ty {
    pub fn is_error(&self) -> bool {
        matches!(self, Ty::Error)
    }

    /// Whether this is the `none` literal type: `option<error>`.
    pub fn is_none(&self) -> bool {
        matches!(self, Ty::Option(inner) if inner.is_error())
    }

    pub fn is_entity(&self) -> bool {
        matches!(self, Ty::Entity(_) | Ty::AnyEntity)
    }

    pub fn is_numeric(&self) -> bool {
        matches!(self, Ty::Int | Ty::Float | Ty::Resource)
    }

    /// Whether this type is an integer-like type (int or resource).
    pub fn is_int_like(&self) -> bool {
        matches!(self, Ty::Int | Ty::Resource)
    }

    /// Display name for diagnostics.
    pub fn display(&self) -> std::string::String {
        match self {
            Ty::Int => "int".into(),
            Ty::Float => "float".into(),
            Ty::Bool => "bool".into(),
            Ty::String => "string".into(),
            Ty::DiceExpr => "DiceExpr".into(),
            Ty::RollResult => "RollResult".into(),
            Ty::TurnBudget => "TurnBudget".into(),
            Ty::Duration => "Duration".into(),
            Ty::Position => "Position".into(),
            Ty::Condition => "Condition".into(),
            Ty::Enum(name) => name.clone(),
            Ty::Struct(name) => name.clone(),
            Ty::Entity(name) => name.clone(),
            Ty::AnyEntity => "entity".into(),
            Ty::List(inner) => format!("list<{}>", inner.display()),
            Ty::Set(inner) => format!("set<{}>", inner.display()),
            Ty::Map(k, v) => format!("map<{}, {}>", k.display(), v.display()),
            Ty::Option(inner) => format!("option<{}>", inner.display()),
            Ty::Resource => "resource".into(),
            Ty::Unit => "unit".into(),
            Ty::Error => "<error>".into(),
        }
    }
}

impl std::fmt::Display for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.display())
    }
}
