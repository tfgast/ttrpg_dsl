use std::collections::HashMap;

use crate::{DiceFilter, Span, Spanned};

// ── Program structure ────────────────────────────────────────────

#[derive(Clone, Default)]
pub struct Program {
    pub items: Vec<Spanned<TopLevel>>,

    // ── Declaration index (built by `build_index()`) ────────────
    pub actions: HashMap<String, ActionDecl>,
    pub derives: HashMap<String, FnDecl>,
    pub mechanics: HashMap<String, FnDecl>,
    pub reactions: HashMap<String, ReactionDecl>,
    pub reaction_order: Vec<String>,
    pub conditions: HashMap<String, ConditionDecl>,
    pub events: HashMap<String, EventDecl>,
    pub prompts: HashMap<String, PromptDecl>,
    pub options: HashMap<String, OptionDecl>,
    pub option_order: Vec<String>,
    pub hooks: HashMap<String, HookDecl>,
    pub hook_order: Vec<String>,
    pub tables: HashMap<String, TableDecl>,
}

impl Program {
    /// Build O(1) lookup indices from `self.items`.
    ///
    /// Must be called after any mutation of `items` (e.g. after `lower_moves`).
    pub fn build_index(&mut self) {
        self.actions.clear();
        self.derives.clear();
        self.mechanics.clear();
        self.reactions.clear();
        self.reaction_order.clear();
        self.conditions.clear();
        self.events.clear();
        self.prompts.clear();
        self.options.clear();
        self.option_order.clear();
        self.hooks.clear();
        self.hook_order.clear();
        self.tables.clear();

        for item in &self.items {
            if let TopLevel::System(system) = &item.node {
                for decl in &system.decls {
                    match &decl.node {
                        DeclKind::Action(a) => {
                            self.actions.insert(a.name.clone(), a.clone());
                        }
                        DeclKind::Derive(f) => {
                            self.derives.insert(f.name.clone(), f.clone());
                        }
                        DeclKind::Mechanic(f) => {
                            self.mechanics.insert(f.name.clone(), f.clone());
                        }
                        DeclKind::Reaction(r) => {
                            self.reactions.insert(r.name.clone(), r.clone());
                            self.reaction_order.push(r.name.clone());
                        }
                        DeclKind::Condition(c) => {
                            self.conditions.insert(c.name.clone(), c.clone());
                        }
                        DeclKind::Event(e) => {
                            self.events.insert(e.name.clone(), e.clone());
                        }
                        DeclKind::Prompt(p) => {
                            self.prompts.insert(p.name.clone(), p.clone());
                        }
                        DeclKind::Option(o) => {
                            self.options.insert(o.name.clone(), o.clone());
                            self.option_order.push(o.name.clone());
                        }
                        DeclKind::Hook(h) => {
                            self.hooks.insert(h.name.clone(), h.clone());
                            self.hook_order.push(h.name.clone());
                        }
                        DeclKind::Table(t) => {
                            self.tables.insert(t.name.clone(), t.clone());
                        }
                        _ => {}
                    }
                }
            }
        }
    }
}

#[derive(Clone)]
pub enum TopLevel {
    Use(UseDecl),
    System(SystemBlock),
}

#[derive(Clone)]
pub struct UseDecl {
    pub path: String,
    pub alias: Option<String>,
    pub span: Span,
}

#[derive(Clone)]
pub struct SystemBlock {
    pub name: String,
    pub decls: Vec<Spanned<DeclKind>>,
}

// ── Declarations ─────────────────────────────────────────────────

#[derive(Clone)]
pub enum DeclKind {
    Enum(EnumDecl),
    Struct(StructDecl),
    Entity(EntityDecl),
    Derive(FnDecl),
    Mechanic(FnDecl),
    Action(ActionDecl),
    Reaction(ReactionDecl),
    Hook(HookDecl),
    Condition(ConditionDecl),
    Prompt(PromptDecl),
    Option(OptionDecl),
    Event(EventDecl),
    Move(MoveDecl),
    Table(TableDecl),
}

#[derive(Clone)]
pub struct EnumDecl {
    pub name: String,
    pub ordered: bool,
    pub variants: Vec<EnumVariant>,
}

#[derive(Clone)]
pub struct EnumVariant {
    pub name: String,
    pub fields: Option<Vec<FieldEntry>>,
    pub span: Span,
}

/// Inline field in enum variant or param list: `name: type`
#[derive(Clone)]
pub struct FieldEntry {
    pub name: String,
    pub ty: Spanned<TypeExpr>,
    pub span: Span,
}

#[derive(Clone)]
pub struct StructDecl {
    pub name: String,
    pub fields: Vec<FieldDef>,
}

#[derive(Clone)]
pub struct EntityDecl {
    pub name: String,
    pub fields: Vec<FieldDef>,
    pub optional_groups: Vec<OptionalGroup>,
}

/// An optional field group declared inside an entity with `optional GroupName { ... }`.
/// Groups can be granted/revoked at runtime; fields are only accessible when active.
#[derive(Clone)]
pub struct OptionalGroup {
    pub name: String,
    pub fields: Vec<FieldDef>,
    pub span: Span,
}

/// Field definition with optional default: `name: type (= expr)?`
#[derive(Clone)]
pub struct FieldDef {
    pub name: String,
    pub ty: Spanned<TypeExpr>,
    pub default: Option<Spanned<ExprKind>>,
    pub span: Span,
}

/// Shared representation for derive and mechanic declarations.
#[derive(Clone)]
pub struct FnDecl {
    pub name: String,
    pub params: Vec<Param>,
    pub return_type: Spanned<TypeExpr>,
    pub body: Block,
    /// True for declarations synthesized by `lower_moves` (e.g., `__{move}_roll`).
    /// Parser always sets this to `false`.
    pub synthetic: bool,
}

#[derive(Clone)]
pub struct Param {
    pub name: String,
    pub ty: Spanned<TypeExpr>,
    pub default: Option<Spanned<ExprKind>>,
    /// Optional group constraints: `param: Entity with Group1, Group2`.
    /// The checker narrows these groups as active within the function body.
    pub with_groups: Vec<String>,
    pub span: Span,
}

#[derive(Clone)]
pub struct ActionDecl {
    pub name: String,
    pub receiver_name: String,
    pub receiver_type: Spanned<TypeExpr>,
    /// Optional group constraints on the receiver: `on actor: Entity with Group1, Group2`.
    pub receiver_with_groups: Vec<String>,
    pub params: Vec<Param>,
    pub cost: Option<CostClause>,
    pub requires: Option<Spanned<ExprKind>>,
    pub resolve: Block,
    /// Preserved from the originating move declaration's trigger string.
    /// `None` for user-written actions, `Some(...)` for actions synthesized from moves.
    pub trigger_text: Option<String>,
    /// True for actions synthesized by `lower_moves`.
    /// Parser always sets this to `false`.
    pub synthetic: bool,
}

#[derive(Clone)]
pub struct CostClause {
    pub tokens: Vec<Spanned<String>>,
    pub span: Span,
}

#[derive(Clone)]
pub struct ReactionDecl {
    pub name: String,
    pub receiver_name: String,
    pub receiver_type: Spanned<TypeExpr>,
    /// Optional group constraints on the receiver: `on reactor: Entity with Group`.
    pub receiver_with_groups: Vec<String>,
    pub trigger: TriggerExpr,
    pub cost: Option<CostClause>,
    pub resolve: Block,
}

#[derive(Clone)]
pub struct HookDecl {
    pub name: String,
    pub receiver_name: String,
    pub receiver_type: Spanned<TypeExpr>,
    /// Optional group constraints on the receiver: `on target: Entity with Group`.
    pub receiver_with_groups: Vec<String>,
    pub trigger: TriggerExpr,
    pub resolve: Block,
}

#[derive(Clone)]
pub struct TriggerExpr {
    pub event_name: String,
    pub bindings: Vec<TriggerBinding>,
    pub span: Span,
}

#[derive(Clone)]
pub struct TriggerBinding {
    pub name: Option<String>,
    pub value: Spanned<ExprKind>,
    pub span: Span,
}

#[derive(Clone)]
pub struct EventDecl {
    pub name: String,
    pub params: Vec<Param>,
    pub fields: Vec<FieldDef>,
}

#[derive(Clone)]
pub struct ConditionDecl {
    pub name: String,
    /// Optional parameters: `condition Frightened(source: Character) on ...`.
    /// Empty vec means no parameters.
    pub params: Vec<Param>,
    pub receiver_name: String,
    pub receiver_type: Spanned<TypeExpr>,
    /// Optional group constraints on the bearer: `on bearer: Entity with Group`.
    pub receiver_with_groups: Vec<String>,
    pub clauses: Vec<ConditionClause>,
}

#[derive(Clone)]
pub enum ConditionClause {
    Modify(ModifyClause),
    Suppress(SuppressClause),
}

#[derive(Clone)]
pub struct ModifyClause {
    pub target: String,
    pub bindings: Vec<ModifyBinding>,
    pub body: Vec<ModifyStmt>,
    pub span: Span,
}

#[derive(Clone)]
pub struct ModifyBinding {
    pub name: String,
    /// `None` means wildcard (`_`) — matches any value.
    pub value: Option<Spanned<ExprKind>>,
    pub span: Span,
}

#[derive(Clone)]
pub enum ModifyStmt {
    Let {
        name: String,
        ty: Option<Spanned<TypeExpr>>,
        value: Spanned<ExprKind>,
        span: Span,
    },
    ParamOverride {
        name: String,
        value: Spanned<ExprKind>,
        span: Span,
    },
    ResultOverride {
        field: String,
        value: Spanned<ExprKind>,
        span: Span,
    },
    If {
        condition: Spanned<ExprKind>,
        then_body: Vec<ModifyStmt>,
        else_body: Option<Vec<ModifyStmt>>,
        span: Span,
    },
}

#[derive(Clone)]
pub struct SuppressClause {
    pub event_name: String,
    pub bindings: Vec<ModifyBinding>,
    pub span: Span,
}

#[derive(Clone)]
pub struct PromptDecl {
    pub name: String,
    pub params: Vec<Param>,
    pub return_type: Spanned<TypeExpr>,
    pub hint: Option<String>,
    pub suggest: Option<Spanned<ExprKind>>,
}

#[derive(Clone)]
pub struct OptionDecl {
    pub name: String,
    pub extends: Option<String>,
    pub description: Option<String>,
    pub default_on: Option<bool>,
    pub when_enabled: Option<Vec<ModifyClause>>,
}

#[derive(Clone)]
pub struct MoveDecl {
    pub name: String,
    pub receiver_name: String,
    pub receiver_type: Spanned<TypeExpr>,
    pub params: Vec<Param>,
    pub trigger_text: String,
    pub roll_expr: Spanned<ExprKind>,
    pub outcomes: Vec<OutcomeBlock>,
}

#[derive(Clone)]
pub struct OutcomeBlock {
    pub name: String,
    pub body: Block,
    pub span: Span,
}

/// A `table` declaration: static lookup function with compact syntax.
///
/// Syntax:
///   table name(key1: Type1, key2: Type2) -> ReturnType {
///       [key1_val, key2_val] => return_val,
///       [key1_val, range]    => return_val,
///       ...
///   }
///
/// For single-key tables:
///   table name(key: Type) -> ReturnType {
///       key_val => return_val,
///       ...
///   }
///
/// Tables are registered as callable functions (like derives), invoked as:
///   let val = name(arg1, arg2)
#[derive(Clone)]
pub struct TableDecl {
    pub name: String,
    pub params: Vec<Param>,
    pub return_type: Spanned<TypeExpr>,
    pub entries: Vec<TableEntry>,
}

/// A single entry in a table: keys => value.
#[derive(Clone)]
pub struct TableEntry {
    pub keys: Vec<Spanned<TableKey>>,
    pub value: Spanned<ExprKind>,
    pub span: Span,
}

/// A key in a table entry — can be a literal, enum variant, range, or wildcard.
#[derive(Clone)]
pub enum TableKey {
    /// An expression used as a key (int literal, string literal, enum variant, etc.)
    Expr(ExprKind),
    /// An inclusive range: `1..=3`
    Range {
        start: Box<Spanned<ExprKind>>,
        end: Box<Spanned<ExprKind>>,
    },
    /// Wildcard `_` — matches anything (must be the last entry).
    Wildcard,
}

// ── Types ────────────────────────────────────────────────────────

#[derive(Clone)]
pub enum TypeExpr {
    Int,
    Bool,
    String,
    Float,
    DiceExpr,
    RollResult,
    TurnBudget,
    Duration,
    Position,
    Condition,
    Named(std::string::String),
    Qualified { qualifier: String, name: String },
    Map(Box<Spanned<TypeExpr>>, Box<Spanned<TypeExpr>>),
    List(Box<Spanned<TypeExpr>>),
    Set(Box<Spanned<TypeExpr>>),
    OptionType(Box<Spanned<TypeExpr>>),
    Resource(Box<Spanned<ExprKind>>, Box<Spanned<ExprKind>>),
}

// ── Expressions ──────────────────────────────────────────────────

pub type Block = Spanned<Vec<Spanned<StmtKind>>>;

#[derive(Clone)]
pub enum ExprKind {
    IntLit(i64),
    StringLit(std::string::String),
    BoolLit(bool),
    NoneLit,
    DiceLit {
        count: u32,
        sides: u32,
        filter: Option<DiceFilter>,
    },
    Ident(std::string::String),
    BinOp {
        op: BinOp,
        lhs: Box<Spanned<ExprKind>>,
        rhs: Box<Spanned<ExprKind>>,
    },
    UnaryOp {
        op: UnaryOp,
        operand: Box<Spanned<ExprKind>>,
    },
    FieldAccess {
        object: Box<Spanned<ExprKind>>,
        field: std::string::String,
    },
    Index {
        object: Box<Spanned<ExprKind>>,
        index: Box<Spanned<ExprKind>>,
    },
    Call {
        callee: Box<Spanned<ExprKind>>,
        args: Vec<Arg>,
    },
    StructLit {
        name: std::string::String,
        fields: Vec<StructFieldInit>,
        base: Option<Box<Spanned<ExprKind>>>,
    },
    ListLit(Vec<Spanned<ExprKind>>),
    Paren(Box<Spanned<ExprKind>>),
    If {
        condition: Box<Spanned<ExprKind>>,
        then_block: Block,
        else_branch: Option<ElseBranch>,
    },
    IfLet {
        pattern: Box<Spanned<PatternKind>>,
        scrutinee: Box<Spanned<ExprKind>>,
        then_block: Block,
        else_branch: Option<ElseBranch>,
    },
    PatternMatch {
        scrutinee: Box<Spanned<ExprKind>>,
        arms: Vec<PatternArm>,
    },
    GuardMatch {
        arms: Vec<GuardArm>,
    },
    For {
        pattern: Box<Spanned<PatternKind>>,
        iterable: ForIterable,
        body: Block,
    },
    /// `entity has GroupName` — tests whether an optional group is active.
    /// Produces a bool and enables flow-sensitive type narrowing.
    Has {
        entity: Box<Spanned<ExprKind>>,
        group_name: String,
    },
}

#[derive(Clone)]
pub enum ForIterable {
    Collection(Box<Spanned<ExprKind>>),
    Range {
        start: Box<Spanned<ExprKind>>,
        end: Box<Spanned<ExprKind>>,
        inclusive: bool,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    And,
    Or,
    Eq,
    NotEq,
    Lt,
    Gt,
    LtEq,
    GtEq,
    In,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,
    Not,
}

#[derive(Clone)]
pub struct Arg {
    pub name: Option<std::string::String>,
    pub value: Spanned<ExprKind>,
    pub span: Span,
}

#[derive(Clone)]
pub struct StructFieldInit {
    pub name: std::string::String,
    pub value: Spanned<ExprKind>,
    pub span: Span,
}

#[derive(Clone)]
pub enum ElseBranch {
    Block(Block),
    If(Box<Spanned<ExprKind>>),
}

#[derive(Clone)]
pub struct PatternArm {
    pub pattern: Spanned<PatternKind>,
    pub body: ArmBody,
    pub span: Span,
}

#[derive(Clone)]
pub struct GuardArm {
    pub guard: GuardKind,
    pub body: ArmBody,
    pub span: Span,
}

#[derive(Clone)]
pub enum GuardKind {
    Wildcard,
    Expr(Spanned<ExprKind>),
}

#[derive(Clone)]
pub enum ArmBody {
    Expr(Spanned<ExprKind>),
    Block(Block),
}

// ── Patterns ─────────────────────────────────────────────────────

#[derive(Clone)]
pub enum PatternKind {
    Wildcard,
    IntLit(i64),
    StringLit(std::string::String),
    BoolLit(bool),
    Ident(std::string::String),
    QualifiedVariant {
        ty: std::string::String,
        variant: std::string::String,
    },
    QualifiedDestructure {
        ty: std::string::String,
        variant: std::string::String,
        fields: Vec<Spanned<PatternKind>>,
    },
    BareDestructure {
        name: std::string::String,
        fields: Vec<Spanned<PatternKind>>,
    },
    NoneLit,
    Some(Box<Spanned<PatternKind>>),
}

// ── Statements ───────────────────────────────────────────────────

#[derive(Clone)]
pub enum StmtKind {
    Let {
        name: std::string::String,
        ty: Option<Spanned<TypeExpr>>,
        value: Spanned<ExprKind>,
    },
    Assign {
        target: LValue,
        op: AssignOp,
        value: Spanned<ExprKind>,
    },
    Expr(Spanned<ExprKind>),
    /// `grant entity.GroupName { field: value, ... }` — activates an optional group.
    Grant {
        entity: Box<Spanned<ExprKind>>,
        group_name: String,
        fields: Vec<StructFieldInit>,
    },
    /// `revoke entity.GroupName` — deactivates an optional group, discarding field values.
    Revoke {
        entity: Box<Spanned<ExprKind>>,
        group_name: String,
    },
}

#[derive(Clone)]
pub struct LValue {
    pub root: std::string::String,
    pub segments: Vec<LValueSegment>,
    pub span: Span,
}

#[derive(Clone)]
pub enum LValueSegment {
    Field(std::string::String),
    Index(Spanned<ExprKind>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssignOp {
    Eq,
    PlusEq,
    MinusEq,
}
