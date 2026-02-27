use std::collections::{HashMap, HashSet};

use crate::name::Name;
use crate::{DiceFilter, Span, Spanned};

// ── Program structure ────────────────────────────────────────────

#[derive(Clone, Default)]
pub struct Program {
    pub items: Vec<Spanned<TopLevel>>,

    // ── Declaration index (built by `build_index()`) ────────────
    pub actions: HashMap<Name, ActionDecl>,
    pub derives: HashMap<Name, FnDecl>,
    pub mechanics: HashMap<Name, FnDecl>,
    pub reactions: HashMap<Name, ReactionDecl>,
    pub reaction_order: Vec<Name>,
    pub conditions: HashMap<Name, ConditionDecl>,
    pub events: HashMap<Name, EventDecl>,
    pub prompts: HashMap<Name, PromptDecl>,
    pub options: HashMap<Name, OptionDecl>,
    pub option_order: Vec<Name>,
    pub hooks: HashMap<Name, HookDecl>,
    pub hook_order: Vec<Name>,
    pub tables: HashMap<Name, TableDecl>,
    pub tags: HashSet<Name>,
    pub next_modify_clause_id: u32,
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
        self.tags.clear();
        self.next_modify_clause_id = 0;

        for item in &mut self.items {
            if let TopLevel::System(system) = &mut item.node {
                for decl in &mut system.decls {
                    match &mut decl.node {
                        DeclKind::Group(_) => {}
                        DeclKind::Tag(t) => {
                            self.tags.insert(t.name.clone());
                        }
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
                            // Assign ModifyClauseIds to condition modify clauses
                            for clause in &mut c.clauses {
                                if let ConditionClause::Modify(m) = clause {
                                    m.id = ModifyClauseId(self.next_modify_clause_id);
                                    self.next_modify_clause_id += 1;
                                }
                            }
                            self.conditions.insert(c.name.clone(), c.clone());
                        }
                        DeclKind::Event(e) => {
                            self.events.insert(e.name.clone(), e.clone());
                        }
                        DeclKind::Prompt(p) => {
                            self.prompts.insert(p.name.clone(), p.clone());
                        }
                        DeclKind::Option(o) => {
                            // Assign ModifyClauseIds to option modify clauses
                            if let Some(ref mut clauses) = o.when_enabled {
                                for m in clauses {
                                    m.id = ModifyClauseId(self.next_modify_clause_id);
                                    self.next_modify_clause_id += 1;
                                }
                            }
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
    pub alias: Option<Name>,
    pub span: Span,
}

#[derive(Clone)]
pub struct SystemBlock {
    pub name: Name,
    pub decls: Vec<Spanned<DeclKind>>,
}

// ── Declarations ─────────────────────────────────────────────────

#[derive(Clone)]
pub enum DeclKind {
    Group(GroupDecl),
    Tag(TagDecl),
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
    Unit(UnitDecl),
}

#[derive(Clone)]
pub struct TagDecl {
    pub name: Name,
}

/// Stable identity for a modify clause, assigned during `build_index()`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ModifyClauseId(pub u32);

/// What a modify clause targets: a specific function or a selector.
#[derive(Clone)]
pub enum ModifyTarget {
    Named(Name),
    Selector(Vec<SelectorPredicate>),
}

/// A predicate in a selector expression.
#[derive(Clone)]
pub enum SelectorPredicate {
    Tag(Name),
    Returns(Spanned<TypeExpr>),
    HasParam { name: Name, ty: Option<Spanned<TypeExpr>> },
}

#[derive(Clone)]
pub struct GroupDecl {
    pub name: Name,
    pub fields: Vec<FieldDef>,
}

#[derive(Clone)]
pub struct EnumDecl {
    pub name: Name,
    pub ordered: bool,
    pub variants: Vec<EnumVariant>,
}

#[derive(Clone)]
pub struct EnumVariant {
    pub name: Name,
    pub fields: Option<Vec<FieldEntry>>,
    pub span: Span,
}

/// Inline field in enum variant or param list: `name: type`
#[derive(Clone)]
pub struct FieldEntry {
    pub name: Name,
    pub ty: Spanned<TypeExpr>,
    pub span: Span,
}

#[derive(Clone)]
pub struct StructDecl {
    pub name: Name,
    pub fields: Vec<FieldDef>,
}

#[derive(Clone)]
pub struct EntityDecl {
    pub name: Name,
    pub fields: Vec<FieldDef>,
    /// Group attachments on the entity:
    /// - `optional GroupName { ... }` / `optional GroupName`
    /// - `include GroupName` (required, always present)
    pub optional_groups: Vec<OptionalGroup>,
}

/// A group attachment declared inside an entity.
///
/// Forms:
/// - `optional GroupName { ... }` (inline optional schema)
/// - `optional GroupName` (external optional schema)
/// - `include GroupName` (external required schema)
#[derive(Clone)]
pub struct OptionalGroup {
    pub name: Name,
    pub fields: Vec<FieldDef>,
    /// True when declared as `optional GroupName` (attached external group),
    /// false when declared inline as `optional GroupName { ... }`.
    pub is_external_ref: bool,
    /// True when declared as `include GroupName` (required group).
    pub is_required: bool,
    pub span: Span,
}

/// Field definition with optional default: `name: type (= expr)?`
#[derive(Clone)]
pub struct FieldDef {
    pub name: Name,
    pub ty: Spanned<TypeExpr>,
    pub default: Option<Spanned<ExprKind>>,
    pub span: Span,
}

/// A group constraint with optional alias: `Group` or `Group as alias`.
#[derive(Debug, Clone, PartialEq)]
pub struct GroupConstraint {
    pub name: Name,
    pub alias: Option<Name>,
}

/// Shared representation for derive and mechanic declarations.
#[derive(Clone)]
pub struct FnDecl {
    pub name: Name,
    pub params: Vec<Param>,
    pub return_type: Spanned<TypeExpr>,
    pub body: Block,
    /// True for declarations synthesized by `lower_moves` (e.g., `__{move}_roll`).
    /// Parser always sets this to `false`.
    pub synthetic: bool,
    /// Tags applied to this function (e.g., `#attack #ranged`).
    pub tags: Vec<Name>,
}

#[derive(Clone)]
pub struct Param {
    pub name: Name,
    pub ty: Spanned<TypeExpr>,
    pub default: Option<Spanned<ExprKind>>,
    /// Optional group constraints: `param: Entity with Group1, Group2`.
    /// The checker narrows these groups as active within the function body.
    pub with_groups: Vec<GroupConstraint>,
    pub span: Span,
}

#[derive(Clone)]
pub struct ActionDecl {
    pub name: Name,
    pub receiver_name: Name,
    pub receiver_type: Spanned<TypeExpr>,
    /// Optional group constraints on the receiver: `on actor: Entity with Group1, Group2`.
    pub receiver_with_groups: Vec<GroupConstraint>,
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
    pub tokens: Vec<Spanned<Name>>,
    pub span: Span,
}

#[derive(Clone)]
pub struct ReactionDecl {
    pub name: Name,
    pub receiver_name: Name,
    pub receiver_type: Spanned<TypeExpr>,
    /// Optional group constraints on the receiver: `on reactor: Entity with Group`.
    pub receiver_with_groups: Vec<GroupConstraint>,
    pub trigger: TriggerExpr,
    pub cost: Option<CostClause>,
    pub resolve: Block,
}

#[derive(Clone)]
pub struct HookDecl {
    pub name: Name,
    pub receiver_name: Name,
    pub receiver_type: Spanned<TypeExpr>,
    /// Optional group constraints on the receiver: `on target: Entity with Group`.
    pub receiver_with_groups: Vec<GroupConstraint>,
    pub trigger: TriggerExpr,
    pub resolve: Block,
}

#[derive(Clone)]
pub struct TriggerExpr {
    pub event_name: Name,
    pub bindings: Vec<TriggerBinding>,
    pub span: Span,
}

#[derive(Clone)]
pub struct TriggerBinding {
    pub name: Option<Name>,
    pub value: Spanned<ExprKind>,
    pub span: Span,
}

#[derive(Clone)]
pub struct EventDecl {
    pub name: Name,
    pub params: Vec<Param>,
    pub fields: Vec<FieldDef>,
}

#[derive(Clone)]
pub struct ConditionDecl {
    pub name: Name,
    /// Optional parameters: `condition Frightened(source: Character) on ...`.
    /// Empty vec means no parameters.
    pub params: Vec<Param>,
    pub receiver_name: Name,
    pub receiver_type: Spanned<TypeExpr>,
    /// Optional group constraints on the bearer: `on bearer: Entity with Group`.
    pub receiver_with_groups: Vec<GroupConstraint>,
    pub clauses: Vec<ConditionClause>,
}

#[derive(Clone)]
pub enum ConditionClause {
    Modify(ModifyClause),
    Suppress(SuppressClause),
}

#[derive(Clone)]
pub struct ModifyClause {
    pub target: ModifyTarget,
    pub bindings: Vec<ModifyBinding>,
    pub body: Vec<ModifyStmt>,
    pub span: Span,
    /// Stable clause identity, assigned during `build_index()`.
    pub id: ModifyClauseId,
}

#[derive(Clone)]
pub struct ModifyBinding {
    pub name: Name,
    /// `None` means wildcard (`_`) — matches any value.
    pub value: Option<Spanned<ExprKind>>,
    pub span: Span,
}

#[derive(Clone)]
pub enum ModifyStmt {
    Let {
        name: Name,
        ty: Option<Spanned<TypeExpr>>,
        value: Spanned<ExprKind>,
        span: Span,
    },
    ParamOverride {
        name: Name,
        value: Spanned<ExprKind>,
        span: Span,
    },
    ResultOverride {
        field: Name,
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
    pub event_name: Name,
    pub bindings: Vec<ModifyBinding>,
    pub span: Span,
}

#[derive(Clone)]
pub struct PromptDecl {
    pub name: Name,
    pub params: Vec<Param>,
    pub return_type: Spanned<TypeExpr>,
    pub hint: Option<String>,
    pub suggest: Option<Spanned<ExprKind>>,
}

#[derive(Clone)]
pub struct OptionDecl {
    pub name: Name,
    pub extends: Option<Name>,
    pub description: Option<String>,
    pub default_on: Option<bool>,
    pub when_enabled: Option<Vec<ModifyClause>>,
}

#[derive(Clone)]
pub struct MoveDecl {
    pub name: Name,
    pub receiver_name: Name,
    pub receiver_type: Spanned<TypeExpr>,
    pub params: Vec<Param>,
    pub trigger_text: String,
    pub roll_expr: Spanned<ExprKind>,
    pub outcomes: Vec<OutcomeBlock>,
}

#[derive(Clone)]
pub struct OutcomeBlock {
    pub name: Name,
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
    pub name: Name,
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

/// A `unit` declaration: dimensioned numeric type with optional suffix.
#[derive(Clone)]
pub struct UnitDecl {
    pub name: Name,
    pub suffix: Option<String>,
    pub fields: Vec<FieldDef>,
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
    Named(Name),
    Qualified { qualifier: Name, name: Name },
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
    UnitLit {
        value: i64,
        suffix: std::string::String,
    },
    Ident(Name),
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
        field: Name,
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
        name: Name,
        fields: Vec<StructFieldInit>,
        base: Option<Box<Spanned<ExprKind>>>,
    },
    ListLit(Vec<Spanned<ExprKind>>),
    MapLit(Vec<(Spanned<ExprKind>, Spanned<ExprKind>)>),
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
    ListComprehension {
        element: Box<Spanned<ExprKind>>,
        pattern: Box<Spanned<PatternKind>>,
        iterable: ForIterable,
        filter: Option<Box<Spanned<ExprKind>>>,
    },
    /// `entity has GroupName` — tests whether an optional group is active.
    /// Produces a bool and enables flow-sensitive type narrowing.
    /// Optional alias: `entity has GroupName as alias`.
    Has {
        entity: Box<Spanned<ExprKind>>,
        group_name: Name,
        alias: Option<Name>,
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
    pub name: Option<Name>,
    pub value: Spanned<ExprKind>,
    pub span: Span,
}

#[derive(Clone)]
pub struct StructFieldInit {
    pub name: Name,
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
    Ident(Name),
    QualifiedVariant {
        ty: Name,
        variant: Name,
    },
    QualifiedDestructure {
        ty: Name,
        variant: Name,
        fields: Vec<Spanned<PatternKind>>,
    },
    BareDestructure {
        name: Name,
        fields: Vec<Spanned<PatternKind>>,
    },
    NoneLit,
    Some(Box<Spanned<PatternKind>>),
}

// ── Statements ───────────────────────────────────────────────────

#[derive(Clone)]
pub enum StmtKind {
    Let {
        name: Name,
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
        group_name: Name,
        fields: Vec<StructFieldInit>,
    },
    /// `revoke entity.GroupName` — deactivates an optional group, discarding field values.
    Revoke {
        entity: Box<Spanned<ExprKind>>,
        group_name: Name,
    },
}

#[derive(Clone)]
pub struct LValue {
    pub root: Name,
    pub segments: Vec<LValueSegment>,
    pub span: Span,
}

#[derive(Clone)]
pub enum LValueSegment {
    Field(Name),
    Index(Spanned<ExprKind>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssignOp {
    Eq,
    PlusEq,
    MinusEq,
}
