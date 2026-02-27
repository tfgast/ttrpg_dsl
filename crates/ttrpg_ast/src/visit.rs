use crate::ast::*;
use crate::name::Name;
use crate::{Span, Spanned};

/// Trait for recursively visiting and mutating every [`Span`] inside an AST node.
///
/// Used for span rebasing (adding a base offset to every span in a parsed program)
/// and any future span-rewriting passes.  Implementations are exhaustive over
/// struct fields and enum variants so the compiler catches new additions.
pub trait VisitSpansMut {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span));
}

// ── Core / blanket impls ─────────────────────────────────────────

impl VisitSpansMut for Span {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        f(self);
    }
}

impl<T: VisitSpansMut> VisitSpansMut for Spanned<T> {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        self.span.visit_spans_mut(f);
        self.node.visit_spans_mut(f);
    }
}

impl<T: VisitSpansMut> VisitSpansMut for Vec<T> {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        for item in self {
            item.visit_spans_mut(f);
        }
    }
}

impl<T: VisitSpansMut> VisitSpansMut for Option<T> {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        if let Some(inner) = self {
            inner.visit_spans_mut(f);
        }
    }
}

impl<T: VisitSpansMut> VisitSpansMut for Box<T> {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        (**self).visit_spans_mut(f);
    }
}

impl VisitSpansMut for String {
    fn visit_spans_mut(&mut self, _f: &mut dyn FnMut(&mut Span)) {}
}

impl VisitSpansMut for Name {
    fn visit_spans_mut(&mut self, _f: &mut dyn FnMut(&mut Span)) {}
}

// ── Program ──────────────────────────────────────────────────────

impl VisitSpansMut for Program {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        // Only visit items — index maps are rebuilt by build_index().
        self.items.visit_spans_mut(f);
    }
}

impl VisitSpansMut for TopLevel {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        match self {
            TopLevel::Use(u) => u.visit_spans_mut(f),
            TopLevel::System(s) => s.visit_spans_mut(f),
        }
    }
}

impl VisitSpansMut for UseDecl {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        self.span.visit_spans_mut(f);
    }
}

impl VisitSpansMut for SystemBlock {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        self.decls.visit_spans_mut(f);
    }
}

// ── Declarations ─────────────────────────────────────────────────

impl VisitSpansMut for DeclKind {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        match self {
            DeclKind::Group(g) => g.visit_spans_mut(f),
            DeclKind::Tag(_) => {} // TagDecl has no spans
            DeclKind::Enum(e) => e.visit_spans_mut(f),
            DeclKind::Struct(s) => s.visit_spans_mut(f),
            DeclKind::Entity(e) => e.visit_spans_mut(f),
            DeclKind::Derive(d) | DeclKind::Mechanic(d) => d.visit_spans_mut(f),
            DeclKind::Action(a) => a.visit_spans_mut(f),
            DeclKind::Reaction(r) => r.visit_spans_mut(f),
            DeclKind::Hook(h) => h.visit_spans_mut(f),
            DeclKind::Condition(c) => c.visit_spans_mut(f),
            DeclKind::Prompt(p) => p.visit_spans_mut(f),
            DeclKind::Option(o) => o.visit_spans_mut(f),
            DeclKind::Event(e) => e.visit_spans_mut(f),
            DeclKind::Move(m) => m.visit_spans_mut(f),
            DeclKind::Table(t) => t.visit_spans_mut(f),
            DeclKind::Unit(u) => u.visit_spans_mut(f),
        }
    }
}

impl VisitSpansMut for GroupDecl {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        self.fields.visit_spans_mut(f);
    }
}

impl VisitSpansMut for EnumDecl {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        self.variants.visit_spans_mut(f);
    }
}

impl VisitSpansMut for EnumVariant {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        self.span.visit_spans_mut(f);
        self.fields.visit_spans_mut(f);
    }
}

impl VisitSpansMut for FieldEntry {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        self.span.visit_spans_mut(f);
        self.ty.visit_spans_mut(f);
    }
}

impl VisitSpansMut for StructDecl {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        self.fields.visit_spans_mut(f);
    }
}

impl VisitSpansMut for EntityDecl {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        self.fields.visit_spans_mut(f);
        self.optional_groups.visit_spans_mut(f);
    }
}

impl VisitSpansMut for OptionalGroup {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        self.span.visit_spans_mut(f);
        self.fields.visit_spans_mut(f);
    }
}

impl VisitSpansMut for FieldDef {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        self.span.visit_spans_mut(f);
        self.ty.visit_spans_mut(f);
        self.default.visit_spans_mut(f);
    }
}

impl VisitSpansMut for FnDecl {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        self.params.visit_spans_mut(f);
        self.return_type.visit_spans_mut(f);
        self.body.visit_spans_mut(f);
    }
}

impl VisitSpansMut for Param {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        self.span.visit_spans_mut(f);
        self.ty.visit_spans_mut(f);
        self.default.visit_spans_mut(f);
    }
}

impl VisitSpansMut for ActionDecl {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        self.receiver_type.visit_spans_mut(f);
        self.params.visit_spans_mut(f);
        self.cost.visit_spans_mut(f);
        self.requires.visit_spans_mut(f);
        self.resolve.visit_spans_mut(f);
    }
}

impl VisitSpansMut for CostClause {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        self.span.visit_spans_mut(f);
        self.tokens.visit_spans_mut(f);
    }
}

impl VisitSpansMut for ReactionDecl {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        self.receiver_type.visit_spans_mut(f);
        self.trigger.visit_spans_mut(f);
        self.cost.visit_spans_mut(f);
        self.resolve.visit_spans_mut(f);
    }
}

impl VisitSpansMut for HookDecl {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        self.receiver_type.visit_spans_mut(f);
        self.trigger.visit_spans_mut(f);
        self.resolve.visit_spans_mut(f);
    }
}

impl VisitSpansMut for TriggerExpr {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        self.span.visit_spans_mut(f);
        self.bindings.visit_spans_mut(f);
    }
}

impl VisitSpansMut for TriggerBinding {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        self.span.visit_spans_mut(f);
        self.value.visit_spans_mut(f);
    }
}

impl VisitSpansMut for EventDecl {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        self.params.visit_spans_mut(f);
        self.fields.visit_spans_mut(f);
    }
}

impl VisitSpansMut for ConditionDecl {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        self.params.visit_spans_mut(f);
        self.receiver_type.visit_spans_mut(f);
        self.clauses.visit_spans_mut(f);
    }
}

impl VisitSpansMut for ConditionClause {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        match self {
            ConditionClause::Modify(m) => m.visit_spans_mut(f),
            ConditionClause::Suppress(s) => s.visit_spans_mut(f),
        }
    }
}

impl VisitSpansMut for ModifyClause {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        self.span.visit_spans_mut(f);
        self.target.visit_spans_mut(f);
        self.bindings.visit_spans_mut(f);
        self.body.visit_spans_mut(f);
    }
}

impl VisitSpansMut for ModifyTarget {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        match self {
            ModifyTarget::Named(_) => {}
            ModifyTarget::Selector(preds) => preds.visit_spans_mut(f),
        }
    }
}

impl VisitSpansMut for SelectorPredicate {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        match self {
            SelectorPredicate::Tag(_) => {}
            SelectorPredicate::Returns(ty) => ty.visit_spans_mut(f),
            SelectorPredicate::HasParam { ty, .. } => ty.visit_spans_mut(f),
        }
    }
}

impl VisitSpansMut for ModifyBinding {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        self.span.visit_spans_mut(f);
        self.value.visit_spans_mut(f);
    }
}

impl VisitSpansMut for ModifyStmt {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        match self {
            ModifyStmt::Let {
                ty, value, span, ..
            } => {
                span.visit_spans_mut(f);
                ty.visit_spans_mut(f);
                value.visit_spans_mut(f);
            }
            ModifyStmt::ParamOverride { value, span, .. } => {
                span.visit_spans_mut(f);
                value.visit_spans_mut(f);
            }
            ModifyStmt::ResultOverride { value, span, .. } => {
                span.visit_spans_mut(f);
                value.visit_spans_mut(f);
            }
            ModifyStmt::If {
                condition,
                then_body,
                else_body,
                span,
            } => {
                span.visit_spans_mut(f);
                condition.visit_spans_mut(f);
                then_body.visit_spans_mut(f);
                else_body.visit_spans_mut(f);
            }
        }
    }
}

impl VisitSpansMut for SuppressClause {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        self.span.visit_spans_mut(f);
        self.bindings.visit_spans_mut(f);
    }
}

impl VisitSpansMut for PromptDecl {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        self.params.visit_spans_mut(f);
        self.return_type.visit_spans_mut(f);
        self.suggest.visit_spans_mut(f);
    }
}

impl VisitSpansMut for OptionDecl {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        self.when_enabled.visit_spans_mut(f);
    }
}

impl VisitSpansMut for MoveDecl {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        self.receiver_type.visit_spans_mut(f);
        self.params.visit_spans_mut(f);
        self.roll_expr.visit_spans_mut(f);
        self.outcomes.visit_spans_mut(f);
    }
}

impl VisitSpansMut for OutcomeBlock {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        self.span.visit_spans_mut(f);
        self.body.visit_spans_mut(f);
    }
}

impl VisitSpansMut for TableDecl {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        self.params.visit_spans_mut(f);
        self.return_type.visit_spans_mut(f);
        self.entries.visit_spans_mut(f);
    }
}

impl VisitSpansMut for TableEntry {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        self.span.visit_spans_mut(f);
        self.keys.visit_spans_mut(f);
        self.value.visit_spans_mut(f);
    }
}

impl VisitSpansMut for TableKey {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        match self {
            TableKey::Expr(e) => e.visit_spans_mut(f),
            TableKey::Range { start, end } => {
                start.visit_spans_mut(f);
                end.visit_spans_mut(f);
            }
            TableKey::Wildcard => {}
        }
    }
}

impl VisitSpansMut for UnitDecl {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        self.fields.visit_spans_mut(f);
    }
}

// ── Types ────────────────────────────────────────────────────────

impl VisitSpansMut for TypeExpr {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        match self {
            TypeExpr::Int
            | TypeExpr::Bool
            | TypeExpr::String
            | TypeExpr::Float
            | TypeExpr::DiceExpr
            | TypeExpr::RollResult
            | TypeExpr::TurnBudget
            | TypeExpr::Duration
            | TypeExpr::Position
            | TypeExpr::Condition
            | TypeExpr::Named(_)
            | TypeExpr::Qualified { .. } => {}
            TypeExpr::List(inner) | TypeExpr::Set(inner) | TypeExpr::OptionType(inner) => {
                inner.visit_spans_mut(f);
            }
            TypeExpr::Map(k, v) => {
                k.visit_spans_mut(f);
                v.visit_spans_mut(f);
            }
            TypeExpr::Resource(lo, hi) => {
                lo.visit_spans_mut(f);
                hi.visit_spans_mut(f);
            }
        }
    }
}

// ── Expressions ──────────────────────────────────────────────────

impl VisitSpansMut for ExprKind {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        match self {
            ExprKind::IntLit(_)
            | ExprKind::StringLit(_)
            | ExprKind::BoolLit(_)
            | ExprKind::NoneLit
            | ExprKind::DiceLit { .. }
            | ExprKind::UnitLit { .. }
            | ExprKind::Ident(_) => {}
            ExprKind::BinOp { lhs, rhs, .. } => {
                lhs.visit_spans_mut(f);
                rhs.visit_spans_mut(f);
            }
            ExprKind::UnaryOp { operand, .. } => {
                operand.visit_spans_mut(f);
            }
            ExprKind::FieldAccess { object, .. } => {
                object.visit_spans_mut(f);
            }
            ExprKind::Index { object, index } => {
                object.visit_spans_mut(f);
                index.visit_spans_mut(f);
            }
            ExprKind::Call { callee, args } => {
                callee.visit_spans_mut(f);
                args.visit_spans_mut(f);
            }
            ExprKind::StructLit { fields, base, .. } => {
                fields.visit_spans_mut(f);
                base.visit_spans_mut(f);
            }
            ExprKind::ListLit(items) => {
                items.visit_spans_mut(f);
            }
            ExprKind::MapLit(entries) => {
                for (k, v) in entries {
                    k.visit_spans_mut(f);
                    v.visit_spans_mut(f);
                }
            }
            ExprKind::Paren(inner) => {
                inner.visit_spans_mut(f);
            }
            ExprKind::If {
                condition,
                then_block,
                else_branch,
            } => {
                condition.visit_spans_mut(f);
                then_block.visit_spans_mut(f);
                else_branch.visit_spans_mut(f);
            }
            ExprKind::IfLet {
                pattern,
                scrutinee,
                then_block,
                else_branch,
            } => {
                pattern.visit_spans_mut(f);
                scrutinee.visit_spans_mut(f);
                then_block.visit_spans_mut(f);
                else_branch.visit_spans_mut(f);
            }
            ExprKind::PatternMatch { scrutinee, arms } => {
                scrutinee.visit_spans_mut(f);
                arms.visit_spans_mut(f);
            }
            ExprKind::GuardMatch { arms } => {
                arms.visit_spans_mut(f);
            }
            ExprKind::For {
                pattern,
                iterable,
                body,
            } => {
                pattern.visit_spans_mut(f);
                iterable.visit_spans_mut(f);
                body.visit_spans_mut(f);
            }
            ExprKind::ListComprehension {
                element,
                pattern,
                iterable,
                filter,
            } => {
                element.visit_spans_mut(f);
                pattern.visit_spans_mut(f);
                iterable.visit_spans_mut(f);
                if let Some(f_expr) = filter {
                    f_expr.visit_spans_mut(f);
                }
            }
            ExprKind::Has { entity, .. } => {
                entity.visit_spans_mut(f);
            }
        }
    }
}

impl VisitSpansMut for ForIterable {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        match self {
            ForIterable::Collection(e) => e.visit_spans_mut(f),
            ForIterable::Range { start, end, .. } => {
                start.visit_spans_mut(f);
                end.visit_spans_mut(f);
            }
        }
    }
}

impl VisitSpansMut for Arg {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        self.span.visit_spans_mut(f);
        self.value.visit_spans_mut(f);
    }
}

impl VisitSpansMut for StructFieldInit {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        self.span.visit_spans_mut(f);
        self.value.visit_spans_mut(f);
    }
}

impl VisitSpansMut for ElseBranch {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        match self {
            ElseBranch::Block(b) => b.visit_spans_mut(f),
            ElseBranch::If(e) => e.visit_spans_mut(f),
        }
    }
}

impl VisitSpansMut for PatternArm {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        self.span.visit_spans_mut(f);
        self.pattern.visit_spans_mut(f);
        self.body.visit_spans_mut(f);
    }
}

impl VisitSpansMut for GuardArm {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        self.span.visit_spans_mut(f);
        self.guard.visit_spans_mut(f);
        self.body.visit_spans_mut(f);
    }
}

impl VisitSpansMut for GuardKind {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        match self {
            GuardKind::Wildcard => {}
            GuardKind::Expr(e) => e.visit_spans_mut(f),
        }
    }
}

impl VisitSpansMut for ArmBody {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        match self {
            ArmBody::Expr(e) => e.visit_spans_mut(f),
            ArmBody::Block(b) => b.visit_spans_mut(f),
        }
    }
}

// ── Patterns ─────────────────────────────────────────────────────

impl VisitSpansMut for PatternKind {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        match self {
            PatternKind::Wildcard
            | PatternKind::IntLit(_)
            | PatternKind::StringLit(_)
            | PatternKind::BoolLit(_)
            | PatternKind::Ident(_)
            | PatternKind::QualifiedVariant { .. }
            | PatternKind::NoneLit => {}
            PatternKind::QualifiedDestructure { fields, .. }
            | PatternKind::BareDestructure { fields, .. } => {
                fields.visit_spans_mut(f);
            }
            PatternKind::Some(inner) => {
                inner.visit_spans_mut(f);
            }
        }
    }
}

// ── Statements ───────────────────────────────────────────────────

impl VisitSpansMut for StmtKind {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        match self {
            StmtKind::Let { ty, value, .. } => {
                ty.visit_spans_mut(f);
                value.visit_spans_mut(f);
            }
            StmtKind::Assign { target, value, .. } => {
                target.visit_spans_mut(f);
                value.visit_spans_mut(f);
            }
            StmtKind::Expr(e) => {
                e.visit_spans_mut(f);
            }
            StmtKind::Grant { entity, fields, .. } => {
                entity.visit_spans_mut(f);
                fields.visit_spans_mut(f);
            }
            StmtKind::Revoke { entity, .. } => {
                entity.visit_spans_mut(f);
            }
            StmtKind::Emit { args, span, .. } => {
                span.visit_spans_mut(f);
                for arg in args {
                    arg.visit_spans_mut(f);
                }
            }
        }
    }
}

impl VisitSpansMut for LValue {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        self.span.visit_spans_mut(f);
        self.segments.visit_spans_mut(f);
    }
}

impl VisitSpansMut for LValueSegment {
    fn visit_spans_mut(&mut self, f: &mut dyn FnMut(&mut Span)) {
        match self {
            LValueSegment::Field(_) => {}
            LValueSegment::Index(e) => e.visit_spans_mut(f),
        }
    }
}
