use ttrpg_ast::ast::*;
use ttrpg_ast::Spanned;

use crate::check::Checker;
use crate::scope::BlockKind;
use crate::ty::Ty;

impl<'a> Checker<'a> {
    pub(crate) fn check_if(
        &mut self,
        condition: &Spanned<ExprKind>,
        then_block: &Block,
        else_branch: Option<&ElseBranch>,
        span: ttrpg_ast::Span,
        hint: Option<&Ty>,
    ) -> Ty {
        let cond_ty = self.check_expr(condition);
        if !cond_ty.is_error() && cond_ty != Ty::Bool {
            self.error(
                format!("if condition must be bool, found {}", cond_ty),
                condition.span,
            );
        }

        // Extract narrowings from `has` conditions for the then-block
        let narrowings = self.extract_has_narrowings(condition);
        let then_ty = if narrowings.is_empty() {
            self.check_block_with_tail_hint(then_block, hint)
        } else {
            self.check_block_with_narrowings_and_hint(then_block, &narrowings, hint)
        };
        self.check_else_branch_type(&then_ty, else_branch, span, hint)
    }

    pub(crate) fn check_if_let(
        &mut self,
        pattern: &Spanned<PatternKind>,
        scrutinee: &Spanned<ExprKind>,
        then_block: &Block,
        else_branch: Option<&ElseBranch>,
        span: ttrpg_ast::Span,
        hint: Option<&Ty>,
    ) -> Ty {
        let scrutinee_ty = self.check_expr(scrutinee);

        // Pattern bindings are scoped to the then-block
        self.scope.push(BlockKind::Inner);
        self.check_pattern(pattern, &scrutinee_ty);
        let then_ty = self.check_block_with_tail_hint(then_block, hint);
        self.scope.pop();

        self.check_else_branch_type(&then_ty, else_branch, span, hint)
    }

    fn check_else_branch_type(
        &mut self,
        then_ty: &Ty,
        else_branch: Option<&ElseBranch>,
        span: ttrpg_ast::Span,
        hint: Option<&Ty>,
    ) -> Ty {
        // Prefer the already-resolved then_ty over the original hint
        let branch_hint = Some(then_ty).filter(|t| !t.is_error()).or(hint);
        match else_branch {
            Some(ElseBranch::Block(else_block)) => {
                let else_ty = self.check_block_with_tail_hint(else_block, branch_hint);
                match self.unify_branch_types(then_ty, &else_ty) {
                    Some(ty) => ty,
                    None => {
                        self.error(
                            format!(
                                "if/else branches have incompatible types: {} and {}",
                                then_ty, else_ty
                            ),
                            span,
                        );
                        Ty::Error
                    }
                }
            }
            Some(ElseBranch::If(if_expr)) => {
                let else_ty = self.check_expr_expecting(if_expr, branch_hint);
                match self.unify_branch_types(then_ty, &else_ty) {
                    Some(ty) => ty,
                    None => {
                        self.error(
                            format!(
                                "if/else branches have incompatible types: {} and {}",
                                then_ty, else_ty
                            ),
                            span,
                        );
                        Ty::Error
                    }
                }
            }
            None => Ty::Unit,
        }
    }

    pub(crate) fn check_pattern_match(
        &mut self,
        scrutinee: &Spanned<ExprKind>,
        arms: &[PatternArm],
        _span: ttrpg_ast::Span,
        hint: Option<&Ty>,
    ) -> Ty {
        let scrutinee_ty = self.check_expr(scrutinee);

        let mut result_ty: Option<Ty> = None;

        for arm in arms {
            self.scope.push(BlockKind::Inner);
            self.check_pattern(&arm.pattern, &scrutinee_ty);
            let arm_hint = result_ty.as_ref().or(hint);
            let arm_ty = self.check_arm_body(&arm.body, arm_hint);
            self.scope.pop();

            if !arm_ty.is_error() {
                match result_ty {
                    Some(ref existing) => match self.unify_branch_types(existing, &arm_ty) {
                        Some(unified) => result_ty = Some(unified),
                        None => {
                            self.error(
                                format!("match arm has type {}, expected {}", arm_ty, existing),
                                arm.span,
                            );
                        }
                    },
                    None => result_ty = Some(arm_ty),
                }
            }
        }

        result_ty.unwrap_or(Ty::Unit)
    }

    pub(crate) fn check_guard_match(
        &mut self,
        arms: &[GuardArm],
        _span: ttrpg_ast::Span,
        hint: Option<&Ty>,
    ) -> Ty {
        let mut result_ty: Option<Ty> = None;
        let mut seen_wildcard = false;

        for arm in arms {
            // Check guard expression
            match &arm.guard {
                GuardKind::Expr(expr) => {
                    if seen_wildcard {
                        self.warning(
                            "unreachable match arm: wildcard `_` must be last".to_string(),
                            expr.span,
                        );
                    }
                    let guard_ty = self.check_expr(expr);
                    if !guard_ty.is_error() && guard_ty != Ty::Bool {
                        self.error(
                            format!("guard condition must be bool, found {}", guard_ty),
                            expr.span,
                        );
                    }
                }
                GuardKind::Wildcard => {
                    if seen_wildcard {
                        self.warning(
                            "duplicate wildcard `_` in guard match".to_string(),
                            arm.span,
                        );
                    }
                    seen_wildcard = true;
                }
            }

            let arm_hint = result_ty.as_ref().or(hint);
            let arm_ty = self.check_arm_body(&arm.body, arm_hint);

            if !arm_ty.is_error() {
                match result_ty {
                    Some(ref existing) => match self.unify_branch_types(existing, &arm_ty) {
                        Some(unified) => result_ty = Some(unified),
                        None => {
                            self.error(
                                format!("match arm has type {}, expected {}", arm_ty, existing),
                                arm.span,
                            );
                        }
                    },
                    None => result_ty = Some(arm_ty),
                }
            }
        }

        result_ty.unwrap_or(Ty::Unit)
    }

    pub(crate) fn check_for(
        &mut self,
        pattern: &Spanned<PatternKind>,
        iterable: &ForIterable,
        body: &Block,
        span: ttrpg_ast::Span,
    ) -> Ty {
        let element_ty = match iterable {
            ForIterable::Collection(expr) => {
                let coll_ty = self.check_expr(expr);
                match coll_ty {
                    Ty::List(inner) | Ty::Set(inner) => *inner,
                    Ty::Map(_, _) => {
                        self.error(
                            "map iteration is not supported; use keys() or values()".to_string(),
                            span,
                        );
                        Ty::Error
                    }
                    Ty::Error => Ty::Error,
                    other => {
                        self.error(format!("expected list or set, found {}", other), span);
                        Ty::Error
                    }
                }
            }
            ForIterable::Range {
                start,
                end,
                inclusive: _,
            } => {
                let start_ty = self.check_expr(start);
                let end_ty = self.check_expr(end);
                if !start_ty.is_error() && !start_ty.is_int_like() {
                    self.error(
                        format!("range start must be int, found {}", start_ty),
                        start.span,
                    );
                }
                if !end_ty.is_error() && !end_ty.is_int_like() {
                    self.error(format!("range end must be int, found {}", end_ty), end.span);
                }
                Ty::Int
            }
        };

        // Pattern bindings are scoped to the loop body.
        // We push scope, check the pattern (which binds with is_local: true),
        // then mark entity-typed bindings as non-local so field mutation works
        // (e.g. `for target in targets { target.HP -= damage }`).
        // Non-entity bindings stay local so the immutable-local guard applies.
        self.scope.push(BlockKind::Inner);
        self.check_pattern_binding(pattern, &element_ty);
        self.scope.mark_current_scope_entities_non_local();
        self.check_block(body);
        self.scope.pop();

        Ty::Unit
    }

    pub(crate) fn check_list_comprehension(
        &mut self,
        element: &Spanned<ExprKind>,
        pattern: &Spanned<PatternKind>,
        iterable: &ForIterable,
        filter: Option<&Spanned<ExprKind>>,
        span: ttrpg_ast::Span,
    ) -> Ty {
        // Resolve element type from iterable (same logic as check_for)
        let iter_elem_ty = match iterable {
            ForIterable::Collection(expr) => {
                let coll_ty = self.check_expr(expr);
                match coll_ty {
                    Ty::List(inner) | Ty::Set(inner) => *inner,
                    Ty::Map(_, _) => {
                        self.error(
                            "map iteration is not supported; use keys() or values()".to_string(),
                            span,
                        );
                        Ty::Error
                    }
                    Ty::Error => Ty::Error,
                    other => {
                        self.error(format!("expected list or set, found {}", other), span);
                        Ty::Error
                    }
                }
            }
            ForIterable::Range {
                start,
                end,
                inclusive: _,
            } => {
                let start_ty = self.check_expr(start);
                let end_ty = self.check_expr(end);
                if !start_ty.is_error() && !start_ty.is_int_like() {
                    self.error(
                        format!("range start must be int, found {}", start_ty),
                        start.span,
                    );
                }
                if !end_ty.is_error() && !end_ty.is_int_like() {
                    self.error(format!("range end must be int, found {}", end_ty), end.span);
                }
                Ty::Int
            }
        };

        // Push scope and bind pattern (binding context — idents are always bindings)
        self.scope.push(BlockKind::Inner);
        self.check_pattern_binding(pattern, &iter_elem_ty);

        // Check filter if present
        if let Some(filter_expr) = filter {
            let filter_ty = self.check_expr(filter_expr);
            if !filter_ty.is_error() && filter_ty != Ty::Bool {
                self.error(
                    format!(
                        "list comprehension filter must be bool, found {}",
                        filter_ty
                    ),
                    filter_expr.span,
                );
            }
        }

        // Check element expression
        let elem_ty = self.check_expr(element);
        self.scope.pop();

        Ty::List(Box::new(elem_ty))
    }

    pub(crate) fn check_arm_body(&mut self, body: &ArmBody, hint: Option<&Ty>) -> Ty {
        match body {
            ArmBody::Expr(expr) => self.check_expr_expecting(expr, hint),
            ArmBody::Block(block) => self.check_block(block),
        }
    }
}
