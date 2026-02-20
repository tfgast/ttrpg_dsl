use ttrpg_ast::ast::*;
use ttrpg_ast::Spanned;

use crate::check::Checker;
use crate::scope::*;
use crate::ty::Ty;

impl<'a> Checker<'a> {
    /// Check a block of statements; returns the type of the block's value
    /// (the last expression-statement, or Unit if none).
    pub fn check_block(&mut self, block: &Block) -> Ty {
        self.scope.push(BlockKind::Inner);

        let stmts = &block.node;
        let mut last_ty = Ty::Unit;

        for (i, stmt) in stmts.iter().enumerate() {
            let is_last = i == stmts.len() - 1;
            last_ty = self.check_stmt(stmt, is_last);
        }

        self.scope.pop();
        last_ty
    }

    fn check_stmt(&mut self, stmt: &Spanned<StmtKind>, is_last: bool) -> Ty {
        match &stmt.node {
            StmtKind::Let { name, ty, value } => {
                let val_ty = self.check_expr(value);

                if let Some(ref type_ann) = ty {
                    self.validate_type(type_ann);
                    let ann_ty = self.env.resolve_type(type_ann);
                    if !val_ty.is_error() && !ann_ty.is_error() && !self.types_compatible(&val_ty, &ann_ty) {
                        self.error(
                            format!(
                                "let `{}`: value has type {}, annotation says {}",
                                name, val_ty, ann_ty
                            ),
                            value.span,
                        );
                    }
                    self.scope.bind(
                        name.clone(),
                        VarBinding {
                            ty: ann_ty,
                            mutable: false,
                        },
                    );
                } else {
                    self.scope.bind(
                        name.clone(),
                        VarBinding {
                            ty: val_ty,
                            mutable: false,
                        },
                    );
                }

                Ty::Unit
            }
            StmtKind::Assign { target, op, value } => {
                self.check_assign(target, *op, value, stmt.span);
                Ty::Unit
            }
            StmtKind::Expr(expr) => {
                let ty = self.check_expr(expr);
                if is_last {
                    ty
                } else {
                    Ty::Unit
                }
            }
        }
    }

    fn check_assign(
        &mut self,
        target: &LValue,
        op: AssignOp,
        value: &Spanned<ExprKind>,
        span: ttrpg_ast::Span,
    ) {
        if target.segments.is_empty() {
            // Direct variable reassignment (e.g. `x = 2`): binding must be mutable
            if let Some(binding) = self.scope.lookup(&target.root) {
                if !binding.mutable {
                    self.error(
                        format!("cannot reassign immutable binding `{}`", target.root),
                        span,
                    );
                    // Still check value expression for other errors
                    self.check_expr(value);
                    return;
                }
            }
        } else {
            // Field/index mutation (e.g. `target.HP += 5`): check block-level permission
            if !self.scope.allows_mutation() {
                // Special case: "turn" is always mutable in action/reaction
                let is_turn = target.root == "turn" && self.scope.allows_turn();
                if !is_turn {
                    self.error(
                        "assignment to entity fields requires action or reaction context"
                            .to_string(),
                        span,
                    );
                }
            }
        }

        // Resolve target type
        let target_ty = self.resolve_lvalue_type(target);
        let value_ty = self.check_expr(value);

        if target_ty.is_error() || value_ty.is_error() {
            return;
        }

        match op {
            AssignOp::Eq => {
                if !self.types_compatible(&value_ty, &target_ty) {
                    self.error(
                        format!(
                            "cannot assign {} to {}",
                            value_ty, target_ty
                        ),
                        value.span,
                    );
                }
            }
            AssignOp::PlusEq | AssignOp::MinusEq => {
                // Target must be numeric
                if !target_ty.is_numeric() && !target_ty.is_int_like() {
                    self.error(
                        format!("cannot use += / -= on type {}", target_ty),
                        span,
                    );
                } else if !value_ty.is_numeric() && !value_ty.is_int_like() {
                    self.error(
                        format!("right side of += / -= must be numeric, found {}", value_ty),
                        value.span,
                    );
                } else if target_ty.is_int_like() && value_ty == Ty::Float {
                    // Prevent int += float (would silently lose precision)
                    self.error(
                        format!(
                            "cannot use float in += / -= on {}: would lose precision",
                            target_ty
                        ),
                        value.span,
                    );
                }
            }
        }
    }

    fn resolve_lvalue_type(&mut self, lvalue: &LValue) -> Ty {
        let root_ty = match self.scope.lookup(&lvalue.root) {
            Some(binding) => binding.ty.clone(),
            None => {
                self.error(
                    format!("undefined variable `{}`", lvalue.root),
                    lvalue.span,
                );
                return Ty::Error;
            }
        };

        let mut current = root_ty;
        for seg in &lvalue.segments {
            if current.is_error() {
                return Ty::Error;
            }
            match seg {
                LValueSegment::Field(name) => {
                    current = self.resolve_field(&current, name, lvalue.span);
                }
                LValueSegment::Index(idx_expr) => {
                    let idx_ty = self.check_expr(idx_expr);
                    if idx_ty.is_error() || current.is_error() {
                        return Ty::Error;
                    }
                    match &current {
                        Ty::List(inner) => {
                            if !idx_ty.is_int_like() {
                                self.error(
                                    format!("list index must be int, found {}", idx_ty),
                                    idx_expr.span,
                                );
                            }
                            current = *inner.clone();
                        }
                        Ty::Map(key, val) => {
                            if !self.types_compatible(&idx_ty, key) {
                                self.error(
                                    format!("map key type is {}, found {}", key, idx_ty),
                                    idx_expr.span,
                                );
                            }
                            current = *val.clone();
                        }
                        _ => {
                            self.error(
                                format!("cannot index into {}", current),
                                lvalue.span,
                            );
                            return Ty::Error;
                        }
                    }
                }
            }
        }

        current
    }
}
