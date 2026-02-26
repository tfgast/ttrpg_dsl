use std::collections::HashSet;

use ttrpg_ast::ast::*;
use ttrpg_ast::Name;
use ttrpg_ast::Spanned;

use crate::check::{Checker, Namespace};
use crate::env::*;
use crate::scope::*;
use crate::ty::Ty;

impl<'a> Checker<'a> {
    /// Bind the receiver (if present) and condition parameters into the current scope.
    /// Used by both modify and suppress clauses to set up their shared context.
    fn bind_condition_context(
        &mut self,
        receiver: Option<(&Name, &Spanned<TypeExpr>, &[Name])>,
        condition_params: &[Param],
    ) {
        if let Some((receiver_name, receiver_type, with_groups)) = receiver {
            let recv_ty = self.env.resolve_type(receiver_type);
            self.scope.bind(
                receiver_name.clone(),
                VarBinding {
                    ty: recv_ty.clone(),
                    mutable: false,
                    is_local: false,
                },
            );
            self.validate_with_groups(receiver_name, &recv_ty, with_groups, receiver_type.span);
        }

        for param in condition_params {
            let ty = self.env.resolve_type(&param.ty);
            self.scope.bind(
                param.name.clone(),
                VarBinding {
                    ty,
                    mutable: false,
                    is_local: false,
                },
            );
        }
    }

    /// Validate clause bindings: check for duplicates, look up expected types via
    /// `lookup_expected`, type-check value expressions, and report errors.
    ///
    /// - `clause_kind`: "modify" or "suppress" (used in duplicate error messages)
    /// - `not_found_msg`: suffix for the unknown-binding error, e.g.
    ///   `"does not match any parameter of \`foo\`"`
    fn validate_clause_bindings(
        &mut self,
        bindings: &[ModifyBinding],
        lookup_expected: impl Fn(&str) -> Option<Ty>,
        clause_kind: &str,
        not_found_msg: &str,
    ) {
        let mut seen_bindings = HashSet::new();
        for binding in bindings {
            if !seen_bindings.insert(binding.name.clone()) {
                self.error(
                    format!("duplicate {} binding `{}`", clause_kind, binding.name),
                    binding.span,
                );
            }
            if let Some(expected) = lookup_expected(&binding.name) {
                if let Some(ref value) = binding.value {
                    let val_ty = self.check_expr_expecting(value, Some(&expected));
                    if !val_ty.is_error() && !self.types_compatible(&val_ty, &expected) {
                        self.error(
                            format!(
                                "{} binding `{}` has type {}, expected {}",
                                clause_kind, binding.name, val_ty, expected
                            ),
                            value.span,
                        );
                    }
                }
            } else {
                if let Some(ref value) = binding.value {
                    self.check_expr(value);
                }
                self.error(
                    format!(
                        "{} binding `{}` {}",
                        clause_kind, binding.name, not_found_msg
                    ),
                    binding.span,
                );
            }
        }
    }

    /// Check a modify clause. `receiver` is `Some` for conditions (which have
    /// a receiver binding) and `None` for options (which have no receiver).
    /// `condition_params` are the condition's declared parameters (empty for options).
    pub fn check_modify_clause(
        &mut self,
        clause: &ModifyClause,
        receiver: Option<(&Name, &Spanned<TypeExpr>, &[Name])>,
        condition_params: &[Param],
    ) {
        // Look up the target function
        let fn_info = match self.env.lookup_fn(&clause.target) {
            Some(info) => info.clone(),
            None => {
                self.error(
                    format!(
                        "modify target `{}` is not a defined function",
                        clause.target
                    ),
                    clause.span,
                );
                return;
            }
        };

        // Check module visibility for modify target (builtins have no owner)
        if fn_info.kind != FnKind::Builtin {
            self.check_name_visible(&clause.target, Namespace::Function, clause.span);
        }

        // Modify clauses can only target derive or mechanic functions
        if fn_info.kind != FnKind::Derive && fn_info.kind != FnKind::Mechanic {
            self.error(
                format!(
                    "modify target `{}` must be a derive or mechanic",
                    clause.target,
                ),
                clause.span,
            );
            return;
        }

        self.scope.push(BlockKind::ModifyClause);

        // Bind receiver and condition params into scope
        self.bind_condition_context(receiver, condition_params);

        // Validate bindings reference real parameters and type-check value expressions
        self.validate_clause_bindings(
            &clause.bindings,
            |name| {
                fn_info
                    .params
                    .iter()
                    .find(|p| p.name == name)
                    .map(|p| p.ty.clone())
            },
            "modify",
            &format!("does not match any parameter of `{}`", clause.target),
        );

        // Bring target function's params into scope as read-only
        for param in &fn_info.params {
            self.scope.bind(
                param.name.clone(),
                VarBinding {
                    ty: param.ty.clone(),
                    mutable: false,
                    is_local: false,
                },
            );
        }

        // Bring `result` into scope with the target's return type (mutable for post-call modification)
        self.scope.bind(
            Name::from("result"),
            VarBinding {
                ty: fn_info.return_type.clone(),
                mutable: true,
                is_local: false,
            },
        );

        // Check modify statements
        for stmt in &clause.body {
            self.check_modify_stmt(stmt, &fn_info);
        }

        self.scope.pop();
    }

    fn check_modify_stmt(&mut self, stmt: &ModifyStmt, fn_info: &FnInfo) {
        match stmt {
            ModifyStmt::Let {
                name,
                ty,
                value,
                span: _,
            } => {
                let bind_ty = if let Some(ref type_ann) = ty {
                    let ann_ty = self.resolve_type_validated(type_ann);
                    let val_ty = self.check_expr_expecting(value, Some(&ann_ty));
                    if !val_ty.is_error()
                        && !ann_ty.is_error()
                        && !self.types_compatible(&val_ty, &ann_ty)
                    {
                        self.error(
                            format!(
                                "let `{}`: value has type {}, annotation says {}",
                                name, val_ty, ann_ty
                            ),
                            value.span,
                        );
                    }
                    ann_ty
                } else {
                    self.check_expr(value)
                };

                self.scope.bind(
                    name.clone(),
                    VarBinding {
                        ty: bind_ty,
                        mutable: false,
                        is_local: true,
                    },
                );
            }
            ModifyStmt::ParamOverride { name, value, span } => {
                if name == "result" {
                    // Direct result assignment: `result = expr`
                    let val_ty = self.check_expr_expecting(value, Some(&fn_info.return_type));
                    if !val_ty.is_error() && !self.types_compatible(&val_ty, &fn_info.return_type) {
                        self.error(
                            format!("result has type {}, found {}", fn_info.return_type, val_ty),
                            value.span,
                        );
                    }
                } else if let Some(param) = fn_info.params.iter().find(|p| p.name == *name) {
                    // Check that the param exists and types match
                    let val_ty = self.check_expr_expecting(value, Some(&param.ty));
                    if !val_ty.is_error() && !self.types_compatible(&val_ty, &param.ty) {
                        self.error(
                            format!(
                                "param override `{}` has type {}, expected {}",
                                name, val_ty, param.ty
                            ),
                            value.span,
                        );
                    }
                } else {
                    self.check_expr(value);
                    self.error(
                        format!("`{}` has no parameter `{}`", fn_info.name, name),
                        *span,
                    );
                }
            }
            ModifyStmt::ResultOverride { field, value, span } => {
                // Resolve the field type from the return type
                let result_ty = &fn_info.return_type;
                let field_ty = self.resolve_field(result_ty, field, *span);
                let val_ty = self.check_expr_expecting(value, Some(&field_ty));
                if !val_ty.is_error()
                    && !field_ty.is_error()
                    && !self.types_compatible(&val_ty, &field_ty)
                {
                    self.error(
                        format!("result.{} has type {}, found {}", field, field_ty, val_ty),
                        value.span,
                    );
                }
            }
            ModifyStmt::If {
                condition,
                then_body,
                else_body,
                span: _,
            } => {
                let cond_ty = self.check_expr(condition);
                if !cond_ty.is_error() && cond_ty != Ty::Bool {
                    self.error(
                        format!("if condition must be bool, found {}", cond_ty),
                        condition.span,
                    );
                }
                self.scope.push(BlockKind::Inner);
                for s in then_body {
                    self.check_modify_stmt(s, fn_info);
                }
                self.scope.pop();
                if let Some(else_stmts) = else_body {
                    self.scope.push(BlockKind::Inner);
                    for s in else_stmts {
                        self.check_modify_stmt(s, fn_info);
                    }
                    self.scope.pop();
                }
            }
        }
    }

    /// Check a suppress clause.
    pub fn check_suppress_clause(
        &mut self,
        clause: &SuppressClause,
        receiver_name: &Name,
        receiver_type: &Spanned<TypeExpr>,
        receiver_with_groups: &[Name],
        condition_params: &[Param],
    ) {
        if let Some(event_info) = self.env.events.get(&clause.event_name).cloned() {
            self.check_name_visible(&clause.event_name, Namespace::Event, clause.span);
            // Push TriggerBinding scope — suppress binding expressions must be side-effect-free
            self.scope.push(BlockKind::TriggerBinding);

            // Bind receiver and condition params into scope
            self.bind_condition_context(
                Some((receiver_name, receiver_type, receiver_with_groups)),
                condition_params,
            );

            // Validate bindings reference real event params or fields, and type-check values
            self.validate_clause_bindings(
                &clause.bindings,
                |name| {
                    event_info
                        .params
                        .iter()
                        .find(|p| p.name == name)
                        .map(|p| &p.ty)
                        .or_else(|| {
                            event_info
                                .fields
                                .iter()
                                .find(|(n, _)| *n == name)
                                .map(|(_, ty)| ty)
                        })
                        .cloned()
                },
                "suppress",
                &format!(
                    "does not match any parameter or field of event `{}`",
                    clause.event_name
                ),
            );

            self.scope.pop();
        } else {
            self.error(
                format!("undefined event `{}`", clause.event_name),
                clause.span,
            );
        }
    }
}
