use std::collections::HashSet;

use ttrpg_ast::ast::*;
use ttrpg_ast::Name;
use ttrpg_ast::Spanned;

use crate::check::{Checker, Namespace};
use crate::env::*;
use crate::scope::*;
use crate::ty::Ty;

/// A selector predicate with types resolved to `Ty` for matching.
enum ResolvedPredicate {
    Tag(Name),
    Returns(Ty),
    HasParam { name: Name, ty: Option<Ty> },
}

impl<'a> Checker<'a> {
    /// Bind the receiver (if present) and condition parameters into the current scope.
    /// Used by both modify and suppress clauses to set up their shared context.
    fn bind_condition_context(
        &mut self,
        receiver: Option<(&Name, &Spanned<TypeExpr>, &[GroupConstraint])>,
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
        receiver: Option<(&Name, &Spanned<TypeExpr>, &[GroupConstraint])>,
        condition_params: &[Param],
    ) {
        match &clause.target {
            ModifyTarget::Named(name) => {
                self.check_modify_named(clause, name, receiver, condition_params);
            }
            ModifyTarget::Selector(preds) => {
                self.check_modify_selector(clause, preds, receiver, condition_params);
            }
            ModifyTarget::Cost(name) => {
                self.check_modify_cost(clause, name, receiver, condition_params);
            }
        }
    }

    /// Check a modify clause targeting a specific named function.
    fn check_modify_named(
        &mut self,
        clause: &ModifyClause,
        target_name: &Name,
        receiver: Option<(&Name, &Spanned<TypeExpr>, &[GroupConstraint])>,
        condition_params: &[Param],
    ) {
        // Look up the target function
        let fn_info = match self.env.lookup_fn(target_name) {
            Some(info) => info.clone(),
            None => {
                self.error(
                    format!("modify target `{}` is not a defined function", target_name),
                    clause.span,
                );
                return;
            }
        };

        // Check module visibility for modify target (builtins have no owner)
        if fn_info.kind != FnKind::Builtin {
            self.check_name_visible(target_name, Namespace::Function, clause.span);
        }

        // Modify clauses can only target derive or mechanic functions
        if fn_info.kind != FnKind::Derive && fn_info.kind != FnKind::Mechanic {
            self.error(
                format!("modify target `{}` must be a derive or mechanic", target_name),
                clause.span,
            );
            return;
        }

        self.check_modify_body(clause, &fn_info, receiver, condition_params);
    }

    /// Check a modify clause targeting an action/reaction's cost.
    fn check_modify_cost(
        &mut self,
        clause: &ModifyClause,
        target_name: &Name,
        receiver: Option<(&Name, &Spanned<TypeExpr>, &[GroupConstraint])>,
        condition_params: &[Param],
    ) {
        // Look up the target function
        let fn_info = match self.env.lookup_fn(target_name) {
            Some(info) => info.clone(),
            None => {
                self.error(
                    format!("modify cost target `{}` is not a defined function", target_name),
                    clause.span,
                );
                return;
            }
        };

        // .cost modify can only target actions or reactions
        if fn_info.kind != FnKind::Action && fn_info.kind != FnKind::Reaction {
            self.error(
                format!(
                    "modify cost target `{}` must be an action or reaction",
                    target_name
                ),
                clause.span,
            );
            return;
        }

        // Check module visibility
        self.check_name_visible(target_name, Namespace::Function, clause.span);

        self.scope.push(BlockKind::ModifyClause);

        // Bind receiver and condition params into scope
        self.bind_condition_context(receiver, condition_params);

        // Validate bindings: the action's receiver is bindable, plus all declared params
        self.validate_clause_bindings(
            &clause.bindings,
            |name| {
                // Check receiver name first
                if let Some(ref recv) = fn_info.receiver {
                    if recv.name == name {
                        return Some(recv.ty.clone());
                    }
                }
                fn_info
                    .params
                    .iter()
                    .find(|p| p.name == name)
                    .map(|p| p.ty.clone())
            },
            "modify",
            &format!("does not match any parameter of `{}`", target_name),
        );

        // Bring target function's params into scope as read-only
        if let Some(ref recv) = fn_info.receiver {
            self.scope.bind(
                recv.name.clone(),
                VarBinding {
                    ty: recv.ty.clone(),
                    mutable: false,
                    is_local: false,
                },
            );
        }
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

        // Check cost modify statements
        for stmt in &clause.body {
            self.check_cost_modify_stmt(stmt, target_name);
        }

        self.scope.pop();
    }

    /// Check a single cost modify statement — only Let, If, CostOverride are valid.
    fn check_cost_modify_stmt(&mut self, stmt: &ModifyStmt, target_name: &Name) {
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
                    self.check_cost_modify_stmt(s, target_name);
                }
                self.scope.pop();
                if let Some(else_stmts) = else_body {
                    self.scope.push(BlockKind::Inner);
                    for s in else_stmts {
                        self.check_cost_modify_stmt(s, target_name);
                    }
                    self.scope.pop();
                }
            }
            ModifyStmt::CostOverride {
                tokens,
                free,
                span: _,
            } => {
                if !free {
                    // Validate cost tokens
                    let expected = self
                        .env
                        .valid_cost_tokens()
                        .into_iter()
                        .map(|n| n.to_string())
                        .collect::<Vec<_>>();

                    for token in tokens {
                        if self.env.resolve_cost_token(&token.node).is_none() {
                            let suffix = if expected.is_empty() {
                                "no valid cost tokens are available".to_string()
                            } else {
                                format!("expected one of: {}", expected.join(", "))
                            };
                            self.error(
                                format!("invalid cost token `{}`; {}", token.node, suffix),
                                token.span,
                            );
                        }
                    }
                }
            }
            ModifyStmt::ParamOverride { span, .. } => {
                self.error(
                    "param overrides are not allowed in cost modify clauses",
                    *span,
                );
            }
            ModifyStmt::ResultOverride { span, .. } => {
                self.error(
                    "result overrides are not allowed in cost modify clauses",
                    *span,
                );
            }
        }
    }

    /// Check a modify clause targeting functions via selector predicates.
    fn check_modify_selector(
        &mut self,
        clause: &ModifyClause,
        preds: &[SelectorPredicate],
        receiver: Option<(&Name, &Spanned<TypeExpr>, &[GroupConstraint])>,
        condition_params: &[Param],
    ) {
        // Resolve predicates into concrete types for matching
        let mut resolved: Vec<ResolvedPredicate> = Vec::new();
        for pred in preds {
            match pred {
                SelectorPredicate::Tag(tag_name) => {
                    // Validate tag is declared and visible
                    if !self.env.tags.contains(tag_name) {
                        self.error(
                            format!("undefined tag `{}`", tag_name),
                            clause.span,
                        );
                        return;
                    }
                    self.check_name_visible(tag_name, Namespace::Tag, clause.span);
                    resolved.push(ResolvedPredicate::Tag(tag_name.clone()));
                }
                SelectorPredicate::Returns(type_expr) => {
                    let ty = self.resolve_type_validated(type_expr);
                    if ty.is_error() {
                        return;
                    }
                    resolved.push(ResolvedPredicate::Returns(ty));
                }
                SelectorPredicate::HasParam { name, ty } => {
                    let resolved_ty = if let Some(te) = ty {
                        let t = self.resolve_type_validated(te);
                        if t.is_error() {
                            return;
                        }
                        Some(t)
                    } else {
                        None
                    };
                    resolved.push(ResolvedPredicate::HasParam {
                        name: name.clone(),
                        ty: resolved_ty,
                    });
                }
            }
        }

        // Compute match set: iterate all functions, keep Derive/Mechanic, exclude synthetic
        let mut match_set: HashSet<Name> = HashSet::new();
        for (fn_name, fn_info) in &self.env.functions {
            if fn_info.kind != FnKind::Derive && fn_info.kind != FnKind::Mechanic {
                continue;
            }
            if fn_info.synthetic {
                continue;
            }
            if self.fn_matches_predicates(fn_info, &resolved) {
                match_set.insert(fn_name.clone());
            }
        }

        if match_set.is_empty() {
            self.diagnostics.push(ttrpg_ast::diagnostic::Diagnostic::warning(
                "selector matches no functions",
                clause.span,
            ));
            return;
        }

        // Build a synthetic FnInfo representing the intersection of all matched functions
        let matched_fns: Vec<&FnInfo> = match_set
            .iter()
            .filter_map(|n| self.env.functions.get(n))
            .collect();

        // Validate bindings: for each binding, every fn must have the param with identical type
        for binding in &clause.bindings {
            let mut binding_ty: Option<Ty> = None;
            let mut all_have_param = true;
            for fi in &matched_fns {
                if let Some(p) = fi.params.iter().find(|p| p.name == binding.name) {
                    match &binding_ty {
                        None => binding_ty = Some(p.ty.clone()),
                        Some(existing) => {
                            if !self.types_compatible(existing, &p.ty) {
                                self.error(
                                    format!(
                                        "selector binding `{}` has inconsistent types across matched functions: {} vs {}",
                                        binding.name, existing, p.ty
                                    ),
                                    binding.span,
                                );
                            }
                        }
                    }
                } else {
                    all_have_param = false;
                }
            }
            if !all_have_param {
                self.error(
                    format!(
                        "selector binding `{}` does not exist on all matched functions",
                        binding.name
                    ),
                    binding.span,
                );
            }
        }

        // Check if body references `result`
        let body_uses_result = clause.body.iter().any(Self::stmt_uses_result);

        // Determine the common return type (needed if body uses result)
        let common_return_type = if body_uses_result {
            let mut ret_ty: Option<Ty> = None;
            let mut consistent = true;
            for fi in &matched_fns {
                match &ret_ty {
                    None => ret_ty = Some(fi.return_type.clone()),
                    Some(existing) => {
                        if !self.types_compatible(existing, &fi.return_type) {
                            consistent = false;
                            break;
                        }
                    }
                }
            }
            if !consistent {
                self.error(
                    "selector modify body references `result` but matched functions have different return types",
                    clause.span,
                );
                return;
            }
            ret_ty.unwrap_or(Ty::Unit)
        } else {
            Ty::Unit
        };

        // Build synthetic FnInfo: intersection of params with identical types
        let synthetic_params = Self::compute_common_params(&matched_fns);
        let synthetic_fn = FnInfo {
            name: Name::from("<selector>"),
            kind: FnKind::Derive,
            params: synthetic_params,
            return_type: common_return_type,
            receiver: None,
            tags: HashSet::new(),
            synthetic: true,
        };

        self.check_modify_body(clause, &synthetic_fn, receiver, condition_params);

        // Store match set for interpreter runtime dispatch
        self.selector_matches.insert(clause.id, match_set);
    }

    /// Test whether a function matches all resolved predicates.
    fn fn_matches_predicates(
        &self,
        fn_info: &FnInfo,
        preds: &[ResolvedPredicate],
    ) -> bool {
        preds.iter().all(|pred| match pred {
            ResolvedPredicate::Tag(tag) => fn_info.tags.contains(tag),
            ResolvedPredicate::Returns(ty) => self.types_compatible(&fn_info.return_type, ty),
            ResolvedPredicate::HasParam { name, ty } => fn_info.params.iter().any(|p| {
                p.name == *name
                    && match ty {
                        Some(t) => self.types_compatible(&p.ty, t),
                        None => true,
                    }
            }),
        })
    }

    /// Compute params that appear in all matched functions with identical types.
    fn compute_common_params(matched_fns: &[&FnInfo]) -> Vec<ParamInfo> {
        if matched_fns.is_empty() {
            return vec![];
        }
        let first = &matched_fns[0];
        first
            .params
            .iter()
            .filter(|p| {
                matched_fns[1..].iter().all(|fi| {
                    fi.params
                        .iter()
                        .any(|fp| fp.name == p.name && fp.ty == p.ty)
                })
            })
            .cloned()
            .collect()
    }

    /// Check whether a modify statement tree references `result`.
    fn stmt_uses_result(stmt: &ModifyStmt) -> bool {
        match stmt {
            ModifyStmt::ResultOverride { .. } => true,
            ModifyStmt::ParamOverride { name, .. } if name == "result" => true,
            ModifyStmt::If {
                then_body,
                else_body,
                ..
            } => {
                then_body.iter().any(Self::stmt_uses_result)
                    || else_body
                        .as_ref()
                        .is_some_and(|stmts| stmts.iter().any(Self::stmt_uses_result))
            }
            _ => false,
        }
    }

    /// Shared body-checking logic for both named and selector modify clauses.
    fn check_modify_body(
        &mut self,
        clause: &ModifyClause,
        fn_info: &FnInfo,
        receiver: Option<(&Name, &Spanned<TypeExpr>, &[GroupConstraint])>,
        condition_params: &[Param],
    ) {
        self.scope.push(BlockKind::ModifyClause);

        // Bind receiver and condition params into scope
        self.bind_condition_context(receiver, condition_params);

        // Validate bindings reference real parameters and type-check value expressions
        let target_label = match &clause.target {
            ModifyTarget::Named(name) | ModifyTarget::Cost(name) => format!("{}", name),
            ModifyTarget::Selector(_) => "matched functions".to_string(),
        };
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
            &format!("does not match any parameter of `{}`", target_label),
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
            self.check_modify_stmt(stmt, fn_info);
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
            ModifyStmt::CostOverride { span, .. } => {
                self.error(
                    "cost overrides are only allowed in `.cost` modify clauses",
                    *span,
                );
            }
        }
    }

    /// Check a suppress clause.
    pub fn check_suppress_clause(
        &mut self,
        clause: &SuppressClause,
        receiver_name: &Name,
        receiver_type: &Spanned<TypeExpr>,
        receiver_with_groups: &[GroupConstraint],
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
