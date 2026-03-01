use ttrpg_ast::ast::*;
use ttrpg_ast::Spanned;

use crate::check::{Checker, Namespace};
use crate::scope::*;
use crate::ty::Ty;

impl<'a> Checker<'a> {
    /// Check a block of statements; returns the type of the block's value
    /// (the last expression-statement, or Unit if none).
    pub fn check_block(&mut self, block: &Block) -> Ty {
        self.check_block_with_tail_hint(block, None)
    }

    /// Like `check_block`, but threads a type hint to the tail expression
    /// so that empty collection literals can infer their type from context
    /// (e.g. return type).
    pub fn check_block_with_tail_hint(&mut self, block: &Block, tail_hint: Option<&Ty>) -> Ty {
        self.scope.push(BlockKind::Inner);

        let stmts = &block.node;
        let mut last_ty = Ty::Unit;

        for (i, stmt) in stmts.iter().enumerate() {
            let is_last = i == stmts.len() - 1;
            if is_last && tail_hint.is_some() {
                last_ty = self.check_stmt_with_hint(stmt, is_last, tail_hint);
            } else {
                last_ty = self.check_stmt_with_hint(stmt, is_last, None);
            }
        }

        self.scope.pop();
        last_ty
    }

    pub(crate) fn check_stmt(&mut self, stmt: &Spanned<StmtKind>, is_last: bool) -> Ty {
        self.check_stmt_with_hint(stmt, is_last, None)
    }

    fn check_stmt_with_hint(
        &mut self,
        stmt: &Spanned<StmtKind>,
        is_last: bool,
        hint: Option<&Ty>,
    ) -> Ty {
        match &stmt.node {
            StmtKind::Let { name, ty, value } => {
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

                Ty::Unit
            }
            StmtKind::Assign { target, op, value } => {
                self.check_assign(target, *op, value, stmt.span);
                Ty::Unit
            }
            StmtKind::Expr(expr) => {
                let ty = if is_last && hint.is_some() {
                    self.check_expr_expecting(expr, hint)
                } else {
                    self.check_expr(expr)
                };
                if is_last {
                    ty
                } else {
                    Ty::Unit
                }
            }
            StmtKind::Grant {
                entity,
                group_name,
                fields,
            } => {
                self.check_grant(entity, group_name, fields, stmt.span);
                Ty::Unit
            }
            StmtKind::Revoke { entity, group_name } => {
                self.check_revoke(entity, group_name, stmt.span);
                Ty::Unit
            }
            StmtKind::Emit {
                event_name,
                args,
                span,
            } => {
                self.check_emit(event_name, args, *span);
                Ty::Unit
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
            // The implicit `turn` binding is mutable for field mutation
            // (turn.actions -= 1), but direct reassignment (turn = ...) is not allowed.
            if target.root == "turn" && self.scope.allows_turn() {
                self.error(
                    "cannot reassign `turn` directly; mutate its fields instead (e.g. `turn.actions -= 1`)".to_string(),
                    span,
                );
                self.check_expr(value);
                return;
            }
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
            // Field/index mutation (e.g. `target.HP += 5`)

            // Local `let` bindings are always immutable for field/index mutation
            if let Some(binding) = self.scope.lookup(&target.root) {
                if binding.is_local && !binding.mutable {
                    self.error(
                        format!(
                            "cannot mutate field/index of immutable binding `{}`",
                            target.root
                        ),
                        span,
                    );
                    self.check_expr(value);
                    return;
                }

                // Trigger payload: direct fields are immutable, but deep paths
                // (e.g. trigger.entity.HP) are allowed for entity state mutation
                if !binding.mutable {
                    if let Ty::Struct(ref s) = binding.ty {
                        if s.starts_with("__event_") && target.segments.len() <= 1 {
                            self.error(
                                format!("cannot mutate field of trigger payload `{}`", target.root),
                                span,
                            );
                            self.check_expr(value);
                            return;
                        }
                    }
                }
            }

            // Params/receivers: check block-level permission
            if !self.scope.allows_mutation() {
                // Special case: "turn" is always mutable in action/reaction
                let is_turn = target.root == "turn" && self.scope.allows_turn();
                if !is_turn {
                    self.error(
                        "assignment to entity fields requires action, reaction, or hook context"
                            .to_string(),
                        span,
                    );
                }
            }
        }

        // Resolve target type
        let target_ty = self.resolve_lvalue_type(target);
        let hint = if matches!(op, AssignOp::Eq) {
            Some(&target_ty)
        } else {
            None
        };
        let value_ty = self.check_expr_expecting(value, hint);

        if target_ty.is_error() || value_ty.is_error() {
            return;
        }

        match op {
            AssignOp::Eq => {
                if !self.types_compatible(&value_ty, &target_ty) {
                    self.error(
                        format!("cannot assign {} to {}", value_ty, target_ty),
                        value.span,
                    );
                }
            }
            AssignOp::PlusEq | AssignOp::MinusEq => {
                // Target must be numeric
                if !target_ty.is_numeric() && !target_ty.is_int_like() {
                    self.error(format!("cannot use += / -= on type {}", target_ty), span);
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
                self.error(format!("undefined variable `{}`", lvalue.root), lvalue.span);
                return Ty::Error;
            }
        };

        let mut current = root_ty;
        let mut path_key = lvalue.root.to_string();
        for (seg_idx, seg) in lvalue.segments.iter().enumerate() {
            if current.is_error() {
                return Ty::Error;
            }
            match seg {
                LValueSegment::Field(name) => {
                    // Check if this field is a group alias
                    let resolved_name = if current.is_entity() {
                        if let Some(real_group) =
                            self.scope.resolve_group_alias(&path_key, name)
                        {
                            self.resolved_lvalue_aliases
                                .insert(lvalue.span, (seg_idx, real_group.clone()));
                            real_group
                        } else {
                            name.clone()
                        }
                    } else {
                        name.clone()
                    };
                    current = self.resolve_field(&current, &resolved_name, lvalue.span);
                    // Check narrowing for optional group access
                    if let Ty::OptionalGroupRef(ref entity_name, ref group_name) = current {
                        if !self.env.is_group_required(entity_name, group_name)
                            && !self.scope.is_group_narrowed(&path_key, group_name)
                        {
                            self.error(
                                    format!(
                                        "access to optional group `{}` on `{}` requires a `has` guard or `with` constraint",
                                        group_name, path_key
                                    ),
                                    lvalue.span,
                                );
                        }
                    }
                    path_key = format!("{}.{}", path_key, name);
                }
                LValueSegment::Index(idx_expr) => {
                    let idx_ty = self.check_expr(idx_expr);
                    if idx_ty.is_error() || current.is_error() {
                        return Ty::Error;
                    }
                    // Narrowing cannot be tracked through dynamic indexing
                    path_key.clear();
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
                            self.error(format!("cannot index into {}", current), lvalue.span);
                            return Ty::Error;
                        }
                    }
                }
            }
        }

        current
    }

    fn check_grant(
        &mut self,
        entity: &Spanned<ExprKind>,
        group_name: &str,
        fields: &[StructFieldInit],
        span: ttrpg_ast::Span,
    ) {
        self.check_name_visible(group_name, Namespace::Group, span);
        // grant/revoke only allowed in action/reaction/hook context
        if !self.scope.allows_mutation() {
            self.error(
                "grant is only allowed in action, reaction, or hook context".to_string(),
                span,
            );
        }

        let entity_ty = self.check_expr(entity);
        if entity_ty.is_error() {
            return;
        }

        let group = match &entity_ty {
            Ty::Entity(entity_name) => {
                match self.env.lookup_optional_group(entity_name, group_name) {
                    Some(g) => g.clone(),
                    None => {
                        self.error(
                            format!(
                                "entity `{}` has no optional group `{}`",
                                entity_name, group_name
                            ),
                            span,
                        );
                        return;
                    }
                }
            }
            Ty::AnyEntity => {
                if self.env.is_group_required_somewhere(group_name) {
                    self.error(
                        format!(
                            "group `{}` is required on some entity types and cannot be granted on type `entity`; use a concrete entity type",
                            group_name
                        ),
                        span,
                    );
                    return;
                }
                match self.env.unique_optional_group_owner(group_name) {
                    Some((_, g)) => g.clone(),
                    None if self.env.has_optional_group_named(group_name) => {
                        self.error(
                            format!(
                                "optional group `{}` is ambiguous on type `entity`; use a concrete entity type",
                                group_name
                            ),
                            span,
                        );
                        return;
                    }
                    None => {
                        self.error(
                            format!("unknown optional group `{}` for type `entity`", group_name),
                            span,
                        );
                        return;
                    }
                }
            }
            _ => {
                self.error(
                    format!("grant requires an entity, found {}", entity_ty),
                    span,
                );
                return;
            }
        };

        if group.required {
            self.error(
                format!(
                    "group `{}` is required on this entity and cannot be granted",
                    group_name
                ),
                span,
            );
            return;
        }

        // Validate field initializers
        let mut seen = std::collections::HashSet::new();
        for field in fields {
            let field_hint = group
                .fields
                .iter()
                .find(|f| f.name == field.name)
                .map(|fi| &fi.ty);
            let field_ty = self.check_expr_expecting(&field.value, field_hint);

            if !seen.insert(field.name.clone()) {
                self.error(
                    format!("duplicate field `{}` in grant", field.name),
                    field.span,
                );
                continue;
            }

            if field_ty.is_error() {
                continue;
            }

            if let Some(fi) = group.fields.iter().find(|f| f.name == field.name) {
                if !self.types_compatible(&field_ty, &fi.ty) {
                    self.error(
                        format!(
                            "field `{}` has type {}, expected {}",
                            field.name, field_ty, fi.ty
                        ),
                        field.span,
                    );
                }
            } else {
                self.error(
                    format!(
                        "optional group `{}` has no field `{}`",
                        group_name, field.name
                    ),
                    field.span,
                );
            }
        }

        // Check for missing required fields (no default)
        for fi in &group.fields {
            if !fi.has_default && !seen.contains(&fi.name) {
                self.error(
                    format!(
                        "missing required field `{}` in grant of `{}`",
                        fi.name, group_name
                    ),
                    span,
                );
            }
        }
    }

    fn check_emit(
        &mut self,
        event_name: &str,
        args: &[Arg],
        span: ttrpg_ast::Span,
    ) {
        // emit only allowed in action/reaction/hook context
        if !self.scope.allows_emit() {
            self.error(
                "emit is only allowed in action, reaction, or hook context".to_string(),
                span,
            );
        }

        // Look up event declaration
        let event_info = match self.env.events.get(event_name) {
            Some(info) => info.clone(),
            None => {
                self.error(format!("undefined event `{}`", event_name), span);
                // Still check arg expressions for other errors
                for arg in args {
                    self.check_expr(&arg.value);
                }
                return;
            }
        };

        // All args must be named
        for arg in args {
            if arg.name.is_none() {
                self.error(
                    "emit arguments must be named (e.g. `param: value`)".to_string(),
                    arg.span,
                );
            }
        }

        // Check for duplicate args
        let mut seen = std::collections::HashSet::new();
        for arg in args {
            if let Some(ref name) = arg.name {
                if !seen.insert(name.clone()) {
                    self.error(
                        format!("duplicate argument `{}` in emit", name),
                        arg.span,
                    );
                }
            }
        }

        // Match each named arg to event param, type-check value
        for arg in args {
            let arg_ty = if let Some(ref name) = arg.name {
                if let Some(param) = event_info.params.iter().find(|p| p.name == *name) {
                    self.check_expr_expecting(&arg.value, Some(&param.ty))
                } else {
                    let ty = self.check_expr(&arg.value);
                    self.error(
                        format!(
                            "event `{}` has no parameter `{}`",
                            event_name, name
                        ),
                        arg.span,
                    );
                    ty
                }
            } else {
                self.check_expr(&arg.value)
            };

            if arg_ty.is_error() {
                continue;
            }

            if let Some(ref name) = arg.name {
                if let Some(param) = event_info.params.iter().find(|p| p.name == *name) {
                    if !self.types_compatible(&arg_ty, &param.ty) {
                        self.error(
                            format!(
                                "argument `{}` has type {}, expected {}",
                                name, arg_ty, param.ty
                            ),
                            arg.span,
                        );
                    }
                }
            }
        }

        // Check all required params (no default) are provided
        for param in &event_info.params {
            if !param.has_default && !seen.contains(&param.name) {
                self.error(
                    format!(
                        "missing required argument `{}` in emit of `{}`",
                        param.name, event_name
                    ),
                    span,
                );
            }
        }
    }

    fn check_revoke(
        &mut self,
        entity: &Spanned<ExprKind>,
        group_name: &str,
        span: ttrpg_ast::Span,
    ) {
        self.check_name_visible(group_name, Namespace::Group, span);
        // grant/revoke only allowed in action/reaction/hook context
        if !self.scope.allows_mutation() {
            self.error(
                "revoke is only allowed in action, reaction, or hook context".to_string(),
                span,
            );
        }

        let entity_ty = self.check_expr(entity);
        if entity_ty.is_error() {
            return;
        }

        match &entity_ty {
            Ty::Entity(entity_name) => {
                match self.env.lookup_optional_group(entity_name, group_name) {
                    Some(group) if group.required => {
                        self.error(
                            format!(
                                "group `{}` is required on this entity and cannot be revoked",
                                group_name
                            ),
                            span,
                        );
                    }
                    Some(_) => {}
                    None => {
                        self.error(
                            format!(
                                "entity `{}` has no optional group `{}`",
                                entity_name, group_name
                            ),
                            span,
                        );
                    }
                }
            }
            Ty::AnyEntity => {
                if self.env.is_group_required_somewhere(group_name) {
                    self.error(
                        format!(
                            "group `{}` is required on some entity types and cannot be revoked on type `entity`; use a concrete entity type",
                            group_name
                        ),
                        span,
                    );
                    return;
                }
                if let Some((_, group)) = self.env.unique_optional_group_owner(group_name) {
                    if group.required {
                        self.error(
                            format!(
                                "group `{}` is required on this entity and cannot be revoked",
                                group_name
                            ),
                            span,
                        );
                    }
                } else if self.env.has_optional_group_named(group_name) {
                    self.error(
                        format!(
                            "optional group `{}` is ambiguous on type `entity`; use a concrete entity type",
                            group_name
                        ),
                        span,
                    );
                } else {
                    self.error(
                        format!("unknown optional group `{}` for type `entity`", group_name),
                        span,
                    );
                }
            }
            _ => {
                self.error(
                    format!("revoke requires an entity, found {}", entity_ty),
                    span,
                );
            }
        }
    }
}
