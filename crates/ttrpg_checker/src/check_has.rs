use ttrpg_ast::Name;
use ttrpg_ast::Spanned;
use ttrpg_ast::ast::*;

use crate::check::{Checker, Namespace};
use crate::ty::Ty;

impl Checker<'_> {
    pub(crate) fn check_has(
        &mut self,
        entity: &Spanned<ExprKind>,
        group_name: &str,
        alias: &Option<Name>,
        span: ttrpg_ast::Span,
    ) -> Ty {
        self.check_name_visible(group_name, Namespace::Group, span);
        let entity_ty = self.check_expr(entity);
        if entity_ty.is_error() {
            return Ty::Bool;
        }
        match &entity_ty {
            Ty::Entity(name) => {
                if self.env.lookup_optional_group(name, group_name).is_none() {
                    self.error(
                        format!("entity `{name}` has no optional group `{group_name}`"),
                        span,
                    );
                }
            }
            Ty::AnyEntity => {
                if self.env.lookup_group(group_name).is_none()
                    && !self.env.has_optional_group_named(group_name)
                {
                    self.error_with_help(
                        format!("unknown optional group `{group_name}` for type `entity`"),
                        span,
                        format!("declare it with: group {group_name} {{ ... }}"),
                    );
                }
            }
            _ => {
                self.error(
                    format!("`has` can only be used with entity types, found {entity_ty}"),
                    span,
                );
            }
        }
        // Validate that alias doesn't shadow an existing field or group on the entity type
        if let Some(alias_name) = alias
            && let Ty::Entity(ent_name) = &entity_ty
        {
            if let Some(fields) = self.env.lookup_fields(ent_name)
                && fields.iter().any(|f| f.name == *alias_name)
            {
                self.error(
                    format!("alias `{alias_name}` shadows a field on entity `{ent_name}`"),
                    span,
                );
            }
            if self
                .env
                .lookup_flattened_field(ent_name, alias_name)
                .is_some()
            {
                self.error(
                    format!("alias `{alias_name}` shadows a field on entity `{ent_name}`"),
                    span,
                );
            }
            if self
                .env
                .lookup_optional_group(ent_name, alias_name)
                .is_some()
            {
                self.error(
                    format!(
                        "alias `{alias_name}` shadows an optional group on entity `{ent_name}`"
                    ),
                    span,
                );
            }
        }
        Ty::Bool
    }

    /// Extract the full dot-separated path key from an expression chain.
    /// Returns `Some("actor")` for `actor`, `Some("actor.foo")` for `actor.foo`, etc.
    /// Returns `None` for expressions involving indexing or non-variable roots,
    /// since narrowing cannot be statically tracked through dynamic access.
    #[allow(clippy::self_only_used_in_recursion)]
    pub(crate) fn extract_path_key(&self, expr: &Spanned<ExprKind>) -> Option<Name> {
        match &expr.node {
            ExprKind::Ident(name) => Some(name.clone()),
            ExprKind::FieldAccess { object, field } => self
                .extract_path_key(object)
                .map(|p| Name::from(format!("{p}.{field}"))),
            ExprKind::Paren(inner) => self.extract_path_key(inner),
            _ => None,
        }
    }

    pub(crate) fn check_is(
        &mut self,
        expr: &Spanned<ExprKind>,
        target_type: &Spanned<TypeExpr>,
        span: ttrpg_ast::Span,
    ) -> Ty {
        // Resolve the target type expression
        let target_ty = self.resolve_type_validated(target_type);

        // Validate: target must be a concrete type, not `any`, `entity`, `error`, or `unit`
        match &target_ty {
            Ty::Any => {
                self.error("`is any` is not meaningful — use a concrete type", span);
                return Ty::Bool;
            }
            Ty::AnyEntity => {
                self.error(
                    "`is entity` is not meaningful — use a specific entity type",
                    span,
                );
                return Ty::Bool;
            }
            Ty::Error => return Ty::Bool,
            _ => {}
        }

        // Check the expression being tested
        let expr_ty = self.check_expr(expr);
        if expr_ty.is_error() {
            return Ty::Bool;
        }

        match &expr_ty {
            // `any` can be tested against any concrete type
            Ty::Any => {}
            // `entity` (AnyEntity) can be tested against entity types
            Ty::AnyEntity => {
                if !matches!(target_ty, Ty::Entity(_)) {
                    self.error(
                        format!(
                            "`is` on entity value requires an entity type, found {}",
                            target_ty.display()
                        ),
                        span,
                    );
                }
            }
            // Specific entity can be tested against entity types
            Ty::Entity(name) => {
                if let Ty::Entity(target_name) = &target_ty {
                    if name == target_name {
                        self.warning(format!("`is {}` is always true here", target_name), span);
                    }
                } else {
                    self.error(
                        format!(
                            "`is` on entity value requires an entity type, found {}",
                            target_ty.display()
                        ),
                        span,
                    );
                }
            }
            // ActiveCondition can be tested against ActiveCondition<CondName>
            Ty::ActiveCondition => {
                if !matches!(target_ty, Ty::TypedActiveCondition(_)) {
                    self.error(
                        format!(
                            "`is` on ActiveCondition requires ActiveCondition<CondName>, found {}",
                            target_ty.display()
                        ),
                        span,
                    );
                }
            }
            // TypedActiveCondition can be tested (always-true warning if same)
            Ty::TypedActiveCondition(name) => {
                if let Ty::TypedActiveCondition(target_name) = &target_ty {
                    if name == target_name {
                        self.warning(
                            format!("`is {}` is always true here", target_ty.display()),
                            span,
                        );
                    }
                } else {
                    self.error(
                        format!(
                            "`is` on ActiveCondition requires ActiveCondition<CondName>, found {}",
                            target_ty.display()
                        ),
                        span,
                    );
                }
            }
            _ => {
                self.error(
                    format!(
                        "`is` can only be used with `any`, entity, or ActiveCondition types, found {}",
                        expr_ty.display()
                    ),
                    span,
                );
            }
        }
        Ty::Bool
    }

    /// Extract `(path_key, target_ty)` narrowing tuples from an `is` condition.
    pub(crate) fn extract_is_narrowings(&self, expr: &Spanned<ExprKind>) -> Vec<(Name, Ty)> {
        match &expr.node {
            ExprKind::Is {
                expr: is_expr,
                target_type,
            } => {
                if let Some(path_key) = self.extract_path_key(is_expr) {
                    let ty = self.env.resolve_type(target_type);
                    if !ty.is_error() {
                        vec![(path_key, ty)]
                    } else {
                        vec![]
                    }
                } else {
                    vec![]
                }
            }
            ExprKind::BinOp {
                op: BinOp::And,
                lhs,
                rhs,
            } => {
                let mut narrowings = self.extract_is_narrowings(lhs);
                narrowings.extend(self.extract_is_narrowings(rhs));
                narrowings
            }
            ExprKind::Paren(inner) => self.extract_is_narrowings(inner),
            _ => vec![],
        }
    }

    /// Extract `(path_key, group_name, alias)` narrowing tuples from a `has` condition.
    /// Supports `entity has Group`, `entity has Group as alias`, `a and b` composition,
    /// and parenthesized expressions.
    pub(crate) fn extract_has_narrowings(
        &self,
        expr: &Spanned<ExprKind>,
    ) -> Vec<(Name, Name, Option<Name>)> {
        match &expr.node {
            ExprKind::Has {
                entity,
                group_name,
                alias,
            } => {
                if let Some(path_key) = self.extract_path_key(entity) {
                    vec![(path_key, group_name.clone(), alias.clone())]
                } else {
                    vec![]
                }
            }
            ExprKind::BinOp {
                op: BinOp::And,
                lhs,
                rhs,
            } => {
                let mut narrowings = self.extract_has_narrowings(lhs);
                narrowings.extend(self.extract_has_narrowings(rhs));
                narrowings
            }
            ExprKind::Paren(inner) => self.extract_has_narrowings(inner),
            _ => vec![],
        }
    }
}
