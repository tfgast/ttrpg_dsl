use ttrpg_ast::ast::*;
use ttrpg_ast::Name;
use ttrpg_ast::Spanned;

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
                    self.error(
                        format!("unknown optional group `{group_name}` for type `entity`"),
                        span,
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
        if let Some(ref alias_name) = alias {
            if let Ty::Entity(ent_name) = &entity_ty {
                if let Some(fields) = self.env.lookup_fields(ent_name) {
                    if fields.iter().any(|f| f.name == *alias_name) {
                        self.error(
                            format!("alias `{alias_name}` shadows a field on entity `{ent_name}`"),
                            span,
                        );
                    }
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
