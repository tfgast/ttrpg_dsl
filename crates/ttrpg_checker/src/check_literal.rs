use std::collections::HashSet;

use ttrpg_ast::ast::*;
use ttrpg_ast::Name;
use ttrpg_ast::Spanned;

use crate::check::{Checker, Namespace};
use crate::env::*;
use crate::ty::Ty;

impl<'a> Checker<'a> {
    pub(crate) fn check_struct_lit(
        &mut self,
        name: &str,
        fields: &[StructFieldInit],
        base: Option<&Spanned<ExprKind>>,
        span: ttrpg_ast::Span,
    ) -> Ty {
        let decl = match self.env.types.get(name) {
            Some(d) => d.clone(),
            None => {
                self.error(format!("undefined type `{}`", name), span);
                return Ty::Error;
            }
        };

        self.check_name_visible(name, Namespace::Type, span);

        let (declared_fields, result_ty) = match &decl {
            DeclInfo::Struct(info) => (&info.fields, Ty::Struct(Name::from(name))),
            DeclInfo::Unit(info) => (&info.fields, Ty::UnitType(Name::from(name))),
            DeclInfo::Entity(_) => {
                self.error(
                    format!(
                        "cannot construct entity `{}` with struct literal syntax",
                        name
                    ),
                    span,
                );
                return Ty::Error;
            }
            DeclInfo::Enum(_) => {
                self.error(
                    format!(
                        "cannot construct enum `{}` with struct literal syntax",
                        name
                    ),
                    span,
                );
                return Ty::Error;
            }
        };

        // Validate base expression if present
        let has_base = if let Some(base_expr) = base {
            let base_ty = self.check_expr(base_expr);
            if !base_ty.is_error() && base_ty != result_ty {
                self.error(
                    format!(
                        "base expression has type {}, expected {}",
                        base_ty, result_ty
                    ),
                    base_expr.span,
                );
            }
            true
        } else {
            false
        };

        // Check each provided field
        let mut seen = HashSet::new();
        for field in fields {
            let field_hint = declared_fields
                .iter()
                .find(|f| f.name == field.name)
                .map(|fi| &fi.ty);
            let field_ty = self.check_expr_expecting(&field.value, field_hint);

            // Detect duplicate initializers
            if !seen.insert(field.name.clone()) {
                self.error(
                    format!("duplicate field `{}` in struct literal", field.name),
                    field.span,
                );
                continue;
            }

            if field_ty.is_error() {
                continue;
            }
            if let Some(fi) = declared_fields.iter().find(|f| f.name == field.name) {
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
                    format!("type `{}` has no field `{}`", name, field.name),
                    field.span,
                );
            }
        }

        // Check for missing required fields (no default) — skip when base provides them
        if !has_base {
            for fi in declared_fields.iter() {
                if !fi.has_default && !seen.contains(&fi.name) {
                    self.error(
                        format!("missing required field `{}` in `{}` literal", fi.name, name),
                        span,
                    );
                }
            }
        }

        result_ty
    }

    pub(crate) fn check_list_lit(
        &mut self,
        elems: &[Spanned<ExprKind>],
        _span: ttrpg_ast::Span,
        elem_hint: Option<&Ty>,
    ) -> Ty {
        if elems.is_empty() {
            // Use the expected element type hint if available (e.g. from return type),
            // otherwise fall back to Error which will produce a type mismatch.
            let elem_ty = elem_hint.cloned().unwrap_or(Ty::Error);
            return Ty::List(Box::new(elem_ty));
        }

        let mut unified_ty = self.check_expr_expecting(&elems[0], elem_hint);
        for elem in &elems[1..] {
            let elem_ty = self.check_expr_expecting(elem, Some(&unified_ty));
            match self.unify_branch_types(&unified_ty, &elem_ty) {
                Some(ty) => unified_ty = ty,
                None => {
                    self.error(
                        format!("list element has type {}, expected {}", elem_ty, unified_ty),
                        elem.span,
                    );
                }
            }
        }

        Ty::List(Box::new(unified_ty))
    }

    pub(crate) fn check_map_lit(
        &mut self,
        entries: &[(Spanned<ExprKind>, Spanned<ExprKind>)],
        _span: ttrpg_ast::Span,
        key_hint: Option<&Ty>,
        val_hint: Option<&Ty>,
    ) -> Ty {
        if entries.is_empty() {
            let key_ty = key_hint.cloned().unwrap_or(Ty::Error);
            let val_ty = val_hint.cloned().unwrap_or(Ty::Error);
            return Ty::Map(Box::new(key_ty), Box::new(val_ty));
        }

        let mut unified_key = self.check_expr_expecting(&entries[0].0, key_hint);
        let mut unified_val = self.check_expr_expecting(&entries[0].1, val_hint);

        for (key, value) in &entries[1..] {
            let key_ty = self.check_expr_expecting(key, Some(&unified_key));
            match self.unify_branch_types(&unified_key, &key_ty) {
                Some(ty) => unified_key = ty,
                None => {
                    self.error(
                        format!("map key has type {}, expected {}", key_ty, unified_key),
                        key.span,
                    );
                }
            }

            let val_ty = self.check_expr_expecting(value, Some(&unified_val));
            match self.unify_branch_types(&unified_val, &val_ty) {
                Some(ty) => unified_val = ty,
                None => {
                    self.error(
                        format!("map value has type {}, expected {}", val_ty, unified_val),
                        value.span,
                    );
                }
            }
        }

        Ty::Map(Box::new(unified_key), Box::new(unified_val))
    }
}
