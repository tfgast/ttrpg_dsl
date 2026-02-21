use ttrpg_ast::ast::*;
use ttrpg_ast::Spanned;

use crate::check::Checker;
use crate::env::DeclInfo;
use crate::scope::VarBinding;
use crate::ty::Ty;

impl<'a> Checker<'a> {
    /// Check a pattern against the scrutinee type, binding variables into scope.
    pub fn check_pattern(&mut self, pattern: &Spanned<PatternKind>, scrutinee_ty: &Ty) {
        match &pattern.node {
            PatternKind::Wildcard => {}

            PatternKind::IntLit(_) => {
                if !scrutinee_ty.is_error() && !scrutinee_ty.is_int_like() {
                    self.error(
                        format!(
                            "integer pattern cannot match type {}",
                            scrutinee_ty
                        ),
                        pattern.span,
                    );
                }
            }

            PatternKind::StringLit(_) => {
                if !scrutinee_ty.is_error() && *scrutinee_ty != Ty::String {
                    self.error(
                        format!(
                            "string pattern cannot match type {}",
                            scrutinee_ty
                        ),
                        pattern.span,
                    );
                }
            }

            PatternKind::BoolLit(_) => {
                if !scrutinee_ty.is_error() && *scrutinee_ty != Ty::Bool {
                    self.error(
                        format!(
                            "bool pattern cannot match type {}",
                            scrutinee_ty
                        ),
                        pattern.span,
                    );
                }
            }

            PatternKind::Ident(name) => {
                // Could be a bare enum variant or a binding variable
                if let Some(enum_name) = self.env.variant_to_enum.get(name).cloned() {
                    // It's a variant — check it matches the scrutinee enum
                    if let Ty::Enum(ref s_enum) = scrutinee_ty {
                        if *s_enum != enum_name {
                            self.error(
                                format!(
                                    "variant `{}` belongs to enum `{}`, not `{}`",
                                    name, enum_name, s_enum
                                ),
                                pattern.span,
                            );
                        }
                    } else if !scrutinee_ty.is_error() {
                        self.error(
                            format!(
                                "variant pattern `{}` cannot match type {}",
                                name, scrutinee_ty
                            ),
                            pattern.span,
                        );
                    }
                    // Reject bare pattern for variants with payload fields
                    if let Some(DeclInfo::Enum(info)) = self.env.types.get(&enum_name) {
                        if let Some(var_info) = info.variants.iter().find(|v| v.name == *name) {
                            if !var_info.fields.is_empty() {
                                self.error(
                                    format!(
                                        "variant `{}` has {} field(s); use destructuring pattern `{}(...)` or a wildcard",
                                        name, var_info.fields.len(), name
                                    ),
                                    pattern.span,
                                );
                            }
                        }
                    }
                } else {
                    // It's a binding variable — bind to scrutinee type
                    if self.scope.has_in_current_scope(name) {
                        self.error(
                            format!("duplicate binding `{}` in pattern", name),
                            pattern.span,
                        );
                    } else {
                        self.scope.bind(
                            name.clone(),
                            VarBinding {
                                ty: scrutinee_ty.clone(),
                                mutable: false,
                                is_local: true,
                            },
                        );
                    }
                }
            }

            PatternKind::QualifiedVariant { ty, variant } => {
                // Type.Variant
                if let Some(DeclInfo::Enum(info)) = self.env.types.get(ty) {
                    if let Some(var_info) = info.variants.iter().find(|v| v.name == *variant) {
                        // Reject bare qualified pattern for variants with payload fields
                        if !var_info.fields.is_empty() {
                            self.error(
                                format!(
                                    "variant `{}.{}` has {} field(s); use destructuring pattern `{}.{}(...)` or a wildcard",
                                    ty, variant, var_info.fields.len(), ty, variant
                                ),
                                pattern.span,
                            );
                        }
                    } else {
                        self.error(
                            format!("enum `{}` has no variant `{}`", ty, variant),
                            pattern.span,
                        );
                    }
                    // Check scrutinee is this enum type
                    if let Ty::Enum(ref s_enum) = scrutinee_ty {
                        if s_enum != ty {
                            self.error(
                                format!(
                                    "qualified variant `{}.{}` cannot match enum `{}`",
                                    ty, variant, s_enum
                                ),
                                pattern.span,
                            );
                        }
                    } else if !scrutinee_ty.is_error() {
                        self.error(
                            format!(
                                "qualified variant pattern cannot match type {}",
                                scrutinee_ty
                            ),
                            pattern.span,
                        );
                    }
                } else {
                    self.error(format!("undefined type `{}`", ty), pattern.span);
                }
            }

            PatternKind::QualifiedDestructure {
                ty,
                variant,
                fields: sub_patterns,
            } => {
                // Type.Variant(patterns)
                if let Some(DeclInfo::Enum(info)) = self.env.types.get(ty) {
                    if let Some(var_info) = info.variants.iter().find(|v| v.name == *variant) {
                        // Check scrutinee type
                        if let Ty::Enum(ref s_enum) = scrutinee_ty {
                            if s_enum != ty {
                                self.error(
                                    format!(
                                        "qualified variant `{}.{}` cannot match enum `{}`",
                                        ty, variant, s_enum
                                    ),
                                    pattern.span,
                                );
                            }
                        } else if !scrutinee_ty.is_error() {
                            self.error(
                                format!(
                                    "qualified variant pattern cannot match type {}",
                                    scrutinee_ty
                                ),
                                pattern.span,
                            );
                        }

                        // Bind sub-pattern fields
                        if sub_patterns.len() != var_info.fields.len() {
                            self.error(
                                format!(
                                    "variant `{}.{}` has {} field(s), found {} in pattern",
                                    ty,
                                    variant,
                                    var_info.fields.len(),
                                    sub_patterns.len()
                                ),
                                pattern.span,
                            );
                        }
                        for (sub, field) in sub_patterns.iter().zip(var_info.fields.iter()) {
                            self.check_pattern(sub, &field.1);
                        }
                    } else {
                        self.error(
                            format!("enum `{}` has no variant `{}`", ty, variant),
                            pattern.span,
                        );
                    }
                } else {
                    self.error(format!("undefined type `{}`", ty), pattern.span);
                }
            }

            PatternKind::BareDestructure {
                name,
                fields: sub_patterns,
            } => {
                // Variant(patterns) — unqualified
                if let Some(enum_name) = self.env.variant_to_enum.get(name).cloned() {
                    if let Some(DeclInfo::Enum(info)) = self.env.types.get(&enum_name) {
                        if let Some(var_info) = info.variants.iter().find(|v| v.name == *name) {
                            // Check scrutinee type
                            if let Ty::Enum(ref s_enum) = scrutinee_ty {
                                if *s_enum != enum_name {
                                    self.error(
                                        format!(
                                            "variant `{}` belongs to enum `{}`, not `{}`",
                                            name, enum_name, s_enum
                                        ),
                                        pattern.span,
                                    );
                                }
                            } else if !scrutinee_ty.is_error() {
                                self.error(
                                    format!(
                                        "variant pattern `{}` cannot match type {}",
                                        name, scrutinee_ty
                                    ),
                                    pattern.span,
                                );
                            }

                            if sub_patterns.len() != var_info.fields.len() {
                                self.error(
                                    format!(
                                        "variant `{}` has {} field(s), found {} in pattern",
                                        name,
                                        var_info.fields.len(),
                                        sub_patterns.len()
                                    ),
                                    pattern.span,
                                );
                            }
                            for (sub, field) in sub_patterns.iter().zip(var_info.fields.iter()) {
                                self.check_pattern(sub, &field.1);
                            }
                        }
                    }
                } else {
                    self.error(
                        format!("undefined variant `{}`", name),
                        pattern.span,
                    );
                }
            }
        }
    }
}
