use ttrpg_ast::ast::*;
use ttrpg_ast::Spanned;

use crate::check::{Checker, Namespace};
use crate::env::DeclInfo;
use crate::scope::VarBinding;
use crate::ty::Ty;

impl<'a> Checker<'a> {
    /// Check a pattern against the scrutinee type, binding variables into scope.
    pub fn check_pattern(&mut self, pattern: &Spanned<PatternKind>, scrutinee_ty: &Ty) {
        match &pattern.node {
            PatternKind::Wildcard => {}

            PatternKind::NoneLit => {
                if !scrutinee_ty.is_error() && !matches!(scrutinee_ty, Ty::Option(_)) {
                    self.error(
                        format!(
                            "`none` pattern cannot match type {}",
                            scrutinee_ty
                        ),
                        pattern.span,
                    );
                }
            }

            PatternKind::Some(inner) => {
                match scrutinee_ty {
                    Ty::Option(inner_ty) => {
                        self.check_pattern(inner, inner_ty);
                    }
                    _ if scrutinee_ty.is_error() => {
                        self.check_pattern(inner, &Ty::Error);
                    }
                    _ => {
                        self.error(
                            format!(
                                "`some(...)` pattern cannot match type {}",
                                scrutinee_ty
                            ),
                            pattern.span,
                        );
                    }
                }
            }

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
                // Could be a bare enum variant or a binding variable.
                // Use scrutinee type to disambiguate multi-owner variants.
                if let Some(owners) = self.env.variant_to_enums.get(name).cloned() {
                    // Determine which enum this variant belongs to in context
                    let enum_name = if let Ty::Enum(ref s_enum) = scrutinee_ty {
                        // Scrutinee type disambiguates
                        if owners.contains(s_enum) {
                            Some(s_enum.clone())
                        } else {
                            // Variant doesn't belong to the scrutinee's enum
                            let owner_list: Vec<String> = owners.iter()
                                .map(|e| format!("`{}`", e))
                                .collect();
                            self.error(
                                format!(
                                    "variant `{}` belongs to {}, not `{}`",
                                    name,
                                    owner_list.join(" and "),
                                    s_enum,
                                ),
                                pattern.span,
                            );
                            None
                        }
                    } else if owners.len() == 1 {
                        if scrutinee_ty.is_error() {
                            Some(owners[0].clone())
                        } else {
                            self.error(
                                format!(
                                    "variant pattern `{}` cannot match type {}",
                                    name, scrutinee_ty
                                ),
                                pattern.span,
                            );
                            None
                        }
                    } else if !scrutinee_ty.is_error() {
                        self.error(
                            format!(
                                "variant pattern `{}` cannot match type {}",
                                name, scrutinee_ty
                            ),
                            pattern.span,
                        );
                        None
                    } else {
                        None
                    };

                    if let Some(ref resolved) = enum_name {
                        self.check_name_visible(name, Namespace::Variant, pattern.span);
                        self.resolved_variants.insert(pattern.span, resolved.clone());
                        // Reject bare pattern for variants with payload fields
                        if let Some(DeclInfo::Enum(info)) = self.env.types.get(resolved) {
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
                    self.check_name_visible(ty, Namespace::Type, pattern.span);
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
                } else if self.env.types.contains_key(ty) {
                    self.error(
                        format!("`{}` is not an enum; qualified variant patterns require an enum type", ty),
                        pattern.span,
                    );
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
                    self.check_name_visible(ty, Namespace::Type, pattern.span);
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
                } else if self.env.types.contains_key(ty) {
                    self.error(
                        format!("`{}` is not an enum; qualified variant patterns require an enum type", ty),
                        pattern.span,
                    );
                } else {
                    self.error(format!("undefined type `{}`", ty), pattern.span);
                }
            }

            PatternKind::BareDestructure {
                name,
                fields: sub_patterns,
            } => {
                // Variant(patterns) — unqualified, disambiguate via scrutinee type
                if let Some(owners) = self.env.variant_to_enums.get(name).cloned() {
                    // Determine which enum this variant belongs to
                    let enum_name = if let Ty::Enum(ref s_enum) = scrutinee_ty {
                        if owners.contains(s_enum) {
                            Some(s_enum.clone())
                        } else {
                            let owner_list: Vec<String> = owners.iter()
                                .map(|e| format!("`{}`", e))
                                .collect();
                            self.error(
                                format!(
                                    "variant `{}` belongs to {}, not `{}`",
                                    name,
                                    owner_list.join(" and "),
                                    s_enum,
                                ),
                                pattern.span,
                            );
                            None
                        }
                    } else if owners.len() == 1 {
                        if scrutinee_ty.is_error() {
                            Some(owners[0].clone())
                        } else {
                            self.error(
                                format!(
                                    "variant pattern `{}` cannot match type {}",
                                    name, scrutinee_ty
                                ),
                                pattern.span,
                            );
                            None
                        }
                    } else if !scrutinee_ty.is_error() {
                        self.error(
                            format!(
                                "variant pattern `{}` cannot match type {}",
                                name, scrutinee_ty
                            ),
                            pattern.span,
                        );
                        None
                    } else {
                        None
                    };

                    if let Some(ref resolved) = enum_name {
                        self.check_name_visible(name, Namespace::Variant, pattern.span);
                        self.resolved_variants.insert(pattern.span, resolved.clone());
                        if let Some(DeclInfo::Enum(info)) = self.env.types.get(resolved) {
                            if let Some(var_info) = info.variants.iter().find(|v| v.name == *name) {
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
