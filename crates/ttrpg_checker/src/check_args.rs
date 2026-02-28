use std::collections::HashSet;

use ttrpg_ast::ast::*;
use ttrpg_ast::Name;

use crate::check::Checker;
use crate::check_call::CallKind;
use crate::env::*;
use crate::scope::BlockKind;
use crate::ty::Ty;

impl<'a> Checker<'a> {
    // ── Alias-qualified expression resolution ──────────────────────

    /// Resolve the target system for a module alias in the current system.
    /// Returns the target system name, or emits an error and returns `None`.
    pub(crate) fn resolve_alias_target(
        &mut self,
        alias: &str,
        _span: ttrpg_ast::Span,
    ) -> Option<Name> {
        let current = self.current_system.as_ref()?;
        let aliases = self.env.system_aliases.get(current)?;
        aliases.get(alias).cloned()
    }

    /// Resolve field access on a module alias: `Alias.Name`.
    /// Handles enum types, enum variants, and conditions from the target system.
    pub(crate) fn resolve_alias_field(
        &mut self,
        alias: &str,
        field: &str,
        span: ttrpg_ast::Span,
    ) -> Ty {
        let target = match self.resolve_alias_target(alias, span) {
            Some(t) => t,
            None => {
                self.error(format!("unknown module alias `{}`", alias), span);
                return Ty::Error;
            }
        };

        // Check if the field is a type in the target system
        if let Some(sys_info) = self.modules.and_then(|m| m.systems.get(&target)) {
            if sys_info.types.contains(field) {
                if let Some(decl) = self.env.types.get(field) {
                    return match decl {
                        DeclInfo::Enum(_) => Ty::EnumType(Name::from(field)),
                        DeclInfo::Struct(_) | DeclInfo::Entity(_) | DeclInfo::Unit(_) => {
                            self.error(
                                format!("type `{}` cannot be used as a value", field),
                                span,
                            );
                            Ty::Error
                        }
                    };
                }
            }

            // Check if the field is a bare enum variant in the target system
            if sys_info.variants.contains(field) {
                if let Some(owners) = self.env.variant_to_enums.get(field) {
                    // Filter to enums that belong to this system
                    let matching: Vec<&Name> = owners
                        .iter()
                        .filter(|e| sys_info.types.contains(e.as_str()))
                        .collect();
                    let enum_name = if matching.len() == 1 {
                        matching[0]
                    } else if matching.len() > 1 {
                        let qualified: Vec<String> = matching
                            .iter()
                            .map(|e| format!("{}.{}.{}", alias, e, field))
                            .collect();
                        self.error(
                            format!(
                                "variant `{}` is ambiguous in system \"{}\" (alias `{}`); use a qualified form: {}",
                                field, target, alias, qualified.join(", ")
                            ),
                            span,
                        );
                        return Ty::Error;
                    } else {
                        self.error(
                            format!(
                                "variant `{}` is not defined by any enum in system \"{}\" (alias `{}`)",
                                field, target, alias
                            ),
                            span,
                        );
                        return Ty::Error;
                    };
                    if let Some(DeclInfo::Enum(info)) = self.env.types.get(enum_name.as_str()) {
                        if let Some(variant) = info.variants.iter().find(|v| v.name == field) {
                            if variant.fields.is_empty() {
                                return Ty::Enum(enum_name.clone());
                            } else {
                                self.error(
                                    format!(
                                        "variant `{}` has payload fields and must be called as a constructor",
                                        field
                                    ),
                                    span,
                                );
                                return Ty::Error;
                            }
                        }
                    }
                }
            }

            // Check if the field is a condition in the target system
            if sys_info.conditions.contains(field) {
                if let Some(cond_info) = self.env.conditions.get(field) {
                    let required_params =
                        cond_info.params.iter().filter(|p| !p.has_default).count();
                    if required_params > 0 {
                        self.error(
                            format!(
                                "condition `{}` requires {} parameter(s); use `{}.{}(...)` to supply them",
                                field, required_params, alias, field
                            ),
                            span,
                        );
                    }
                    return Ty::Condition;
                }
            }
        }

        self.error(
            format!(
                "no type, variant, or condition `{}` in system \"{}\" (alias `{}`)",
                field, target, alias
            ),
            span,
        );
        Ty::Error
    }

    /// Resolve a call through a module alias: `Alias.name(args)`.
    /// Handles function calls, condition calls, and enum constructors.
    pub(crate) fn resolve_alias_call(
        &mut self,
        alias: &str,
        field: &str,
        args: &[Arg],
        span: ttrpg_ast::Span,
    ) -> Ty {
        let target = match self.resolve_alias_target(alias, span) {
            Some(t) => t,
            None => {
                self.error(format!("unknown module alias `{}`", alias), span);
                for arg in args {
                    self.check_expr(&arg.value);
                }
                return Ty::Error;
            }
        };

        if let Some(sys_info) = self.modules.and_then(|m| m.systems.get(&target)) {
            // Check if it's a condition call
            if sys_info.conditions.contains(field) {
                if let Some(cond_info) = self.env.conditions.get(field).cloned() {
                    return self.check_alias_condition_call(field, &cond_info.params, args, span);
                }
            }

            // Check if it's a function call
            if sys_info.functions.contains(field) {
                // Delegate to normal function checking with the resolved name
                return self.check_alias_function_call(field, args, span);
            }

            // Check if it's an enum variant constructor
            if sys_info.variants.contains(field) {
                if let Some(owners) = self.env.variant_to_enums.get(field) {
                    // Filter to enums that belong to this system
                    let matching: Vec<&Name> = owners
                        .iter()
                        .filter(|e| sys_info.types.contains(e.as_str()))
                        .collect();
                    let enum_name = if matching.len() == 1 {
                        matching[0].clone()
                    } else if matching.len() > 1 {
                        let qualified: Vec<String> = matching
                            .iter()
                            .map(|e| format!("{}.{}.{}", alias, e, field))
                            .collect();
                        self.error(
                            format!(
                                "variant `{}` is ambiguous in system \"{}\" (alias `{}`); use a qualified form: {}",
                                field, target, alias, qualified.join(", ")
                            ),
                            span,
                        );
                        for arg in args {
                            self.check_expr(&arg.value);
                        }
                        return Ty::Error;
                    } else {
                        self.error(
                            format!(
                                "variant `{}` is not defined by any enum in system \"{}\" (alias `{}`)",
                                field, target, alias
                            ),
                            span,
                        );
                        for arg in args {
                            self.check_expr(&arg.value);
                        }
                        return Ty::Error;
                    };
                    return self.check_enum_constructor(&enum_name, field, args, span);
                }
            }
        }

        self.error(
            format!(
                "no function, condition, or variant `{}` in system \"{}\" (alias `{}`)",
                field, target, alias
            ),
            span,
        );
        for arg in args {
            self.check_expr(&arg.value);
        }
        Ty::Error
    }

    /// Validate arguments against a parameter list. Handles named/positional resolution,
    /// duplicate detection, type compatibility, with-group constraints, and required parameters.
    pub(crate) fn check_args(
        &mut self,
        callee_name: &str,
        kind: CallKind,
        params: &[ParamInfo],
        args: &[Arg],
        span: ttrpg_ast::Span,
    ) {
        let mut satisfied: HashSet<usize> = HashSet::new();
        let mut next_positional = 0usize;

        for arg in args.iter() {
            let param_idx = if let Some(ref name) = arg.name {
                params.iter().position(|p| p.name == *name)
            } else {
                while next_positional < params.len() && satisfied.contains(&next_positional) {
                    next_positional += 1;
                }
                if next_positional < params.len() {
                    let idx = next_positional;
                    next_positional += 1;
                    Some(idx)
                } else {
                    None
                }
            };

            let param_hint = param_idx.map(|idx| &params[idx].ty);
            let arg_ty = self.check_expr_expecting(&arg.value, param_hint);

            if let Some(idx) = param_idx {
                if !satisfied.insert(idx) {
                    self.error(
                        format!("duplicate argument for parameter `{}`", params[idx].name),
                        arg.span,
                    );
                }

                if !arg_ty.is_error() && !self.types_compatible(&arg_ty, &params[idx].ty) {
                    match kind {
                        CallKind::Condition => {
                            self.error(
                                format!(
                                    "condition `{}` parameter `{}` has type {}, got {}",
                                    callee_name, params[idx].name, params[idx].ty, arg_ty
                                ),
                                arg.value.span,
                            );
                        }
                        CallKind::Function => {
                            self.error(
                                format!(
                                    "argument `{}` has type {}, expected {}",
                                    params[idx].name, arg_ty, params[idx].ty
                                ),
                                arg.span,
                            );
                        }
                    }
                }

                // Check `with` group constraints at call site (skip for disjunctive)
                if !params[idx].with_groups.is_empty() && !params[idx].with_disjunctive {
                    if let Some(path_key) = self.extract_path_key(&arg.value) {
                        for group in &params[idx].with_groups {
                            if !self.scope.is_group_narrowed(&path_key, group) {
                                self.error(
                                    format!(
                                        "argument `{}` requires `{}` to have group `{}` proven active via `has` guard or `with` constraint",
                                        params[idx].name, path_key, group
                                    ),
                                    arg.span,
                                );
                            }
                        }
                    } else {
                        for group in &params[idx].with_groups {
                            self.error(
                                format!(
                                    "argument `{}` requires group `{}` proven active, but the expression cannot be statically tracked",
                                    params[idx].name, group
                                ),
                                arg.span,
                            );
                        }
                    }
                }
            } else if let Some(ref name) = arg.name {
                match kind {
                    CallKind::Condition => {
                        self.error(
                            format!("condition `{}` has no parameter `{}`", callee_name, name),
                            arg.span,
                        );
                    }
                    CallKind::Function => {
                        self.error(
                            format!("`{}` has no parameter `{}`", callee_name, name),
                            arg.span,
                        );
                    }
                }
            } else {
                match kind {
                    CallKind::Condition => {
                        self.error(
                            format!(
                                "condition `{}` accepts at most {} argument(s), found {}",
                                callee_name,
                                params.len(),
                                args.len()
                            ),
                            span,
                        );
                    }
                    CallKind::Function => {
                        self.error(
                            format!(
                                "`{}` expects at most {} argument(s), found {}",
                                callee_name,
                                params.len(),
                                args.len()
                            ),
                            span,
                        );
                    }
                }
                break;
            }
        }

        // Check that all required (non-default) parameters were provided
        for (idx, param) in params.iter().enumerate() {
            if !param.has_default && !satisfied.contains(&idx) {
                match kind {
                    CallKind::Condition => {
                        self.error(
                            format!(
                                "missing required argument `{}` in call to condition `{}`",
                                param.name, callee_name
                            ),
                            span,
                        );
                    }
                    CallKind::Function => {
                        self.error(
                            format!(
                                "missing required argument `{}` in call to `{}`",
                                param.name, callee_name
                            ),
                            span,
                        );
                    }
                }
            }
        }
    }

    /// Type-check a condition call reached through an alias (reuses condition checking logic).
    fn check_alias_condition_call(
        &mut self,
        name: &str,
        params: &[ParamInfo],
        args: &[Arg],
        span: ttrpg_ast::Span,
    ) -> Ty {
        self.check_args(name, CallKind::Condition, params, args, span);
        Ty::Condition
    }

    /// Type-check a function call reached through an alias (delegates to normal function checking).
    fn check_alias_function_call(
        &mut self,
        name: &str,
        args: &[Arg],
        span: ttrpg_ast::Span,
    ) -> Ty {
        let fn_info = match self.env.lookup_fn(name) {
            Some(info) => info.clone(),
            None => {
                self.error(format!("undefined function `{}`", name), span);
                for arg in args {
                    self.check_expr(&arg.value);
                }
                return Ty::Error;
            }
        };

        // In TriggerBinding context, only side-effect-free builtins are allowed
        if !self.scope.allows_calls() {
            let is_pure_builtin = fn_info.kind == FnKind::Builtin
                && matches!(
                    name,
                    "floor" | "ceil" | "min" | "max" | "distance" | "error"
                );
            if !is_pure_builtin {
                self.error(
                    format!(
                        "`{}` cannot be called in trigger/suppress binding context",
                        name
                    ),
                    span,
                );
            }
        }

        // Check permission level for builtins
        if fn_info.kind == FnKind::Builtin {
            self.check_builtin_permissions(name, span);
        }

        // Reject direct reaction/hook calls
        if fn_info.kind == FnKind::Reaction || fn_info.kind == FnKind::Hook {
            let kind_name = if fn_info.kind == FnKind::Reaction {
                "reactions"
            } else {
                "hooks"
            };
            self.error(
                format!(
                    "{} cannot be called directly; `{}` is triggered by events",
                    kind_name, name
                ),
                span,
            );
        }

        // Check context restrictions for actions
        if fn_info.kind == FnKind::Action {
            let current_ctx = self.scope.current_block_kind();
            if !matches!(
                current_ctx,
                Some(BlockKind::ActionResolve)
                    | Some(BlockKind::ReactionResolve)
                    | Some(BlockKind::HookResolve)
            ) {
                self.error(
                    format!(
                        "`{}` is an action and can only be called from action or reaction context",
                        name
                    ),
                    span,
                );
            }
        }

        // Build effective params
        let effective_params: Vec<ParamInfo> = if let Some(ref receiver) = fn_info.receiver {
            let mut params = vec![receiver.clone()];
            params.extend(fn_info.params.iter().cloned());
            params
        } else {
            fn_info.params.clone()
        };

        self.check_args(name, CallKind::Function, &effective_params, args, span);
        fn_info.return_type.clone()
    }
}
