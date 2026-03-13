use std::collections::HashSet;

use ttrpg_ast::Name;
use ttrpg_ast::Spanned;
use ttrpg_ast::ast::*;

use crate::check::{Checker, Namespace};
use crate::env::*;
use crate::scope::BlockKind;
use crate::ty::Ty;

/// Controls error message phrasing for condition vs function calls.
pub(crate) enum CallKind {
    Condition,
    Function,
}

impl Checker<'_> {
    pub(crate) fn check_call(
        &mut self,
        callee: &Spanned<ExprKind>,
        args: &[Arg],
        span: ttrpg_ast::Span,
        hint: Option<&Ty>,
    ) -> Ty {
        // Resolve the callee name
        let callee_name = match &callee.node {
            ExprKind::Ident(name) => name.clone(),
            ExprKind::FieldAccess { object, field } => {
                // Qualified call like Type.Variant(args) — enum constructor
                let obj_ty = self.check_expr(object);
                if obj_ty.is_error() {
                    return Ty::Error;
                }
                if let Ty::EnumType(enum_name) = &obj_ty {
                    return self.check_enum_constructor(enum_name, field, args, span);
                }
                // Alias-qualified call: Alias.function(args)
                if let Ty::ModuleAlias(alias_name) = &obj_ty {
                    return self.resolve_alias_call(alias_name, field, args, span);
                }
                // Action method call: entity.Action(args)
                if obj_ty.is_entity()
                    && let Some(fn_info) = self.env.lookup_fn(field).cloned()
                    && fn_info.kind == FnKind::Action
                {
                    // Check module visibility (same as direct call path)
                    self.check_name_visible(field, Namespace::Function, span);

                    // Select the best overload for this receiver type.
                    // If found, use its params for arg checking; otherwise
                    // verify against the representative and report mismatch.
                    let resolved = self
                        .env
                        .lookup_action_overload(field, &obj_ty)
                        .cloned()
                        .unwrap_or(fn_info);

                    if let Some(ref receiver) = resolved.receiver
                        && !self.types_compatible(&obj_ty, &receiver.ty)
                    {
                        self.error(
                            format!(
                                "action `{}` expects receiver of type {}, found {}",
                                field,
                                receiver.ty.display(),
                                obj_ty.display()
                            ),
                            span,
                        );
                    }

                    // Check context restrictions (same as function-call path)
                    let current_ctx = self.scope.current_block_kind();
                    if !matches!(
                        current_ctx,
                        Some(
                            BlockKind::FunctionBody
                                | BlockKind::ActionResolve
                                | BlockKind::ReactionResolve
                                | BlockKind::HookResolve
                                | BlockKind::WithBudget
                                | BlockKind::PeriodicBlock
                                | BlockKind::OnEventBlock
                        )
                    ) {
                        self.error(
                                    format!(
                                        "`{field}` is an action and can only be called from function, action, reaction, or hook context"
                                    ),
                                    span,
                                );
                    }

                    // Check args against action params (without receiver — it's the object)
                    self.check_args(field, CallKind::Function, &resolved.params, args, span);
                    return resolved.return_type.clone();
                }
                // Check if the field is a fn-ref type on a struct (e.g., entry.resolve(args))
                if let Ty::Struct(ref struct_name) = obj_ty
                    && let Some(crate::env::DeclInfo::Struct(info)) =
                        self.env.types.get(struct_name.as_str())
                    && let Some(field_info) = info.fields.iter().find(|f| f.name == *field)
                    && let Ty::Fn(ref param_tys, ref ret_ty) = field_info.ty
                {
                    let param_tys = param_tys.clone();
                    let ret_ty = ret_ty.clone();
                    return self.check_fn_ref_call(&param_tys, &ret_ty, args, span);
                }
                // Method call: obj.method(args)
                return self.check_method_call(&obj_ty, field, args, span);
            }
            _ => {
                // General fallback: evaluate the callee as an expression and check
                // if it produces a function reference type.
                let callee_ty = self.check_expr(callee);
                if let Ty::Fn(ref param_tys, ref ret_ty) = callee_ty {
                    return self.check_fn_ref_call(param_tys, ret_ty, args, span);
                }
                if !callee_ty.is_error() {
                    self.error(
                        format!("expression of type {} is not callable", callee_ty.display()),
                        span,
                    );
                }
                for arg in args {
                    self.check_expr(&arg.value);
                }
                return Ty::Error;
            }
        };

        // If a local binding shadows the name, it wins.
        // If the binding is a fn type, allow calling through it.
        if let Some(binding) = self.scope.lookup(&callee_name) {
            let binding_ty = binding.ty.clone();
            if let Ty::Fn(ref param_tys, ref ret_ty) = binding_ty {
                return self.check_fn_ref_call(param_tys, ret_ty, args, span);
            }
            self.error(
                format!(
                    "`{callee_name}` is a local binding of type {binding_ty}, not a callable function"
                ),
                callee.span,
            );
            for arg in args {
                self.check_expr(&arg.value);
            }
            return Ty::Error;
        }

        // Check if it's a condition call (e.g., Frightened(source: attacker))
        if let Some(cond_info) = self.env.conditions.get(&callee_name).cloned() {
            self.check_name_visible(&callee_name, Namespace::Condition, span);
            self.check_args(
                &callee_name,
                CallKind::Condition,
                &cond_info.params,
                args,
                span,
            );
            return Ty::Condition;
        }

        // Check ordinal() / from_ordinal() builtins for ordered enums
        if callee_name == "ordinal" {
            return self.check_ordinal_call(args, span);
        }
        if callee_name == "from_ordinal" {
            return self.check_from_ordinal_call(args, span);
        }
        if callee_name == "try_from_ordinal" {
            return self.check_try_from_ordinal_call(args, span);
        }

        // Check collection builtins (polymorphic — can't use FnInfo)
        match callee_name.as_str() {
            "len" => return self.check_len_call(args, span),
            "keys" => return self.check_keys_call(args, span),
            "values" => return self.check_values_call(args, span),
            "first" => return self.check_first_call(args, span),
            "last" => return self.check_last_call(args, span),
            "append" => return self.check_append_call(args, span),
            "concat" => return self.check_concat_call(args, span),
            "reverse" => return self.check_reverse_call(args, span),
            "sum" => return self.check_sum_call(args, span),
            "any" => return self.check_any_call(args, span),
            "all" => return self.check_all_call(args, span),
            "sort" => return self.check_sort_call(args, span),
            "take" => return self.check_take_call(args, span),
            "max" => return self.check_max_call(args, span),
            "min" => return self.check_min_call(args, span),
            "some" => return self.check_some_call(args, span),
            "revoke" => return self.check_revoke_call(args, span),
            "to_any" => return self.check_to_any_call(args, span),
            "conditions" if args.len() == 2 => return self.check_typed_conditions_call(args, span),
            "has_condition" => return self.check_typed_has_condition_call(args, span),
            _ => {}
        }

        // Check if it's an enum variant constructor (bare name)
        if let Some(enum_name) =
            self.resolve_bare_variant_with_hint(&callee_name, callee.span, hint)
        {
            self.check_name_visible(&callee_name, Namespace::Variant, span);
            return self.check_enum_constructor(&enum_name, &callee_name, args, span);
        } else if self.is_known_variant(&callee_name) {
            // Ambiguity error already emitted
            for arg in args {
                self.check_expr(&arg.value);
            }
            return Ty::Error;
        }

        // Look up function
        let fn_info = match self.env.lookup_fn(&callee_name) {
            Some(info) => info.clone(),
            None => {
                self.error(format!("undefined function `{callee_name}`"), callee.span);
                for arg in args {
                    self.check_expr(&arg.value);
                }
                return Ty::Error;
            }
        };

        // Check module visibility (builtins are always visible — they have no owner)
        if fn_info.kind != FnKind::Builtin {
            self.check_name_visible(&callee_name, Namespace::Function, span);
        }

        // In TriggerBinding context, only side-effect-free builtins are allowed
        if !self.scope.allows_calls() {
            let is_pure_builtin = fn_info.kind == FnKind::Builtin
                && matches!(
                    callee_name.as_str(),
                    "floor"
                        | "ceil"
                        | "min"
                        | "max"
                        | "distance"
                        | "conditions"
                        | "has_condition"
                        | "error"
                        | "budget_of"
                );
            if !is_pure_builtin {
                self.error(
                    format!("`{callee_name}` cannot be called in trigger/suppress binding context"),
                    span,
                );
            }
        }

        // Check permission level for builtins
        if fn_info.kind == FnKind::Builtin {
            self.check_builtin_permissions(&callee_name, span);
        }

        // Special-case: validate tag string literal for transfer_conditions/process_periodic_conditions
        if fn_info.kind == FnKind::Builtin
            && matches!(
                callee_name.as_str(),
                "transfer_conditions" | "process_periodic_conditions"
            )
        {
            // Tag is the last argument (index 2 for transfer_conditions, index 1 for process_periodic_conditions)
            let tag_idx = if callee_name == "transfer_conditions" {
                2
            } else {
                1
            };
            if let Some(tag_arg) = args.get(tag_idx)
                && let ExprKind::StringLit(ref tag_str) = tag_arg.value.node
            {
                let tag_name: ttrpg_ast::Name = tag_str.as_str().into();
                if !self.env.tags.contains(&tag_name) {
                    self.error_with_help(
                        format!(
                            "undeclared tag `{tag_str}` in {callee_name}() — \
                             no `tag {tag_str}` declaration found"
                        ),
                        tag_arg.value.span,
                        format!("declare it with: tag {tag_str}"),
                    );
                }
            }
        }

        // Reject direct reaction/hook calls — they are triggered by events, not called
        if fn_info.kind == FnKind::Reaction || fn_info.kind == FnKind::Hook {
            let kind_name = if fn_info.kind == FnKind::Reaction {
                "reactions"
            } else {
                "hooks"
            };
            self.error(
                format!(
                    "{kind_name} cannot be called directly; `{callee_name}` is triggered by events"
                ),
                span,
            );
        }

        // Check context restrictions for functions (callable from function/action/reaction/hook/with_budget/lifecycle)
        if fn_info.kind == FnKind::Function {
            let current_ctx = self.scope.current_block_kind();
            if !matches!(
                current_ctx,
                Some(
                    BlockKind::FunctionBody
                        | BlockKind::ActionResolve
                        | BlockKind::ReactionResolve
                        | BlockKind::HookResolve
                        | BlockKind::WithBudget
                        | BlockKind::LifecycleBlock
                        | BlockKind::PeriodicBlock
                        | BlockKind::OnEventBlock
                )
            ) {
                self.error(
                    format!(
                        "`{callee_name}` is a function and can only be called from function, action, reaction, hook, or lifecycle context"
                    ),
                    span,
                );
            }
        }

        // Check context restrictions for actions
        if fn_info.kind == FnKind::Action {
            let current_ctx = self.scope.current_block_kind();
            if !matches!(
                current_ctx,
                Some(
                    BlockKind::FunctionBody
                        | BlockKind::ActionResolve
                        | BlockKind::ReactionResolve
                        | BlockKind::HookResolve
                        | BlockKind::WithBudget
                        | BlockKind::LifecycleBlock
                        | BlockKind::PeriodicBlock
                        | BlockKind::OnEventBlock
                )
            ) {
                self.error(
                    format!(
                        "`{callee_name}` is an action and can only be called from function, action, reaction, hook, or lifecycle context"
                    ),
                    span,
                );
            }
        }

        // Build effective params: include receiver as first param for actions/reactions
        let effective_params: Vec<ParamInfo> = if let Some(ref receiver) = fn_info.receiver {
            let mut params = vec![receiver.clone()];
            params.extend(fn_info.params.iter().cloned());
            params
        } else {
            fn_info.params.clone()
        };

        self.check_args(
            &callee_name,
            CallKind::Function,
            &effective_params,
            args,
            span,
        );
        fn_info.return_type.clone()
    }

    pub(crate) fn check_enum_constructor(
        &mut self,
        enum_name: &str,
        variant_name: &str,
        args: &[Arg],
        span: ttrpg_ast::Span,
    ) -> Ty {
        let info = match self.env.types.get(enum_name) {
            Some(DeclInfo::Enum(info)) => info.clone(),
            _ => {
                self.error(format!("undefined enum `{enum_name}`"), span);
                return Ty::Error;
            }
        };

        let variant = match info.variants.iter().find(|v| v.name == variant_name) {
            Some(v) => v,
            None => {
                self.error(
                    format!("enum `{enum_name}` has no variant `{variant_name}`"),
                    span,
                );
                return Ty::Error;
            }
        };

        if variant.fields.is_empty() && !args.is_empty() {
            self.error(
                format!(
                    "variant `{}` takes no arguments, found {}",
                    variant_name,
                    args.len()
                ),
                span,
            );
            return Ty::Enum(Name::from(enum_name));
        }

        // Track which field indices are satisfied (like check_call)
        let mut satisfied: HashSet<usize> = HashSet::new();
        let mut next_positional = 0usize;

        for arg in args {
            let field_idx = if let Some(ref name) = arg.name {
                variant.fields.iter().position(|(n, _)| n == name)
            } else {
                // Skip fields already claimed by named args
                while next_positional < variant.fields.len() && satisfied.contains(&next_positional)
                {
                    next_positional += 1;
                }
                if next_positional < variant.fields.len() {
                    let idx = next_positional;
                    next_positional += 1;
                    Some(idx)
                } else {
                    None
                }
            };

            let field_hint = field_idx.map(|idx| &variant.fields[idx].1);
            let arg_ty = self.check_expr_expecting(&arg.value, field_hint);

            if let Some(idx) = field_idx {
                if !satisfied.insert(idx) {
                    self.error(
                        format!(
                            "duplicate argument for variant field `{}`",
                            variant.fields[idx].0
                        ),
                        arg.span,
                    );
                }

                if !arg_ty.is_error() {
                    let (ref fname, ref expected) = variant.fields[idx];
                    if !self.types_compatible(&arg_ty, expected) {
                        self.error(
                            format!("variant field `{fname}` has type {expected}, found {arg_ty}"),
                            arg.span,
                        );
                    }
                }
            } else if let Some(ref name) = arg.name {
                self.error(
                    format!("variant `{variant_name}` has no field `{name}`"),
                    arg.span,
                );
            } else {
                self.error(
                    format!(
                        "variant `{}` takes {} argument(s), found {}",
                        variant_name,
                        variant.fields.len(),
                        args.len()
                    ),
                    span,
                );
                break;
            }
        }

        // Check for missing required fields (those without defaults)
        for (idx, (fname, _)) in variant.fields.iter().enumerate() {
            if !satisfied.contains(&idx) {
                let has_default = variant.has_defaults.get(idx).copied().unwrap_or(false);
                if !has_default {
                    self.error(
                        format!("missing required field `{fname}` in variant `{variant_name}`"),
                        span,
                    );
                }
            }
        }

        Ty::Enum(Name::from(enum_name))
    }

    /// Check a call through a function reference (fn type).
    /// Validates positional args against the fn type's parameter types.
    /// Named args are not supported for fn ref calls (no param names available).
    fn check_fn_ref_call(
        &mut self,
        param_tys: &[Ty],
        ret_ty: &Ty,
        args: &[Arg],
        span: ttrpg_ast::Span,
    ) -> Ty {
        // Reject named arguments — fn types don't carry parameter names
        for arg in args {
            if let Some(ref name) = arg.name {
                self.error(
                    format!(
                        "named argument `{name}` is not supported when calling through a function reference"
                    ),
                    arg.span,
                );
            }
        }

        if args.len() != param_tys.len() {
            self.error(
                format!(
                    "function reference expects {} argument(s), found {}",
                    param_tys.len(),
                    args.len()
                ),
                span,
            );
        }

        // Check each argument type (exact match, not types_compatible)
        for (i, arg) in args.iter().enumerate() {
            let hint = param_tys.get(i);
            let arg_ty = self.check_expr_expecting(&arg.value, hint);
            if !arg_ty.is_error()
                && let Some(expected) = param_tys.get(i)
                && !expected.is_error()
                && arg_ty != *expected
            {
                self.error(
                    format!(
                        "argument {} has type {}, expected {}",
                        i + 1,
                        arg_ty.display(),
                        expected.display()
                    ),
                    arg.span,
                );
            }
        }

        ret_ty.clone()
    }
}
