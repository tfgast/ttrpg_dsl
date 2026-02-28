use std::collections::HashSet;

use ttrpg_ast::ast::*;
use ttrpg_ast::Name;
use ttrpg_ast::Spanned;

use crate::check::{Checker, Namespace};
use crate::env::*;
use crate::scope::BlockKind;
use crate::ty::Ty;

/// Controls error message phrasing for condition vs function calls.
pub(crate) enum CallKind {
    Condition,
    Function,
}

impl<'a> Checker<'a> {
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
                if obj_ty.is_entity() {
                    if let Some(fn_info) = self.env.lookup_fn(field).cloned() {
                        if fn_info.kind == FnKind::Action {
                            // Verify receiver type compatibility
                            if let Some(ref receiver) = fn_info.receiver {
                                if !self.types_compatible(&obj_ty, &receiver.ty) {
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
                            }

                            // Check context restrictions (same as function-call path)
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
                                        field
                                    ),
                                    span,
                                );
                            }

                            // Check args against action params (without receiver — it's the object)
                            self.check_args(field, CallKind::Function, &fn_info.params, args, span);
                            return fn_info.return_type.clone();
                        }
                    }
                }
                // Method call: obj.method(args)
                return self.check_method_call(&obj_ty, field, args, span);
            }
            _ => {
                self.error("callee must be a function name".to_string(), span);
                return Ty::Error;
            }
        };

        // If a local binding shadows the name, it wins — local values aren't callable.
        if let Some(binding) = self.scope.lookup(&callee_name) {
            self.error(
                format!(
                    "`{}` is a local binding of type {}, not a callable function",
                    callee_name, binding.ty
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
            "some" => return self.check_some_call(args, span),
            "revoke" => return self.check_revoke_call(args, span),
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
                self.error(format!("undefined function `{}`", callee_name), callee.span);
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
                    "floor" | "ceil" | "min" | "max" | "distance" | "error"
                );
            if !is_pure_builtin {
                self.error(
                    format!(
                        "`{}` cannot be called in trigger/suppress binding context",
                        callee_name
                    ),
                    span,
                );
            }
        }

        // Check permission level for builtins
        if fn_info.kind == FnKind::Builtin {
            self.check_builtin_permissions(&callee_name, span);
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
                    "{} cannot be called directly; `{}` is triggered by events",
                    kind_name, callee_name
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
                        callee_name
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
                self.error(format!("undefined enum `{}`", enum_name), span);
                return Ty::Error;
            }
        };

        let variant = match info.variants.iter().find(|v| v.name == variant_name) {
            Some(v) => v,
            None => {
                self.error(
                    format!("enum `{}` has no variant `{}`", enum_name, variant_name),
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
                while next_positional < variant.fields.len()
                    && satisfied.contains(&next_positional)
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
                            format!(
                                "variant field `{}` has type {}, found {}",
                                fname, expected, arg_ty
                            ),
                            arg.span,
                        );
                    }
                }
            } else if let Some(ref name) = arg.name {
                self.error(
                    format!("variant `{}` has no field `{}`", variant_name, name),
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

        // All variant fields are required (no defaults)
        for (idx, (fname, _)) in variant.fields.iter().enumerate() {
            if !satisfied.contains(&idx) {
                self.error(
                    format!(
                        "missing required field `{}` in variant `{}`",
                        fname, variant_name
                    ),
                    span,
                );
            }
        }

        Ty::Enum(Name::from(enum_name))
    }
}
