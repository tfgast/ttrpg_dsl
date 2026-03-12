use ttrpg_ast::ast::*;

use crate::check::{Checker, Namespace};
use crate::env::*;
use crate::ty::Ty;

impl Checker<'_> {
    pub(crate) fn check_ordinal_call(&mut self, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
        if args.len() != 1 {
            self.error(
                format!("`ordinal` expects 1 argument, found {}", args.len()),
                span,
            );
            for arg in args {
                self.check_expr(&arg.value);
            }
            return Ty::Error;
        }
        let arg_ty = self.check_expr(&args[0].value);
        if arg_ty.is_error() {
            return Ty::Error;
        }
        if let Ty::Enum(ref name) = arg_ty {
            if let Some(DeclInfo::Enum(info)) = self.env.types.get(name.as_str())
                && !info.ordered
            {
                self.error(
                    format!("`ordinal` requires an ordered enum, but `{name}` is not ordered"),
                    span,
                );
            }
            return Ty::Int;
        }
        self.error(
            format!("`ordinal` expects an enum value, found {arg_ty}"),
            span,
        );
        Ty::Error
    }

    pub(crate) fn check_from_ordinal_call(&mut self, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
        if args.len() != 2 {
            self.error(
                format!("`from_ordinal` expects 2 arguments, found {}", args.len()),
                span,
            );
            for arg in args {
                self.check_expr(&arg.value);
            }
            return Ty::Error;
        }
        let enum_ty = self.check_expr(&args[0].value);
        let idx_ty = self.check_expr(&args[1].value);
        if enum_ty.is_error() || idx_ty.is_error() {
            return Ty::Error;
        }
        let enum_name = if let Ty::EnumType(ref name) = enum_ty {
            name.clone()
        } else {
            self.error(
                format!("`from_ordinal` first argument must be an enum type, found {enum_ty}"),
                span,
            );
            return Ty::Error;
        };
        if let Some(DeclInfo::Enum(info)) = self.env.types.get(enum_name.as_str())
            && !info.ordered
        {
            self.error(
                format!(
                    "`from_ordinal` requires an ordered enum, but `{enum_name}` is not ordered"
                ),
                span,
            );
        }
        if !idx_ty.is_int_like() {
            self.error(
                format!("`from_ordinal` second argument must be int, found {idx_ty}"),
                span,
            );
        }
        Ty::Enum(enum_name)
    }

    pub(crate) fn check_try_from_ordinal_call(
        &mut self,
        args: &[Arg],
        span: ttrpg_ast::Span,
    ) -> Ty {
        if args.len() != 2 {
            self.error(
                format!(
                    "`try_from_ordinal` expects 2 arguments, found {}",
                    args.len()
                ),
                span,
            );
            for arg in args {
                self.check_expr(&arg.value);
            }
            return Ty::Error;
        }
        let enum_ty = self.check_expr(&args[0].value);
        let idx_ty = self.check_expr(&args[1].value);
        if enum_ty.is_error() || idx_ty.is_error() {
            return Ty::Error;
        }
        let enum_name = if let Ty::EnumType(ref name) = enum_ty {
            name.clone()
        } else {
            self.error(
                format!("`try_from_ordinal` first argument must be an enum type, found {enum_ty}"),
                span,
            );
            return Ty::Error;
        };
        if let Some(DeclInfo::Enum(info)) = self.env.types.get(enum_name.as_str())
            && !info.ordered
        {
            self.error(
                format!(
                    "`try_from_ordinal` requires an ordered enum, but `{enum_name}` is not ordered"
                ),
                span,
            );
        }
        if !idx_ty.is_int_like() {
            self.error(
                format!("`try_from_ordinal` second argument must be int, found {idx_ty}"),
                span,
            );
        }
        Ty::Option(Box::new(Ty::Enum(enum_name)))
    }

    // ── Collection builtins ─────────────────────────────────────

    pub(crate) fn check_len_call(&mut self, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
        if args.len() != 1 {
            self.error(
                format!("`len` expects 1 argument, found {}", args.len()),
                span,
            );
            for arg in args {
                self.check_expr(&arg.value);
            }
            return Ty::Error;
        }
        let arg_ty = self.check_expr(&args[0].value);
        if arg_ty.is_error() {
            return Ty::Error;
        }
        match arg_ty {
            Ty::List(_) | Ty::Set(_) | Ty::Map(_, _) => Ty::Int,
            _ => {
                self.error(
                    format!("`len` expects a list, set, or map, found {arg_ty}"),
                    span,
                );
                Ty::Error
            }
        }
    }

    pub(crate) fn check_keys_call(&mut self, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
        if args.len() != 1 {
            self.error(
                format!("`keys` expects 1 argument, found {}", args.len()),
                span,
            );
            for arg in args {
                self.check_expr(&arg.value);
            }
            return Ty::Error;
        }
        let arg_ty = self.check_expr(&args[0].value);
        if arg_ty.is_error() {
            return Ty::Error;
        }
        match arg_ty {
            Ty::Map(k, _) => Ty::List(k),
            _ => {
                self.error(format!("`keys` expects a map, found {arg_ty}"), span);
                Ty::Error
            }
        }
    }

    pub(crate) fn check_values_call(&mut self, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
        if args.len() != 1 {
            self.error(
                format!("`values` expects 1 argument, found {}", args.len()),
                span,
            );
            for arg in args {
                self.check_expr(&arg.value);
            }
            return Ty::Error;
        }
        let arg_ty = self.check_expr(&args[0].value);
        if arg_ty.is_error() {
            return Ty::Error;
        }
        match arg_ty {
            Ty::Map(_, v) => Ty::List(v),
            _ => {
                self.error(format!("`values` expects a map, found {arg_ty}"), span);
                Ty::Error
            }
        }
    }

    pub(crate) fn check_first_call(&mut self, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
        if args.len() != 1 {
            self.error(
                format!("`first` expects 1 argument, found {}", args.len()),
                span,
            );
            for arg in args {
                self.check_expr(&arg.value);
            }
            return Ty::Error;
        }
        let arg_ty = self.check_expr(&args[0].value);
        if arg_ty.is_error() {
            return Ty::Error;
        }
        match arg_ty {
            Ty::List(inner) => Ty::Option(inner),
            _ => {
                self.error(format!("`first` expects a list, found {arg_ty}"), span);
                Ty::Error
            }
        }
    }

    pub(crate) fn check_last_call(&mut self, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
        if args.len() != 1 {
            self.error(
                format!("`last` expects 1 argument, found {}", args.len()),
                span,
            );
            for arg in args {
                self.check_expr(&arg.value);
            }
            return Ty::Error;
        }
        let arg_ty = self.check_expr(&args[0].value);
        if arg_ty.is_error() {
            return Ty::Error;
        }
        match arg_ty {
            Ty::List(inner) => Ty::Option(inner),
            _ => {
                self.error(format!("`last` expects a list, found {arg_ty}"), span);
                Ty::Error
            }
        }
    }

    pub(crate) fn check_append_call(&mut self, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
        if args.len() != 2 {
            self.error(
                format!("`append` expects 2 arguments, found {}", args.len()),
                span,
            );
            for arg in args {
                self.check_expr(&arg.value);
            }
            return Ty::Error;
        }
        let list_ty = self.check_expr(&args[0].value);
        let elem_hint = match &list_ty {
            Ty::List(inner) => Some(inner.as_ref()),
            _ => None,
        };
        let elem_ty = self.check_expr_expecting(&args[1].value, elem_hint);
        if list_ty.is_error() || elem_ty.is_error() {
            return Ty::Error;
        }
        match list_ty {
            Ty::List(ref inner) => {
                if !self.types_compatible(inner, &elem_ty) {
                    self.error(
                        format!(
                            "`append` element type mismatch: list is {list_ty}, but got {elem_ty}"
                        ),
                        span,
                    );
                }
                list_ty
            }
            _ => {
                self.error(
                    format!("`append` first argument must be a list, found {list_ty}"),
                    span,
                );
                Ty::Error
            }
        }
    }

    pub(crate) fn check_concat_call(&mut self, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
        if args.len() != 2 {
            self.error(
                format!("`concat` expects 2 arguments, found {}", args.len()),
                span,
            );
            for arg in args {
                self.check_expr(&arg.value);
            }
            return Ty::Error;
        }
        let first_ty = self.check_expr(&args[0].value);
        let second_ty = self.check_expr_expecting(&args[1].value, Some(&first_ty));
        if first_ty.is_error() || second_ty.is_error() {
            return Ty::Error;
        }
        match (&first_ty, &second_ty) {
            (Ty::List(_), Ty::List(_)) => {
                if !self.types_compatible(&first_ty, &second_ty) {
                    self.error(
                        format!("`concat` list type mismatch: {first_ty} vs {second_ty}"),
                        span,
                    );
                }
                first_ty
            }
            (Ty::List(_), _) => {
                self.error(
                    format!("`concat` second argument must be a list, found {second_ty}"),
                    span,
                );
                Ty::Error
            }
            _ => {
                self.error(
                    format!("`concat` expects two lists, found {first_ty} and {second_ty}"),
                    span,
                );
                Ty::Error
            }
        }
    }

    pub(crate) fn check_reverse_call(&mut self, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
        if args.len() != 1 {
            self.error(
                format!("`reverse` expects 1 argument, found {}", args.len()),
                span,
            );
            for arg in args {
                self.check_expr(&arg.value);
            }
            return Ty::Error;
        }
        let arg_ty = self.check_expr(&args[0].value);
        if arg_ty.is_error() {
            return Ty::Error;
        }
        match arg_ty {
            Ty::List(_) => arg_ty,
            _ => {
                self.error(format!("`reverse` expects a list, found {arg_ty}"), span);
                Ty::Error
            }
        }
    }

    pub(crate) fn check_sum_call(&mut self, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
        if args.len() != 1 {
            self.error(
                format!("`sum` expects 1 argument, found {}", args.len()),
                span,
            );
            for arg in args {
                self.check_expr(&arg.value);
            }
            return Ty::Error;
        }
        let arg_ty = self.check_expr(&args[0].value);
        if arg_ty.is_error() {
            return Ty::Error;
        }
        match arg_ty {
            Ty::List(ref inner) => match inner.as_ref() {
                Ty::Int => Ty::Int,
                Ty::Float => Ty::Float,
                _ => {
                    self.error(
                        format!("`sum` requires list<int> or list<float>, found {arg_ty}"),
                        span,
                    );
                    Ty::Error
                }
            },
            _ => {
                self.error(format!("`sum` expects a list, found {arg_ty}"), span);
                Ty::Error
            }
        }
    }

    /// `max(a: Int, b: Int) -> Int` or `max(list: List[Int]) -> Int`
    pub(crate) fn check_max_call(&mut self, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
        self.check_min_max_call("max", args, span)
    }

    /// `min(a: Int, b: Int) -> Int` or `min(list: List[Int]) -> Int`
    pub(crate) fn check_min_call(&mut self, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
        self.check_min_max_call("min", args, span)
    }

    fn check_min_max_call(&mut self, name: &str, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
        match args.len() {
            2 => {
                let a_ty = self.check_expr(&args[0].value);
                let b_ty = self.check_expr(&args[1].value);
                if a_ty.is_error() || b_ty.is_error() {
                    return Ty::Error;
                }
                if a_ty != Ty::Int || b_ty != Ty::Int {
                    self.error(
                        format!("`{name}` expects (int, int) or (list<int>), got ({a_ty}, {b_ty})"),
                        span,
                    );
                    return Ty::Error;
                }
                Ty::Int
            }
            1 => {
                let arg_ty = self.check_expr(&args[0].value);
                if arg_ty.is_error() {
                    return Ty::Error;
                }
                match arg_ty {
                    Ty::List(ref inner) if matches!(inner.as_ref(), Ty::Int) => Ty::Int,
                    _ => {
                        self.error(
                            format!("`{name}` expects (int, int) or (list<int>), got ({arg_ty})"),
                            span,
                        );
                        Ty::Error
                    }
                }
            }
            _ => {
                self.error(
                    format!("`{name}` expects 1 or 2 arguments, found {}", args.len()),
                    span,
                );
                for arg in args {
                    self.check_expr(&arg.value);
                }
                Ty::Error
            }
        }
    }

    pub(crate) fn check_any_call(&mut self, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
        if args.len() != 1 {
            self.error(
                format!("`any` expects 1 argument, found {}", args.len()),
                span,
            );
            for arg in args {
                self.check_expr(&arg.value);
            }
            return Ty::Error;
        }
        let arg_ty = self.check_expr(&args[0].value);
        if arg_ty.is_error() {
            return Ty::Error;
        }
        match arg_ty {
            Ty::List(ref inner) if **inner == Ty::Bool => Ty::Bool,
            Ty::List(_) => {
                self.error(format!("`any` requires list<bool>, found {arg_ty}"), span);
                Ty::Error
            }
            _ => {
                self.error(format!("`any` expects a list, found {arg_ty}"), span);
                Ty::Error
            }
        }
    }

    pub(crate) fn check_all_call(&mut self, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
        if args.len() != 1 {
            self.error(
                format!("`all` expects 1 argument, found {}", args.len()),
                span,
            );
            for arg in args {
                self.check_expr(&arg.value);
            }
            return Ty::Error;
        }
        let arg_ty = self.check_expr(&args[0].value);
        if arg_ty.is_error() {
            return Ty::Error;
        }
        match arg_ty {
            Ty::List(ref inner) if **inner == Ty::Bool => Ty::Bool,
            Ty::List(_) => {
                self.error(format!("`all` requires list<bool>, found {arg_ty}"), span);
                Ty::Error
            }
            _ => {
                self.error(format!("`all` expects a list, found {arg_ty}"), span);
                Ty::Error
            }
        }
    }

    pub(crate) fn check_sort_call(&mut self, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
        if args.len() != 1 {
            self.error(
                format!("`sort` expects 1 argument, found {}", args.len()),
                span,
            );
            for arg in args {
                self.check_expr(&arg.value);
            }
            return Ty::Error;
        }
        let arg_ty = self.check_expr(&args[0].value);
        if arg_ty.is_error() {
            return Ty::Error;
        }
        match arg_ty {
            Ty::List(_) => arg_ty,
            _ => {
                self.error(format!("`sort` expects a list, found {arg_ty}"), span);
                Ty::Error
            }
        }
    }

    pub(crate) fn check_take_call(&mut self, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
        if args.len() != 2 {
            self.error(
                format!("`take` expects 2 arguments, found {}", args.len()),
                span,
            );
            for arg in args {
                self.check_expr(&arg.value);
            }
            return Ty::Error;
        }
        let list_ty = self.check_expr(&args[0].value);
        let n_ty = self.check_expr(&args[1].value);
        if list_ty.is_error() || n_ty.is_error() {
            return Ty::Error;
        }
        if n_ty != Ty::Int {
            self.error(
                format!("`take` expects int as second argument, found {n_ty}"),
                span,
            );
            return Ty::Error;
        }
        match list_ty {
            Ty::List(_) => list_ty,
            _ => {
                self.error(
                    format!("`take` expects a list as first argument, found {list_ty}"),
                    span,
                );
                Ty::Error
            }
        }
    }

    pub(crate) fn check_some_call(&mut self, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
        if args.len() != 1 {
            self.error(
                format!("`some` expects 1 argument, found {}", args.len()),
                span,
            );
            for arg in args {
                self.check_expr(&arg.value);
            }
            return Ty::Error;
        }
        let arg_ty = self.check_expr(&args[0].value);
        if arg_ty.is_error() {
            return Ty::Error;
        }
        Ty::Option(Box::new(arg_ty))
    }

    /// `revoke(inv)` accepts both `Invocation` and `option<Invocation>`.
    pub(crate) fn check_revoke_call(&mut self, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
        self.check_builtin_permissions("revoke", span);
        if args.len() != 1 {
            self.error(
                format!("`revoke` expects 1 argument, found {}", args.len()),
                span,
            );
            for arg in args {
                self.check_expr(&arg.value);
            }
            return Ty::Error;
        }
        let arg_ty = self.check_expr(&args[0].value);
        if arg_ty.is_error() {
            return Ty::Unit;
        }
        match &arg_ty {
            Ty::Invocation => Ty::Unit,
            Ty::Option(inner) if **inner == Ty::Invocation => Ty::Unit,
            // Also accept none (option<error>) since it's compatible with option<Invocation>
            _ if arg_ty.is_none() => Ty::Unit,
            _ => {
                self.error(
                    format!("`revoke` expects Invocation or option<Invocation>, found {arg_ty}"),
                    span,
                );
                Ty::Error
            }
        }
    }

    pub(crate) fn check_builtin_permissions(&mut self, name: &str, span: ttrpg_ast::Span) {
        match name {
            "roll" => {
                if !self.scope.allows_dice() {
                    self.error(
                        "roll() can only be called in mechanic, action, reaction, or hook blocks"
                            .to_string(),
                        span,
                    );
                }
            }
            "apply_condition" | "remove_condition" => {
                if !self.scope.allows_mutation() {
                    self.error(
                        format!("{name}() can only be called in function, action, reaction, or hook blocks"),
                        span,
                    );
                } else if !self.scope.allows_condition_manipulation() {
                    self.error(
                        format!("{name}() cannot be called inside on_apply/on_remove blocks"),
                        span,
                    );
                }
            }
            "invocation" => {
                if !self.scope.allows_invocation() {
                    self.error(
                        "invocation() can only be called in action, reaction, or hook blocks"
                            .to_string(),
                        span,
                    );
                }
            }
            "revoke" => {
                if !self.scope.allows_mutation() {
                    self.error(
                        "revoke() can only be called in function, action, reaction, or hook blocks"
                            .to_string(),
                        span,
                    );
                } else if !self.scope.allows_condition_manipulation() {
                    self.error(
                        "revoke() cannot be called inside on_apply/on_remove blocks".to_string(),
                        span,
                    );
                }
            }
            "advance_time" => {
                if !self.scope.is_inside_function() {
                    self.error(
                        "advance_time() can only be called in function blocks".to_string(),
                        span,
                    );
                }
            }
            "despawn" | "transfer_conditions" => {
                if !self.scope.allows_mutation() {
                    self.error(
                        format!("{name}() can only be called in function, action, reaction, hook, or lifecycle blocks"),
                        span,
                    );
                }
            }
            "suspend" => {
                // suspend() is lifecycle-only — runtime enforced (checker just checks mutation context)
                if !self.scope.allows_mutation() {
                    self.error(
                        "suspend() can only be called in lifecycle blocks (on_apply/on_remove)"
                            .to_string(),
                        span,
                    );
                }
            }
            "suspend_with_source" | "remove_suspension_source" => {
                if !self.scope.allows_mutation() {
                    self.error(
                        format!("{name}() can only be called in function, action, reaction, or hook blocks"),
                        span,
                    );
                }
            }
            _ => {}
        }
    }

    /// `conditions(entity, ConditionName) -> list<TypedActiveCondition<ConditionName>>`
    ///
    /// Two-arg overload: second arg must be a bare condition identifier (not a string).
    /// Returns a typed list where each element has params and `.state` accessible.
    pub(crate) fn check_typed_conditions_call(
        &mut self,
        args: &[Arg],
        span: ttrpg_ast::Span,
    ) -> Ty {
        // Check first arg (entity)
        let entity_ty = self.check_expr(&args[0].value);
        if !entity_ty.is_error() && !entity_ty.is_entity() {
            self.error(
                format!(
                    "`conditions` expects entity as first argument, got {}",
                    entity_ty.display()
                ),
                span,
            );
        }

        // Second arg must be a bare condition identifier
        let cond_name = match &args[1].value.node {
            ttrpg_ast::ast::ExprKind::Ident(name) => {
                if self.env.conditions.contains_key(name) {
                    self.check_name_visible(name, Namespace::Condition, args[1].value.span);
                    name.clone()
                } else {
                    self.error(
                        format!("`{name}` is not a known condition"),
                        args[1].value.span,
                    );
                    return Ty::Error;
                }
            }
            _ => {
                self.error(
                    "second argument to `conditions` must be a condition name",
                    args[1].value.span,
                );
                // Still check the expression for cascading errors
                self.check_expr(&args[1].value);
                return Ty::Error;
            }
        };

        Ty::List(Box::new(Ty::TypedActiveCondition(cond_name)))
    }

    /// `has_condition(entity, ConditionName) -> bool`
    ///
    /// Second arg must be a bare condition identifier (not a string).
    /// Returns true if the entity has an active instance of the named condition.
    pub(crate) fn check_typed_has_condition_call(
        &mut self,
        args: &[Arg],
        span: ttrpg_ast::Span,
    ) -> Ty {
        if args.len() != 2 {
            self.error(
                format!(
                    "`has_condition` expects 2 arguments, found {}",
                    args.len()
                ),
                span,
            );
            return Ty::Error;
        }

        // Check first arg (entity)
        let entity_ty = self.check_expr(&args[0].value);
        if !entity_ty.is_error() && !entity_ty.is_entity() {
            self.error(
                format!(
                    "`has_condition` expects entity as first argument, got {}",
                    entity_ty.display()
                ),
                span,
            );
        }

        // Second arg must be a bare condition identifier
        match &args[1].value.node {
            ttrpg_ast::ast::ExprKind::Ident(name) => {
                if self.env.conditions.contains_key(name) {
                    self.check_name_visible(name, Namespace::Condition, args[1].value.span);
                } else {
                    self.error(
                        format!("`{name}` is not a known condition"),
                        args[1].value.span,
                    );
                    return Ty::Error;
                }
            }
            _ => {
                self.error(
                    "second argument to `has_condition` must be a condition name",
                    args[1].value.span,
                );
                self.check_expr(&args[1].value);
                return Ty::Error;
            }
        };

        Ty::Bool
    }

    /// `to_any(value) -> any` — wraps any value into the `any` type.
    pub(crate) fn check_to_any_call(&mut self, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
        if args.len() != 1 {
            self.error(
                format!("`to_any` expects 1 argument, found {}", args.len()),
                span,
            );
            for arg in args {
                self.check_expr(&arg.value);
            }
            return Ty::Error;
        }
        let arg_ty = self.check_expr(&args[0].value);
        if arg_ty.is_error() {
            return Ty::Error;
        }
        Ty::Any
    }
}
