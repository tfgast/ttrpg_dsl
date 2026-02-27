use ttrpg_ast::ast::*;

use crate::check::Checker;
use crate::env::*;
use crate::ty::Ty;

impl<'a> Checker<'a> {
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
            if let Some(DeclInfo::Enum(info)) = self.env.types.get(name.as_str()) {
                if !info.ordered {
                    self.error(
                        format!(
                            "`ordinal` requires an ordered enum, but `{}` is not ordered",
                            name
                        ),
                        span,
                    );
                }
            }
            return Ty::Int;
        }
        self.error(
            format!("`ordinal` expects an enum value, found {}", arg_ty),
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
                format!(
                    "`from_ordinal` first argument must be an enum type, found {}",
                    enum_ty
                ),
                span,
            );
            return Ty::Error;
        };
        if let Some(DeclInfo::Enum(info)) = self.env.types.get(enum_name.as_str()) {
            if !info.ordered {
                self.error(
                    format!(
                        "`from_ordinal` requires an ordered enum, but `{}` is not ordered",
                        enum_name
                    ),
                    span,
                );
            }
        }
        if !idx_ty.is_int_like() {
            self.error(
                format!(
                    "`from_ordinal` second argument must be int, found {}",
                    idx_ty
                ),
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
                format!(
                    "`try_from_ordinal` first argument must be an enum type, found {}",
                    enum_ty
                ),
                span,
            );
            return Ty::Error;
        };
        if let Some(DeclInfo::Enum(info)) = self.env.types.get(enum_name.as_str()) {
            if !info.ordered {
                self.error(
                    format!(
                        "`try_from_ordinal` requires an ordered enum, but `{}` is not ordered",
                        enum_name
                    ),
                    span,
                );
            }
        }
        if !idx_ty.is_int_like() {
            self.error(
                format!(
                    "`try_from_ordinal` second argument must be int, found {}",
                    idx_ty
                ),
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
                    format!("`len` expects a list, set, or map, found {}", arg_ty),
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
                self.error(format!("`keys` expects a map, found {}", arg_ty), span);
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
                self.error(format!("`values` expects a map, found {}", arg_ty), span);
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
                self.error(format!("`first` expects a list, found {}", arg_ty), span);
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
                self.error(format!("`last` expects a list, found {}", arg_ty), span);
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
                            "`append` element type mismatch: list is {}, but got {}",
                            list_ty, elem_ty
                        ),
                        span,
                    );
                }
                list_ty
            }
            _ => {
                self.error(
                    format!("`append` first argument must be a list, found {}", list_ty),
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
                        format!("`concat` list type mismatch: {} vs {}", first_ty, second_ty),
                        span,
                    );
                }
                first_ty
            }
            (Ty::List(_), _) => {
                self.error(
                    format!(
                        "`concat` second argument must be a list, found {}",
                        second_ty
                    ),
                    span,
                );
                Ty::Error
            }
            _ => {
                self.error(
                    format!(
                        "`concat` expects two lists, found {} and {}",
                        first_ty, second_ty
                    ),
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
                self.error(format!("`reverse` expects a list, found {}", arg_ty), span);
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
                        format!("`sum` requires list<int> or list<float>, found {}", arg_ty),
                        span,
                    );
                    Ty::Error
                }
            },
            _ => {
                self.error(format!("`sum` expects a list, found {}", arg_ty), span);
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
                self.error(format!("`any` requires list<bool>, found {}", arg_ty), span);
                Ty::Error
            }
            _ => {
                self.error(format!("`any` expects a list, found {}", arg_ty), span);
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
                self.error(format!("`all` requires list<bool>, found {}", arg_ty), span);
                Ty::Error
            }
            _ => {
                self.error(format!("`all` expects a list, found {}", arg_ty), span);
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
                self.error(format!("`sort` expects a list, found {}", arg_ty), span);
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

    pub(crate) fn check_builtin_permissions(&mut self, name: &str, span: ttrpg_ast::Span) {
        match name {
            "roll" => {
                if !self.scope.allows_dice() {
                    self.error(
                        "roll() can only be called in mechanic, action, or reaction blocks"
                            .to_string(),
                        span,
                    );
                }
            }
            "apply_condition" | "remove_condition" => {
                if !self.scope.allows_mutation() {
                    self.error(
                        format!("{}() can only be called in action or reaction blocks", name),
                        span,
                    );
                }
            }
            _ => {}
        }
    }
}
