use ttrpg_ast::ast::*;

use crate::check::Checker;
use crate::ty::Ty;

impl Checker<'_> {
    pub(crate) fn check_method_call(
        &mut self,
        obj_ty: &Ty,
        method: &str,
        args: &[Arg],
        span: ttrpg_ast::Span,
    ) -> Ty {
        match obj_ty {
            Ty::Option(inner) => self.check_option_method(inner, method, args, span),
            Ty::List(inner) => self.check_list_method(inner.clone(), method, args, span),
            Ty::Set(inner) => self.check_set_method(inner, method, args, span),
            Ty::Map(k, v) => self.check_map_method(k.clone(), v.clone(), method, args, span),
            Ty::DiceExpr => self.check_dice_method(method, args, span),
            Ty::String => self.check_string_method(method, args, span),
            _ => {
                self.error(format!("type {obj_ty} has no methods"), span);
                Ty::Error
            }
        }
    }

    fn check_option_method(
        &mut self,
        inner_ty: &Ty,
        method: &str,
        args: &[Arg],
        span: ttrpg_ast::Span,
    ) -> Ty {
        match method {
            "unwrap" => {
                if !args.is_empty() {
                    self.error(
                        format!("unwrap() takes no arguments, found {}", args.len()),
                        span,
                    );
                }
                if inner_ty.is_error() {
                    // bare `none.unwrap()` — can't determine inner type
                    Ty::Error
                } else {
                    inner_ty.clone()
                }
            }
            "unwrap_or" => {
                if args.len() != 1 {
                    self.error(
                        format!("unwrap_or() takes exactly 1 argument, found {}", args.len()),
                        span,
                    );
                    return if inner_ty.is_error() {
                        Ty::Error
                    } else {
                        inner_ty.clone()
                    };
                }
                let arg_ty = self.check_expr_expecting(&args[0].value, Some(inner_ty));
                if inner_ty.is_error() {
                    // bare `none.unwrap_or(x)` — infer from the default
                    arg_ty
                } else {
                    if !arg_ty.is_error() && !self.types_compatible(&arg_ty, inner_ty) {
                        self.error(
                            format!("unwrap_or() default has type {arg_ty}, expected {inner_ty}"),
                            span,
                        );
                    }
                    inner_ty.clone()
                }
            }
            "is_some" | "is_none" => {
                if !args.is_empty() {
                    self.error(
                        format!("{}() takes no arguments, found {}", method, args.len()),
                        span,
                    );
                }
                Ty::Bool
            }
            _ => {
                self.error(
                    format!(
                        "option type has no method `{method}`; available methods: unwrap, unwrap_or, is_some, is_none"
                    ),
                    span,
                );
                Ty::Error
            }
        }
    }

    fn check_list_method(
        &mut self,
        inner: Box<Ty>,
        method: &str,
        args: &[Arg],
        span: ttrpg_ast::Span,
    ) -> Ty {
        match method {
            "len" => {
                if !args.is_empty() {
                    self.error(
                        format!("len() takes no arguments, found {}", args.len()),
                        span,
                    );
                }
                Ty::Int
            }
            "first" | "last" => {
                if !args.is_empty() {
                    self.error(
                        format!("{}() takes no arguments, found {}", method, args.len()),
                        span,
                    );
                }
                Ty::Option(inner)
            }
            "reverse" => {
                if !args.is_empty() {
                    self.error(
                        format!("reverse() takes no arguments, found {}", args.len()),
                        span,
                    );
                }
                Ty::List(inner)
            }
            "append" => {
                if args.len() != 1 {
                    self.error(
                        format!("append() takes 1 argument, found {}", args.len()),
                        span,
                    );
                    for arg in args {
                        self.check_expr(&arg.value);
                    }
                    return Ty::Error;
                }
                let elem_ty = self.check_expr_expecting(&args[0].value, Some(&inner));
                if !elem_ty.is_error() && !self.types_compatible(&elem_ty, &inner) {
                    self.error(
                        format!(
                            ".append() element type mismatch: list is list<{inner}>, but got {elem_ty}"
                        ),
                        span,
                    );
                }
                Ty::List(inner)
            }
            "concat" => {
                if args.len() != 1 {
                    self.error(
                        format!("concat() takes 1 argument, found {}", args.len()),
                        span,
                    );
                    for arg in args {
                        self.check_expr(&arg.value);
                    }
                    return Ty::Error;
                }
                let list_ty = Ty::List(inner.clone());
                let arg_ty = self.check_expr_expecting(&args[0].value, Some(&list_ty));
                if !arg_ty.is_error() && !self.types_compatible(&arg_ty, &list_ty) {
                    self.error(
                        format!(".concat() type mismatch: list<{inner}> vs {arg_ty}"),
                        span,
                    );
                }
                Ty::List(inner)
            }
            "sum" => {
                if !args.is_empty() {
                    self.error(
                        format!("sum() takes no arguments, found {}", args.len()),
                        span,
                    );
                }
                match *inner {
                    Ty::Int => Ty::Int,
                    Ty::Float => Ty::Float,
                    _ => {
                        self.error(
                            format!("sum() requires list<int> or list<float>, found list<{inner}>"),
                            span,
                        );
                        Ty::Error
                    }
                }
            }
            "any" | "all" => {
                if !args.is_empty() {
                    self.error(
                        format!("{}() takes no arguments, found {}", method, args.len()),
                        span,
                    );
                }
                if *inner != Ty::Bool && *inner != Ty::Error {
                    self.error(
                        format!("{method}() requires list<bool>, found list<{inner}>"),
                        span,
                    );
                }
                Ty::Bool
            }
            "sort" => {
                if !args.is_empty() {
                    self.error(
                        format!("sort() takes no arguments, found {}", args.len()),
                        span,
                    );
                }
                Ty::List(inner)
            }
            "to_set" => {
                if !args.is_empty() {
                    self.error(
                        format!("to_set() takes no arguments, found {}", args.len()),
                        span,
                    );
                }
                Ty::Set(inner)
            }
            _ => {
                self.error(
                    format!(
                        "list type has no method `{method}`; available methods: len, first, last, reverse, append, concat, sum, any, all, sort, to_set"
                    ),
                    span,
                );
                Ty::Error
            }
        }
    }

    fn check_set_method(
        &mut self,
        inner: &Ty,
        method: &str,
        args: &[Arg],
        span: ttrpg_ast::Span,
    ) -> Ty {
        match method {
            "len" => {
                if !args.is_empty() {
                    self.error(
                        format!("len() takes no arguments, found {}", args.len()),
                        span,
                    );
                }
                Ty::Int
            }
            "add" | "remove" => {
                if args.len() != 1 {
                    self.error(
                        format!("{}() takes 1 argument, found {}", method, args.len()),
                        span,
                    );
                    for arg in args {
                        self.check_expr(&arg.value);
                    }
                    return Ty::Error;
                }
                let elem_ty = self.check_expr_expecting(&args[0].value, Some(inner));
                if !elem_ty.is_error() && !self.types_compatible(&elem_ty, inner) {
                    self.error(
                        format!(
                            ".{method}() element type mismatch: set is set<{inner}>, but got {elem_ty}"
                        ),
                        span,
                    );
                }
                Ty::Set(Box::new(inner.clone()))
            }
            "union" | "intersection" | "difference" => {
                if args.len() != 1 {
                    self.error(
                        format!("{}() takes 1 argument, found {}", method, args.len()),
                        span,
                    );
                    for arg in args {
                        self.check_expr(&arg.value);
                    }
                    return Ty::Error;
                }
                let set_ty = Ty::Set(Box::new(inner.clone()));
                let arg_ty = self.check_expr_expecting(&args[0].value, Some(&set_ty));
                if !arg_ty.is_error() && !self.types_compatible(&arg_ty, &set_ty) {
                    self.error(
                        format!(".{method}() type mismatch: set<{inner}> vs {arg_ty}"),
                        span,
                    );
                }
                Ty::Set(Box::new(inner.clone()))
            }
            "to_list" => {
                if !args.is_empty() {
                    self.error(
                        format!("to_list() takes no arguments, found {}", args.len()),
                        span,
                    );
                }
                Ty::List(Box::new(inner.clone()))
            }
            "contains" => {
                if args.len() != 1 {
                    self.error(
                        format!("contains() takes 1 argument, found {}", args.len()),
                        span,
                    );
                    for arg in args {
                        self.check_expr(&arg.value);
                    }
                    return Ty::Error;
                }
                let elem_ty = self.check_expr_expecting(&args[0].value, Some(inner));
                if !elem_ty.is_error() && !self.types_compatible(&elem_ty, inner) {
                    self.error(
                        format!(
                            ".contains() element type mismatch: set is set<{inner}>, but got {elem_ty}"
                        ),
                        span,
                    );
                }
                Ty::Bool
            }
            _ => {
                self.error(
                    format!(
                        "set type has no method `{method}`; available methods: len, add, remove, union, intersection, difference, to_list, contains"
                    ),
                    span,
                );
                Ty::Error
            }
        }
    }

    fn check_map_method(
        &mut self,
        k: Box<Ty>,
        v: Box<Ty>,
        method: &str,
        args: &[Arg],
        span: ttrpg_ast::Span,
    ) -> Ty {
        match method {
            "len" => {
                if !args.is_empty() {
                    self.error(
                        format!("len() takes no arguments, found {}", args.len()),
                        span,
                    );
                }
                Ty::Int
            }
            "keys" => {
                if !args.is_empty() {
                    self.error(
                        format!("keys() takes no arguments, found {}", args.len()),
                        span,
                    );
                }
                Ty::List(k)
            }
            "values" => {
                if !args.is_empty() {
                    self.error(
                        format!("values() takes no arguments, found {}", args.len()),
                        span,
                    );
                }
                Ty::List(v)
            }
            _ => {
                self.error(
                    format!(
                        "map type has no method `{method}`; available methods: len, keys, values"
                    ),
                    span,
                );
                Ty::Error
            }
        }
    }

    fn check_dice_method(&mut self, method: &str, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
        match method {
            "multiply" => {
                if args.len() != 1 {
                    self.error(
                        format!("multiply() takes 1 argument, found {}", args.len()),
                        span,
                    );
                    for arg in args {
                        self.check_expr(&arg.value);
                    }
                    return Ty::Error;
                }
                let factor_ty = self.check_expr_expecting(&args[0].value, Some(&Ty::Int));
                if !factor_ty.is_error() && factor_ty != Ty::Int {
                    self.error(
                        format!("multiply() factor must be int, found {factor_ty}"),
                        span,
                    );
                }
                Ty::DiceExpr
            }
            "roll" => {
                if !args.is_empty() {
                    self.error(
                        format!("roll() takes no arguments, found {}", args.len()),
                        span,
                    );
                }
                if !self.scope.allows_dice() {
                    self.error(
                        ".roll() can only be called in mechanic, action, reaction, or hook blocks"
                            .to_string(),
                        span,
                    );
                }
                Ty::RollResult
            }
            _ => {
                self.error(
                    format!(
                        "DiceExpr type has no method `{method}`; available methods: multiply, roll"
                    ),
                    span,
                );
                Ty::Error
            }
        }
    }

    fn check_string_method(&mut self, method: &str, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
        match method {
            "len" => {
                if !args.is_empty() {
                    self.error(
                        format!("len() takes no arguments, found {}", args.len()),
                        span,
                    );
                }
                Ty::Int
            }
            "contains" | "starts_with" | "ends_with" => {
                if args.len() != 1 {
                    self.error(
                        format!(
                            "{}() takes exactly 1 argument, found {}",
                            method,
                            args.len()
                        ),
                        span,
                    );
                    for arg in args {
                        self.check_expr(&arg.value);
                    }
                    return Ty::Bool;
                }
                let arg_ty = self.check_expr_expecting(&args[0].value, Some(&Ty::String));
                if !arg_ty.is_error() && !self.types_compatible(&arg_ty, &Ty::String) {
                    self.error(
                        format!("{method}() argument must be string, found {arg_ty}"),
                        span,
                    );
                }
                Ty::Bool
            }
            _ => {
                self.error(
                    format!(
                        "string type has no method `{method}`; available methods: len, contains, starts_with, ends_with"
                    ),
                    span,
                );
                Ty::Error
            }
        }
    }
}
