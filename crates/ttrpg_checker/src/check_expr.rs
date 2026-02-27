use std::collections::HashSet;

use ttrpg_ast::ast::*;
use ttrpg_ast::Name;
use ttrpg_ast::Spanned;

use crate::check::{Checker, Namespace};
use crate::env::*;
use crate::scope::BlockKind;
use crate::ty::Ty;

/// Controls error message phrasing for condition vs function calls.
enum CallKind {
    Condition,
    Function,
}

impl<'a> Checker<'a> {
    /// Type-check an expression, returning its resolved type.
    pub fn check_expr(&mut self, expr: &Spanned<ExprKind>) -> Ty {
        self.check_expr_expecting(expr, None)
    }

    /// Type-check an expression with an optional expected-type hint.
    ///
    /// The hint is used to disambiguate bare enum variants when multiple
    /// enums share the same variant name.
    pub fn check_expr_expecting(&mut self, expr: &Spanned<ExprKind>, hint: Option<&Ty>) -> Ty {
        match &expr.node {
            ExprKind::IntLit(_) => Ty::Int,
            ExprKind::StringLit(_) => Ty::String,
            ExprKind::BoolLit(_) => Ty::Bool,
            ExprKind::NoneLit => Ty::Option(Box::new(Ty::Error)),

            ExprKind::DiceLit { .. } => {
                if matches!(
                    self.scope.current_block_kind(),
                    Some(BlockKind::TriggerBinding)
                ) {
                    self.error(
                        "dice literals are not allowed in trigger/suppress binding context"
                            .to_string(),
                        expr.span,
                    );
                }
                Ty::DiceExpr
            }

            ExprKind::UnitLit { suffix, .. } => {
                if let Some(unit_name) = self.env.suffix_to_unit.get(suffix.as_str()).cloned() {
                    Ty::UnitType(unit_name)
                } else {
                    self.error(format!("unknown unit suffix `{}`", suffix), expr.span);
                    Ty::Error
                }
            }

            ExprKind::Ident(name) => self.check_ident(name, expr.span, hint),

            ExprKind::BinOp { op, lhs, rhs } => self.check_binop(*op, lhs, rhs, expr.span),

            ExprKind::UnaryOp { op, operand } => self.check_unary(*op, operand, expr.span),

            ExprKind::FieldAccess { object, field } => {
                self.check_field_access(object, field, expr.span)
            }

            ExprKind::Index { object, index } => self.check_index(object, index, expr.span),

            ExprKind::Call { callee, args } => self.check_call(callee, args, expr.span, hint),

            ExprKind::StructLit { name, fields, base } => {
                self.check_struct_lit(name, fields, base.as_deref(), expr.span)
            }

            ExprKind::ListLit(elems) => {
                let elem_hint = match hint {
                    Some(Ty::List(inner)) => Some(inner.as_ref()),
                    _ => None,
                };
                self.check_list_lit(elems, expr.span, elem_hint)
            }

            ExprKind::MapLit(entries) => self.check_map_lit(entries, expr.span),

            ExprKind::Paren(inner) => self.check_expr_expecting(inner, hint),

            ExprKind::If {
                condition,
                then_block,
                else_branch,
            } => self.check_if(condition, then_block, else_branch.as_ref(), expr.span),

            ExprKind::IfLet {
                pattern,
                scrutinee,
                then_block,
                else_branch,
            } => self.check_if_let(
                pattern,
                scrutinee,
                then_block,
                else_branch.as_ref(),
                expr.span,
            ),

            ExprKind::PatternMatch { scrutinee, arms } => {
                self.check_pattern_match(scrutinee, arms, expr.span, hint)
            }

            ExprKind::GuardMatch { arms } => self.check_guard_match(arms, expr.span, hint),

            ExprKind::For {
                pattern,
                iterable,
                body,
            } => self.check_for(pattern, iterable, body, expr.span),

            ExprKind::ListComprehension {
                element,
                pattern,
                iterable,
                filter,
            } => self.check_list_comprehension(
                element,
                pattern,
                iterable,
                filter.as_deref(),
                expr.span,
            ),

            ExprKind::Has { entity, group_name } => self.check_has(entity, group_name, expr.span),
        }
    }

    fn check_ident(&mut self, name: &str, span: ttrpg_ast::Span, hint: Option<&Ty>) -> Ty {
        // Check scope first
        if let Some(binding) = self.scope.lookup(name) {
            return binding.ty.clone();
        }

        // Check if it's an enum variant (may be unique or ambiguous)
        if let Some(enum_name) = self.resolve_bare_variant_with_hint(name, span, hint) {
            // Only bare (no-payload) variants can be used as identifiers
            if let Some(DeclInfo::Enum(info)) = self.env.types.get(&enum_name) {
                if let Some(variant) = info.variants.iter().find(|v| v.name == name) {
                    if variant.fields.is_empty() {
                        self.check_name_visible(name, Namespace::Variant, span);
                        return Ty::Enum(enum_name);
                    }
                }
            }
        } else if self.is_known_variant(name) {
            // Ambiguity error was already emitted by resolve_bare_variant
            return Ty::Error;
        }

        // Check if it's a condition name
        if let Some(cond_info) = self.env.conditions.get(name) {
            self.check_name_visible(name, Namespace::Condition, span);
            let required_params = cond_info.params.iter().filter(|p| !p.has_default).count();
            if required_params > 0 {
                self.error(
                    format!(
                        "condition `{}` requires {} parameter(s); use `{}(...)` to supply them",
                        name, required_params, name
                    ),
                    span,
                );
            }
            return Ty::Condition;
        }

        // Enum type names resolve as values to support qualified variant access
        // (e.g., `DamageType.fire`). Struct/entity names are NOT values — they
        // exist only in the type namespace. Using a struct/entity name bare in
        // expression position is an error; instances come from struct literals
        // or function parameters, not from the type name itself.
        if let Some(decl) = self.env.types.get(name) {
            self.check_name_visible(name, Namespace::Type, span);
            return match decl {
                DeclInfo::Enum(_) => Ty::EnumType(Name::from(name)),
                DeclInfo::Struct(_) | DeclInfo::Entity(_) | DeclInfo::Unit(_) => {
                    self.error(format!("type `{}` cannot be used as a value", name), span);
                    Ty::Error
                }
            };
        }

        // Check if it's a module alias (e.g., `Core` from `use "Core" as Core`)
        if let Some(ref current) = self.current_system {
            if let Some(aliases) = self.env.system_aliases.get(current) {
                if aliases.contains_key(name) {
                    return Ty::ModuleAlias(Name::from(name));
                }
            }
        }

        self.error(format!("undefined variable `{}`", name), span);
        Ty::Error
    }

    fn check_binop(
        &mut self,
        op: BinOp,
        lhs: &Spanned<ExprKind>,
        rhs: &Spanned<ExprKind>,
        span: ttrpg_ast::Span,
    ) -> Ty {
        let lhs_ty = self.check_expr(lhs);
        let rhs_hint = match op {
            BinOp::Eq | BinOp::NotEq | BinOp::Lt | BinOp::Gt | BinOp::LtEq | BinOp::GtEq => {
                Some(&lhs_ty)
            }
            _ => None,
        };
        let rhs_ty = self.check_expr_expecting(rhs, rhs_hint);

        if lhs_ty.is_error() || rhs_ty.is_error() {
            return Ty::Error;
        }

        match op {
            BinOp::Add => self.check_add(&lhs_ty, &rhs_ty, span),
            BinOp::Sub => self.check_sub(&lhs_ty, &rhs_ty, span),
            BinOp::Mul => self.check_mul(&lhs_ty, &rhs_ty, span),
            BinOp::Div => self.check_div(&lhs_ty, &rhs_ty, span),
            BinOp::And | BinOp::Or => {
                if lhs_ty != Ty::Bool {
                    self.error(
                        format!("left operand of logical op must be bool, found {}", lhs_ty),
                        lhs.span,
                    );
                }
                if rhs_ty != Ty::Bool {
                    self.error(
                        format!("right operand of logical op must be bool, found {}", rhs_ty),
                        rhs.span,
                    );
                }
                Ty::Bool
            }
            BinOp::Eq | BinOp::NotEq => {
                self.check_comparison(&lhs_ty, &rhs_ty, lhs, rhs, span, false)
            }
            BinOp::Lt | BinOp::Gt | BinOp::LtEq | BinOp::GtEq => {
                self.check_comparison(&lhs_ty, &rhs_ty, lhs, rhs, span, true)
            }
            BinOp::In => self.check_in_op(&lhs_ty, &rhs_ty, rhs, span),
        }
    }

    fn check_add(&mut self, lhs: &Ty, rhs: &Ty, span: ttrpg_ast::Span) -> Ty {
        match (lhs, rhs) {
            // DiceExpr algebra
            (Ty::DiceExpr, Ty::DiceExpr) => Ty::DiceExpr,
            (Ty::DiceExpr, t) if t.is_int_like() => Ty::DiceExpr,
            (t, Ty::DiceExpr) if t.is_int_like() => Ty::DiceExpr,
            // Numeric
            (Ty::Int, Ty::Int)
            | (Ty::Resource, Ty::Int)
            | (Ty::Int, Ty::Resource)
            | (Ty::Resource, Ty::Resource) => Ty::Int,
            (Ty::Float, t) | (t, Ty::Float) if t.is_numeric() => Ty::Float,
            // String concatenation
            (Ty::String, Ty::String) => Ty::String,
            // Unit types: same-type addition
            (Ty::UnitType(a), Ty::UnitType(b)) if a == b => Ty::UnitType(a.clone()),
            _ => {
                self.error(format!("cannot add {} and {}", lhs, rhs), span);
                Ty::Error
            }
        }
    }

    fn check_sub(&mut self, lhs: &Ty, rhs: &Ty, span: ttrpg_ast::Span) -> Ty {
        match (lhs, rhs) {
            // DiceExpr - int
            (Ty::DiceExpr, t) if t.is_int_like() => Ty::DiceExpr,
            // Numeric
            (l, r) if l.is_int_like() && r.is_int_like() => Ty::Int,
            (Ty::Float, t) | (t, Ty::Float) if t.is_numeric() => Ty::Float,
            // Unit types: same-type subtraction
            (Ty::UnitType(a), Ty::UnitType(b)) if a == b => Ty::UnitType(a.clone()),
            _ => {
                self.error(format!("cannot subtract {} from {}", rhs, lhs), span);
                Ty::Error
            }
        }
    }

    fn check_mul(&mut self, lhs: &Ty, rhs: &Ty, span: ttrpg_ast::Span) -> Ty {
        // DiceExpr * anything is an error
        if *lhs == Ty::DiceExpr || *rhs == Ty::DiceExpr {
            self.error(
                "cannot multiply DiceExpr; use multiply_dice() or .multiply() instead".to_string(),
                span,
            );
            return Ty::Error;
        }

        match (lhs, rhs) {
            (l, r) if l.is_int_like() && r.is_int_like() => Ty::Int,
            (Ty::Float, t) | (t, Ty::Float) if t.is_numeric() => Ty::Float,
            // Unit types: int * unit or unit * int
            (Ty::Int, Ty::UnitType(a)) | (Ty::UnitType(a), Ty::Int) => Ty::UnitType(a.clone()),
            _ => {
                self.error(format!("cannot multiply {} and {}", lhs, rhs), span);
                Ty::Error
            }
        }
    }

    fn check_div(&mut self, lhs: &Ty, rhs: &Ty, span: ttrpg_ast::Span) -> Ty {
        // DiceExpr / anything is an error
        if *lhs == Ty::DiceExpr || *rhs == Ty::DiceExpr {
            self.error(
                "cannot divide DiceExpr; use multiply_dice() or .multiply() instead".to_string(),
                span,
            );
            return Ty::Error;
        }

        match (lhs, rhs) {
            // int / int -> float (always)
            (l, r) if l.is_int_like() && r.is_int_like() => Ty::Float,
            (Ty::Float, t) | (t, Ty::Float) if t.is_numeric() => Ty::Float,
            // Unit types: same-type division produces float (dimensionless ratio)
            (Ty::UnitType(a), Ty::UnitType(b)) if a == b => Ty::Float,
            _ => {
                self.error(format!("cannot divide {} by {}", lhs, rhs), span);
                Ty::Error
            }
        }
    }

    fn check_comparison(
        &mut self,
        lhs_ty: &Ty,
        rhs_ty: &Ty,
        lhs: &Spanned<ExprKind>,
        rhs: &Spanned<ExprKind>,
        span: ttrpg_ast::Span,
        ordering: bool,
    ) -> Ty {
        // DiceExpr in comparison is always an error
        if *lhs_ty == Ty::DiceExpr {
            self.error(
                "cannot compare DiceExpr directly; call roll() first".to_string(),
                lhs.span,
            );
            return Ty::Bool;
        }
        if *rhs_ty == Ty::DiceExpr {
            self.error(
                "cannot compare DiceExpr directly; call roll() first".to_string(),
                rhs.span,
            );
            return Ty::Bool;
        }

        // RollResult auto-coerces to .total (int) in comparisons
        let l = if *lhs_ty == Ty::RollResult {
            &Ty::Int
        } else {
            lhs_ty
        };
        let r = if *rhs_ty == Ty::RollResult {
            &Ty::Int
        } else {
            rhs_ty
        };

        if ordering {
            // <, >, <=, >= only for orderable types
            if !self.types_orderable(l, r) {
                self.error(format!("cannot order {} and {}", lhs_ty, rhs_ty), span);
            }
        } else {
            // ==, != for any comparable types
            if !self.types_comparable(l, r) {
                self.error(format!("cannot compare {} and {}", lhs_ty, rhs_ty), span);
            }
        }

        Ty::Bool
    }

    fn types_comparable(&self, a: &Ty, b: &Ty) -> bool {
        if a == b {
            return true;
        }
        // Numeric types are comparable to each other
        if a.is_numeric() && b.is_numeric() {
            return true;
        }
        // Same-type unit types are comparable
        if let (Ty::UnitType(na), Ty::UnitType(nb)) = (a, b) {
            if na == nb {
                return true;
            }
        }
        // none (Option(Error)) is comparable with any Option(T)
        match (a, b) {
            (Ty::Option(inner), _) if inner.is_error() && matches!(b, Ty::Option(_)) => {
                return true;
            }
            (_, Ty::Option(inner)) if inner.is_error() && matches!(a, Ty::Option(_)) => {
                return true;
            }
            _ => {}
        }
        false
    }

    /// Whether two types support ordering operators (<, >, <=, >=).
    fn types_orderable(&self, a: &Ty, b: &Ty) -> bool {
        // Numeric types are orderable with each other
        if a.is_numeric() && b.is_numeric() {
            return true;
        }
        // Same-type ordering for strings, ordered enums, and unit types
        if a == b {
            if let Ty::Enum(name) = a {
                if let Some(DeclInfo::Enum(info)) = self.env.types.get(name.as_str()) {
                    return info.ordered;
                }
                return false;
            }
            if matches!(a, Ty::UnitType(_)) {
                return true;
            }
            return matches!(a, Ty::Int | Ty::Float | Ty::Resource | Ty::String);
        }
        false
    }

    fn check_in_op(
        &mut self,
        lhs: &Ty,
        rhs: &Ty,
        rhs_expr: &Spanned<ExprKind>,
        span: ttrpg_ast::Span,
    ) -> Ty {
        match rhs {
            Ty::List(inner) | Ty::Set(inner) => {
                if !self.types_compatible(lhs, inner) {
                    self.error(format!("cannot check if {} is in {}", lhs, rhs), span);
                }
                Ty::Bool
            }
            Ty::Map(key, _) => {
                if !self.types_compatible(lhs, key) {
                    self.error(format!("cannot check if {} is in {}", lhs, rhs), span);
                }
                Ty::Bool
            }
            _ => {
                self.error(
                    format!(
                        "right-hand side of `in` must be a collection, found {}",
                        rhs
                    ),
                    rhs_expr.span,
                );
                Ty::Bool
            }
        }
    }

    fn check_unary(
        &mut self,
        op: UnaryOp,
        operand: &Spanned<ExprKind>,
        span: ttrpg_ast::Span,
    ) -> Ty {
        let ty = self.check_expr(operand);
        if ty.is_error() {
            return Ty::Error;
        }

        match op {
            UnaryOp::Neg => {
                if ty.is_numeric() || matches!(ty, Ty::UnitType(_)) {
                    ty
                } else {
                    self.error(format!("cannot negate {}", ty), span);
                    Ty::Error
                }
            }
            UnaryOp::Not => {
                if ty == Ty::Bool {
                    Ty::Bool
                } else {
                    self.error(format!("cannot apply `!` to {}", ty), span);
                    Ty::Error
                }
            }
        }
    }

    pub fn check_field_access(
        &mut self,
        object: &Spanned<ExprKind>,
        field: &str,
        span: ttrpg_ast::Span,
    ) -> Ty {
        let obj_ty = self.check_expr(object);
        if obj_ty.is_error() {
            return Ty::Error;
        }

        let result_ty = self.resolve_field(&obj_ty, field, span);

        // If this resolved to a group reference, check narrowing for optional groups.
        if let Ty::OptionalGroupRef(ref entity_name, ref group_name) = result_ty {
            if !self.env.is_group_required(entity_name, group_name) {
                let group_name = group_name.clone();
                if let Some(path_key) = self.extract_path_key(object) {
                    if !self.scope.is_group_narrowed(&path_key, &group_name) {
                        self.error(
                            format!(
                                "access to optional group `{}` on `{}` requires a `has` guard or `with` constraint",
                                group_name, path_key
                            ),
                            span,
                        );
                    }
                } else {
                    self.error(
                        format!(
                            "access to optional group `{}` requires a `has` guard or `with` constraint",
                            group_name
                        ),
                        span,
                    );
                }
            }
        }

        result_ty
    }

    pub fn resolve_field(&mut self, obj_ty: &Ty, field: &str, span: ttrpg_ast::Span) -> Ty {
        match obj_ty {
            Ty::Struct(name) | Ty::Entity(name) | Ty::UnitType(name) => {
                // Check for event payload synthetic structs
                if let Some(event_name) = name.strip_prefix("__event_") {
                    if let Some(event_info) = self.env.events.get(event_name) {
                        if let Some((_, ty)) = event_info.fields.iter().find(|(n, _)| n == field) {
                            return ty.clone();
                        }
                        // Also check event params
                        if let Some(param) = event_info.params.iter().find(|p| p.name == field) {
                            return param.ty.clone();
                        }
                        self.error(
                            format!("event `{}` has no field `{}`", event_name, field),
                            span,
                        );
                        return Ty::Error;
                    }
                }

                // Check for optional group access on entities
                if matches!(obj_ty, Ty::Entity(_))
                    && self.env.lookup_optional_group(name, field).is_some()
                {
                    return Ty::OptionalGroupRef(name.clone(), Name::from(field));
                }

                if let Some(fields) = self.env.lookup_fields(name) {
                    if let Some(fi) = fields.iter().find(|f| f.name == field) {
                        return fi.ty.clone();
                    }
                }

                // Check for flattened included-group field
                if matches!(obj_ty, Ty::Entity(_)) {
                    if let Some(group_name) =
                        self.env.lookup_flattened_field(name, field)
                    {
                        if let Some(group) =
                            self.env.lookup_optional_group(name, group_name)
                        {
                            if let Some(fi) = group.fields.iter().find(|f| f.name == field) {
                                return fi.ty.clone();
                            }
                        }
                    }
                }

                self.error(format!("type `{}` has no field `{}`", name, field), span);
                Ty::Error
            }
            Ty::AnyEntity => {
                if let Some((owner, group)) = self.env.unique_optional_group_owner(field) {
                    return Ty::OptionalGroupRef(owner, group.name.clone());
                }
                if self.env.has_optional_group_named(field) {
                    self.error(
                        format!(
                            "optional group `{}` is ambiguous on type `entity`; use a concrete entity type",
                            field
                        ),
                        span,
                    );
                } else {
                    self.error(
                        format!("type `entity` has no field or optional group `{}`", field),
                        span,
                    );
                }
                Ty::Error
            }
            Ty::OptionalGroupRef(entity_name, group_name) => {
                if let Some(group) = self.env.lookup_optional_group(entity_name, group_name) {
                    if let Some(fi) = group.fields.iter().find(|f| f.name == field) {
                        return fi.ty.clone();
                    }
                } else if let Some(group) = self.env.lookup_group(group_name) {
                    if let Some(fi) = group.fields.iter().find(|f| f.name == field) {
                        return fi.ty.clone();
                    }
                }
                self.error(
                    format!("optional group `{}` has no field `{}`", group_name, field),
                    span,
                );
                Ty::Error
            }
            Ty::RollResult => {
                for (fname, ref fty) in TypeEnv::roll_result_fields() {
                    if fname == field {
                        return fty.clone();
                    }
                }
                self.error(format!("RollResult has no field `{}`", field), span);
                Ty::Error
            }
            Ty::TurnBudget => {
                // Prefer user-defined struct TurnBudget fields if present,
                // fall back to hardcoded fields otherwise.
                if let Some(fields) = self.env.lookup_fields("TurnBudget") {
                    if let Some(fi) = fields.iter().find(|f| f.name == field) {
                        return fi.ty.clone();
                    }
                    self.error(format!("TurnBudget has no field `{}`", field), span);
                    return Ty::Error;
                }
                for (fname, ref fty) in TypeEnv::turn_budget_fields() {
                    if fname == field {
                        return fty.clone();
                    }
                }
                self.error(format!("TurnBudget has no field `{}`", field), span);
                Ty::Error
            }
            // Qualified enum variant: EnumType.Variant (namespace access)
            Ty::EnumType(enum_name) => {
                if let Some(DeclInfo::Enum(info)) = self.env.types.get(enum_name) {
                    if let Some(variant) = info.variants.iter().find(|v| v.name == field) {
                        if !variant.fields.is_empty() {
                            self.error(
                                format!(
                                    "variant `{}` has payload fields and must be called as a constructor",
                                    field
                                ),
                                span,
                            );
                            return Ty::Error;
                        }
                        return Ty::Enum(enum_name.clone());
                    }
                }
                self.error(
                    format!("enum `{}` has no variant `{}`", enum_name, field),
                    span,
                );
                Ty::Error
            }
            // Module alias: resolve through alias to the target system
            Ty::ModuleAlias(alias_name) => self.resolve_alias_field(alias_name, field, span),
            // Runtime enum values do not support field access
            Ty::Enum(enum_name) => {
                self.error(
                    format!(
                        "cannot access field `{}` on enum value of type `{}`; use pattern matching instead",
                        field, enum_name
                    ),
                    span,
                );
                Ty::Error
            }
            Ty::Option(_) => {
                if field == "unwrap" || field == "unwrap_or" {
                    self.error(
                        format!(
                            "`.{}` is a method on option; call it as `.{}()`",
                            field, field
                        ),
                        span,
                    );
                } else {
                    self.error(format!("option type has no field `{}`", field), span);
                }
                Ty::Error
            }
            _ => {
                self.error(
                    format!("cannot access field `{}` on type {}", field, obj_ty),
                    span,
                );
                Ty::Error
            }
        }
    }

    fn check_method_call(
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
                self.error(format!("type {} has no methods", obj_ty), span);
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
                            format!(
                                "unwrap_or() default has type {}, expected {}",
                                arg_ty, inner_ty
                            ),
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
                        "option type has no method `{}`; available methods: unwrap, unwrap_or, is_some, is_none",
                        method
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
                if !elem_ty.is_error() && !self.types_compatible(&inner, &elem_ty) {
                    self.error(
                        format!(
                            ".append() element type mismatch: list is list<{}>, but got {}",
                            inner, elem_ty
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
                if !arg_ty.is_error() && !self.types_compatible(&list_ty, &arg_ty) {
                    self.error(
                        format!(".concat() type mismatch: list<{}> vs {}", inner, arg_ty),
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
                            format!(
                                "sum() requires list<int> or list<float>, found list<{}>",
                                inner
                            ),
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
                        format!("{}() requires list<bool>, found list<{}>", method, inner),
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
            _ => {
                self.error(
                    format!(
                        "list type has no method `{}`; available methods: len, first, last, reverse, append, concat, sum, any, all, sort",
                        method
                    ),
                    span,
                );
                Ty::Error
            }
        }
    }

    fn check_set_method(
        &mut self,
        _inner: &Ty,
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
            _ => {
                self.error(
                    format!(
                        "set type has no method `{}`; available methods: len",
                        method
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
                        "map type has no method `{}`; available methods: len, keys, values",
                        method
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
                        format!("multiply() factor must be int, found {}", factor_ty),
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
                        ".roll() can only be called in mechanic, action, or reaction blocks"
                            .to_string(),
                        span,
                    );
                }
                Ty::RollResult
            }
            _ => {
                self.error(
                    format!(
                        "DiceExpr type has no method `{}`; available methods: multiply, roll",
                        method
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
                        format!("{}() argument must be string, found {}", method, arg_ty),
                        span,
                    );
                }
                Ty::Bool
            }
            _ => {
                self.error(
                    format!(
                        "string type has no method `{}`; available methods: len, contains, starts_with, ends_with",
                        method
                    ),
                    span,
                );
                Ty::Error
            }
        }
    }

    fn check_index(
        &mut self,
        object: &Spanned<ExprKind>,
        index: &Spanned<ExprKind>,
        span: ttrpg_ast::Span,
    ) -> Ty {
        let obj_ty = self.check_expr(object);
        let key_hint = match &obj_ty {
            Ty::Map(key, _) => Some(key.as_ref()),
            _ => None,
        };
        let idx_ty = self.check_expr_expecting(index, key_hint);

        if obj_ty.is_error() || idx_ty.is_error() {
            return Ty::Error;
        }

        match &obj_ty {
            Ty::List(_) => {
                if !idx_ty.is_int_like() {
                    self.error(
                        format!("list index must be int, found {}", idx_ty),
                        index.span,
                    );
                }
                if let Ty::List(inner) = &obj_ty {
                    *inner.clone()
                } else {
                    unreachable!()
                }
            }
            Ty::Map(key, val) => {
                if !self.types_compatible(&idx_ty, key) {
                    self.error(
                        format!("map key type is {}, found {}", key, idx_ty),
                        index.span,
                    );
                }
                *val.clone()
            }
            _ => {
                self.error(format!("cannot index into {}", obj_ty), span);
                Ty::Error
            }
        }
    }

    fn check_call(
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

    fn check_ordinal_call(&mut self, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
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

    fn check_from_ordinal_call(&mut self, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
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

    fn check_try_from_ordinal_call(&mut self, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
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

    fn check_len_call(&mut self, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
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

    fn check_keys_call(&mut self, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
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

    fn check_values_call(&mut self, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
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

    fn check_first_call(&mut self, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
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

    fn check_last_call(&mut self, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
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

    fn check_append_call(&mut self, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
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

    fn check_concat_call(&mut self, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
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

    fn check_reverse_call(&mut self, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
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

    fn check_sum_call(&mut self, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
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

    fn check_any_call(&mut self, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
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

    fn check_all_call(&mut self, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
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

    fn check_sort_call(&mut self, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
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

    fn check_some_call(&mut self, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
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

    fn check_enum_constructor(
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

    fn check_builtin_permissions(&mut self, name: &str, span: ttrpg_ast::Span) {
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

    fn check_struct_lit(
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

    fn check_list_lit(
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

    fn check_map_lit(
        &mut self,
        entries: &[(Spanned<ExprKind>, Spanned<ExprKind>)],
        _span: ttrpg_ast::Span,
    ) -> Ty {
        if entries.is_empty() {
            return Ty::Map(Box::new(Ty::Error), Box::new(Ty::Error));
        }

        let mut unified_key = self.check_expr(&entries[0].0);
        let mut unified_val = self.check_expr_expecting(&entries[0].1, None);

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

    fn check_if(
        &mut self,
        condition: &Spanned<ExprKind>,
        then_block: &Block,
        else_branch: Option<&ElseBranch>,
        span: ttrpg_ast::Span,
    ) -> Ty {
        let cond_ty = self.check_expr(condition);
        if !cond_ty.is_error() && cond_ty != Ty::Bool {
            self.error(
                format!("if condition must be bool, found {}", cond_ty),
                condition.span,
            );
        }

        // Extract narrowings from `has` conditions for the then-block
        let narrowings = self.extract_has_narrowings(condition);
        let then_ty = if narrowings.is_empty() {
            self.check_block(then_block)
        } else {
            self.check_block_with_narrowings(then_block, &narrowings)
        };
        self.check_else_branch_type(&then_ty, else_branch, span)
    }

    fn check_if_let(
        &mut self,
        pattern: &Spanned<PatternKind>,
        scrutinee: &Spanned<ExprKind>,
        then_block: &Block,
        else_branch: Option<&ElseBranch>,
        span: ttrpg_ast::Span,
    ) -> Ty {
        let scrutinee_ty = self.check_expr(scrutinee);

        // Pattern bindings are scoped to the then-block
        self.scope.push(BlockKind::Inner);
        self.check_pattern(pattern, &scrutinee_ty);
        let then_ty = self.check_block(then_block);
        self.scope.pop();

        self.check_else_branch_type(&then_ty, else_branch, span)
    }

    fn check_else_branch_type(
        &mut self,
        then_ty: &Ty,
        else_branch: Option<&ElseBranch>,
        span: ttrpg_ast::Span,
    ) -> Ty {
        match else_branch {
            Some(ElseBranch::Block(else_block)) => {
                let else_ty = self.check_block(else_block);
                match self.unify_branch_types(then_ty, &else_ty) {
                    Some(ty) => ty,
                    None => {
                        self.error(
                            format!(
                                "if/else branches have incompatible types: {} and {}",
                                then_ty, else_ty
                            ),
                            span,
                        );
                        Ty::Error
                    }
                }
            }
            Some(ElseBranch::If(if_expr)) => {
                let else_ty = self.check_expr(if_expr);
                match self.unify_branch_types(then_ty, &else_ty) {
                    Some(ty) => ty,
                    None => {
                        self.error(
                            format!(
                                "if/else branches have incompatible types: {} and {}",
                                then_ty, else_ty
                            ),
                            span,
                        );
                        Ty::Error
                    }
                }
            }
            None => Ty::Unit,
        }
    }

    fn check_pattern_match(
        &mut self,
        scrutinee: &Spanned<ExprKind>,
        arms: &[PatternArm],
        _span: ttrpg_ast::Span,
        hint: Option<&Ty>,
    ) -> Ty {
        let scrutinee_ty = self.check_expr(scrutinee);

        let mut result_ty: Option<Ty> = None;

        for arm in arms {
            self.scope.push(BlockKind::Inner);
            self.check_pattern(&arm.pattern, &scrutinee_ty);
            let arm_hint = result_ty.as_ref().or(hint);
            let arm_ty = self.check_arm_body(&arm.body, arm_hint);
            self.scope.pop();

            if !arm_ty.is_error() {
                match result_ty {
                    Some(ref existing) => match self.unify_branch_types(existing, &arm_ty) {
                        Some(unified) => result_ty = Some(unified),
                        None => {
                            self.error(
                                format!("match arm has type {}, expected {}", arm_ty, existing),
                                arm.span,
                            );
                        }
                    },
                    None => result_ty = Some(arm_ty),
                }
            }
        }

        result_ty.unwrap_or(Ty::Unit)
    }

    fn check_guard_match(
        &mut self,
        arms: &[GuardArm],
        _span: ttrpg_ast::Span,
        hint: Option<&Ty>,
    ) -> Ty {
        let mut result_ty: Option<Ty> = None;
        let mut seen_wildcard = false;

        for arm in arms {
            // Check guard expression
            match &arm.guard {
                GuardKind::Expr(expr) => {
                    if seen_wildcard {
                        self.warning(
                            "unreachable match arm: wildcard `_` must be last".to_string(),
                            expr.span,
                        );
                    }
                    let guard_ty = self.check_expr(expr);
                    if !guard_ty.is_error() && guard_ty != Ty::Bool {
                        self.error(
                            format!("guard condition must be bool, found {}", guard_ty),
                            expr.span,
                        );
                    }
                }
                GuardKind::Wildcard => {
                    if seen_wildcard {
                        self.warning(
                            "duplicate wildcard `_` in guard match".to_string(),
                            arm.span,
                        );
                    }
                    seen_wildcard = true;
                }
            }

            let arm_hint = result_ty.as_ref().or(hint);
            let arm_ty = self.check_arm_body(&arm.body, arm_hint);

            if !arm_ty.is_error() {
                match result_ty {
                    Some(ref existing) => match self.unify_branch_types(existing, &arm_ty) {
                        Some(unified) => result_ty = Some(unified),
                        None => {
                            self.error(
                                format!("match arm has type {}, expected {}", arm_ty, existing),
                                arm.span,
                            );
                        }
                    },
                    None => result_ty = Some(arm_ty),
                }
            }
        }

        result_ty.unwrap_or(Ty::Unit)
    }

    fn check_for(
        &mut self,
        pattern: &Spanned<PatternKind>,
        iterable: &ForIterable,
        body: &Block,
        span: ttrpg_ast::Span,
    ) -> Ty {
        let element_ty = match iterable {
            ForIterable::Collection(expr) => {
                let coll_ty = self.check_expr(expr);
                match coll_ty {
                    Ty::List(inner) | Ty::Set(inner) => *inner,
                    Ty::Map(_, _) => {
                        self.error(
                            "map iteration is not supported; use keys() or values()".to_string(),
                            span,
                        );
                        Ty::Error
                    }
                    Ty::Error => Ty::Error,
                    other => {
                        self.error(format!("expected list or set, found {}", other), span);
                        Ty::Error
                    }
                }
            }
            ForIterable::Range {
                start,
                end,
                inclusive: _,
            } => {
                let start_ty = self.check_expr(start);
                let end_ty = self.check_expr(end);
                if !start_ty.is_error() && !start_ty.is_int_like() {
                    self.error(
                        format!("range start must be int, found {}", start_ty),
                        start.span,
                    );
                }
                if !end_ty.is_error() && !end_ty.is_int_like() {
                    self.error(format!("range end must be int, found {}", end_ty), end.span);
                }
                Ty::Int
            }
        };

        // Pattern bindings are scoped to the loop body.
        // We push scope, check the pattern (which binds with is_local: true),
        // then mark entity-typed bindings as non-local so field mutation works
        // (e.g. `for target in targets { target.HP -= damage }`).
        // Non-entity bindings stay local so the immutable-local guard applies.
        self.scope.push(BlockKind::Inner);
        self.check_pattern(pattern, &element_ty);
        self.scope.mark_current_scope_entities_non_local();
        self.check_block(body);
        self.scope.pop();

        Ty::Unit
    }

    fn check_list_comprehension(
        &mut self,
        element: &Spanned<ExprKind>,
        pattern: &Spanned<PatternKind>,
        iterable: &ForIterable,
        filter: Option<&Spanned<ExprKind>>,
        span: ttrpg_ast::Span,
    ) -> Ty {
        // Resolve element type from iterable (same logic as check_for)
        let iter_elem_ty = match iterable {
            ForIterable::Collection(expr) => {
                let coll_ty = self.check_expr(expr);
                match coll_ty {
                    Ty::List(inner) | Ty::Set(inner) => *inner,
                    Ty::Map(_, _) => {
                        self.error(
                            "map iteration is not supported; use keys() or values()".to_string(),
                            span,
                        );
                        Ty::Error
                    }
                    Ty::Error => Ty::Error,
                    other => {
                        self.error(format!("expected list or set, found {}", other), span);
                        Ty::Error
                    }
                }
            }
            ForIterable::Range {
                start,
                end,
                inclusive: _,
            } => {
                let start_ty = self.check_expr(start);
                let end_ty = self.check_expr(end);
                if !start_ty.is_error() && !start_ty.is_int_like() {
                    self.error(
                        format!("range start must be int, found {}", start_ty),
                        start.span,
                    );
                }
                if !end_ty.is_error() && !end_ty.is_int_like() {
                    self.error(format!("range end must be int, found {}", end_ty), end.span);
                }
                Ty::Int
            }
        };

        // Push scope and bind pattern
        self.scope.push(BlockKind::Inner);
        self.check_pattern(pattern, &iter_elem_ty);

        // Check filter if present
        if let Some(filter_expr) = filter {
            let filter_ty = self.check_expr(filter_expr);
            if !filter_ty.is_error() && filter_ty != Ty::Bool {
                self.error(
                    format!(
                        "list comprehension filter must be bool, found {}",
                        filter_ty
                    ),
                    filter_expr.span,
                );
            }
        }

        // Check element expression
        let elem_ty = self.check_expr(element);
        self.scope.pop();

        Ty::List(Box::new(elem_ty))
    }

    fn check_arm_body(&mut self, body: &ArmBody, hint: Option<&Ty>) -> Ty {
        match body {
            ArmBody::Expr(expr) => self.check_expr_expecting(expr, hint),
            ArmBody::Block(block) => self.check_block(block),
        }
    }

    fn check_has(
        &mut self,
        entity: &Spanned<ExprKind>,
        group_name: &str,
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
                        format!("entity `{}` has no optional group `{}`", name, group_name),
                        span,
                    );
                }
            }
            Ty::AnyEntity => {
                if self.env.lookup_group(group_name).is_none()
                    && !self.env.has_optional_group_named(group_name)
                {
                    self.error(
                        format!("unknown optional group `{}` for type `entity`", group_name),
                        span,
                    );
                }
            }
            _ => {
                self.error(
                    format!(
                        "`has` can only be used with entity types, found {}",
                        entity_ty
                    ),
                    span,
                );
            }
        }
        Ty::Bool
    }

    /// Extract the full dot-separated path key from an expression chain.
    /// Returns `Some("actor")` for `actor`, `Some("actor.foo")` for `actor.foo`, etc.
    /// Returns `None` for expressions involving indexing or non-variable roots,
    /// since narrowing cannot be statically tracked through dynamic access.
    fn extract_path_key(&self, expr: &Spanned<ExprKind>) -> Option<Name> {
        match &expr.node {
            ExprKind::Ident(name) => Some(name.clone()),
            ExprKind::FieldAccess { object, field } => self
                .extract_path_key(object)
                .map(|p| Name::from(format!("{}.{}", p, field))),
            ExprKind::Paren(inner) => self.extract_path_key(inner),
            _ => None,
        }
    }

    /// Extract `(path_key, group_name)` narrowing pairs from a `has` condition.
    /// Supports `entity has Group`, `a and b` composition, and parenthesized expressions.
    fn extract_has_narrowings(&self, expr: &Spanned<ExprKind>) -> Vec<(Name, Name)> {
        match &expr.node {
            ExprKind::Has { entity, group_name } => {
                if let Some(path_key) = self.extract_path_key(entity) {
                    vec![(path_key, group_name.clone())]
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

    // ── Alias-qualified expression resolution ──────────────────────

    /// Resolve the target system for a module alias in the current system.
    /// Returns the target system name, or emits an error and returns `None`.
    fn resolve_alias_target(&mut self, alias: &str, _span: ttrpg_ast::Span) -> Option<Name> {
        let current = self.current_system.as_ref()?;
        let aliases = self.env.system_aliases.get(current)?;
        aliases.get(alias).cloned()
    }

    /// Resolve field access on a module alias: `Alias.Name`.
    /// Handles enum types, enum variants, and conditions from the target system.
    fn resolve_alias_field(&mut self, alias: &str, field: &str, span: ttrpg_ast::Span) -> Ty {
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
                            self.error(format!("type `{}` cannot be used as a value", field), span);
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
    fn resolve_alias_call(
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
    fn check_args(
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

                // Check `with` group constraints at call site
                if !params[idx].with_groups.is_empty() {
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
    fn check_alias_function_call(&mut self, name: &str, args: &[Arg], span: ttrpg_ast::Span) -> Ty {
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
