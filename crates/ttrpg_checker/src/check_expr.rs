use ttrpg_ast::ast::*;
use ttrpg_ast::Name;
use ttrpg_ast::Spanned;

use crate::check::{Checker, Namespace};
use crate::env::*;
use crate::scope::BlockKind;
use crate::ty::Ty;

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

            ExprKind::Has {
                entity,
                group_name,
                alias,
            } => self.check_has(entity, group_name, alias, expr.span),
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

        // Check if `field` is a group alias on this entity variable
        let resolved_field: std::borrow::Cow<str> = if obj_ty.is_entity() {
            if let Some(path_key) = self.extract_path_key(object) {
                if let Some(real_group) = self.scope.resolve_group_alias(&path_key, field) {
                    self.resolved_group_aliases
                        .insert(span, real_group.clone());
                    std::borrow::Cow::Owned(real_group.into_inner())
                } else {
                    std::borrow::Cow::Borrowed(field)
                }
            } else {
                std::borrow::Cow::Borrowed(field)
            }
        } else {
            std::borrow::Cow::Borrowed(field)
        };

        let result_ty = self.resolve_field(&obj_ty, &resolved_field, span);

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
}
