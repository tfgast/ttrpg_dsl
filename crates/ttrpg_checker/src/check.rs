use std::collections::HashSet;

use ttrpg_ast::ast::*;
use ttrpg_ast::diagnostic::Diagnostic;
use ttrpg_ast::Span;

use crate::env::*;
use crate::scope::*;
use crate::ty::Ty;

pub struct Checker<'a> {
    pub env: &'a TypeEnv,
    pub scope: ScopeStack,
    pub diagnostics: Vec<Diagnostic>,
}

impl<'a> Checker<'a> {
    pub fn new(env: &'a TypeEnv) -> Self {
        Self {
            env,
            scope: ScopeStack::new(),
            diagnostics: Vec::new(),
        }
    }

    pub fn error(&mut self, message: impl Into<String>, span: Span) {
        self.diagnostics.push(Diagnostic::error(message, span));
    }

    pub fn warning(&mut self, message: impl Into<String>, span: Span) {
        self.diagnostics.push(Diagnostic::warning(message, span));
    }

    /// Validate type names in a type expression, emitting diagnostics for unknowns.
    pub fn validate_type(&mut self, texpr: &ttrpg_ast::Spanned<TypeExpr>) {
        self.env
            .validate_type_names(texpr, &mut self.diagnostics);
    }

    /// Check all declarations in the program.
    pub fn check_program(&mut self, program: &Program) {
        for item in &program.items {
            if let TopLevel::System(system) = &item.node {
                for decl in &system.decls {
                    self.check_decl(decl);
                }
            }
        }
    }

    fn check_decl(&mut self, decl: &ttrpg_ast::Spanned<DeclKind>) {
        match &decl.node {
            DeclKind::Derive(f) => self.check_derive(f),
            DeclKind::Mechanic(f) => self.check_mechanic(f),
            DeclKind::Action(a) => self.check_action(a),
            DeclKind::Reaction(r) => self.check_reaction(r),
            DeclKind::Condition(c) => self.check_condition(c),
            DeclKind::Struct(s) => self.check_struct_defaults(s),
            DeclKind::Entity(e) => self.check_entity_defaults(e),
            DeclKind::Prompt(p) => self.check_prompt(p),
            DeclKind::Event(e) => self.check_event(e),
            DeclKind::Enum(_) => {}
            DeclKind::Option(o) => self.check_option(o),
            DeclKind::Move(m) => self.check_move(m),
        }
    }

    fn check_derive(&mut self, f: &FnDecl) {
        self.scope.push(BlockKind::Derive);
        self.bind_params(&f.params);
        let body_ty = self.check_block(&f.body);
        let ret_ty = self.env.resolve_type(&f.return_type);
        self.check_return_type(&body_ty, &ret_ty, f.body.span);
        self.scope.pop();
    }

    fn check_mechanic(&mut self, f: &FnDecl) {
        self.scope.push(BlockKind::Mechanic);
        self.bind_params(&f.params);
        let body_ty = self.check_block(&f.body);
        let ret_ty = self.env.resolve_type(&f.return_type);
        self.check_return_type(&body_ty, &ret_ty, f.body.span);
        self.scope.pop();
    }

    fn check_action(&mut self, a: &ActionDecl) {
        self.scope.push(BlockKind::ActionResolve);

        // Bind receiver (field-mutable via action context, but not rebindable)
        let recv_ty = self.env.resolve_type(&a.receiver_type);
        self.scope.bind(
            a.receiver_name.clone(),
            VarBinding {
                ty: recv_ty,
                mutable: false,
                is_local: false,
            },
        );

        // Bind params
        self.bind_params(&a.params);

        // Bind turn keyword
        self.scope.bind(
            "turn".into(),
            VarBinding {
                ty: Ty::TurnBudget,
                mutable: true,
                is_local: false,
            },
        );

        // Check requires clause
        if let Some(ref requires) = a.requires {
            let req_ty = self.check_expr(requires);
            if !req_ty.is_error() && req_ty != Ty::Bool {
                self.error(
                    format!("requires clause must be bool, found {}", req_ty),
                    requires.span,
                );
            }
        }

        // Check resolve block
        self.check_block(&a.resolve);

        self.scope.pop();
    }

    fn check_reaction(&mut self, r: &ReactionDecl) {
        self.scope.push(BlockKind::ReactionResolve);

        // Bind receiver (field-mutable via reaction context, but not rebindable)
        let recv_ty = self.env.resolve_type(&r.receiver_type);
        self.scope.bind(
            r.receiver_name.clone(),
            VarBinding {
                ty: recv_ty,
                mutable: false,
                is_local: false,
            },
        );

        // Validate trigger event exists and bind trigger
        if let Some(event_info) = self.env.events.get(&r.trigger.event_name) {
            // Check trigger bindings: validate names match event params/fields and types match.
            // NOTE: `trigger` is bound AFTER the binding loop so that binding
            // expressions cannot reference the trigger itself (e.g.
            // `damage(actor: trigger.actor)` is invalid).
            let event_info = event_info.clone();
            let mut positional_index = 0usize;
            let mut seen_bindings = HashSet::new();

            // By design: positional trigger bindings use fill-the-gaps resolution.
            // All named bindings are collected first, then positional bindings fill the
            // remaining slots left-to-right. This means the positional mapping depends
            // on the full set of named bindings, not just those preceding the positional
            // one. This is more permissive than Python (which forbids positional after
            // keyword) but keeps the implementation simple and the behavior predictable:
            // named bindings always claim their slot, positional bindings always fill
            // the leftmost unclaimed slot.
            let named_param_names: HashSet<String> = r
                .trigger
                .bindings
                .iter()
                .filter_map(|b| b.name.clone())
                .collect();

            for binding in &r.trigger.bindings {
                if let Some(ref name) = binding.name {
                    if !seen_bindings.insert(name.clone()) {
                        self.error(
                            format!("duplicate trigger binding `{}`", name),
                            binding.span,
                        );
                    }
                    let expected_ty = event_info
                        .params
                        .iter()
                        .find(|p| p.name == *name)
                        .map(|p| &p.ty)
                        .or_else(|| {
                            event_info
                                .fields
                                .iter()
                                .find(|(n, _)| n == name)
                                .map(|(_, ty)| ty)
                        })
                        .cloned();

                    if let Some(expected) = expected_ty {
                        let val_ty = self.check_expr(&binding.value);
                        if !val_ty.is_error() && !self.types_compatible(&val_ty, &expected) {
                            self.error(
                                format!(
                                    "trigger binding `{}` has type {}, expected {}",
                                    name, val_ty, expected
                                ),
                                binding.value.span,
                            );
                        }
                    } else {
                        self.check_expr(&binding.value);
                        self.error(
                            format!(
                                "trigger binding `{}` does not match any parameter of event `{}`",
                                name, r.trigger.event_name
                            ),
                            binding.span,
                        );
                    }
                } else {
                    // Positional binding — match against event params by position,
                    // skipping params already bound by name
                    while positional_index < event_info.params.len()
                        && named_param_names
                            .contains(&event_info.params[positional_index].name)
                    {
                        positional_index += 1;
                    }
                    if positional_index < event_info.params.len() {
                        let expected = &event_info.params[positional_index].ty;
                        let param_name = &event_info.params[positional_index].name;
                        let val_ty = self.check_expr(&binding.value);
                        if !val_ty.is_error() && !self.types_compatible(&val_ty, expected) {
                            self.error(
                                format!(
                                    "positional trigger binding {} has type {}, expected {} (parameter `{}`)",
                                    positional_index, val_ty, expected, param_name
                                ),
                                binding.value.span,
                            );
                        }
                    } else {
                        self.check_expr(&binding.value);
                        self.error(
                            format!(
                                "too many positional trigger bindings for event `{}` (expected {})",
                                r.trigger.event_name, event_info.params.len()
                            ),
                            binding.span,
                        );
                    }
                    positional_index += 1;
                }
            }

            // Bind `trigger` with event payload fields as a synthetic struct.
            // Placed after the binding loop so binding expressions cannot
            // reference `trigger` itself.
            self.scope.bind(
                "trigger".into(),
                VarBinding {
                    ty: Ty::Struct(format!("__event_{}", r.trigger.event_name)),
                    mutable: false,
                    is_local: false,
                },
            );
        } else {
            self.error(
                format!("undefined event `{}`", r.trigger.event_name),
                r.trigger.span,
            );
            // Still bind trigger as error so body doesn't cascade
            self.scope.bind(
                "trigger".into(),
                VarBinding {
                    ty: Ty::Error,
                    mutable: false,
                    is_local: false,
                },
            );
        }

        // Bind turn keyword
        self.scope.bind(
            "turn".into(),
            VarBinding {
                ty: Ty::TurnBudget,
                mutable: true,
                is_local: false,
            },
        );

        // Check resolve block
        self.check_block(&r.resolve);

        self.scope.pop();
    }

    fn check_condition(&mut self, c: &ConditionDecl) {
        for clause in &c.clauses {
            match clause {
                ConditionClause::Modify(m) => {
                    self.check_modify_clause(
                        m,
                        Some((&c.receiver_name, &c.receiver_type)),
                    );
                }
                ConditionClause::Suppress(s) => {
                    self.check_suppress_clause(s, &c.receiver_name, &c.receiver_type);
                }
            }
        }
    }

    fn check_option(&mut self, o: &OptionDecl) {
        if let Some(ref clauses) = o.when_enabled {
            for clause in clauses {
                self.check_modify_clause(clause, None);
            }
        }
    }

    fn check_move(&mut self, m: &MoveDecl) {
        self.scope.push(BlockKind::ActionResolve);

        // Bind receiver
        let recv_ty = self.env.resolve_type(&m.receiver_type);
        self.scope.bind(
            m.receiver_name.clone(),
            VarBinding {
                ty: recv_ty,
                mutable: false,
                is_local: false,
            },
        );

        // Bind params
        self.bind_params(&m.params);

        // Bind turn keyword
        self.scope.bind(
            "turn".into(),
            VarBinding {
                ty: Ty::TurnBudget,
                mutable: true,
                is_local: false,
            },
        );

        // Check roll expression must be DiceExpr
        let roll_ty = self.check_expr(&m.roll_expr);
        if !roll_ty.is_error() && roll_ty != Ty::DiceExpr {
            self.error(
                format!(
                    "move `{}` roll expression must be DiceExpr, found {}",
                    m.name, roll_ty
                ),
                m.roll_expr.span,
            );
        }

        // Check each outcome block
        for outcome in &m.outcomes {
            self.scope.push(BlockKind::ActionResolve);
            self.check_block(&outcome.body);
            self.scope.pop();
        }

        self.scope.pop();
    }

    fn check_prompt(&mut self, p: &PromptDecl) {
        self.scope.push(BlockKind::Derive);
        self.bind_params(&p.params);

        if let Some(ref suggest) = p.suggest {
            let suggest_ty = self.check_expr(suggest);
            let ret_ty = self.env.resolve_type(&p.return_type);
            if !suggest_ty.is_error() && !self.types_compatible(&suggest_ty, &ret_ty) {
                self.error(
                    format!(
                        "suggest expression has type {}, expected {}",
                        suggest_ty, ret_ty
                    ),
                    suggest.span,
                );
            }
        }

        self.scope.pop();
    }

    fn check_event(&mut self, e: &EventDecl) {
        self.scope.push(BlockKind::Derive);
        for param in &e.params {
            if let Some(ref default) = param.default {
                let def_ty = self.check_expr(default);
                let param_ty = self.env.resolve_type(&param.ty);
                if !def_ty.is_error() && !self.types_compatible(&def_ty, &param_ty) {
                    self.error(
                        format!(
                            "event `{}` parameter `{}` default has type {}, expected {}",
                            e.name, param.name, def_ty, param_ty
                        ),
                        default.span,
                    );
                }
            }
        }
        self.scope.pop();
    }

    fn check_struct_defaults(&mut self, s: &StructDecl) {
        // Check default expressions for fields
        self.scope.push(BlockKind::Derive);
        for field in &s.fields {
            if let Some(ref default) = field.default {
                let def_ty = self.check_expr(default);
                let field_ty = self.env.resolve_type(&field.ty);
                if !def_ty.is_error() && !self.types_compatible(&def_ty, &field_ty) {
                    self.error(
                        format!(
                            "field `{}` default has type {}, expected {}",
                            field.name, def_ty, field_ty
                        ),
                        default.span,
                    );
                }
            }
        }
        self.scope.pop();
    }

    fn check_entity_defaults(&mut self, e: &EntityDecl) {
        self.scope.push(BlockKind::Derive);
        for field in &e.fields {
            if let Some(ref default) = field.default {
                let def_ty = self.check_expr(default);
                let field_ty = self.env.resolve_type(&field.ty);
                if !def_ty.is_error() && !self.types_compatible(&def_ty, &field_ty) {
                    self.error(
                        format!(
                            "field `{}` default has type {}, expected {}",
                            field.name, def_ty, field_ty
                        ),
                        default.span,
                    );
                }
            }
        }
        self.scope.pop();
    }

    fn bind_params(&mut self, params: &[Param]) {
        for param in params {
            let ty = self.env.resolve_type(&param.ty);
            if let Some(ref default) = param.default {
                let def_ty = self.check_expr(default);
                if !def_ty.is_error() && !self.types_compatible(&def_ty, &ty) {
                    self.error(
                        format!(
                            "parameter `{}` default has type {}, expected {}",
                            param.name, def_ty, ty
                        ),
                        default.span,
                    );
                }
            }
            self.scope.bind(
                param.name.clone(),
                VarBinding {
                    ty,
                    mutable: false,
                    is_local: false,
                },
            );
        }
    }

    fn check_return_type(&mut self, body_ty: &Ty, ret_ty: &Ty, span: Span) {
        if body_ty.is_error() || ret_ty.is_error() {
            return;
        }
        if !self.types_compatible(body_ty, ret_ty) {
            self.error(
                format!(
                    "function body has type {}, expected return type {}",
                    body_ty, ret_ty
                ),
                span,
            );
        }
    }

    /// Check type compatibility. Allows Resource <-> Int coercion
    /// and built-in/user-defined type equivalence.
    pub fn types_compatible(&self, actual: &Ty, expected: &Ty) -> bool {
        if actual == expected {
            return true;
        }
        // Resource is int-like for reads
        if actual.is_int_like() && expected.is_int_like() {
            return true;
        }
        // none (Option(Error)) is compatible with any Option(T)
        match (actual, expected) {
            (Ty::Option(inner), _) if inner.is_error() && matches!(expected, Ty::Option(_)) => {
                return true;
            }
            (_, Ty::Option(inner)) if inner.is_error() && matches!(actual, Ty::Option(_)) => {
                return true;
            }
            _ => {}
        }
        // AnyEntity matches any Entity(_)
        match (actual, expected) {
            (Ty::Entity(_), Ty::AnyEntity)
            | (Ty::AnyEntity, Ty::Entity(_))
            | (Ty::AnyEntity, Ty::AnyEntity) => return true,
            _ => {}
        }
        // Built-in type keywords and user-defined types with the same name are equivalent
        match (actual, expected) {
            (Ty::Enum(name), Ty::Duration) | (Ty::Duration, Ty::Enum(name))
                if name == "Duration" =>
            {
                return true;
            }
            (Ty::Struct(name), Ty::TurnBudget) | (Ty::TurnBudget, Ty::Struct(name))
                if name == "TurnBudget" =>
            {
                return true;
            }
            _ => {}
        }
        false
    }

    /// Unify two branch types (if/else, match arms), returning the preferred
    /// result type or `None` if incompatible.
    ///
    /// When one side is `none` (i.e. `option<error>`), the concrete option type
    /// from the other side is preferred so that the inferred type carries the
    /// real element type forward.
    pub fn unify_branch_types(&self, a: &Ty, b: &Ty) -> Option<Ty> {
        if a.is_error() {
            return Some(b.clone());
        }
        if b.is_error() {
            return Some(a.clone());
        }
        // Prefer the concrete side when the other is `none`
        if a.is_none() && self.types_compatible(a, b) {
            return Some(b.clone());
        }
        if b.is_none() && self.types_compatible(b, a) {
            return Some(a.clone());
        }
        if self.types_compatible(a, b) {
            return Some(a.clone());
        }
        if self.types_compatible(b, a) {
            return Some(b.clone());
        }
        None
    }
}
