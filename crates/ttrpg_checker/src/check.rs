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
            DeclKind::Prompt(_) | DeclKind::Event(_) | DeclKind::Enum(_) => {}
            DeclKind::Option(_) | DeclKind::Move(_) => {}
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

        // Bind receiver as mutable
        let recv_ty = self.env.resolve_type(&a.receiver_type);
        self.scope.bind(
            a.receiver_name.clone(),
            VarBinding {
                ty: recv_ty,
                mutable: true,
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

        // Bind receiver as mutable
        let recv_ty = self.env.resolve_type(&r.receiver_type);
        self.scope.bind(
            r.receiver_name.clone(),
            VarBinding {
                ty: recv_ty,
                mutable: true,
            },
        );

        // Validate trigger event exists and bind trigger
        if let Some(event_info) = self.env.events.get(&r.trigger.event_name) {
            // Bind `trigger` with event payload fields as a synthetic struct
            // For simplicity, bind trigger as Entity type that happens to have
            // the event's payload fields. We'll handle field access resolution
            // in check_expr by checking event fields directly.
            self.scope.bind(
                "trigger".into(),
                VarBinding {
                    ty: Ty::Struct(format!("__event_{}", r.trigger.event_name)),
                    mutable: false,
                },
            );

            // Check trigger bindings: validate names match event params/fields and types match.
            let event_info = event_info.clone();
            for binding in &r.trigger.bindings {
                if let Some(ref name) = binding.name {
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
                        self.error(
                            format!(
                                "trigger binding `{}` does not match any parameter of event `{}`",
                                name, r.trigger.event_name
                            ),
                            binding.span,
                        );
                    }
                } else {
                    // Positional binding — still type-check the value
                    self.check_expr(&binding.value);
                }
            }
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
                },
            );
        }

        // Bind turn keyword
        self.scope.bind(
            "turn".into(),
            VarBinding {
                ty: Ty::TurnBudget,
                mutable: true,
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
                    self.check_modify_clause(m, &c.receiver_name, &c.receiver_type);
                }
                ConditionClause::Suppress(s) => {
                    self.check_suppress_clause(s, &c.receiver_name, &c.receiver_type);
                }
            }
        }
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
            self.scope.bind(
                param.name.clone(),
                VarBinding {
                    ty,
                    mutable: false,
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
}
