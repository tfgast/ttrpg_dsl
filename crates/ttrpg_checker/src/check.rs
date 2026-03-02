use std::collections::{HashMap, HashSet};

use ttrpg_ast::ast::*;
use ttrpg_ast::diagnostic::Diagnostic;
use ttrpg_ast::module::ModuleMap;
use ttrpg_ast::Name;
use ttrpg_ast::{Span, Spanned};

use crate::env::*;
use crate::scope::*;
use crate::ty::Ty;

type SelectorMatchMap = HashMap<ModifyClauseId, HashSet<Name>>;

/// Namespace for visibility checks — which owner map to consult.
#[derive(Debug, Clone, Copy)]
pub enum Namespace {
    Group,
    Type,
    Function,
    Condition,
    Event,
    Variant,
    Option,
    Tag,
}

pub struct Checker<'a> {
    pub env: &'a TypeEnv,
    pub scope: ScopeStack,
    pub diagnostics: Vec<Diagnostic>,
    /// The ModuleMap, if module-aware checking is enabled.
    pub modules: Option<&'a ModuleMap>,
    /// The system currently being checked (set during check_program iteration).
    pub current_system: Option<Name>,
    /// Maps each bare variant expression span to its resolved owning enum.
    /// Transferred to `TypeEnv` after checking for use by the interpreter.
    pub resolved_variants: HashMap<Span, Name>,
    /// Maps FieldAccess spans where a group alias was used → real group name.
    /// Transferred to `TypeEnv` for interpreter use.
    pub resolved_group_aliases: HashMap<Span, Name>,
    /// Maps LValue spans where a group alias was used → (segment_index, real_group_name).
    /// Transferred to `TypeEnv` for interpreter use.
    pub resolved_lvalue_aliases: HashMap<Span, (usize, Name)>,
    /// Maps selector-targeted modify clause IDs → set of matched function names.
    /// Transferred to `TypeEnv` for interpreter use.
    pub selector_matches: SelectorMatchMap,
}

impl<'a> Checker<'a> {
    pub fn new(env: &'a TypeEnv, modules: Option<&'a ModuleMap>) -> Self {
        Self {
            env,
            scope: ScopeStack::new(),
            diagnostics: Vec::new(),
            modules,
            current_system: None,
            resolved_variants: HashMap::new(),
            resolved_group_aliases: HashMap::new(),
            resolved_lvalue_aliases: HashMap::new(),
            selector_matches: HashMap::new(),
        }
    }

    pub fn error(&mut self, message: impl Into<String>, span: Span) {
        self.diagnostics.push(Diagnostic::error(message, span));
    }

    pub fn warning(&mut self, message: impl Into<String>, span: Span) {
        self.diagnostics.push(Diagnostic::warning(message, span));
    }

    /// Try to resolve a bare variant name to its unique owning enum.
    ///
    /// - 1 owner: records the resolution and returns the enum name.
    /// - >1 owners: emits an ambiguity error listing qualified forms, returns `None`.
    /// - 0 owners: returns `None` (not a variant at all).
    pub fn resolve_bare_variant(&mut self, variant: &str, span: Span) -> Option<Name> {
        self.resolve_bare_variant_with_hint(variant, span, None)
    }

    /// Like `resolve_bare_variant`, but uses an expected-type hint to
    /// disambiguate when multiple enums share the variant name.
    pub fn resolve_bare_variant_with_hint(
        &mut self,
        variant: &str,
        span: Span,
        hint: Option<&Ty>,
    ) -> Option<Name> {
        let all_owners = match self.env.variant_to_enums.get(variant) {
            Some(owners) => owners.clone(),
            None => return None,
        };

        // Filter owners by system visibility when in module-aware mode
        let owners: Vec<Name> = if let Some(ref current) = self.current_system {
            if let Some(vis) = self.env.system_visibility.get(current) {
                all_owners
                    .iter()
                    .filter(|o| vis.types.contains(o.as_str()))
                    .cloned()
                    .collect()
            } else {
                all_owners
            }
        } else {
            all_owners
        };

        if owners.is_empty() {
            // Variant exists globally but no owning enum is visible — emit visibility error
            // using the first global owner for the error message
            self.check_name_visible(variant, Namespace::Variant, span);
            return None;
        }

        if owners.len() == 1 {
            let enum_name = owners[0].clone();
            self.resolved_variants.insert(span, enum_name.clone());
            Some(enum_name)
        } else {
            // Try to disambiguate via expected-type hint
            if let Some(hinted) = enum_name_from_hint(hint) {
                if owners.iter().any(|o| o == hinted) {
                    let n = Name::from(hinted);
                    self.resolved_variants.insert(span, n.clone());
                    return Some(n);
                }
            }
            let qualified: Vec<String> = owners
                .iter()
                .map(|e| format!("{}.{}", e, variant))
                .collect();
            let owners_display: Vec<&str> = owners.iter().map(|o| o.as_str()).collect();
            self.error(
                format!(
                    "ambiguous variant `{}`; could belong to: {}. Use qualified form: {}",
                    variant,
                    owners_display.join(", "),
                    qualified.join(" or "),
                ),
                span,
            );
            None
        }
    }

    /// Check whether a name is a known enum variant (regardless of how many enums own it).
    pub fn is_known_variant(&self, name: &str) -> bool {
        self.env.variant_to_enums.contains_key(name)
    }

    /// Check whether `name` is visible in the current system.
    ///
    /// No-op when `current_system` is `None` (single-file mode) or when the
    /// name has no owner (builtins, fallback types). Emits a diagnostic but
    /// does NOT return `Ty::Error` — callers continue with the real type so
    /// that a missing import doesn't cascade into phantom type errors.
    pub fn check_name_visible(&mut self, name: &str, ns: Namespace, span: Span) {
        let current = match &self.current_system {
            Some(s) => s.clone(),
            None => return,
        };

        // Look up the owning system for this name in the appropriate namespace
        let owner = match ns {
            Namespace::Group => self.env.group_owner.get(name),
            Namespace::Type => self.env.type_owner.get(name),
            Namespace::Function => self.env.function_owner.get(name),
            Namespace::Condition => self.env.condition_owner.get(name),
            Namespace::Event => self.env.event_owner.get(name),
            Namespace::Variant => {
                // Derive owner from enum's type_owner to avoid single-owner
                // overwrite when multiple systems share a variant name.
                self.env.variant_to_enums.get(name).and_then(|enums| {
                    enums
                        .iter()
                        .find_map(|e| self.env.type_owner.get(e.as_str()))
                })
            }
            Namespace::Option => self.env.option_owner.get(name),
            Namespace::Tag => self.env.tag_owner.get(name),
        };

        // No owner → builtin or fallback type, always visible
        let owner = match owner {
            Some(o) => o,
            None => return,
        };

        // Check the visibility set for the current system
        if let Some(vis) = self.env.system_visibility.get(&current) {
            let visible = match ns {
                Namespace::Group => vis.groups.contains(name),
                Namespace::Type => vis.types.contains(name),
                Namespace::Function => vis.functions.contains(name),
                Namespace::Condition => vis.conditions.contains(name),
                Namespace::Event => vis.events.contains(name),
                Namespace::Variant => vis.variants.contains(name),
                Namespace::Option => vis.options.contains(name),
                Namespace::Tag => vis.tags.contains(name),
            };
            if !visible {
                self.error(
                    format!(
                        "`{}` is defined in system \"{}\"; add `use \"{}\"` to access it from \"{}\"",
                        name, owner, owner, current
                    ),
                    span,
                );
            }
        }
    }

    /// Validate type names in a type expression, emitting diagnostics for unknowns.
    pub fn validate_type(&mut self, texpr: &ttrpg_ast::Spanned<TypeExpr>) {
        self.env.validate_type_names(texpr, &mut self.diagnostics);
    }

    /// Validate, check visibility, and resolve a type expression in one step.
    pub(crate) fn resolve_type_validated(&mut self, texpr: &ttrpg_ast::Spanned<TypeExpr>) -> Ty {
        self.validate_type(texpr);
        self.check_type_visible(texpr);
        self.env.resolve_type(texpr)
    }

    /// Check visibility of all named types referenced in a type expression.
    ///
    /// Walks the `TypeExpr` tree and calls [`check_name_visible`] for each
    /// user-defined or overridable type it finds. Builtins with no owner
    /// (e.g. the default `Duration`) are handled gracefully — `check_name_visible`
    /// is a no-op when the name has no registered owner.
    pub fn check_type_visible(&mut self, texpr: &ttrpg_ast::Spanned<TypeExpr>) {
        match &texpr.node {
            TypeExpr::Named(name) => {
                if name == "entity" {
                    return;
                }
                self.check_name_visible(name, Namespace::Type, texpr.span);
            }
            // TurnBudget/Duration keywords may resolve to user-defined types
            TypeExpr::TurnBudget => {
                self.check_name_visible("TurnBudget", Namespace::Type, texpr.span);
            }
            TypeExpr::Duration => {
                self.check_name_visible("Duration", Namespace::Type, texpr.span);
            }
            TypeExpr::List(inner) | TypeExpr::Set(inner) | TypeExpr::OptionType(inner) => {
                self.check_type_visible(inner);
            }
            TypeExpr::Map(k, v) => {
                self.check_type_visible(k);
                self.check_type_visible(v);
            }
            // Builtins (Int, Float, Bool, etc.), Resource bounds, Qualified — nothing to check
            _ => {}
        }
    }

    /// Check all declarations in the program.
    pub fn check_program(&mut self, program: &Program) {
        for item in &program.items {
            if let TopLevel::System(system) = &item.node {
                self.current_system = if self.modules.is_some() {
                    Some(system.name.clone())
                } else {
                    None
                };
                for decl in &system.decls {
                    self.check_decl(decl);
                }
            }
        }
        self.current_system = None;
    }

    fn check_decl(&mut self, decl: &ttrpg_ast::Spanned<DeclKind>) {
        match &decl.node {
            DeclKind::Group(g) => self.check_group_defaults(g),
            DeclKind::Derive(f) => self.check_derive(f),
            DeclKind::Mechanic(f) => self.check_mechanic(f),
            DeclKind::Action(a) => self.check_action(a),
            DeclKind::Reaction(r) => self.check_reaction(r),
            DeclKind::Condition(c) => self.check_condition(c),
            DeclKind::Struct(s) => self.check_struct_defaults(s),
            DeclKind::Entity(e) => self.check_entity_defaults(e),
            DeclKind::Prompt(p) => self.check_prompt(p),
            DeclKind::Event(e) => self.check_event(e),
            DeclKind::Enum(e) => self.check_enum_visibility(e),
            DeclKind::Option(o) => self.check_option(o),
            DeclKind::Hook(h) => self.check_hook(h),
            DeclKind::Table(t) => self.check_table(t),
            DeclKind::Unit(u) => self.check_unit_defaults(u),
            DeclKind::Tag(_) => {} // Validated during collection
            DeclKind::Move(_) => {
                self.error(
                    "move declarations must be lowered before type-checking",
                    decl.span,
                );
            }
        }
    }

    fn check_enum_visibility(&mut self, e: &EnumDecl) {
        for variant in &e.variants {
            if let Some(ref fields) = variant.fields {
                for field in fields {
                    self.check_type_visible(&field.ty);
                }
            }
        }
    }

    fn check_derive(&mut self, f: &FnDecl) {
        self.scope.push(BlockKind::Derive);
        self.check_type_visible(&f.return_type);
        self.bind_params(&f.params);
        let ret_ty = self.env.resolve_type(&f.return_type);
        let body_ty = self.check_block_with_tail_hint(&f.body, Some(&ret_ty));
        self.check_return_type(&body_ty, &ret_ty, f.body.span);
        self.scope.pop();
    }

    fn check_mechanic(&mut self, f: &FnDecl) {
        self.scope.push(BlockKind::Mechanic);
        self.check_type_visible(&f.return_type);
        self.bind_params(&f.params);
        let ret_ty = self.env.resolve_type(&f.return_type);
        let body_ty = self.check_block_with_tail_hint(&f.body, Some(&ret_ty));
        self.check_return_type(&body_ty, &ret_ty, f.body.span);
        self.scope.pop();
    }

    fn check_table(&mut self, t: &TableDecl) {
        // Tables are pure — use Derive scope (no dice, no mutation)
        self.scope.push(BlockKind::Derive);
        self.check_type_visible(&t.return_type);

        // Check param type visibility (matching derive/mechanic behavior)
        for param in &t.params {
            self.check_type_visible(&param.ty);
        }

        // Resolve param types
        let param_tys: Vec<Ty> = t
            .params
            .iter()
            .map(|p| self.env.resolve_type(&p.ty))
            .collect();
        let ret_ty = self.env.resolve_type(&t.return_type);

        // Track wildcard position for unreachable-entry warnings
        let mut seen_wildcard = false;

        for entry in &t.entries {
            // Warn if this entry follows a full wildcard (all keys are wildcards)
            if seen_wildcard {
                self.warning(
                    "unreachable table entry: wildcard `_` entry must be last".to_string(),
                    entry.span,
                );
            }

            // Check key count matches param count
            if entry.keys.len() != t.params.len() {
                self.error(
                    format!(
                        "table entry has {} key(s), expected {} (one per parameter)",
                        entry.keys.len(),
                        t.params.len()
                    ),
                    entry.span,
                );
                continue;
            }

            // Detect full-wildcard entries (every key is `_`)
            if entry
                .keys
                .iter()
                .all(|k| matches!(k.node, TableKey::Wildcard))
            {
                seen_wildcard = true;
            }

            // Type-check each key against its corresponding param type
            for (key, expected_ty) in entry.keys.iter().zip(param_tys.iter()) {
                match &key.node {
                    TableKey::Expr(expr_kind) => {
                        let key_expr = Spanned {
                            node: expr_kind.clone(),
                            span: key.span,
                        };
                        let key_ty = self.check_expr_expecting(&key_expr, Some(expected_ty));
                        if !key_ty.is_error()
                            && !expected_ty.is_error()
                            && !self.types_compatible(&key_ty, expected_ty)
                        {
                            self.error(
                                format!("table key has type {}, expected {}", key_ty, expected_ty),
                                key.span,
                            );
                        }
                    }
                    TableKey::Range { start, end } => {
                        // Ranges are only valid for int keys
                        if !expected_ty.is_error() && *expected_ty != Ty::Int {
                            self.error(
                                format!(
                                    "range keys are only valid for int parameters, found {}",
                                    expected_ty
                                ),
                                key.span,
                            );
                        }
                        let start_ty = self.check_expr(start);
                        if !start_ty.is_error() && start_ty != Ty::Int {
                            self.error(
                                format!("range start must be int, found {}", start_ty),
                                start.span,
                            );
                        }
                        let end_ty = self.check_expr(end);
                        if !end_ty.is_error() && end_ty != Ty::Int {
                            self.error(
                                format!("range end must be int, found {}", end_ty),
                                end.span,
                            );
                        }
                    }
                    TableKey::Wildcard => {
                        // Wildcard matches any type — always valid
                    }
                }
            }

            // Type-check the value expression
            let val_ty = self.check_expr_expecting(&entry.value, Some(&ret_ty));
            if !val_ty.is_error() && !ret_ty.is_error() && !self.types_compatible(&val_ty, &ret_ty)
            {
                self.error(
                    format!("table entry value has type {}, expected {}", val_ty, ret_ty),
                    entry.value.span,
                );
            }
        }

        self.scope.pop();
    }

    fn check_action(&mut self, a: &ActionDecl) {
        self.scope.push(BlockKind::ActionResolve);

        // Bind receiver (field-mutable via action context, but not rebindable)
        self.check_type_visible(&a.receiver_type);
        let recv_ty = self.env.resolve_type(&a.receiver_type);
        self.scope.bind(
            a.receiver_name.clone(),
            VarBinding {
                ty: recv_ty.clone(),
                mutable: false,
                is_local: false,
            },
        );

        // Validate and narrow receiver with_groups
        self.validate_with_groups(
            &a.receiver_name,
            &recv_ty,
            &a.receiver_with_groups,
            a.receiver_type.span,
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
        self.check_type_visible(&r.receiver_type);
        let recv_ty = self.env.resolve_type(&r.receiver_type);
        self.scope.bind(
            r.receiver_name.clone(),
            VarBinding {
                ty: recv_ty.clone(),
                mutable: false,
                is_local: false,
            },
        );

        // Validate and narrow receiver with_groups
        self.validate_with_groups(
            &r.receiver_name,
            &recv_ty,
            &r.receiver_with_groups,
            r.receiver_type.span,
        );

        self.check_trigger_and_body(&r.trigger, &r.resolve);

        self.scope.pop();
    }

    fn check_hook(&mut self, h: &HookDecl) {
        self.scope.push(BlockKind::HookResolve);

        // Bind receiver
        self.check_type_visible(&h.receiver_type);
        let recv_ty = self.env.resolve_type(&h.receiver_type);
        self.scope.bind(
            h.receiver_name.clone(),
            VarBinding {
                ty: recv_ty.clone(),
                mutable: false,
                is_local: false,
            },
        );

        // Validate and narrow receiver with_groups
        self.validate_with_groups(
            &h.receiver_name,
            &recv_ty,
            &h.receiver_with_groups,
            h.receiver_type.span,
        );

        self.check_trigger_and_body(&h.trigger, &h.resolve);

        self.scope.pop();
    }

    /// Shared logic for reaction and hook: validate trigger event, check
    /// bindings, bind `trigger` and `turn`, then type-check the body block.
    fn check_trigger_and_body(&mut self, trigger: &TriggerExpr, body: &Block) {
        // Validate trigger event exists and bind trigger
        if let Some(event_info) = self.env.events.get(&trigger.event_name) {
            self.check_name_visible(&trigger.event_name, Namespace::Event, trigger.span);
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
            let named_param_names: HashSet<Name> = trigger
                .bindings
                .iter()
                .filter_map(|b| b.name.clone())
                .collect();

            // Trigger binding expressions must be side-effect-free
            self.scope.push(BlockKind::TriggerBinding);
            for binding in &trigger.bindings {
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
                                name, trigger.event_name
                            ),
                            binding.span,
                        );
                    }
                } else {
                    // Positional binding — match against event params by position,
                    // skipping params already bound by name
                    while positional_index < event_info.params.len()
                        && named_param_names.contains(&event_info.params[positional_index].name)
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
                                trigger.event_name,
                                event_info.params.len()
                            ),
                            binding.span,
                        );
                    }
                    positional_index += 1;
                }
            }

            self.scope.pop(); // TriggerBinding

            // Bind `trigger` with event payload fields as a synthetic struct.
            // Placed after the binding loop so binding expressions cannot
            // reference `trigger` itself.
            self.scope.bind(
                "trigger".into(),
                VarBinding {
                    ty: Ty::Struct(Name::from(format!("__event_{}", trigger.event_name))),
                    mutable: false,
                    is_local: false,
                },
            );
        } else {
            self.error(
                format!("undefined event `{}`", trigger.event_name),
                trigger.span,
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

        // Check body
        self.check_block(body);
    }

    fn check_condition(&mut self, c: &ConditionDecl) {
        // Check visibility of receiver and parameter types
        self.check_type_visible(&c.receiver_type);
        for param in &c.params {
            self.check_type_visible(&param.ty);
        }
        // Check visibility of extended parent conditions
        for parent in &c.extends {
            self.check_name_visible(parent.node.as_str(), Namespace::Condition, parent.span);
        }

        // Type-check default expressions for condition parameters
        // Bind incrementally so later defaults can reference earlier params
        self.scope.push(BlockKind::Derive);
        for param in &c.params {
            let param_ty = self.env.resolve_type(&param.ty);
            if let Some(ref default) = param.default {
                let def_ty = self.check_expr_expecting(default, Some(&param_ty));
                if !def_ty.is_error() && !self.types_compatible(&def_ty, &param_ty) {
                    self.error(
                        format!(
                            "condition `{}` parameter `{}` default has type {}, expected {}",
                            c.name, param.name, def_ty, param_ty
                        ),
                        default.span,
                    );
                }
            }
            self.scope.bind(
                param.name.clone(),
                VarBinding {
                    ty: param_ty,
                    mutable: false,
                    is_local: false,
                },
            );
        }
        self.scope.pop();

        for clause in &c.clauses {
            match clause {
                ConditionClause::Modify(m) => {
                    self.check_modify_clause(
                        m,
                        Some((&c.receiver_name, &c.receiver_type, &c.receiver_with_groups)),
                        &c.params,
                    );
                }
                ConditionClause::Suppress(s) => {
                    self.check_suppress_clause(
                        s,
                        &c.receiver_name,
                        &c.receiver_type,
                        &c.receiver_with_groups,
                        &c.params,
                    );
                }
            }
        }
    }

    fn check_option(&mut self, o: &OptionDecl) {
        if let Some(ref clauses) = o.when_enabled {
            for clause in clauses {
                self.check_modify_clause(clause, None, &[]);
            }
        }
    }

    fn check_prompt(&mut self, p: &PromptDecl) {
        self.scope.push(BlockKind::Derive);
        self.check_type_visible(&p.return_type);
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
        // Check visibility of parameter and field types
        for param in &e.params {
            self.check_type_visible(&param.ty);
        }
        for field in &e.fields {
            self.check_type_visible(&field.ty);
        }

        // Bind incrementally so later defaults can reference earlier params
        self.scope.push(BlockKind::Derive);
        for param in &e.params {
            let param_ty = self.env.resolve_type(&param.ty);
            if let Some(ref default) = param.default {
                let def_ty = self.check_expr_expecting(default, Some(&param_ty));
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
            self.scope.bind(
                param.name.clone(),
                VarBinding {
                    ty: param_ty,
                    mutable: false,
                    is_local: false,
                },
            );
        }
        self.scope.pop();
    }

    fn check_struct_defaults(&mut self, s: &StructDecl) {
        // Check visibility of field types
        for field in &s.fields {
            self.check_type_visible(&field.ty);
        }

        // Check default expressions for fields
        self.scope.push(BlockKind::Derive);
        for field in &s.fields {
            if let Some(ref default) = field.default {
                let field_ty = self.env.resolve_type(&field.ty);
                let def_ty = self.check_expr_expecting(default, Some(&field_ty));
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

    fn check_unit_defaults(&mut self, u: &UnitDecl) {
        for field in &u.fields {
            self.check_type_visible(&field.ty);
        }
        self.scope.push(BlockKind::Derive);
        for field in &u.fields {
            if let Some(ref default) = field.default {
                let field_ty = self.env.resolve_type(&field.ty);
                let def_ty = self.check_expr_expecting(default, Some(&field_ty));
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

    fn check_group_defaults(&mut self, g: &GroupDecl) {
        for field in &g.fields {
            self.check_type_visible(&field.ty);
        }
        self.scope.push(BlockKind::Derive);
        for field in &g.fields {
            if let Some(ref default) = field.default {
                let field_ty = self.env.resolve_type(&field.ty);
                let def_ty = self.check_expr_expecting(default, Some(&field_ty));
                if !def_ty.is_error() && !self.types_compatible(&def_ty, &field_ty) {
                    self.error(
                        format!(
                            "field `{}` in group `{}` default has type {}, expected {}",
                            field.name, g.name, def_ty, field_ty
                        ),
                        default.span,
                    );
                }
            }
        }
        self.scope.pop();
    }

    fn check_entity_defaults(&mut self, e: &EntityDecl) {
        // Check visibility of field types (including optional groups)
        for field in &e.fields {
            self.check_type_visible(&field.ty);
        }
        for group in &e.optional_groups {
            self.check_name_visible(&group.name, Namespace::Group, group.span);
            if group.is_external_ref {
                if self.env.lookup_group(&group.name).is_none() {
                    self.error(format!("unknown group `{}`", group.name), group.span);
                }
            } else {
                for field in &group.fields {
                    self.check_type_visible(&field.ty);
                }
            }
        }

        self.scope.push(BlockKind::Derive);
        for field in &e.fields {
            if let Some(ref default) = field.default {
                let field_ty = self.env.resolve_type(&field.ty);
                let def_ty = self.check_expr_expecting(default, Some(&field_ty));
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
        // Check optional group field defaults
        for group in &e.optional_groups {
            if !group.is_external_ref {
                for field in &group.fields {
                    if let Some(ref default) = field.default {
                        let field_ty = self.env.resolve_type(&field.ty);
                        let def_ty = self.check_expr_expecting(default, Some(&field_ty));
                        if !def_ty.is_error() && !self.types_compatible(&def_ty, &field_ty) {
                            self.error(
                                format!(
                                    "field `{}` in group `{}` default has type {}, expected {}",
                                    field.name, group.name, def_ty, field_ty
                                ),
                                default.span,
                            );
                        }
                    }
                }
            }
        }
        self.scope.pop();
    }

    fn bind_params(&mut self, params: &[Param]) {
        for param in params {
            self.check_type_visible(&param.ty);
            let ty = self.env.resolve_type(&param.ty);
            if let Some(ref default) = param.default {
                let def_ty = self.check_expr_expecting(default, Some(&ty));
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
                    ty: ty.clone(),
                    mutable: false,
                    is_local: false,
                },
            );
            // Validate and narrow with_groups
            self.validate_with_groups(&param.name, &ty, &param.with_groups, param.span);
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

    /// Validate `with` group constraints on a parameter or receiver, and add narrowings.
    ///
    /// For conjunctive constraints (`with A, B`), each group is narrowed and aliased.
    /// For disjunctive constraints (`with A | B`), groups are validated but NOT narrowed —
    /// the author must use `has` guards to access group fields.
    pub fn validate_with_groups(
        &mut self,
        var_name: &Name,
        ty: &Ty,
        with_clause: &WithClause,
        span: Span,
    ) {
        for entry in &with_clause.groups {
            let group_name = &entry.name;
            self.check_name_visible(group_name, Namespace::Group, span);
            match ty {
                Ty::Entity(entity_name) => {
                    if self
                        .env
                        .lookup_optional_group(entity_name, group_name)
                        .is_none()
                    {
                        self.error(
                            format!(
                                "entity `{}` has no optional group `{}`",
                                entity_name, group_name
                            ),
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
                _ if !ty.is_error() => {
                    self.error(
                        format!(
                            "`with` constraint on `{}` requires entity type, found {}",
                            var_name, ty
                        ),
                        span,
                    );
                }
                _ => {}
            }
            // Only narrow and alias for conjunctive constraints
            if !with_clause.disjunctive {
                self.scope
                    .narrow_group(var_name.clone(), group_name.clone());
                if let Some(ref alias) = entry.alias {
                    self.scope
                        .add_group_alias(var_name.clone(), alias.clone(), group_name.clone());
                }
            }
        }
    }

    /// Check a block with additional narrowings injected into the scope.
    pub fn check_block_with_narrowings(
        &mut self,
        block: &Block,
        narrowings: &[(Name, Name, Option<Name>)],
    ) -> Ty {
        self.check_block_with_narrowings_and_hint(block, narrowings, None)
    }

    pub fn check_block_with_narrowings_and_hint(
        &mut self,
        block: &Block,
        narrowings: &[(Name, Name, Option<Name>)],
        hint: Option<&Ty>,
    ) -> Ty {
        self.scope.push(BlockKind::Inner);
        for (var, group, alias) in narrowings {
            self.scope.narrow_group(var.clone(), group.clone());
            if let Some(alias) = alias {
                self.scope
                    .add_group_alias(var.clone(), alias.clone(), group.clone());
            }
        }
        let stmts = &block.node;
        let mut last_ty = Ty::Unit;
        for (i, stmt) in stmts.iter().enumerate() {
            let is_last = i == stmts.len() - 1;
            if is_last && hint.is_some() {
                last_ty = self.check_stmt_with_hint(stmt, is_last, hint);
            } else {
                last_ty = self.check_stmt(stmt, is_last);
            }
        }
        self.scope.pop();
        last_ty
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
        // ActiveCondition is accepted where Condition is expected (remove_condition overload)
        if matches!((actual, expected), (Ty::ActiveCondition, Ty::Condition)) {
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

/// Extract an enum name from a type hint, if it refers to an enum.
fn enum_name_from_hint(hint: Option<&Ty>) -> Option<&str> {
    match hint? {
        Ty::Enum(name) => Some(name.as_str()),
        Ty::Duration => Some("Duration"),
        _ => None,
    }
}
