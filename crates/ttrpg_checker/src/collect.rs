use std::collections::HashSet;

use ttrpg_ast::ast::*;
use ttrpg_ast::diagnostic::Diagnostic;
use ttrpg_ast::Span;

use crate::builtins::register_builtins;
use crate::env::*;
use crate::ty::Ty;

const VALID_COST_TOKENS: &[&str] = &["action", "bonus_action", "reaction"];

/// Check if a name uses the reserved `__` prefix. Returns `true` if the name
/// is reserved (and emits a diagnostic).
fn check_reserved_prefix(name: &str, span: Span, diagnostics: &mut Vec<Diagnostic>) -> bool {
    if name.starts_with("__") {
        diagnostics.push(Diagnostic::error(
            format!("names starting with `__` are reserved for internal use: `{}`", name),
            span,
        ));
        true
    } else {
        false
    }
}

/// Pass 1: Collect all top-level declarations into a TypeEnv.
pub fn collect(program: &Program) -> (TypeEnv, Vec<Diagnostic>) {
    let mut env = TypeEnv::new();
    let mut diagnostics = Vec::new();

    // Register builtins
    for builtin in register_builtins() {
        env.builtins.insert(builtin.name.clone(), builtin);
    }

    // Pass 1a: register all type names as stubs (across all systems)
    for item in &program.items {
        if let TopLevel::System(system) = &item.node {
            pass_1a(&system.decls, &mut env, &mut diagnostics);
        }
    }

    // Register built-in types AFTER pass_1a so user-defined types take
    // precedence (e.g., `enum Duration { ... }` overrides the builtin).
    register_builtin_types(&mut env);

    // Pass 1b: resolve all signatures
    for item in &program.items {
        if let TopLevel::System(system) = &item.node {
            pass_1b(&system.decls, &mut env, &mut diagnostics);
        }
    }

    (env, diagnostics)
}

/// Pass 1a: Register type names (enums, structs, entities) as stubs.
fn pass_1a(
    decls: &[ttrpg_ast::Spanned<DeclKind>],
    env: &mut TypeEnv,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for decl in decls {
        let (name, stub) = match &decl.node {
            DeclKind::Enum(e) => (
                e.name.clone(),
                DeclInfo::Enum(EnumInfo {
                    name: e.name.clone(),
                    ordered: e.ordered,
                    variants: Vec::new(),
                }),
            ),
            DeclKind::Struct(s) => (
                s.name.clone(),
                DeclInfo::Struct(StructInfo {
                    name: s.name.clone(),
                    fields: Vec::new(),
                }),
            ),
            DeclKind::Entity(e) => (
                e.name.clone(),
                DeclInfo::Entity(EntityInfo {
                    name: e.name.clone(),
                    fields: Vec::new(),
                    optional_groups: Vec::new(),
                }),
            ),
            _ => continue,
        };

        // Reject reserved `__` prefix on type declarations
        if check_reserved_prefix(&name, decl.span, diagnostics) {
            continue;
        }

        // TurnBudget must be a struct — the built-in turn binding and
        // types_compatible only handle struct TurnBudget.
        if name == "TurnBudget" && !matches!(&stub, DeclInfo::Struct(_)) {
            diagnostics.push(Diagnostic::error(
                "`TurnBudget` must be defined as a struct",
                decl.span,
            ));
            continue;
        }

        // Duration must be an enum — rulesets define duration variants
        // as enum members (e.g., `rounds(count: int)`, `indefinite`).
        if name == "Duration" && !matches!(&stub, DeclInfo::Enum(_)) {
            diagnostics.push(Diagnostic::error(
                "`Duration` must be defined as an enum",
                decl.span,
            ));
            continue;
        }

        use std::collections::hash_map::Entry;
        match env.types.entry(name) {
            Entry::Occupied(e) => {
                diagnostics.push(Diagnostic::error(
                    format!("duplicate type declaration `{}`", e.key()),
                    decl.span,
                ));
            }
            Entry::Vacant(e) => {
                e.insert(stub);
            }
        }
    }
}

/// Pass 1b: Resolve all signatures — field types, param types, return types.
fn pass_1b(
    decls: &[ttrpg_ast::Spanned<DeclKind>],
    env: &mut TypeEnv,
    diagnostics: &mut Vec<Diagnostic>,
) {
    // Track which type names we've already processed so that duplicate
    // declarations (already reported in pass_1a) don't overwrite the
    // first valid entry's fields/variants.
    let mut processed_types = HashSet::new();
    for decl in decls {
        match &decl.node {
            DeclKind::Enum(e) => {
                if processed_types.insert(e.name.clone()) {
                    collect_enum(e, env, diagnostics);
                }
            }
            DeclKind::Struct(s) => {
                if processed_types.insert(s.name.clone()) {
                    collect_struct(s, env, diagnostics);
                }
            }
            DeclKind::Entity(e) => {
                if processed_types.insert(e.name.clone()) {
                    collect_entity(e, env, diagnostics);
                }
            }
            DeclKind::Derive(f) => {
                if !f.synthetic && check_reserved_prefix(&f.name, decl.span, diagnostics) {
                    continue;
                }
                collect_fn(
                    &f.name,
                    FnKind::Derive,
                    &f.params,
                    Some(&f.return_type),
                    None,
                    env,
                    diagnostics,
                    decl.span,
                );
            }
            DeclKind::Mechanic(f) => {
                if !f.synthetic && check_reserved_prefix(&f.name, decl.span, diagnostics) {
                    continue;
                }
                collect_fn(
                    &f.name,
                    FnKind::Mechanic,
                    &f.params,
                    Some(&f.return_type),
                    None,
                    env,
                    diagnostics,
                    decl.span,
                );
            }
            DeclKind::Action(a) => {
                if !a.synthetic && check_reserved_prefix(&a.name, decl.span, diagnostics) {
                    continue;
                }
                collect_action(a, env, diagnostics, decl.span);
            }
            DeclKind::Reaction(r) => {
                if check_reserved_prefix(&r.name, decl.span, diagnostics) {
                    continue;
                }
                collect_reaction(r, env, diagnostics, decl.span);
            }
            DeclKind::Condition(c) => {
                if check_reserved_prefix(&c.name, decl.span, diagnostics) {
                    continue;
                }
                collect_condition(c, env, diagnostics, decl.span);
            }
            DeclKind::Prompt(p) => {
                if check_reserved_prefix(&p.name, decl.span, diagnostics) {
                    continue;
                }
                collect_prompt(p, env, diagnostics, decl.span);
            }
            DeclKind::Event(e) => {
                if check_reserved_prefix(&e.name, decl.span, diagnostics) {
                    continue;
                }
                collect_event(e, env, diagnostics, decl.span);
            }
            DeclKind::Option(o) => {
                if check_reserved_prefix(&o.name, decl.span, diagnostics) {
                    continue;
                }
                collect_option(o, env, diagnostics, decl.span);
            }
            DeclKind::Hook(h) => {
                if check_reserved_prefix(&h.name, decl.span, diagnostics) {
                    continue;
                }
                collect_hook(h, env, diagnostics, decl.span);
            }
            DeclKind::Move(_) => {
                diagnostics.push(Diagnostic::error(
                    "move declarations must be lowered before type-checking",
                    decl.span,
                ));
            }
        }
    }
}

fn collect_enum(e: &EnumDecl, env: &mut TypeEnv, diagnostics: &mut Vec<Diagnostic>) {
    let mut variants = Vec::new();
    let mut seen_variants = HashSet::new();

    for v in &e.variants {
        // Check for duplicate variant names within this enum
        if !seen_variants.insert(v.name.clone()) {
            diagnostics.push(Diagnostic::error(
                format!("duplicate variant `{}` in enum `{}`", v.name, e.name),
                v.span,
            ));
            continue;
        }

        let fields = match &v.fields {
            Some(field_entries) => {
                let mut seen_fields = HashSet::new();
                field_entries
                    .iter()
                    .filter_map(|f| {
                        env.validate_type_names(&f.ty, diagnostics);
                        if !seen_fields.insert(f.name.clone()) {
                            diagnostics.push(Diagnostic::error(
                                format!(
                                    "duplicate field `{}` in variant `{}`",
                                    f.name, v.name
                                ),
                                f.span,
                            ));
                            return None;
                        }
                        Some((f.name.clone(), env.resolve_type(&f.ty)))
                    })
                    .collect()
            }
            None => Vec::new(),
        };

        // Register variant → enum mapping
        if let Some(existing) = env.variant_to_enum.get(&v.name) {
            diagnostics.push(Diagnostic::error(
                format!(
                    "variant `{}` already defined in enum `{}`",
                    v.name, existing
                ),
                v.span,
            ));
        } else {
            env.variant_to_enum.insert(v.name.clone(), e.name.clone());
        }

        // Warn if variant name shadows a function
        if env.functions.contains_key(&v.name) || env.builtins.contains_key(&v.name) {
            diagnostics.push(Diagnostic::warning(
                format!(
                    "enum variant `{}` shadows function with the same name; the function will be uncallable in bare form",
                    v.name
                ),
                v.span,
            ));
        }

        variants.push(VariantInfo {
            name: v.name.clone(),
            fields,
        });
    }

    // Update the stub with full variant info
    if let Some(DeclInfo::Enum(info)) = env.types.get_mut(&e.name) {
        info.variants = variants;
    }
}

fn collect_struct(s: &StructDecl, env: &mut TypeEnv, diagnostics: &mut Vec<Diagnostic>) {
    let mut seen = HashSet::new();
    let fields: Vec<FieldInfo> = s
        .fields
        .iter()
        .filter_map(|f| {
            env.validate_type_names(&f.ty, diagnostics);
            if !seen.insert(f.name.clone()) {
                diagnostics.push(Diagnostic::error(
                    format!("duplicate field `{}` in struct `{}`", f.name, s.name),
                    f.span,
                ));
                return None;
            }
            Some(FieldInfo {
                name: f.name.clone(),
                ty: env.resolve_type(&f.ty),
                has_default: f.default.is_some(),
            })
        })
        .collect();

    if let Some(DeclInfo::Struct(info)) = env.types.get_mut(&s.name) {
        info.fields = fields;
    }
}

fn collect_entity(e: &EntityDecl, env: &mut TypeEnv, diagnostics: &mut Vec<Diagnostic>) {
    let mut seen = HashSet::new();
    let fields: Vec<FieldInfo> = e
        .fields
        .iter()
        .filter_map(|f| {
            env.validate_type_names(&f.ty, diagnostics);
            if !seen.insert(f.name.clone()) {
                diagnostics.push(Diagnostic::error(
                    format!("duplicate field `{}` in entity `{}`", f.name, e.name),
                    f.span,
                ));
                return None;
            }
            Some(FieldInfo {
                name: f.name.clone(),
                ty: env.resolve_type(&f.ty),
                has_default: f.default.is_some(),
            })
        })
        .collect();

    // Collect optional groups
    let mut seen_groups = HashSet::new();
    let optional_groups: Vec<OptionalGroupInfo> = e
        .optional_groups
        .iter()
        .filter_map(|g| {
            if seen.contains(&g.name) {
                diagnostics.push(Diagnostic::error(
                    format!(
                        "optional group `{}` conflicts with field of the same name in entity `{}`",
                        g.name, e.name
                    ),
                    g.span,
                ));
                return None;
            }
            if !seen_groups.insert(g.name.clone()) {
                diagnostics.push(Diagnostic::error(
                    format!(
                        "duplicate optional group `{}` in entity `{}`",
                        g.name, e.name
                    ),
                    g.span,
                ));
                return None;
            }
            let mut seen_fields = HashSet::new();
            let group_fields: Vec<FieldInfo> = g
                .fields
                .iter()
                .filter_map(|f| {
                    env.validate_type_names(&f.ty, diagnostics);
                    if !seen_fields.insert(f.name.clone()) {
                        diagnostics.push(Diagnostic::error(
                            format!(
                                "duplicate field `{}` in optional group `{}`",
                                f.name, g.name
                            ),
                            f.span,
                        ));
                        return None;
                    }
                    Some(FieldInfo {
                        name: f.name.clone(),
                        ty: env.resolve_type(&f.ty),
                        has_default: f.default.is_some(),
                    })
                })
                .collect();
            Some(OptionalGroupInfo {
                name: g.name.clone(),
                fields: group_fields,
            })
        })
        .collect();

    if let Some(DeclInfo::Entity(info)) = env.types.get_mut(&e.name) {
        info.fields = fields;
        info.optional_groups = optional_groups;
    }
}

#[allow(clippy::too_many_arguments)]
fn collect_fn(
    name: &str,
    kind: FnKind,
    params: &[Param],
    return_type: Option<&ttrpg_ast::Spanned<TypeExpr>>,
    receiver: Option<ParamInfo>,
    env: &mut TypeEnv,
    diagnostics: &mut Vec<Diagnostic>,
    span: Span,
) {
    if env.functions.contains_key(name) {
        diagnostics.push(Diagnostic::error(
            format!("duplicate function declaration `{}`", name),
            span,
        ));
        return;
    }

    // Warn if function name collides with an enum variant
    if env.variant_to_enum.contains_key(name) {
        diagnostics.push(Diagnostic::warning(
            format!(
                "function `{}` has the same name as an enum variant; the function will be uncallable in bare form",
                name
            ),
            span,
        ));
    }

    // `result` is reserved in derive/mechanic signatures because modify
    // clauses bind it as the implicit return-value override.
    if kind == FnKind::Derive || kind == FnKind::Mechanic {
        for p in params {
            if p.name == "result" {
                diagnostics.push(Diagnostic::error(
                    format!(
                        "`result` is reserved and cannot be used as a parameter name in `{}`",
                        name
                    ),
                    p.span,
                ));
            }
        }
    }

    let mut seen_params = HashSet::new();
    let param_infos: Vec<ParamInfo> = params
        .iter()
        .map(|p| {
            env.validate_type_names(&p.ty, diagnostics);
            if !seen_params.insert(p.name.clone()) {
                diagnostics.push(Diagnostic::error(
                    format!("duplicate parameter `{}` in function `{}`", p.name, name),
                    p.span,
                ));
            }
            ParamInfo {
                name: p.name.clone(),
                ty: env.resolve_type(&p.ty),
                has_default: p.default.is_some(),
                with_groups: p.with_groups.clone(),
            }
        })
        .collect();

    let ret_ty = return_type
        .map(|rt| {
            env.validate_type_names(rt, diagnostics);
            env.resolve_type(rt)
        })
        .unwrap_or(Ty::Unit);

    env.functions.insert(
        name.to_string(),
        FnInfo {
            name: name.to_string(),
            kind,
            params: param_infos,
            return_type: ret_ty,
            receiver,
        },
    );
}

/// Actions are intentionally stored in `env.functions` and callable as regular
/// functions. Method-call syntax (`receiver.action()`) is not yet implemented;
/// when it is, a `FnKind` gate may be added to restrict call sites.
fn collect_action(
    a: &ActionDecl,
    env: &mut TypeEnv,
    diagnostics: &mut Vec<Diagnostic>,
    span: Span,
) {
    if let Some(ref cost) = a.cost {
        validate_cost_tokens(cost, diagnostics);
    }

    env.validate_type_names(&a.receiver_type, diagnostics);
    let recv_ty = env.resolve_type(&a.receiver_type);
    if !recv_ty.is_error() && !recv_ty.is_entity() {
        diagnostics.push(Diagnostic::error(
            format!(
                "action `{}` receiver type must be an entity, found {}",
                a.name,
                recv_ty.display()
            ),
            a.receiver_type.span,
        ));
    }

    // Detect implicit name shadowing
    if a.receiver_name == "turn" {
        diagnostics.push(Diagnostic::error(
            format!(
                "action `{}` receiver `turn` shadows the implicit turn budget binding",
                a.name
            ),
            span,
        ));
    }
    for p in &a.params {
        if p.name == "turn" {
            diagnostics.push(Diagnostic::error(
                format!(
                    "action `{}` parameter `turn` shadows the implicit turn budget binding",
                    a.name
                ),
                p.span,
            ));
        }
        if p.name == a.receiver_name {
            diagnostics.push(Diagnostic::error(
                format!(
                    "action `{}` parameter `{}` shadows the receiver binding",
                    a.name, p.name
                ),
                p.span,
            ));
        }
    }

    let receiver = ParamInfo {
        name: a.receiver_name.clone(),
        ty: env.resolve_type(&a.receiver_type),
        has_default: false,
        with_groups: a.receiver_with_groups.clone(),
    };

    collect_fn(
        &a.name,
        FnKind::Action,
        &a.params,
        None,
        Some(receiver),
        env,
        diagnostics,
        span,
    );
}

/// Reactions are intentionally stored in `env.functions` and callable as regular
/// functions. See [`collect_action`] for rationale.
fn collect_reaction(
    r: &ReactionDecl,
    env: &mut TypeEnv,
    diagnostics: &mut Vec<Diagnostic>,
    span: Span,
) {
    if let Some(ref cost) = r.cost {
        validate_cost_tokens(cost, diagnostics);
    }

    env.validate_type_names(&r.receiver_type, diagnostics);
    let recv_ty = env.resolve_type(&r.receiver_type);
    if !recv_ty.is_error() && !recv_ty.is_entity() {
        diagnostics.push(Diagnostic::error(
            format!(
                "reaction `{}` receiver type must be an entity, found {}",
                r.name,
                recv_ty.display()
            ),
            r.receiver_type.span,
        ));
    }

    // Detect implicit name shadowing
    if r.receiver_name == "trigger" {
        diagnostics.push(Diagnostic::error(
            format!(
                "reaction `{}` receiver `trigger` shadows the implicit trigger binding",
                r.name
            ),
            span,
        ));
    }
    if r.receiver_name == "turn" {
        diagnostics.push(Diagnostic::error(
            format!(
                "reaction `{}` receiver `turn` shadows the implicit turn budget binding",
                r.name
            ),
            span,
        ));
    }

    let receiver = ParamInfo {
        name: r.receiver_name.clone(),
        ty: env.resolve_type(&r.receiver_type),
        has_default: false,
        with_groups: r.receiver_with_groups.clone(),
    };

    collect_fn(
        &r.name,
        FnKind::Reaction,
        &[],
        None,
        Some(receiver),
        env,
        diagnostics,
        span,
    );
}

fn collect_hook(
    h: &HookDecl,
    env: &mut TypeEnv,
    diagnostics: &mut Vec<Diagnostic>,
    span: Span,
) {
    env.validate_type_names(&h.receiver_type, diagnostics);
    let recv_ty = env.resolve_type(&h.receiver_type);
    if !recv_ty.is_error() && !recv_ty.is_entity() {
        diagnostics.push(Diagnostic::error(
            format!(
                "hook `{}` receiver type must be an entity, found {}",
                h.name,
                recv_ty.display()
            ),
            h.receiver_type.span,
        ));
    }

    // Detect implicit name shadowing
    if h.receiver_name == "trigger" {
        diagnostics.push(Diagnostic::error(
            format!(
                "hook `{}` receiver `trigger` shadows the implicit trigger binding",
                h.name
            ),
            span,
        ));
    }
    if h.receiver_name == "turn" {
        diagnostics.push(Diagnostic::error(
            format!(
                "hook `{}` receiver `turn` shadows the implicit turn budget binding",
                h.name
            ),
            span,
        ));
    }

    let receiver = ParamInfo {
        name: h.receiver_name.clone(),
        ty: env.resolve_type(&h.receiver_type),
        has_default: false,
        with_groups: h.receiver_with_groups.clone(),
    };

    collect_fn(
        &h.name,
        FnKind::Hook,
        &[],
        None,
        Some(receiver),
        env,
        diagnostics,
        span,
    );
}

fn collect_condition(
    c: &ConditionDecl,
    env: &mut TypeEnv,
    diagnostics: &mut Vec<Diagnostic>,
    span: Span,
) {
    let name = &c.name;
    if env.conditions.contains_key(name) {
        diagnostics.push(Diagnostic::error(
            format!("duplicate condition declaration `{}`", name),
            span,
        ));
        return;
    }

    // Validate and resolve condition params
    let mut param_infos = Vec::new();
    let mut seen_params = HashSet::new();
    for param in &c.params {
        env.validate_type_names(&param.ty, diagnostics);
        if !seen_params.insert(param.name.clone()) {
            diagnostics.push(Diagnostic::error(
                format!(
                    "duplicate parameter `{}` in condition `{}`",
                    param.name, name
                ),
                param.span,
            ));
        }
        let ty = env.resolve_type(&param.ty);
        param_infos.push(ParamInfo {
            name: param.name.clone(),
            ty,
            has_default: param.default.is_some(),
            with_groups: param.with_groups.clone(),
        });
    }

    env.validate_type_names(&c.receiver_type, diagnostics);
    let recv_ty = env.resolve_type(&c.receiver_type);
    if !recv_ty.is_error() && !recv_ty.is_entity() {
        diagnostics.push(Diagnostic::error(
            format!(
                "condition `{}` receiver type must be an entity, found {}",
                name,
                recv_ty.display()
            ),
            c.receiver_type.span,
        ));
    }
    env.conditions.insert(
        name.clone(),
        ConditionInfo {
            name: name.clone(),
            params: param_infos,
            receiver_name: c.receiver_name.clone(),
            receiver_type: env.resolve_type(&c.receiver_type),
        },
    );
}

fn collect_prompt(
    p: &PromptDecl,
    env: &mut TypeEnv,
    diagnostics: &mut Vec<Diagnostic>,
    span: Span,
) {
    collect_fn(
        &p.name,
        FnKind::Prompt,
        &p.params,
        Some(&p.return_type),
        None,
        env,
        diagnostics,
        span,
    );
}

fn collect_event(
    e: &EventDecl,
    env: &mut TypeEnv,
    diagnostics: &mut Vec<Diagnostic>,
    span: Span,
) {
    if env.events.contains_key(&e.name) {
        diagnostics.push(Diagnostic::error(
            format!("duplicate event declaration `{}`", e.name),
            span,
        ));
        return;
    }

    let mut seen_params = HashSet::new();
    let params: Vec<ParamInfo> = e
        .params
        .iter()
        .map(|p| {
            env.validate_type_names(&p.ty, diagnostics);
            if !seen_params.insert(p.name.clone()) {
                diagnostics.push(Diagnostic::error(
                    format!("duplicate parameter `{}` in event `{}`", p.name, e.name),
                    p.span,
                ));
            }
            ParamInfo {
                name: p.name.clone(),
                ty: env.resolve_type(&p.ty),
                has_default: p.default.is_some(),
                with_groups: p.with_groups.clone(),
            }
        })
        .collect();

    let mut seen_fields = HashSet::new();
    let fields: Vec<(String, Ty)> = e
        .fields
        .iter()
        .filter_map(|f| {
            env.validate_type_names(&f.ty, diagnostics);
            if seen_params.contains(&f.name) {
                diagnostics.push(Diagnostic::error(
                    format!(
                        "event `{}` field `{}` collides with a parameter of the same name",
                        e.name, f.name
                    ),
                    f.span,
                ));
                return None;
            }
            if !seen_fields.insert(f.name.clone()) {
                diagnostics.push(Diagnostic::error(
                    format!("duplicate field `{}` in event `{}`", f.name, e.name),
                    f.span,
                ));
                return None;
            }
            Some((f.name.clone(), env.resolve_type(&f.ty)))
        })
        .collect();

    env.events.insert(
        e.name.clone(),
        EventInfo {
            name: e.name.clone(),
            params,
            fields,
        },
    );
}

fn collect_option(
    o: &OptionDecl,
    env: &mut TypeEnv,
    diagnostics: &mut Vec<Diagnostic>,
    span: Span,
) {
    if !env.options.insert(o.name.clone()) {
        diagnostics.push(Diagnostic::error(
            format!("duplicate option declaration `{}`", o.name),
            span,
        ));
    }

    if o.extends.is_some() {
        diagnostics.push(Diagnostic::warning(
            "option `extends` is not yet validated (requires module resolution)".to_string(),
            span,
        ));
    }
}

/// Register built-in type declarations that exist even without user definitions.
fn register_builtin_types(env: &mut TypeEnv) {
    // Duration enum (built-in fallback).
    // Rulesets are expected to define their own `enum Duration { ... }` with
    // system-appropriate variants. This minimal fallback provides only
    // `indefinite` — the one truly universal duration concept.
    if !env.types.contains_key("Duration") {
        let variants = vec![VariantInfo {
            name: "indefinite".into(),
            fields: vec![],
        }];
        for v in &variants {
            env.variant_to_enum
                .entry(v.name.clone())
                .or_insert_with(|| "Duration".into());
        }
        env.types.insert(
            "Duration".into(),
            DeclInfo::Enum(EnumInfo {
                name: "Duration".into(),
                ordered: false,
                variants,
            }),
        );
    }
}

fn validate_cost_tokens(cost: &CostClause, diagnostics: &mut Vec<Diagnostic>) {
    for token in &cost.tokens {
        if !VALID_COST_TOKENS.contains(&token.node.as_str()) {
            diagnostics.push(Diagnostic::error(
                format!(
                    "invalid cost token `{}`; expected one of: action, bonus_action, reaction",
                    token.node
                ),
                token.span,
            ));
        }
    }
}
