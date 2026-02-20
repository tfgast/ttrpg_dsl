use ttrpg_ast::ast::*;
use ttrpg_ast::diagnostic::Diagnostic;
use ttrpg_ast::Span;

use crate::builtins::register_builtins;
use crate::env::*;
use crate::ty::Ty;

const VALID_COST_TOKENS: &[&str] = &["action", "bonus_action", "reaction"];

/// Pass 1: Collect all top-level declarations into a TypeEnv.
pub fn collect(program: &Program) -> (TypeEnv, Vec<Diagnostic>) {
    let mut env = TypeEnv::new();
    let mut diagnostics = Vec::new();

    // Register builtins
    for builtin in register_builtins() {
        env.builtins.insert(builtin.name.clone(), builtin);
    }

    // Register built-in types (Duration enum, RollResult fields, etc.)
    register_builtin_types(&mut env);

    for item in &program.items {
        if let TopLevel::System(system) = &item.node {
            // Pass 1a: register all type names as stubs
            pass_1a(&system.decls, &mut env, &mut diagnostics);
            // Pass 1b: resolve all signatures
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
                }),
            ),
            _ => continue,
        };

        if env.types.contains_key(&name) {
            diagnostics.push(Diagnostic::error(
                format!("duplicate type declaration `{}`", name),
                decl.span,
            ));
        } else {
            env.types.insert(name, stub);
        }
    }
}

/// Pass 1b: Resolve all signatures — field types, param types, return types.
fn pass_1b(
    decls: &[ttrpg_ast::Spanned<DeclKind>],
    env: &mut TypeEnv,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for decl in decls {
        match &decl.node {
            DeclKind::Enum(e) => collect_enum(e, env, diagnostics),
            DeclKind::Struct(s) => collect_struct(s, env, diagnostics),
            DeclKind::Entity(e) => collect_entity(e, env, diagnostics),
            DeclKind::Derive(f) => collect_fn(
                &f.name,
                FnKind::Derive,
                &f.params,
                Some(&f.return_type),
                None,
                env,
                diagnostics,
                decl.span,
            ),
            DeclKind::Mechanic(f) => collect_fn(
                &f.name,
                FnKind::Mechanic,
                &f.params,
                Some(&f.return_type),
                None,
                env,
                diagnostics,
                decl.span,
            ),
            DeclKind::Action(a) => collect_action(a, env, diagnostics, decl.span),
            DeclKind::Reaction(r) => collect_reaction(r, env, diagnostics, decl.span),
            DeclKind::Condition(c) => collect_condition(c, env, diagnostics, decl.span),
            DeclKind::Prompt(p) => collect_prompt(p, env, diagnostics, decl.span),
            DeclKind::Event(e) => collect_event(e, env, diagnostics, decl.span),
            DeclKind::Option(_) | DeclKind::Move(_) => {
                // Options and moves: skip for now (v0 doesn't deeply check these)
            }
        }
    }
}

fn collect_enum(e: &EnumDecl, env: &mut TypeEnv, diagnostics: &mut Vec<Diagnostic>) {
    let mut variants = Vec::new();

    for v in &e.variants {
        let fields = match &v.fields {
            Some(field_entries) => field_entries
                .iter()
                .map(|f| {
                    env.validate_type_names(&f.ty, diagnostics);
                    (f.name.clone(), env.resolve_type(&f.ty))
                })
                .collect(),
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
    let fields: Vec<(String, Ty)> = s
        .fields
        .iter()
        .map(|f| {
            env.validate_type_names(&f.ty, diagnostics);
            (f.name.clone(), env.resolve_type(&f.ty))
        })
        .collect();

    if let Some(DeclInfo::Struct(info)) = env.types.get_mut(&s.name) {
        info.fields = fields;
    }
}

fn collect_entity(e: &EntityDecl, env: &mut TypeEnv, diagnostics: &mut Vec<Diagnostic>) {
    let fields: Vec<(String, Ty)> = e
        .fields
        .iter()
        .map(|f| {
            env.validate_type_names(&f.ty, diagnostics);
            (f.name.clone(), env.resolve_type(&f.ty))
        })
        .collect();

    if let Some(DeclInfo::Entity(info)) = env.types.get_mut(&e.name) {
        info.fields = fields;
    }
}

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

    let param_infos: Vec<ParamInfo> = params
        .iter()
        .map(|p| {
            env.validate_type_names(&p.ty, diagnostics);
            ParamInfo {
                name: p.name.clone(),
                ty: env.resolve_type(&p.ty),
                has_default: p.default.is_some(),
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
    let receiver = ParamInfo {
        name: a.receiver_name.clone(),
        ty: env.resolve_type(&a.receiver_type),
        has_default: false,
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
    let receiver = ParamInfo {
        name: r.receiver_name.clone(),
        ty: env.resolve_type(&r.receiver_type),
        has_default: false,
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

    env.validate_type_names(&c.receiver_type, diagnostics);
    env.conditions.insert(
        name.clone(),
        ConditionInfo {
            name: name.clone(),
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

    let params: Vec<ParamInfo> = e
        .params
        .iter()
        .map(|p| {
            env.validate_type_names(&p.ty, diagnostics);
            ParamInfo {
                name: p.name.clone(),
                ty: env.resolve_type(&p.ty),
                has_default: p.default.is_some(),
            }
        })
        .collect();

    let fields: Vec<(String, Ty)> = e
        .fields
        .iter()
        .map(|f| {
            env.validate_type_names(&f.ty, diagnostics);
            (f.name.clone(), env.resolve_type(&f.ty))
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

/// Register built-in type declarations that exist even without user definitions.
fn register_builtin_types(env: &mut TypeEnv) {
    // Duration enum (built-in)
    if !env.types.contains_key("Duration") {
        let variants = vec![
            VariantInfo {
                name: "end_of_turn".into(),
                fields: vec![],
            },
            VariantInfo {
                name: "start_of_next_turn".into(),
                fields: vec![],
            },
            VariantInfo {
                name: "rounds".into(),
                fields: vec![("count".into(), Ty::Int)],
            },
            VariantInfo {
                name: "minutes".into(),
                fields: vec![("count".into(), Ty::Int)],
            },
            VariantInfo {
                name: "indefinite".into(),
                fields: vec![],
            },
        ];
        for v in &variants {
            env.variant_to_enum
                .entry(v.name.clone())
                .or_insert_with(|| "Duration".into());
        }
        env.types.insert(
            "Duration".into(),
            DeclInfo::Enum(EnumInfo {
                name: "Duration".into(),
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
