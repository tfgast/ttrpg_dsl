use std::collections::HashSet;

use ttrpg_ast::ast::*;
use ttrpg_ast::diagnostic::Diagnostic;
use ttrpg_ast::module::ModuleMap;
use ttrpg_ast::Name;
use ttrpg_ast::Span;

use crate::builtins::register_builtins;
use crate::env::*;
use crate::ty::Ty;

/// Check if a name uses the reserved `__` prefix. Returns `true` if the name
/// is reserved (and emits a diagnostic).
fn check_reserved_prefix(name: &str, span: Span, diagnostics: &mut Vec<Diagnostic>) -> bool {
    if name.starts_with("__") {
        diagnostics.push(Diagnostic::error(
            format!(
                "names starting with `__` are reserved for internal use: `{}`",
                name
            ),
            span,
        ));
        true
    } else {
        false
    }
}

/// Pass 1: Collect all top-level declarations into a TypeEnv.
pub fn collect(program: &Program) -> (TypeEnv, Vec<Diagnostic>) {
    collect_inner(program, None)
}

/// Pass 1 with module awareness: populate ownership maps and visibility.
pub fn collect_with_modules(program: &Program, modules: &ModuleMap) -> (TypeEnv, Vec<Diagnostic>) {
    collect_inner(program, Some(modules))
}

fn collect_inner(program: &Program, modules: Option<&ModuleMap>) -> (TypeEnv, Vec<Diagnostic>) {
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
    // `processed_types` is shared across all systems so that a duplicate type
    // declaration in a later system doesn't overwrite the first definition.
    let mut processed_types: HashSet<Name> = HashSet::new();
    for item in &program.items {
        if let TopLevel::System(system) = &item.node {
            pass_1b(
                &system.decls,
                &mut env,
                &mut diagnostics,
                &mut processed_types,
            );
        }
    }

    // Validate cost clauses after all types are collected so TurnBudget-driven
    // custom tokens are resolved correctly regardless of declaration order.
    validate_all_cost_tokens(program, &env, &mut diagnostics);

    // Validate option extends chains (circular detection)
    validate_option_extends(program, &env, &mut diagnostics);

    // If module map provided, populate ownership and visibility
    if let Some(modules) = modules {
        populate_module_metadata(&mut env, modules, &mut diagnostics);
    }

    (env, diagnostics)
}

/// Populate ownership maps, visibility, and aliases from the ModuleMap.
fn populate_module_metadata(
    env: &mut TypeEnv,
    modules: &ModuleMap,
    diagnostics: &mut Vec<Diagnostic>,
) {
    // Populate ownership maps from ModuleMap system info
    for (sys_name, sys_info) in &modules.systems {
        for name in &sys_info.groups {
            env.group_owner.insert(name.clone(), sys_name.clone());
        }
        for name in &sys_info.types {
            env.type_owner.insert(name.clone(), sys_name.clone());
        }
        for name in &sys_info.functions {
            env.function_owner.insert(name.clone(), sys_name.clone());
        }
        for name in &sys_info.conditions {
            env.condition_owner.insert(name.clone(), sys_name.clone());
        }
        for name in &sys_info.events {
            env.event_owner.insert(name.clone(), sys_name.clone());
        }
        for name in &sys_info.options {
            env.option_owner.insert(name.clone(), sys_name.clone());
        }
        for name in &sys_info.tags {
            env.tag_owner.insert(name.clone(), sys_name.clone());
        }
    }

    // Compute per-system visibility (own + imported)
    for (sys_name, sys_info) in &modules.systems {
        let mut vis = VisibleNames::default();

        // Own declarations
        vis.groups.extend(sys_info.groups.iter().cloned());
        vis.types.extend(sys_info.types.iter().cloned());
        vis.functions.extend(sys_info.functions.iter().cloned());
        vis.conditions.extend(sys_info.conditions.iter().cloned());
        vis.events.extend(sys_info.events.iter().cloned());
        vis.variants.extend(sys_info.variants.iter().cloned());
        vis.options.extend(sys_info.options.iter().cloned());
        vis.tags.extend(sys_info.tags.iter().cloned());

        // Imported declarations
        for import in &sys_info.imports {
            if let Some(imported_sys) = modules.systems.get(&import.system_name) {
                vis.groups.extend(imported_sys.groups.iter().cloned());
                vis.types.extend(imported_sys.types.iter().cloned());
                vis.functions.extend(imported_sys.functions.iter().cloned());
                vis.conditions
                    .extend(imported_sys.conditions.iter().cloned());
                vis.events.extend(imported_sys.events.iter().cloned());
                vis.variants.extend(imported_sys.variants.iter().cloned());
                vis.options.extend(imported_sys.options.iter().cloned());
                vis.tags.extend(imported_sys.tags.iter().cloned());
            }
        }

        env.system_visibility.insert(sys_name.clone(), vis);
    }

    // Compute per-system aliases
    for (sys_name, sys_info) in &modules.systems {
        let mut aliases = std::collections::HashMap::new();
        for import in &sys_info.imports {
            if let Some(ref alias) = import.alias {
                aliases.insert(alias.clone(), import.system_name.clone());
            }
        }
        if !aliases.is_empty() {
            env.system_aliases.insert(sys_name.clone(), aliases);
        }
    }

    // Alias-vs-builtin validation (eager, declaration-site check)
    for (sys_name, aliases) in &env.system_aliases.clone() {
        for alias in aliases.keys() {
            if env.builtins.contains_key(alias) {
                diagnostics.push(Diagnostic::error(
                    format!("alias \"{}\" shadows builtin function \"{}\"", alias, alias),
                    ttrpg_ast::Span::dummy(),
                ));
            }
        }
        let _ = sys_name; // used for context if we add spans later
    }
}

/// Pass 1a: Register type names (enums, structs, entities) as stubs.
fn pass_1a(
    decls: &[ttrpg_ast::Spanned<DeclKind>],
    env: &mut TypeEnv,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for decl in decls {
        // Register tag declarations alongside type stubs
        if let DeclKind::Tag(t) = &decl.node {
            if check_reserved_prefix(&t.name, decl.span, diagnostics) {
                continue;
            }
            if !env.tags.insert(t.name.clone()) {
                diagnostics.push(Diagnostic::error(
                    format!("duplicate tag declaration `{}`", t.name),
                    decl.span,
                ));
            }
            continue;
        }

        let (name, stub) = match &decl.node {
            DeclKind::Group(_) | DeclKind::Tag(_) => continue,
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
            DeclKind::Unit(u) => (
                u.name.clone(),
                DeclInfo::Unit(UnitInfo {
                    name: u.name.clone(),
                    fields: Vec::new(),
                    suffix: None,
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
    processed_types: &mut HashSet<Name>,
) {
    // First, collect top-level group schemas so entities can reference groups
    // declared later in the same system.
    for decl in decls {
        if let DeclKind::Group(g) = &decl.node {
            if check_reserved_prefix(&g.name, decl.span, diagnostics) {
                continue;
            }
            collect_group(g, env, diagnostics, decl.span);
        }
    }

    for decl in decls {
        match &decl.node {
            DeclKind::Group(_) | DeclKind::Tag(_) => {}
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
                    &f.tags,
                    f.synthetic,
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
                    &f.tags,
                    f.synthetic,
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
            DeclKind::Table(t) => {
                if check_reserved_prefix(&t.name, decl.span, diagnostics) {
                    continue;
                }
                collect_fn(
                    &t.name,
                    FnKind::Table,
                    &t.params,
                    Some(&t.return_type),
                    None,
                    &[],
                    false,
                    env,
                    diagnostics,
                    decl.span,
                );
            }
            DeclKind::Unit(u) => {
                if processed_types.insert(u.name.clone()) {
                    collect_unit(u, env, diagnostics, decl.span);
                }
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
                        if !seen_fields.insert(f.name.clone()) {
                            diagnostics.push(Diagnostic::error(
                                format!("duplicate field `{}` in variant `{}`", f.name, v.name),
                                f.span,
                            ));
                            return None;
                        }
                        Some((
                            f.name.clone(),
                            env.resolve_type_validated(&f.ty, diagnostics),
                        ))
                    })
                    .collect()
            }
            None => Vec::new(),
        };

        // Register variant → enum mapping (multiple enums may share a variant name)
        env.variant_to_enums
            .entry(v.name.clone())
            .or_default()
            .push(e.name.clone());

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
            if !seen.insert(f.name.clone()) {
                diagnostics.push(Diagnostic::error(
                    format!("duplicate field `{}` in struct `{}`", f.name, s.name),
                    f.span,
                ));
                return None;
            }
            Some(FieldInfo {
                name: f.name.clone(),
                ty: env.resolve_type_validated(&f.ty, diagnostics),
                has_default: f.default.is_some(),
            })
        })
        .collect();

    if let Some(DeclInfo::Struct(info)) = env.types.get_mut(&s.name) {
        info.fields = fields;
    }
}

fn collect_group(g: &GroupDecl, env: &mut TypeEnv, diagnostics: &mut Vec<Diagnostic>, span: Span) {
    if env.groups.contains_key(&g.name) {
        diagnostics.push(Diagnostic::error(
            format!("duplicate group declaration `{}`", g.name),
            span,
        ));
        return;
    }

    let mut seen_fields = HashSet::new();
    let fields: Vec<FieldInfo> = g
        .fields
        .iter()
        .filter_map(|f| {
            if !seen_fields.insert(f.name.clone()) {
                diagnostics.push(Diagnostic::error(
                    format!("duplicate field `{}` in group `{}`", f.name, g.name),
                    f.span,
                ));
                return None;
            }
            Some(FieldInfo {
                name: f.name.clone(),
                ty: env.resolve_type_validated(&f.ty, diagnostics),
                has_default: f.default.is_some(),
            })
        })
        .collect();

    env.groups.insert(
        g.name.clone(),
        OptionalGroupInfo {
            name: g.name.clone(),
            fields,
            required: false,
        },
    );
}

fn collect_entity(e: &EntityDecl, env: &mut TypeEnv, diagnostics: &mut Vec<Diagnostic>) {
    let mut seen = HashSet::new();
    let fields: Vec<FieldInfo> = e
        .fields
        .iter()
        .filter_map(|f| {
            if !seen.insert(f.name.clone()) {
                diagnostics.push(Diagnostic::error(
                    format!("duplicate field `{}` in entity `{}`", f.name, e.name),
                    f.span,
                ));
                return None;
            }
            Some(FieldInfo {
                name: f.name.clone(),
                ty: env.resolve_type_validated(&f.ty, diagnostics),
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
                        "group `{}` conflicts with field of the same name in entity `{}`",
                        g.name, e.name
                    ),
                    g.span,
                ));
                return None;
            }
            if !seen_groups.insert(g.name.clone()) {
                diagnostics.push(Diagnostic::error(
                    format!("duplicate group `{}` in entity `{}`", g.name, e.name),
                    g.span,
                ));
                return None;
            }
            if g.is_external_ref {
                return match env.lookup_group(&g.name).cloned() {
                    Some(mut schema) => {
                        schema.required = g.is_required;
                        Some(schema)
                    }
                    None => {
                        let kind = if g.is_required {
                            "included"
                        } else {
                            "attached"
                        };
                        diagnostics.push(Diagnostic::error(
                            format!("unknown group `{}` {} to entity `{}`", g.name, kind, e.name),
                            g.span,
                        ));
                        None
                    }
                };
            }
            let mut seen_fields = HashSet::new();
            let group_fields: Vec<FieldInfo> = g
                .fields
                .iter()
                .filter_map(|f| {
                    if !seen_fields.insert(f.name.clone()) {
                        diagnostics.push(Diagnostic::error(
                            format!("duplicate field `{}` in group `{}`", f.name, g.name),
                            f.span,
                        ));
                        return None;
                    }
                    Some(FieldInfo {
                        name: f.name.clone(),
                        ty: env.resolve_type_validated(&f.ty, diagnostics),
                        has_default: f.default.is_some(),
                    })
                })
                .collect();
            Some(OptionalGroupInfo {
                name: g.name.clone(),
                fields: group_fields,
                required: g.is_required,
            })
        })
        .collect();

    // Build flattened field map for included groups.
    // Detect collisions: included group fields must not conflict with entity
    // own fields, group names, or fields from other included groups.
    {
        // "flat namespace": entity own field names + all group names
        let mut flat_namespace: HashSet<Name> = seen.clone();
        for g in &optional_groups {
            flat_namespace.insert(g.name.clone());
        }

        // Track which included group owns each flattened field
        let mut included_field_owner: std::collections::HashMap<Name, Name> =
            std::collections::HashMap::new();

        for g in &optional_groups {
            if !g.required {
                continue;
            }
            // Find the AST node for error spans
            let ast_span = e
                .optional_groups
                .iter()
                .find(|ag| ag.name == g.name)
                .map(|ag| ag.span)
                .unwrap_or(Span::dummy());

            for field in &g.fields {
                if flat_namespace.contains(&field.name) {
                    diagnostics.push(Diagnostic::error(
                        format!(
                            "included group `{}` field `{}` conflicts with entity `{}` field or group of the same name",
                            g.name, field.name, e.name
                        ),
                        ast_span,
                    ));
                } else if let Some(other_group) = included_field_owner.get(&field.name) {
                    diagnostics.push(Diagnostic::error(
                        format!(
                            "field `{}` defined in both included groups `{}` and `{}`",
                            field.name, other_group, g.name
                        ),
                        ast_span,
                    ));
                } else {
                    included_field_owner.insert(field.name.clone(), g.name.clone());
                    env.flattened_group_fields.insert(
                        (e.name.clone(), field.name.clone()),
                        g.name.clone(),
                    );
                }
            }
        }
    }

    if let Some(DeclInfo::Entity(info)) = env.types.get_mut(&e.name) {
        info.fields = fields;
        info.optional_groups = optional_groups;
    }
}

fn collect_unit(
    u: &ttrpg_ast::ast::UnitDecl,
    env: &mut TypeEnv,
    diagnostics: &mut Vec<Diagnostic>,
    span: Span,
) {
    // Validate: exactly one field, must be int
    if u.fields.is_empty() {
        diagnostics.push(Diagnostic::error(
            format!("unit type `{}` must have exactly one field", u.name),
            span,
        ));
        return;
    }
    if u.fields.len() > 1 {
        diagnostics.push(Diagnostic::error(
            format!(
                "unit type `{}` must have exactly one field, found {}",
                u.name,
                u.fields.len()
            ),
            span,
        ));
        return;
    }

    let field = &u.fields[0];
    let field_ty = env.resolve_type_validated(&field.ty, diagnostics);
    if field_ty != Ty::Int {
        diagnostics.push(Diagnostic::error(
            format!(
                "unit type `{}` field `{}` must be int, found {}",
                u.name, field.name, field_ty
            ),
            field.span,
        ));
    }

    // Validate suffix if present
    if let Some(ref suffix) = u.suffix {
        // Must start with a letter
        if !suffix.starts_with(|c: char| c.is_ascii_alphabetic()) {
            diagnostics.push(Diagnostic::error(
                format!("unit suffix `{}` must start with a letter", suffix),
                span,
            ));
        }

        // Check uniqueness
        if let Some(existing) = env.suffix_to_unit.get(suffix) {
            diagnostics.push(Diagnostic::error(
                format!(
                    "duplicate unit suffix `{}`; already declared by `{}`",
                    suffix, existing
                ),
                span,
            ));
        } else {
            env.suffix_to_unit.insert(suffix.clone(), u.name.clone());
        }
    }

    // Update the stub with resolved info
    let field_info = FieldInfo {
        name: field.name.clone(),
        ty: field_ty,
        has_default: field.default.is_some(),
    };
    if let Some(DeclInfo::Unit(info)) = env.types.get_mut(&u.name) {
        info.fields = vec![field_info];
        info.suffix = u.suffix.clone();
    }
}

#[allow(clippy::too_many_arguments)]
fn collect_fn(
    name: &str,
    kind: FnKind,
    params: &[Param],
    return_type: Option<&ttrpg_ast::Spanned<TypeExpr>>,
    receiver: Option<ParamInfo>,
    tags: &[Name],
    synthetic: bool,
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
    if env.variant_to_enums.contains_key(name) {
        diagnostics.push(Diagnostic::warning(
            format!(
                "function `{}` has the same name as an enum variant; the function will be uncallable in bare form",
                name
            ),
            span,
        ));
    }

    // `result` is reserved in derive/mechanic/table signatures because modify
    // clauses bind it as the implicit return-value override.
    if kind == FnKind::Derive || kind == FnKind::Mechanic || kind == FnKind::Table {
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
            if !seen_params.insert(p.name.clone()) {
                diagnostics.push(Diagnostic::error(
                    format!("duplicate parameter `{}` in function `{}`", p.name, name),
                    p.span,
                ));
            }
            ParamInfo {
                name: p.name.clone(),
                ty: env.resolve_type_validated(&p.ty, diagnostics),
                has_default: p.default.is_some(),
                with_groups: p.with_groups.iter().map(|g| g.name.clone()).collect(),
            }
        })
        .collect();

    let ret_ty = return_type
        .map(|rt| env.resolve_type_validated(rt, diagnostics))
        .unwrap_or(Ty::Unit);

    // Validate tags: each must be declared in env.tags
    let mut tag_set = HashSet::new();
    for tag in tags {
        if !env.tags.contains(tag) {
            diagnostics.push(Diagnostic::error(
                format!("undeclared tag `{}` on function `{}`", tag, name),
                span,
            ));
        }
        tag_set.insert(tag.clone());
    }

    env.functions.insert(
        Name::from(name),
        FnInfo {
            name: Name::from(name),
            kind,
            params: param_infos,
            return_type: ret_ty,
            receiver,
            tags: tag_set,
            synthetic,
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
    let recv_ty = env.resolve_type_validated(&a.receiver_type, diagnostics);
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
        with_groups: a.receiver_with_groups.iter().map(|g| g.name.clone()).collect(),
    };

    collect_fn(
        &a.name,
        FnKind::Action,
        &a.params,
        None,
        Some(receiver),
        &[],
        false,
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
    let recv_ty = env.resolve_type_validated(&r.receiver_type, diagnostics);
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
        with_groups: r.receiver_with_groups.iter().map(|g| g.name.clone()).collect(),
    };

    collect_fn(
        &r.name,
        FnKind::Reaction,
        &[],
        None,
        Some(receiver),
        &[],
        false,
        env,
        diagnostics,
        span,
    );
}

fn collect_hook(h: &HookDecl, env: &mut TypeEnv, diagnostics: &mut Vec<Diagnostic>, span: Span) {
    let recv_ty = env.resolve_type_validated(&h.receiver_type, diagnostics);
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
        with_groups: h.receiver_with_groups.iter().map(|g| g.name.clone()).collect(),
    };

    collect_fn(
        &h.name,
        FnKind::Hook,
        &[],
        None,
        Some(receiver),
        &[],
        false,
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
        if !seen_params.insert(param.name.clone()) {
            diagnostics.push(Diagnostic::error(
                format!(
                    "duplicate parameter `{}` in condition `{}`",
                    param.name, name
                ),
                param.span,
            ));
        }
        let ty = env.resolve_type_validated(&param.ty, diagnostics);
        param_infos.push(ParamInfo {
            name: param.name.clone(),
            ty,
            has_default: param.default.is_some(),
            with_groups: param.with_groups.iter().map(|g| g.name.clone()).collect(),
        });
    }

    let recv_ty = env.resolve_type_validated(&c.receiver_type, diagnostics);
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
        &[],
        false,
        env,
        diagnostics,
        span,
    );
}

fn collect_event(e: &EventDecl, env: &mut TypeEnv, diagnostics: &mut Vec<Diagnostic>, span: Span) {
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
            if !seen_params.insert(p.name.clone()) {
                diagnostics.push(Diagnostic::error(
                    format!("duplicate parameter `{}` in event `{}`", p.name, e.name),
                    p.span,
                ));
            }
            ParamInfo {
                name: p.name.clone(),
                ty: env.resolve_type_validated(&p.ty, diagnostics),
                has_default: p.default.is_some(),
                with_groups: p.with_groups.iter().map(|g| g.name.clone()).collect(),
            }
        })
        .collect();

    let mut seen_fields = HashSet::new();
    let fields: Vec<(Name, Ty)> = e
        .fields
        .iter()
        .filter_map(|f| {
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
            Some((
                f.name.clone(),
                env.resolve_type_validated(&f.ty, diagnostics),
            ))
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

    // Note: forward references are allowed — parent validation is deferred
    // to validate_option_extends() which runs after all options are collected.
}

/// Validate option extends chains after all options are collected.
/// Detects unknown parent references and circular extends (A→B→A).
pub fn validate_option_extends(
    program: &Program,
    env: &TypeEnv,
    diagnostics: &mut Vec<Diagnostic>,
) {
    use std::collections::HashMap;

    // Collect all extends relationships
    let mut extends_map: HashMap<Name, (Name, Span)> = HashMap::new();
    for item in &program.items {
        if let TopLevel::System(system) = &item.node {
            for decl in &system.decls {
                if let DeclKind::Option(o) = &decl.node {
                    if let Some(ref parent) = o.extends {
                        extends_map.insert(o.name.clone(), (parent.clone(), decl.span));
                    }
                }
            }
        }
    }

    // Check for unknown parent references
    for (child, (parent, span)) in &extends_map {
        if !env.options.contains(parent.as_str()) {
            diagnostics.push(Diagnostic::error(
                format!("option \"{}\" extends unknown option \"{}\"", child, parent),
                *span,
            ));
        }
    }

    // Check for circular extends
    for start_name in extends_map.keys() {
        let mut visited = HashSet::new();
        let mut current = start_name.clone();
        loop {
            if !visited.insert(current.clone()) {
                // Circular — build the chain for the error message
                let mut chain: Vec<String> = vec![start_name.to_string()];
                let mut c = start_name.clone();
                while let Some((parent, _)) = extends_map.get(&c) {
                    chain.push(parent.to_string());
                    if parent == start_name {
                        break;
                    }
                    c = parent.clone();
                }
                let (_, span) = &extends_map[start_name];
                diagnostics.push(Diagnostic::error(
                    format!("circular option extends: {}", chain.join(" \u{2192} ")),
                    *span,
                ));
                break;
            }
            match extends_map.get(&current) {
                Some((parent, _)) => current = parent.clone(),
                None => break,
            }
        }
    }
}

/// Register built-in type declarations that exist even without user definitions.
fn register_builtin_types(env: &mut TypeEnv) {
    // Duration enum (built-in fallback).
    // Rulesets are expected to define their own `enum Duration { ... }` with
    // system-appropriate variants. This minimal fallback provides only
    // `indefinite` — the one truly universal duration concept.
    if !env.types.contains_key("Duration") {
        let duration_name = Name::from("Duration");
        let variants = vec![VariantInfo {
            name: "indefinite".into(),
            fields: vec![],
        }];
        for v in &variants {
            let owners = env.variant_to_enums.entry(v.name.clone()).or_default();
            if !owners.iter().any(|o| o == "Duration") {
                owners.push(duration_name.clone());
            }
        }
        env.types.insert(
            duration_name.clone(),
            DeclInfo::Enum(EnumInfo {
                name: duration_name,
                ordered: false,
                variants,
            }),
        );
    }
}

fn validate_all_cost_tokens(program: &Program, env: &TypeEnv, diagnostics: &mut Vec<Diagnostic>) {
    for item in &program.items {
        if let TopLevel::System(system) = &item.node {
            for decl in &system.decls {
                match &decl.node {
                    DeclKind::Action(a) => {
                        if let Some(ref cost) = a.cost {
                            validate_cost_tokens(cost, env, diagnostics);
                        }
                    }
                    DeclKind::Reaction(r) => {
                        if let Some(ref cost) = r.cost {
                            validate_cost_tokens(cost, env, diagnostics);
                        }
                    }
                    _ => {}
                }
            }
        }
    }
}

fn validate_cost_tokens(cost: &CostClause, env: &TypeEnv, diagnostics: &mut Vec<Diagnostic>) {
    if cost.free {
        return;
    }

    let expected = env
        .valid_cost_tokens()
        .into_iter()
        .map(|n| n.to_string())
        .collect::<Vec<_>>();

    for token in &cost.tokens {
        if env.resolve_cost_token(&token.node).is_none() {
            let suffix = if expected.is_empty() {
                "no valid cost tokens are available".to_string()
            } else {
                format!("expected one of: {}", expected.join(", "))
            };
            diagnostics.push(Diagnostic::error(
                format!("invalid cost token `{}`; {}", token.node, suffix),
                token.span,
            ));
        }
    }
}
