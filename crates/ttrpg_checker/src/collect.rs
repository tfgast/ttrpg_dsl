use std::collections::HashSet;

use rustc_hash::FxHashMap;
use ttrpg_ast::Name;
use ttrpg_ast::Span;
use ttrpg_ast::ast::*;
use ttrpg_ast::diagnostic::Diagnostic;
use ttrpg_ast::module::ModuleMap;

use crate::builtins::register_builtins;
use crate::env::*;
use crate::ty::Ty;

/// Check if a name uses the reserved `__` prefix. Returns `true` if the name
/// is reserved (and emits a diagnostic).
fn check_reserved_prefix(name: &str, span: Span, diagnostics: &mut Vec<Diagnostic>) -> bool {
    if name.starts_with("__") {
        diagnostics.push(Diagnostic::error(
            format!("names starting with `__` are reserved for internal use: `{name}`"),
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

    // Collect all top-level groups across all systems BEFORE pass_1b.
    // This ensures entities can reference groups from any system via
    // `include` or `optional`, regardless of file/system ordering.
    for item in &program.items {
        if let TopLevel::System(system) = &item.node {
            collect_all_groups(&system.decls, &mut env, &mut diagnostics);
        }
    }

    // Pass 1b: resolve all signatures
    // `processed_types` is shared across all systems so that a duplicate type
    // declaration in a later system doesn't overwrite the first definition.
    let mut processed_types: HashSet<Name> = HashSet::new();
    // BudgetSpec is always the built-in definition (interpreter hard-codes
    // { actor, budget } extraction), so prevent pass_1b from overwriting it.
    processed_types.insert(Name::from("BudgetSpec"));
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

    // Validate condition extends (parent existence, receiver compat, cycles)
    validate_condition_extends(program, &env, &mut diagnostics);

    // Merge inherited state fields after extends validation
    merge_condition_state_fields(&mut env, &mut diagnostics);

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
        let mut aliases = FxHashMap::default();
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
                    format!("alias \"{alias}\" shadows builtin function \"{alias}\""),
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

        // EffectSource must be an enum (variant validation deferred to pass_1b).
        if name == "EffectSource" && !matches!(&stub, DeclInfo::Enum(_)) {
            diagnostics.push(Diagnostic::error(
                "`EffectSource` must be defined as an enum",
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
/// Collect all top-level group schemas from a system's declarations.
/// Called across all systems before pass_1b so that entities can reference
/// groups from any system via `include` or `optional`.
fn collect_all_groups(
    decls: &[ttrpg_ast::Spanned<DeclKind>],
    env: &mut TypeEnv,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for decl in decls {
        if let DeclKind::Group(g) = &decl.node {
            if check_reserved_prefix(&g.name, decl.span, diagnostics) {
                continue;
            }
            collect_group(g, env, diagnostics, decl.span);
        }
    }
}

fn pass_1b(
    decls: &[ttrpg_ast::Spanned<DeclKind>],
    env: &mut TypeEnv,
    diagnostics: &mut Vec<Diagnostic>,
    processed_types: &mut HashSet<Name>,
) {
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
            DeclKind::Function(f) => {
                if check_reserved_prefix(&f.name, decl.span, diagnostics) {
                    continue;
                }
                collect_fn(
                    &f.name,
                    FnKind::Function,
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
            DeclKind::Const(c) => {
                if check_reserved_prefix(&c.name, decl.span, diagnostics) {
                    continue;
                }
                collect_const(c, env, diagnostics, decl.span);
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

        let (fields, has_defaults) = match &v.fields {
            Some(field_entries) => {
                let mut seen_fields = HashSet::new();
                let mut fields = Vec::new();
                let mut defaults = Vec::new();
                let mut seen_required_after_default = false;
                let mut last_default_name = None;
                for f in field_entries {
                    if !seen_fields.insert(f.name.clone()) {
                        diagnostics.push(Diagnostic::error(
                            format!("duplicate field `{}` in variant `{}`", f.name, v.name),
                            f.span,
                        ));
                        continue;
                    }
                    let has_default = f.default.is_some();
                    if has_default {
                        last_default_name = Some(f.name.clone());
                    } else if last_default_name.is_some() && !seen_required_after_default {
                        seen_required_after_default = true;
                        diagnostics.push(Diagnostic::error(
                            format!(
                                "required field `{}` follows field `{}` which has a default; \
                                 fields with defaults must come last",
                                f.name,
                                last_default_name.as_ref().unwrap()
                            ),
                            f.span,
                        ));
                    }
                    fields.push((
                        f.name.clone(),
                        env.resolve_type_validated(&f.ty, diagnostics),
                    ));
                    defaults.push(has_default);
                }
                (fields, defaults)
            }
            None => (Vec::new(), Vec::new()),
        };

        // Register variant → enum mapping (multiple enums may share a variant name)
        env.variant_to_enums
            .entry(v.name.clone())
            .or_default()
            .push(e.name.clone());

        // Warn if variant name starts with lowercase (convention: PascalCase)
        if v.name
            .chars()
            .next()
            .is_some_and(|c| c.is_ascii_lowercase())
        {
            let suggestion = v
                .name
                .split('_')
                .map(|part| {
                    let mut chars = part.chars();
                    match chars.next() {
                        Some(c) => {
                            let upper: String = c.to_uppercase().collect();
                            format!("{upper}{}", chars.as_str())
                        }
                        None => String::new(),
                    }
                })
                .collect::<String>();
            diagnostics.push(Diagnostic::warning(
                format!(
                    "enum variant `{}` starts with a lowercase letter; \
                     convention is PascalCase (e.g., `{suggestion}`)",
                    v.name,
                ),
                v.span,
            ));
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
            has_defaults,
        });
    }

    // Update the stub with full variant info
    if let Some(DeclInfo::Enum(info)) = env.types.get_mut(&e.name) {
        info.variants = variants;
    }

    // EffectSource must have a plain `Unknown` variant (no fields).
    if e.name == "EffectSource"
        && let Some(DeclInfo::Enum(info)) = env.types.get(&e.name)
        && !info
            .variants
            .iter()
            .any(|v| v.name == "Unknown" && v.fields.is_empty())
    {
        // Use the first variant's span as best-effort location
        if let Some(first_variant) = e.variants.first() {
            diagnostics.push(Diagnostic::error(
                "`EffectSource` must have a plain `Unknown` variant (no fields)",
                first_variant.span,
            ));
        }
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
                restricted: f.restricted,
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
                restricted: f.restricted,
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
                restricted: f.restricted,
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
                        diagnostics.push(
                            Diagnostic::error(
                                format!(
                                    "unknown group `{}` {} to entity `{}`",
                                    g.name, kind, e.name
                                ),
                                g.span,
                            )
                            .with_help(format!("declare it with: group {} {{ ... }}", g.name)),
                        );
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
                        restricted: f.restricted,
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
                .map_or(Span::dummy(), |ag| ag.span);

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
                    env.flattened_group_fields
                        .insert((e.name.clone(), field.name.clone()), g.name.clone());
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
                format!("unit suffix `{suffix}` must start with a letter"),
                span,
            ));
        }

        // Check uniqueness
        if let Some(existing) = env.suffix_to_unit.get(suffix) {
            diagnostics.push(Diagnostic::error(
                format!("duplicate unit suffix `{suffix}`; already declared by `{existing}`"),
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
        restricted: field.restricted,
    };
    if let Some(DeclInfo::Unit(info)) = env.types.get_mut(&u.name) {
        info.fields = vec![field_info];
        info.suffix.clone_from(&u.suffix);
    }
}

fn collect_const(
    c: &ttrpg_ast::ast::ConstDecl,
    env: &mut TypeEnv,
    diagnostics: &mut Vec<Diagnostic>,
    span: Span,
) {
    // Check for name conflicts with functions
    if env.functions.contains_key(&c.name) {
        diagnostics.push(Diagnostic::error(
            format!(
                "const `{}` conflicts with existing function/derive/mechanic",
                c.name
            ),
            span,
        ));
        return;
    }

    // Check for duplicate const names
    if env.consts.contains_key(&c.name) {
        diagnostics.push(Diagnostic::error(
            format!("duplicate const declaration `{}`", c.name),
            span,
        ));
        return;
    }

    // Resolve type annotation if present; otherwise defer to check pass
    let ty = if let Some(ref ty_expr) = c.ty {
        env.resolve_type_validated(ty_expr, diagnostics)
    } else {
        Ty::Error // Will be inferred during check pass
    };

    env.consts.insert(c.name.clone(), ty);
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
            format!("duplicate function declaration `{name}`"),
            span,
        ));
        return;
    }

    // Warn if function name collides with an enum variant
    if env.variant_to_enums.contains_key(name) {
        diagnostics.push(Diagnostic::warning(
            format!(
                "function `{name}` has the same name as an enum variant; the function will be uncallable in bare form"
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
                        "`result` is reserved and cannot be used as a parameter name in `{name}`"
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
                with_groups: p
                    .with_groups
                    .groups
                    .iter()
                    .map(|g| g.name.clone())
                    .collect(),
                with_disjunctive: p.with_groups.disjunctive,
            }
        })
        .collect();

    let ret_ty = return_type.map_or(Ty::Unit, |rt| env.resolve_type_validated(rt, diagnostics));

    // Validate tags: each must be declared in env.tags
    let mut tag_set = HashSet::new();
    for tag in tags {
        if !env.tags.contains(tag) {
            diagnostics.push(
                Diagnostic::error(format!("undeclared tag `{tag}` on function `{name}`"), span)
                    .with_help(format!("declare it with: tag {tag}")),
            );
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
            trigger: None,
        },
    );
}

/// Actions are stored in `env.functions` (representative entry for name resolution)
/// and `env.action_overloads` (all overloads for type-based dispatch).
///
/// Multiple actions with the same name are allowed if they have different receiver
/// types. Duplicate receiver types for the same action name are an error.
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
        ty: recv_ty.clone(),
        has_default: false,
        with_groups: a
            .receiver_with_groups
            .groups
            .iter()
            .map(|g| g.name.clone())
            .collect(),
        with_disjunctive: a.receiver_with_groups.disjunctive,
    };

    // Check for duplicate receiver type in existing overloads
    if let Some(existing) = env.action_overloads.get(a.name.as_str()) {
        if existing
            .iter()
            .any(|fi| fi.receiver.as_ref().is_some_and(|r| r.ty == recv_ty))
        {
            diagnostics.push(Diagnostic::error(
                format!(
                    "duplicate action `{}` for receiver type {}",
                    a.name,
                    recv_ty.display()
                ),
                span,
            ));
        }

        // Check that all overloads agree on return type
        if let Some(first) = existing.first() {
            let new_return_ty = a
                .return_type
                .as_ref()
                .map_or(Ty::Unit, |rt| env.resolve_type_validated(rt, diagnostics));
            if first.return_type != new_return_ty {
                diagnostics.push(Diagnostic::error(
                    format!(
                        "action `{}` overloads must all have the same return type (expected {}, found {})",
                        a.name,
                        first.return_type.display(),
                        new_return_ty.display()
                    ),
                    span,
                ));
            }
        }

        // Check for name collision with a non-action function
        if let Some(existing_fn) = env.functions.get(a.name.as_str())
            && existing_fn.kind != FnKind::Action
        {
            diagnostics.push(Diagnostic::error(
                format!(
                    "action `{}` conflicts with existing {} of the same name",
                    a.name,
                    match existing_fn.kind {
                        FnKind::Function => "function",
                        FnKind::Derive => "derive",
                        FnKind::Mechanic => "mechanic",
                        FnKind::Table => "table",
                        _ => "declaration",
                    }
                ),
                span,
            ));
        }
    }

    // Build FnInfo for this overload
    let mut seen_params = HashSet::new();
    let param_infos: Vec<ParamInfo> = a
        .params
        .iter()
        .map(|p| {
            if !seen_params.insert(p.name.clone()) {
                diagnostics.push(Diagnostic::error(
                    format!("duplicate parameter `{}` in action `{}`", p.name, a.name),
                    p.span,
                ));
            }
            ParamInfo {
                name: p.name.clone(),
                ty: env.resolve_type_validated(&p.ty, diagnostics),
                has_default: p.default.is_some(),
                with_groups: p
                    .with_groups
                    .groups
                    .iter()
                    .map(|g| g.name.clone())
                    .collect(),
                with_disjunctive: p.with_groups.disjunctive,
            }
        })
        .collect();

    // Validate tags
    let mut tag_set = HashSet::new();
    for tag in &a.tags {
        if !env.tags.contains(tag) {
            diagnostics.push(
                Diagnostic::error(
                    format!("undeclared tag `{tag}` on action `{}`", a.name),
                    span,
                )
                .with_help(format!("declare it with: tag {tag}")),
            );
        }
        tag_set.insert(tag.clone());
    }

    // Resolve return type directly — no implicit wrapping.
    // Users declare `-> option<T>` explicitly to account for veto/requires-fail.
    let return_type = if let Some(ref rt) = a.return_type {
        env.resolve_type_validated(rt, diagnostics)
    } else {
        Ty::Unit
    };

    let fn_info = FnInfo {
        name: a.name.clone(),
        kind: FnKind::Action,
        params: param_infos,
        return_type,
        receiver: Some(receiver),
        tags: tag_set,
        synthetic: false,
        trigger: None,
    };

    // Store in action_overloads
    env.action_overloads
        .entry(a.name.clone())
        .or_default()
        .push(fn_info.clone());

    // Store representative in env.functions (first overload wins, or update to AnyEntity receiver)
    if !env.functions.contains_key(a.name.as_str()) {
        env.functions.insert(a.name.clone(), fn_info);
    }
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
        with_groups: r
            .receiver_with_groups
            .groups
            .iter()
            .map(|g| g.name.clone())
            .collect(),
        with_disjunctive: r.receiver_with_groups.disjunctive,
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

    if let Some(fi) = env.functions.get_mut(&Name::from(r.name.as_str())) {
        fi.trigger = Some(TriggerInfo {
            event_name: r.trigger.event_name.clone(),
        });
    }

    env.trigger_index
        .entry(r.trigger.event_name.clone())
        .or_default()
        .push(Name::from(r.name.as_str()));
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
        with_groups: h
            .receiver_with_groups
            .groups
            .iter()
            .map(|g| g.name.clone())
            .collect(),
        with_disjunctive: h.receiver_with_groups.disjunctive,
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

    if let Some(fi) = env.functions.get_mut(&Name::from(h.name.as_str())) {
        fi.trigger = Some(TriggerInfo {
            event_name: h.trigger.event_name.clone(),
        });
    }

    env.trigger_index
        .entry(h.trigger.event_name.clone())
        .or_default()
        .push(Name::from(h.name.as_str()));
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
            format!("duplicate condition declaration `{name}`"),
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
            with_groups: param
                .with_groups
                .groups
                .iter()
                .map(|g| g.name.clone())
                .collect(),
            with_disjunctive: param.with_groups.disjunctive,
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

    // Detect implicit name shadowing: `state` and `self` are reserved
    if c.receiver_name == "state" {
        diagnostics.push(Diagnostic::error(
            format!(
                "condition `{name}` receiver `state` shadows the implicit condition state binding"
            ),
            span,
        ));
    }
    if c.receiver_name == "self" {
        diagnostics.push(Diagnostic::error(
            format!(
                "condition `{name}` receiver `self` shadows the implicit self binding in periodic blocks"
            ),
            span,
        ));
    }
    for p in &c.params {
        if p.name == "state" {
            diagnostics.push(Diagnostic::error(
                format!(
                    "condition `{name}` parameter `state` shadows the implicit condition state binding"
                ),
                p.span,
            ));
        }
        if p.name == "self" {
            diagnostics.push(Diagnostic::error(
                format!(
                    "condition `{name}` parameter `self` shadows the implicit self binding in periodic blocks"
                ),
                p.span,
            ));
        }
    }

    // Validate tags: each must be declared in env.tags
    let mut tag_set = HashSet::new();
    for tag in &c.tags {
        if !env.tags.contains(tag) {
            diagnostics.push(
                Diagnostic::error(
                    format!("undeclared tag `{tag}` on condition `{name}`"),
                    span,
                )
                .with_help(format!("declare it with: tag {tag}")),
            );
        }
        tag_set.insert(tag.clone());
    }

    // Resolve own state field types (not yet type-checking defaults — that happens in Pass 2)
    let own_state_fields: Vec<(Name, Ty)> = c
        .state_fields
        .iter()
        .map(|sf| (sf.name.clone(), env.resolve_type(&sf.ty)))
        .collect();

    env.conditions.insert(
        name.clone(),
        ConditionInfo {
            name: name.clone(),
            params: param_infos,
            extends: c.extends.iter().map(|s| s.node.clone()).collect(),
            receiver_name: c.receiver_name.clone(),
            receiver_type: env.resolve_type(&c.receiver_type),
            tags: tag_set,
            own_state_fields,
            merged_state_fields: Vec::new(), // populated by merge_condition_state_fields()
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
    if let Some(existing) = env.events.get(&e.name) {
        // Allow user-defined override of builtin events (e.g., modify_applied).
        // Spec: "User-defined events with the name modify_applied take precedence
        //        over the built-in (consistent with Duration/TurnBudget override
        //        semantics)."
        if existing.builtin {
            env.events.remove(&e.name);
        } else {
            diagnostics.push(Diagnostic::error(
                format!("duplicate event declaration `{}`", e.name),
                span,
            ));
            return;
        }
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
                with_groups: p
                    .with_groups
                    .groups
                    .iter()
                    .map(|g| g.name.clone())
                    .collect(),
                with_disjunctive: p.with_groups.disjunctive,
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
            builtin: false,
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
                if let DeclKind::Option(o) = &decl.node
                    && let Some(ref parent) = o.extends
                {
                    extends_map.insert(o.name.clone(), (parent.clone(), decl.span));
                }
            }
        }
    }

    // Collect system names — `extends` can reference a system or another option
    let system_names: HashSet<&str> = program
        .items
        .iter()
        .filter_map(|item| {
            if let TopLevel::System(system) = &item.node {
                Some(system.name.as_str())
            } else {
                None
            }
        })
        .collect();

    // Check for unknown parent references
    for (child, (parent, span)) in &extends_map {
        if !env.options.contains(parent.as_str()) && !system_names.contains(parent.as_str()) {
            diagnostics.push(Diagnostic::error(
                format!("option \"{child}\" extends unknown option \"{parent}\""),
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
                // Circular — build the chain for the error message.
                // `current` is the node where the cycle was detected; walk
                // from start_name and stop when we revisit `current`.
                let cycle_node = current.clone();
                let mut chain: Vec<String> = vec![start_name.to_string()];
                let mut c = start_name.clone();
                while let Some((parent, _)) = extends_map.get(&c) {
                    chain.push(parent.to_string());
                    if *parent == cycle_node {
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

pub fn validate_condition_extends(
    program: &Program,
    env: &TypeEnv,
    diagnostics: &mut Vec<Diagnostic>,
) {
    use std::collections::HashMap;

    // Collect all extends relationships: child -> [(parent_name, span)]
    let mut extends_map: HashMap<Name, Vec<(Name, Span)>> = HashMap::new();
    for item in &program.items {
        if let TopLevel::System(system) = &item.node {
            for decl in &system.decls {
                if let DeclKind::Condition(c) = &decl.node
                    && !c.extends.is_empty()
                {
                    let parents: Vec<(Name, Span)> =
                        c.extends.iter().map(|s| (s.node.clone(), s.span)).collect();
                    extends_map.insert(c.name.clone(), parents);
                }
            }
        }
    }

    // Check parent existence, receiver compatibility, and parent params
    for (child_name, parents) in &extends_map {
        let child_info = match env.conditions.get(child_name) {
            Some(info) => info,
            None => continue,
        };
        for (parent_name, span) in parents {
            // Parent must exist as a condition
            let parent_info = match env.conditions.get(parent_name) {
                Some(info) => info,
                None => {
                    diagnostics.push(
                        Diagnostic::error(
                            format!(
                                "condition `{child_name}` extends unknown condition `{parent_name}`"
                            ),
                            *span,
                        )
                        .with_help(format!(
                            "declare it with: condition {parent_name} on bearer: <type> {{ ... }}"
                        )),
                    );
                    continue;
                }
            };

            // Receiver type compatibility: child's receiver must be the same entity
            // type as parent, or parent accepts AnyEntity
            if !matches!(parent_info.receiver_type, Ty::AnyEntity)
                && child_info.receiver_type != parent_info.receiver_type
            {
                diagnostics.push(Diagnostic::error(
                    format!(
                        "condition `{}` extends `{}` but receiver types differ: {} vs {}",
                        child_name,
                        parent_name,
                        child_info.receiver_type.display(),
                        parent_info.receiver_type.display()
                    ),
                    *span,
                ));
            }

            // Parents with required params are rejected (child doesn't forward them)
            let has_required = parent_info.params.iter().any(|p| !p.has_default);
            if has_required {
                diagnostics.push(Diagnostic::error(
                    format!(
                        "condition `{child_name}` extends `{parent_name}` which has required parameters"
                    ),
                    *span,
                ));
            }
        }
    }

    // Cycle detection: three-color DFS for multi-parent DAGs.
    // Gray = on current path, Black = fully explored.
    // Visiting a Gray node means a cycle; visiting a Black node means
    // diamond inheritance (legal, not a cycle).
    let mut color: HashMap<Name, u8> = HashMap::new(); // 0=white, 1=gray, 2=black
    let all_names: Vec<Name> = extends_map.keys().cloned().collect();
    for start_name in &all_names {
        if color.get(start_name).copied().unwrap_or(0) != 0 {
            continue; // already explored
        }
        // Iterative DFS with explicit stack tracking enter/exit
        enum Action {
            Enter(Name),
            Exit(Name),
        }
        let mut stack = vec![Action::Enter(start_name.clone())];
        while let Some(action) = stack.pop() {
            match action {
                Action::Enter(ref name) => {
                    match color.get(name).copied().unwrap_or(0) {
                        1 => {
                            // Gray → cycle found. Build chain for error.
                            let span = extends_map.get(name).map_or_else(Span::dummy, |v| v[0].1);
                            diagnostics.push(Diagnostic::error(
                                format!("circular condition extends involving `{name}`"),
                                span,
                            ));
                            continue;
                        }
                        2 => continue, // Black → already fully explored (diamond)
                        _ => {}
                    }
                    color.insert(name.clone(), 1); // Gray
                    stack.push(Action::Exit(name.clone()));
                    if let Some(parents) = extends_map.get(name) {
                        for (parent, _) in parents.iter().rev() {
                            stack.push(Action::Enter(parent.clone()));
                        }
                    }
                }
                Action::Exit(ref name) => {
                    color.insert(name.clone(), 2); // Black
                }
            }
        }
    }
}

/// Post-collect pass: merge inherited state fields for conditions with `extends`.
///
/// For each condition, walks the ancestor chain in DFS order (parents first),
/// collects their state fields, checks for:
/// - Sibling parent conflicts (two parents declare the same field name)
/// - Child redeclaration of an inherited field name
/// Then stores the merged result (ancestors + own) in `merged_state_fields`.
fn merge_condition_state_fields(env: &mut TypeEnv, diagnostics: &mut Vec<Diagnostic>) {
    // Collect the list of all condition names to iterate (avoid borrow issues)
    let cond_names: Vec<Name> = env.conditions.keys().cloned().collect();

    // For conditions without extends, merged = own
    for name in &cond_names {
        let info = &env.conditions[name];
        if info.extends.is_empty() {
            let own = info.own_state_fields.clone();
            env.conditions.get_mut(name).unwrap().merged_state_fields = own;
        }
    }

    // For conditions with extends, walk ancestor chain and merge
    for name in &cond_names {
        let info = &env.conditions[name];
        if info.extends.is_empty() {
            continue;
        }

        // Walk the ancestor chain in DFS order (parents first, diamond dedup)
        let mut merged: Vec<(Name, Ty)> = Vec::new();
        let mut seen_fields: HashSet<Name> = HashSet::new();
        let mut visited: HashSet<Name> = HashSet::new();
        let mut has_error = false;

        fn walk_ancestors(
            cond_name: &Name,
            env: &TypeEnv,
            merged: &mut Vec<(Name, Ty)>,
            seen_fields: &mut HashSet<Name>,
            visited: &mut HashSet<Name>,
            diagnostics: &mut Vec<Diagnostic>,
            has_error: &mut bool,
            is_root: bool,
        ) {
            if !visited.insert(cond_name.clone()) {
                return; // diamond dedup or cycle (already caught by validate_condition_extends)
            }
            let info = match env.conditions.get(cond_name) {
                Some(i) => i,
                None => return, // unknown condition (already reported)
            };

            // Recurse into parents first (ancestor-first order)
            for parent_name in &info.extends {
                walk_ancestors(
                    parent_name,
                    env,
                    merged,
                    seen_fields,
                    visited,
                    diagnostics,
                    has_error,
                    false,
                );
            }

            // Add this condition's own state fields
            for (field_name, field_ty) in &info.own_state_fields {
                if !seen_fields.insert(field_name.clone()) {
                    // Field name already exists from an ancestor or sibling parent
                    if is_root {
                        diagnostics.push(Diagnostic::error(
                            format!(
                                "condition `{cond_name}` redeclares inherited state field `{field_name}`"
                            ),
                            Span::dummy(),
                        ));
                    } else {
                        diagnostics.push(Diagnostic::error(
                            format!(
                                "conflicting state field `{field_name}` in condition inheritance \
                                 chain: multiple ancestors declare the same field name"
                            ),
                            Span::dummy(),
                        ));
                    }
                    *has_error = true;
                } else {
                    merged.push((field_name.clone(), field_ty.clone()));
                }
            }
        }

        walk_ancestors(
            name,
            env,
            &mut merged,
            &mut seen_fields,
            &mut visited,
            diagnostics,
            &mut has_error,
            true,
        );

        if !has_error {
            env.conditions.get_mut(name).unwrap().merged_state_fields = merged;
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
            name: "Indefinite".into(),
            fields: vec![],
            has_defaults: vec![],
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

    // EffectSource enum (built-in fallback).
    // Rulesets may define their own `enum EffectSource { Unknown, Spell(...), ... }`.
    // This minimal fallback provides only `Unknown` — the default for conditions
    // applied without explicit source metadata.
    if !env.types.contains_key("EffectSource") {
        let es_name = Name::from("EffectSource");
        let variants = vec![VariantInfo {
            name: "Unknown".into(),
            fields: vec![],
            has_defaults: vec![],
        }];
        for v in &variants {
            let owners = env.variant_to_enums.entry(v.name.clone()).or_default();
            if !owners.iter().any(|o| o == "EffectSource") {
                owners.push(es_name.clone());
            }
        }
        env.types.insert(
            es_name.clone(),
            DeclInfo::Enum(EnumInfo {
                name: es_name,
                ordered: false,
                variants,
            }),
        );
    }

    // BudgetSpec struct — used by with_budgets for multi-entity provisioning.
    // Always register the built-in definition (overwriting any user-defined
    // version) because the interpreter hard-codes { actor, budget } extraction.
    {
        env.types.insert(
            Name::from("BudgetSpec"),
            DeclInfo::Struct(StructInfo {
                name: Name::from("BudgetSpec"),
                fields: vec![
                    FieldInfo {
                        name: Name::from("actor"),
                        ty: Ty::AnyEntity,
                        has_default: false,
                        restricted: false,
                    },
                    FieldInfo {
                        name: Name::from("budget"),
                        ty: Ty::TurnBudget,
                        has_default: false,
                        restricted: false,
                    },
                ],
            }),
        );
    }

    // Built-in `modify_applied` event — emitted by the interpreter when a
    // condition's modify clause fires. Hooks can listen for this to implement
    // "until next use" duration patterns.
    env.events
        .entry(Name::from("modify_applied"))
        .or_insert_with(|| EventInfo {
            name: Name::from("modify_applied"),
            params: vec![
                ParamInfo {
                    name: "bearer".into(),
                    ty: Ty::AnyEntity,
                    has_default: false,
                    with_groups: vec![],
                    with_disjunctive: false,
                },
                ParamInfo {
                    name: "condition".into(),
                    ty: Ty::ActiveCondition,
                    has_default: false,
                    with_groups: vec![],
                    with_disjunctive: false,
                },
            ],
            fields: vec![(Name::from("target_fn"), Ty::String)],
            builtin: true,
        });

    // Presence enum — used by suspend() builtins.
    if !env.types.contains_key("Presence") {
        let presence_name = Name::from("Presence");
        let variants = vec![
            VariantInfo {
                name: "OnMap".into(),
                fields: vec![],
                has_defaults: vec![],
            },
            VariantInfo {
                name: "OffBoard".into(),
                fields: vec![],
                has_defaults: vec![],
            },
        ];
        for v in &variants {
            let owners = env.variant_to_enums.entry(v.name.clone()).or_default();
            if !owners.iter().any(|o| o == "Presence") {
                owners.push(presence_name.clone());
            }
        }
        env.types.insert(
            presence_name.clone(),
            DeclInfo::Enum(EnumInfo {
                name: presence_name,
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
