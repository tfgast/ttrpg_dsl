//! Module resolution: validates imports, detects global name collisions,
//! computes per-system visibility, and desugars `TypeExpr::Qualified`.
//!
//! Runs after parsing/lowering and span rebasing, before checking.

use std::collections::{HashMap, HashSet};

use ttrpg_ast::ast::*;
use ttrpg_ast::diagnostic::Diagnostic;
use ttrpg_ast::module::{ImportInfo, ModuleMap, SystemInfo};
use ttrpg_ast::{Span, Spanned};

/// Per-file metadata extracted by `parse_multi` before calling `resolve_modules`.
pub struct FileSystemInfo {
    /// Systems defined in this file (by name).
    pub system_names: Vec<String>,
    /// `use` declarations in this file.
    pub use_decls: Vec<UseDecl>,
}

/// Namespace discriminant for collision detection and visibility checks.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Namespace {
    Type,
    Function,
    Condition,
    Event,
    Option,
    Variant,
}

/// Takes an already-rebased, merged program. Produces ModuleMap + validation diagnostics.
/// All spans in the input program are already global offsets.
pub fn resolve_modules(
    program: &mut Program,
    file_systems: &[FileSystemInfo],
) -> (ModuleMap, Vec<Diagnostic>) {
    let mut diagnostics = Vec::new();

    // Step 1: Build system registry — which declarations belong to which system
    let mut system_decls: HashMap<String, Vec<DeclOwnership>> = HashMap::new();

    for item in program.items.iter() {
        if let TopLevel::System(system) = &item.node {
            let entry = system_decls.entry(system.name.clone()).or_default();
            for decl in &system.decls {
                entry.push(DeclOwnership::from_decl(&decl.node, decl.span));
            }
        }
    }

    // Step 2: Build SystemInfo for each system (per-namespace declaration sets)
    let mut module_map = ModuleMap::default();

    for (sys_name, decl_list) in &system_decls {
        let mut info = SystemInfo::default();
        let mut seen_names: HashMap<(Namespace, String), Span> = HashMap::new();

        for owned in decl_list {
            for (ns, name) in &owned.names {
                if let Some(&prev_span) = seen_names.get(&(*ns, name.clone())) {
                    diagnostics.push(Diagnostic::error(
                        format!(
                            "duplicate declaration `{}` in system \"{}\"",
                            name, sys_name
                        ),
                        owned.span,
                    ));
                    // Also point to first definition
                    diagnostics.push(Diagnostic::warning(
                        format!("first definition of `{}` here", name),
                        prev_span,
                    ));
                } else {
                    seen_names.insert((*ns, name.clone()), owned.span);
                    match ns {
                        Namespace::Type => { info.types.insert(name.clone()); }
                        Namespace::Function => { info.functions.insert(name.clone()); }
                        Namespace::Condition => { info.conditions.insert(name.clone()); }
                        Namespace::Event => { info.events.insert(name.clone()); }
                        Namespace::Option => { info.options.insert(name.clone()); }
                        Namespace::Variant => { info.variants.insert(name.clone()); }
                    }
                }
            }
        }

        module_map.systems.insert(sys_name.clone(), info);
    }

    // Step 3: Collect per-file use declarations and associate with systems
    // All uses in a file apply to ALL system blocks in that file.
    // Per-system imports = union of uses from all files containing it.
    let mut system_imports: HashMap<String, Vec<(ImportInfo, Span)>> = HashMap::new();

    for file_info in file_systems {
        for use_decl in &file_info.use_decls {
            let import = ImportInfo {
                system_name: use_decl.path.clone(),
                alias: use_decl.alias.clone(),
                span: use_decl.span,
            };
            for sys_name in &file_info.system_names {
                system_imports
                    .entry(sys_name.clone())
                    .or_default()
                    .push((import.clone(), use_decl.span));
            }
        }

        // Warning: use with no system block in file
        if file_info.system_names.is_empty() && !file_info.use_decls.is_empty() {
            for use_decl in &file_info.use_decls {
                diagnostics.push(Diagnostic::warning(
                    format!(
                        "`use \"{}\"` has no effect: no system blocks in this file",
                        use_decl.path
                    ),
                    use_decl.span,
                ));
            }
        }
    }

    // Step 4: Validate imports
    for (sys_name, imports) in &system_imports {
        // Track aliases: alias_name → (target_system, span)
        let mut aliases: HashMap<String, (String, Span)> = HashMap::new();
        let mut deduped_imports: Vec<ImportInfo> = Vec::new();

        for (import, _span) in imports {
            // Check target exists
            if !module_map.systems.contains_key(&import.system_name) {
                diagnostics.push(Diagnostic::error(
                    format!("unknown system \"{}\"", import.system_name),
                    import.span,
                ));
                continue;
            }

            // Check self-import
            if import.system_name == *sys_name {
                diagnostics.push(Diagnostic::warning(
                    format!(
                        "system \"{}\" imports itself (no effect)",
                        sys_name
                    ),
                    import.span,
                ));
                continue;
            }

            // Check alias collision
            if let Some(ref alias) = import.alias {
                if let Some((existing_target, existing_span)) = aliases.get(alias) {
                    if *existing_target != import.system_name {
                        diagnostics.push(Diagnostic::error(
                            format!(
                                "duplicate alias \"{}\": already used for \"{}\"",
                                alias, existing_target
                            ),
                            import.span,
                        ));
                        diagnostics.push(Diagnostic::warning(
                            format!("previous use of alias \"{}\" here", alias),
                            *existing_span,
                        ));
                        continue;
                    }
                    // Same alias → same target: idempotent, skip duplicate
                    continue;
                }

                // Check alias vs own declaration (all namespaces including variants)
                if let Some(sys_info) = module_map.systems.get(sys_name) {
                    if system_has_name(sys_info, alias) {
                        diagnostics.push(Diagnostic::error(
                            format!(
                                "alias \"{}\" conflicts with declaration \"{}\"",
                                alias, alias
                            ),
                            import.span,
                        ));
                        continue;
                    }
                }

                // Check alias vs imported names
                // (names from the current target AND all previously accepted imports)
                let mut shadowed_system = None;
                let all_systems = std::iter::once(import.system_name.as_str())
                    .chain(deduped_imports.iter().map(|i| i.system_name.as_str()));
                for check_sys in all_systems {
                    if let Some(sys_info) = module_map.systems.get(check_sys) {
                        if system_has_name(sys_info, alias) {
                            shadowed_system = Some(check_sys.to_string());
                            break;
                        }
                    }
                }
                if let Some(source_system) = shadowed_system {
                    diagnostics.push(Diagnostic::error(
                        format!(
                            "alias \"{}\" shadows declaration \"{}\" imported from \"{}\"",
                            alias, alias, source_system
                        ),
                        import.span,
                    ));
                    continue;
                }

                aliases.insert(alias.clone(), (import.system_name.clone(), import.span));
            }

            deduped_imports.push(import.clone());
        }

        if let Some(sys_info) = module_map.systems.get_mut(sys_name) {
            sys_info.imports = deduped_imports;
        }
    }

    // Step 5: Detect global name collisions across systems
    // Each namespace is checked independently
    detect_cross_system_collisions(&module_map, &mut diagnostics);

    // Step 6: Desugar TypeExpr::Qualified → TypeExpr::Named
    // Walk all AST nodes and replace qualified types after validation
    desugar_qualified_types(program, &module_map, file_systems, &mut diagnostics);

    (module_map, diagnostics)
}

/// Check whether a system exports a name in any namespace.
fn system_has_name(info: &SystemInfo, name: &str) -> bool {
    info.types.contains(name)
        || info.functions.contains(name)
        || info.conditions.contains(name)
        || info.events.contains(name)
        || info.options.contains(name)
        || info.variants.contains(name)
}

/// Ownership info for a single declaration.
struct DeclOwnership {
    names: Vec<(Namespace, String)>,
    span: Span,
}

impl DeclOwnership {
    fn from_decl(decl: &DeclKind, span: Span) -> Self {
        let mut names = Vec::new();
        match decl {
            DeclKind::Enum(e) => {
                names.push((Namespace::Type, e.name.clone()));
                for v in &e.variants {
                    names.push((Namespace::Variant, v.name.clone()));
                }
            }
            DeclKind::Struct(s) => {
                names.push((Namespace::Type, s.name.clone()));
            }
            DeclKind::Entity(e) => {
                names.push((Namespace::Type, e.name.clone()));
            }
            DeclKind::Derive(f) | DeclKind::Mechanic(f) => {
                names.push((Namespace::Function, f.name.clone()));
            }
            DeclKind::Action(a) => {
                names.push((Namespace::Function, a.name.clone()));
            }
            DeclKind::Reaction(r) => {
                names.push((Namespace::Function, r.name.clone()));
            }
            DeclKind::Hook(h) => {
                names.push((Namespace::Function, h.name.clone()));
            }
            DeclKind::Condition(c) => {
                names.push((Namespace::Condition, c.name.clone()));
            }
            DeclKind::Prompt(p) => {
                names.push((Namespace::Function, p.name.clone()));
            }
            DeclKind::Option(o) => {
                names.push((Namespace::Option, o.name.clone()));
            }
            DeclKind::Event(e) => {
                names.push((Namespace::Event, e.name.clone()));
            }
            DeclKind::Move(_) => {
                // Moves should be lowered before resolution
            }
        }
        Self { names, span }
    }
}

/// Detect cross-system duplicate declarations in each namespace.
fn detect_cross_system_collisions(
    module_map: &ModuleMap,
    diagnostics: &mut Vec<Diagnostic>,
) {
    // For each namespace, collect: name → Vec<(system_name)>
    // We can't track spans here easily since ModuleMap doesn't store them,
    // but the error message names both systems which is sufficient.
    let namespaces: &[(Namespace, &str)] = &[
        (Namespace::Type, "type"),
        (Namespace::Function, "function"),
        (Namespace::Condition, "condition"),
        (Namespace::Event, "event"),
        (Namespace::Option, "option"),
        (Namespace::Variant, "enum variant"),
    ];

    for &(ns, ns_label) in namespaces {
        let mut name_owners: HashMap<&str, Vec<&str>> = HashMap::new();

        for (sys_name, sys_info) in &module_map.systems {
            let names: &HashSet<String> = match ns {
                Namespace::Type => &sys_info.types,
                Namespace::Function => &sys_info.functions,
                Namespace::Condition => &sys_info.conditions,
                Namespace::Event => &sys_info.events,
                Namespace::Option => &sys_info.options,
                Namespace::Variant => &sys_info.variants,
            };
            for name in names {
                name_owners.entry(name.as_str()).or_default().push(sys_name.as_str());
            }
        }

        for (name, owners) in &name_owners {
            if owners.len() > 1 {
                let mut sorted_owners = owners.clone();
                sorted_owners.sort();
                diagnostics.push(Diagnostic::error(
                    format!(
                        "duplicate {} \"{}\": defined in \"{}\" and \"{}\"",
                        ns_label, name, sorted_owners[0], sorted_owners[1]
                    ),
                    Span::dummy(),
                ));
            }
        }
    }
}

/// Walk all type expressions in the program and desugar `TypeExpr::Qualified`
/// to `TypeExpr::Named`, after validating the alias and type ownership.
fn desugar_qualified_types(
    program: &mut Program,
    module_map: &ModuleMap,
    file_systems: &[FileSystemInfo],
    diagnostics: &mut Vec<Diagnostic>,
) {
    // Build alias → system_name map per system
    let mut system_aliases: HashMap<String, HashMap<String, String>> = HashMap::new();
    for file_info in file_systems {
        for use_decl in &file_info.use_decls {
            if let Some(ref alias) = use_decl.alias {
                for sys_name in &file_info.system_names {
                    system_aliases
                        .entry(sys_name.clone())
                        .or_default()
                        .insert(alias.clone(), use_decl.path.clone());
                }
            }
        }
    }

    // Walk all items and desugar qualified types
    for item in &mut program.items {
        if let TopLevel::System(system) = &mut item.node {
            let aliases = system_aliases.get(&system.name);
            for decl in &mut system.decls {
                desugar_decl_types(&mut decl.node, &system.name, aliases, module_map, diagnostics);
            }
        }
    }
}

/// Desugar qualified types in a single declaration.
fn desugar_decl_types(
    decl: &mut DeclKind,
    current_system: &str,
    aliases: Option<&HashMap<String, String>>,
    module_map: &ModuleMap,
    diagnostics: &mut Vec<Diagnostic>,
) {
    match decl {
        DeclKind::Enum(e) => {
            for v in &mut e.variants {
                if let Some(ref mut fields) = v.fields {
                    for f in fields {
                        desugar_type_expr(&mut f.ty, current_system, aliases, module_map, diagnostics);
                    }
                }
            }
        }
        DeclKind::Struct(s) => {
            for f in &mut s.fields {
                desugar_type_expr(&mut f.ty, current_system, aliases, module_map, diagnostics);
            }
        }
        DeclKind::Entity(e) => {
            for f in &mut e.fields {
                desugar_type_expr(&mut f.ty, current_system, aliases, module_map, diagnostics);
            }
            for g in &mut e.optional_groups {
                for f in &mut g.fields {
                    desugar_type_expr(&mut f.ty, current_system, aliases, module_map, diagnostics);
                }
            }
        }
        DeclKind::Derive(f) | DeclKind::Mechanic(f) => {
            desugar_type_expr(&mut f.return_type, current_system, aliases, module_map, diagnostics);
            for p in &mut f.params {
                desugar_type_expr(&mut p.ty, current_system, aliases, module_map, diagnostics);
            }
        }
        DeclKind::Action(a) => {
            desugar_type_expr(&mut a.receiver_type, current_system, aliases, module_map, diagnostics);
            for p in &mut a.params {
                desugar_type_expr(&mut p.ty, current_system, aliases, module_map, diagnostics);
            }
        }
        DeclKind::Reaction(r) => {
            desugar_type_expr(&mut r.receiver_type, current_system, aliases, module_map, diagnostics);
        }
        DeclKind::Hook(h) => {
            desugar_type_expr(&mut h.receiver_type, current_system, aliases, module_map, diagnostics);
        }
        DeclKind::Condition(c) => {
            desugar_type_expr(&mut c.receiver_type, current_system, aliases, module_map, diagnostics);
            for p in &mut c.params {
                desugar_type_expr(&mut p.ty, current_system, aliases, module_map, diagnostics);
            }
        }
        DeclKind::Prompt(p) => {
            desugar_type_expr(&mut p.return_type, current_system, aliases, module_map, diagnostics);
            for param in &mut p.params {
                desugar_type_expr(&mut param.ty, current_system, aliases, module_map, diagnostics);
            }
        }
        DeclKind::Event(e) => {
            for p in &mut e.params {
                desugar_type_expr(&mut p.ty, current_system, aliases, module_map, diagnostics);
            }
            for f in &mut e.fields {
                desugar_type_expr(&mut f.ty, current_system, aliases, module_map, diagnostics);
            }
        }
        DeclKind::Option(_) | DeclKind::Move(_) => {}
    }
}

/// Desugar a single `TypeExpr::Qualified` to `TypeExpr::Named`.
fn desugar_type_expr(
    texpr: &mut Spanned<TypeExpr>,
    current_system: &str,
    aliases: Option<&HashMap<String, String>>,
    module_map: &ModuleMap,
    diagnostics: &mut Vec<Diagnostic>,
) {
    match &texpr.node {
        TypeExpr::Qualified { qualifier, name } => {
            let qualifier = qualifier.clone();
            let name = name.clone();

            // Resolve alias to target system
            let target_system = aliases.and_then(|a| a.get(&qualifier));
            match target_system {
                Some(target) => {
                    // Verify the type belongs to the target system
                    if let Some(sys_info) = module_map.systems.get(target) {
                        if sys_info.types.contains(&name) {
                            // Valid — desugar to Named
                            texpr.node = TypeExpr::Named(name);
                        } else {
                            diagnostics.push(Diagnostic::error(
                                format!(
                                    "no type \"{}\" in system \"{}\" (alias \"{}\")",
                                    name, target, qualifier
                                ),
                                texpr.span,
                            ));
                        }
                    } else {
                        diagnostics.push(Diagnostic::error(
                            format!("unknown system \"{}\"", target),
                            texpr.span,
                        ));
                    }
                }
                None => {
                    diagnostics.push(Diagnostic::error(
                        format!(
                            "unknown module alias \"{}\" in system \"{}\"",
                            qualifier, current_system
                        ),
                        texpr.span,
                    ));
                }
            }
        }
        TypeExpr::List(inner) | TypeExpr::Set(inner) | TypeExpr::OptionType(inner) => {
            // Need to recurse into nested types — but we have an immutable borrow.
            // Extract, desugar, put back via unsafe-free pattern.
            let mut inner_clone = inner.as_ref().clone();
            desugar_type_expr(&mut inner_clone, current_system, aliases, module_map, diagnostics);
            match &mut texpr.node {
                TypeExpr::List(ref mut inner) |
                TypeExpr::Set(ref mut inner) |
                TypeExpr::OptionType(ref mut inner) => {
                    **inner = inner_clone;
                }
                _ => unreachable!(),
            }
        }
        TypeExpr::Map(k, v) => {
            let mut k_clone = k.as_ref().clone();
            let mut v_clone = v.as_ref().clone();
            desugar_type_expr(&mut k_clone, current_system, aliases, module_map, diagnostics);
            desugar_type_expr(&mut v_clone, current_system, aliases, module_map, diagnostics);
            if let TypeExpr::Map(ref mut k, ref mut v) = &mut texpr.node {
                **k = k_clone;
                **v = v_clone;
            }
        }
        _ => {} // Primitive types, Named, Resource — no desugaring needed
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ttrpg_ast::diagnostic::Severity;
    use ttrpg_ast::Spanned;

    fn make_program(items: Vec<Spanned<TopLevel>>) -> Program {
        let mut p = Program { items, ..Default::default() };
        p.build_index();
        p
    }

    fn make_system(name: &str, decls: Vec<Spanned<DeclKind>>) -> Spanned<TopLevel> {
        Spanned::new(
            TopLevel::System(SystemBlock {
                name: name.to_string(),
                decls,
            }),
            Span::dummy(),
        )
    }

    fn make_enum(name: &str, variants: &[&str]) -> Spanned<DeclKind> {
        Spanned::new(
            DeclKind::Enum(EnumDecl {
                name: name.to_string(),
                ordered: false,
                variants: variants
                    .iter()
                    .map(|v| EnumVariant {
                        name: v.to_string(),
                        fields: None,
                        span: Span::dummy(),
                    })
                    .collect(),
            }),
            Span::dummy(),
        )
    }

    fn make_derive(name: &str) -> Spanned<DeclKind> {
        Spanned::new(
            DeclKind::Derive(FnDecl {
                name: name.to_string(),
                params: vec![],
                return_type: Spanned::new(TypeExpr::Int, Span::dummy()),
                body: Spanned::new(vec![], Span::dummy()),
                synthetic: false,
            }),
            Span::dummy(),
        )
    }

    fn make_event(name: &str) -> Spanned<DeclKind> {
        Spanned::new(
            DeclKind::Event(EventDecl {
                name: name.to_string(),
                params: vec![],
                fields: vec![],
            }),
            Span::dummy(),
        )
    }

    fn make_condition(name: &str) -> Spanned<DeclKind> {
        Spanned::new(
            DeclKind::Condition(ConditionDecl {
                name: name.to_string(),
                params: vec![],
                receiver_name: "bearer".to_string(),
                receiver_type: Spanned::new(TypeExpr::Named("Character".into()), Span::dummy()),
                receiver_with_groups: vec![],
                clauses: vec![],
            }),
            Span::dummy(),
        )
    }

    #[test]
    fn single_system_no_imports() {
        let mut program = make_program(vec![
            make_system("Core", vec![
                make_enum("Ability", &["STR", "DEX"]),
                make_derive("modifier"),
            ]),
        ]);
        let file_systems = vec![FileSystemInfo {
            system_names: vec!["Core".into()],
            use_decls: vec![],
        }];

        let (map, diags) = resolve_modules(&mut program, &file_systems);
        assert!(diags.is_empty(), "unexpected diagnostics: {:?}", diags);
        let core = map.systems.get("Core").unwrap();
        assert!(core.types.contains("Ability"));
        assert!(core.functions.contains("modifier"));
        assert!(core.variants.contains("STR"));
        assert!(core.variants.contains("DEX"));
    }

    #[test]
    fn cross_system_duplicate_type_detected() {
        let mut program = make_program(vec![
            make_system("A", vec![make_enum("Ability", &["STR"])]),
            make_system("B", vec![make_enum("Ability", &["DEX"])]),
        ]);
        let file_systems = vec![FileSystemInfo {
            system_names: vec!["A".into(), "B".into()],
            use_decls: vec![],
        }];

        let (_map, diags) = resolve_modules(&mut program, &file_systems);
        let errors: Vec<_> = diags.iter().filter(|d| d.severity == Severity::Error).collect();
        assert!(!errors.is_empty(), "expected collision error");
        assert!(errors.iter().any(|d| d.message.contains("duplicate type \"Ability\"")));
    }

    #[test]
    fn cross_system_duplicate_variant_detected() {
        let mut program = make_program(vec![
            make_system("A", vec![make_enum("Ability", &["STR"])]),
            make_system("B", vec![make_enum("Stat", &["STR"])]),
        ]);
        let file_systems = vec![FileSystemInfo {
            system_names: vec!["A".into(), "B".into()],
            use_decls: vec![],
        }];

        let (_map, diags) = resolve_modules(&mut program, &file_systems);
        let errors: Vec<_> = diags.iter().filter(|d| d.severity == Severity::Error).collect();
        assert!(errors.iter().any(|d| d.message.contains("duplicate enum variant \"STR\"")));
    }

    #[test]
    fn same_name_different_namespace_ok() {
        let mut program = make_program(vec![
            make_system("A", vec![make_enum("Foo", &[])]),
            make_system("B", vec![make_derive("Foo")]),
        ]);
        let file_systems = vec![FileSystemInfo {
            system_names: vec!["A".into(), "B".into()],
            use_decls: vec![],
        }];

        let (_map, diags) = resolve_modules(&mut program, &file_systems);
        let errors: Vec<_> = diags.iter().filter(|d| d.severity == Severity::Error).collect();
        assert!(errors.is_empty(), "type Foo and function Foo should not collide: {:?}", errors);
    }

    #[test]
    fn unknown_import_target() {
        let mut program = make_program(vec![
            make_system("Core", vec![make_derive("modifier")]),
        ]);
        let file_systems = vec![FileSystemInfo {
            system_names: vec!["Core".into()],
            use_decls: vec![UseDecl {
                path: "Unknown".into(),
                alias: None,
                span: Span::new(0, 7),
            }],
        }];

        let (_map, diags) = resolve_modules(&mut program, &file_systems);
        assert!(diags.iter().any(|d| d.message.contains("unknown system \"Unknown\"")));
    }

    #[test]
    fn self_import_warning() {
        let mut program = make_program(vec![
            make_system("Core", vec![make_derive("modifier")]),
        ]);
        let file_systems = vec![FileSystemInfo {
            system_names: vec!["Core".into()],
            use_decls: vec![UseDecl {
                path: "Core".into(),
                alias: None,
                span: Span::new(0, 4),
            }],
        }];

        let (_map, diags) = resolve_modules(&mut program, &file_systems);
        let warnings: Vec<_> = diags.iter().filter(|d| d.severity == Severity::Warning).collect();
        assert!(warnings.iter().any(|d| d.message.contains("imports itself")));
    }

    #[test]
    fn duplicate_alias_different_targets() {
        let mut program = make_program(vec![
            make_system("A", vec![make_derive("foo")]),
            make_system("B", vec![make_derive("bar")]),
            make_system("Main", vec![make_derive("main_fn")]),
        ]);
        let file_systems = vec![FileSystemInfo {
            system_names: vec!["Main".into()],
            use_decls: vec![
                UseDecl { path: "A".into(), alias: Some("X".into()), span: Span::new(0, 10) },
                UseDecl { path: "B".into(), alias: Some("X".into()), span: Span::new(20, 30) },
            ],
        }];

        let (_map, diags) = resolve_modules(&mut program, &file_systems);
        assert!(diags.iter().any(|d| d.message.contains("duplicate alias \"X\"")));
    }

    #[test]
    fn same_alias_same_target_idempotent() {
        let mut program = make_program(vec![
            make_system("A", vec![make_derive("foo")]),
            make_system("Main", vec![make_derive("main_fn")]),
        ]);
        // Two files both import A as X for the same system
        let file_systems = vec![
            FileSystemInfo {
                system_names: vec!["Main".into()],
                use_decls: vec![
                    UseDecl { path: "A".into(), alias: Some("X".into()), span: Span::new(0, 10) },
                ],
            },
            FileSystemInfo {
                system_names: vec!["Main".into()],
                use_decls: vec![
                    UseDecl { path: "A".into(), alias: Some("X".into()), span: Span::new(50, 60) },
                ],
            },
        ];

        let (_map, diags) = resolve_modules(&mut program, &file_systems);
        let errors: Vec<_> = diags.iter().filter(|d| d.severity == Severity::Error).collect();
        assert!(errors.is_empty(), "same alias→same target should be idempotent: {:?}", errors);
    }

    #[test]
    fn alias_conflicts_with_own_declaration() {
        let mut program = make_program(vec![
            make_system("Other", vec![make_derive("bar")]),
            make_system("Main", vec![make_derive("Foo")]),
        ]);
        let file_systems = vec![FileSystemInfo {
            system_names: vec!["Main".into()],
            use_decls: vec![UseDecl {
                path: "Other".into(),
                alias: Some("Foo".into()),
                span: Span::new(0, 10),
            }],
        }];

        let (_map, diags) = resolve_modules(&mut program, &file_systems);
        assert!(diags.iter().any(|d| d.message.contains("alias \"Foo\" conflicts with declaration")));
    }

    #[test]
    fn use_with_no_system_block_warning() {
        let mut program = make_program(vec![
            make_system("Other", vec![make_derive("bar")]),
        ]);
        let file_systems = vec![
            FileSystemInfo {
                system_names: vec!["Other".into()],
                use_decls: vec![],
            },
            FileSystemInfo {
                system_names: vec![], // No systems in this file
                use_decls: vec![UseDecl {
                    path: "Other".into(),
                    alias: None,
                    span: Span::new(0, 5),
                }],
            },
        ];

        let (_map, diags) = resolve_modules(&mut program, &file_systems);
        assert!(diags.iter().any(|d| d.message.contains("no system blocks in this file")));
    }

    #[test]
    fn valid_import_recorded() {
        let mut program = make_program(vec![
            make_system("Core", vec![
                make_enum("Ability", &["STR"]),
                make_derive("modifier"),
            ]),
            make_system("Homebrew", vec![make_derive("custom")]),
        ]);
        let file_systems = vec![FileSystemInfo {
            system_names: vec!["Core".into(), "Homebrew".into()],
            use_decls: vec![UseDecl {
                path: "Core".into(),
                alias: Some("C".into()),
                span: Span::new(0, 10),
            }],
        }];

        let (map, diags) = resolve_modules(&mut program, &file_systems);
        let errors: Vec<_> = diags.iter().filter(|d| d.severity == Severity::Error).collect();
        assert!(errors.is_empty(), "unexpected errors: {:?}", errors);

        // Homebrew should have Core as an import (use decl applies to all systems in file)
        let homebrew = map.systems.get("Homebrew").unwrap();
        assert_eq!(homebrew.imports.len(), 1);
        assert_eq!(homebrew.imports[0].system_name, "Core");
        assert_eq!(homebrew.imports[0].alias, Some("C".into()));

        // Core also gets the import (applies to all systems in file), but it's a self-import → filtered
        let core = map.systems.get("Core").unwrap();
        assert_eq!(core.imports.len(), 0);
    }

    #[test]
    fn duplicate_within_merged_system() {
        let mut program = make_program(vec![
            make_system("Core", vec![make_derive("modifier")]),
            make_system("Core", vec![make_derive("modifier")]), // same system, same name
        ]);
        let file_systems = vec![FileSystemInfo {
            system_names: vec!["Core".into()],
            use_decls: vec![],
        }];

        let (_map, diags) = resolve_modules(&mut program, &file_systems);
        assert!(diags.iter().any(|d| d.message.contains("duplicate declaration `modifier`")));
    }

    #[test]
    fn alias_conflicts_with_own_variant() {
        // Bug fix: alias vs own enum variant should be detected
        let mut program = make_program(vec![
            make_system("Other", vec![make_derive("bar")]),
            make_system("Main", vec![make_enum("DamageType", &["fire", "cold"])]),
        ]);
        let file_systems = vec![FileSystemInfo {
            system_names: vec!["Main".into()],
            use_decls: vec![UseDecl {
                path: "Other".into(),
                alias: Some("fire".into()),
                span: Span::new(0, 10),
            }],
        }];

        let (_map, diags) = resolve_modules(&mut program, &file_systems);
        assert!(
            diags.iter().any(|d| d.message.contains("alias \"fire\" conflicts with declaration")),
            "alias should conflict with own variant: {:?}", diags
        );
    }

    #[test]
    fn alias_shadows_cross_import_name() {
        // Bug fix: alias should be checked against ALL imported systems, not just the current target
        // use "A" (A exports type Foo) + use "B" as Foo → alias Foo shadows A's Foo
        let mut program = make_program(vec![
            make_system("A", vec![make_enum("Foo", &["X"])]),
            make_system("B", vec![make_derive("bar")]),
            make_system("Main", vec![make_derive("main_fn")]),
        ]);
        let file_systems = vec![FileSystemInfo {
            system_names: vec!["Main".into()],
            use_decls: vec![
                UseDecl { path: "A".into(), alias: None, span: Span::new(0, 5) },
                UseDecl { path: "B".into(), alias: Some("Foo".into()), span: Span::new(10, 25) },
            ],
        }];

        let (_map, diags) = resolve_modules(&mut program, &file_systems);
        let errors: Vec<_> = diags.iter().filter(|d| d.severity == Severity::Error).collect();
        assert!(
            errors.iter().any(|d| d.message.contains("alias \"Foo\" shadows")),
            "alias Foo should shadow imported type Foo from A: {:?}", errors
        );
    }

    #[test]
    fn alias_shadows_cross_import_variant() {
        // Alias shadows an enum variant from a different imported system
        let mut program = make_program(vec![
            make_system("A", vec![make_enum("DamageType", &["fire", "cold"])]),
            make_system("B", vec![make_derive("bar")]),
            make_system("Main", vec![make_derive("main_fn")]),
        ]);
        let file_systems = vec![FileSystemInfo {
            system_names: vec!["Main".into()],
            use_decls: vec![
                UseDecl { path: "A".into(), alias: None, span: Span::new(0, 5) },
                UseDecl { path: "B".into(), alias: Some("fire".into()), span: Span::new(10, 25) },
            ],
        }];

        let (_map, diags) = resolve_modules(&mut program, &file_systems);
        let errors: Vec<_> = diags.iter().filter(|d| d.severity == Severity::Error).collect();
        assert!(
            errors.iter().any(|d| d.message.contains("alias \"fire\" shadows")),
            "alias fire should shadow imported variant fire from A: {:?}", errors
        );
    }

    #[test]
    fn alias_shadows_cross_import_condition() {
        // Alias shadows a condition from a different imported system
        let mut program = make_program(vec![
            make_system("A", vec![make_condition("Stunned")]),
            make_system("B", vec![make_derive("bar")]),
            make_system("Main", vec![make_derive("main_fn")]),
        ]);
        let file_systems = vec![FileSystemInfo {
            system_names: vec!["Main".into()],
            use_decls: vec![
                UseDecl { path: "A".into(), alias: None, span: Span::new(0, 5) },
                UseDecl { path: "B".into(), alias: Some("Stunned".into()), span: Span::new(10, 25) },
            ],
        }];

        let (_map, diags) = resolve_modules(&mut program, &file_systems);
        let errors: Vec<_> = diags.iter().filter(|d| d.severity == Severity::Error).collect();
        assert!(
            errors.iter().any(|d| d.message.contains("alias \"Stunned\" shadows")),
            "alias Stunned should shadow imported condition from A: {:?}", errors
        );
    }

    #[test]
    fn alias_shadows_target_system_name() {
        // Original behavior preserved: alias shadows name from the target system itself
        let mut program = make_program(vec![
            make_system("A", vec![make_enum("Foo", &["X"]), make_derive("bar")]),
            make_system("Main", vec![make_derive("main_fn")]),
        ]);
        let file_systems = vec![FileSystemInfo {
            system_names: vec!["Main".into()],
            use_decls: vec![UseDecl {
                path: "A".into(),
                alias: Some("Foo".into()),
                span: Span::new(0, 10),
            }],
        }];

        let (_map, diags) = resolve_modules(&mut program, &file_systems);
        let errors: Vec<_> = diags.iter().filter(|d| d.severity == Severity::Error).collect();
        assert!(
            errors.iter().any(|d| d.message.contains("alias \"Foo\" shadows")),
            "alias Foo should shadow type Foo from target system A: {:?}", errors
        );
    }

    #[test]
    fn alias_no_conflict_with_unrelated_names() {
        // Alias that doesn't conflict with anything should work fine
        let mut program = make_program(vec![
            make_system("A", vec![make_enum("Foo", &["X"])]),
            make_system("B", vec![make_derive("bar")]),
            make_system("Main", vec![make_derive("main_fn")]),
        ]);
        let file_systems = vec![FileSystemInfo {
            system_names: vec!["Main".into()],
            use_decls: vec![
                UseDecl { path: "A".into(), alias: None, span: Span::new(0, 5) },
                UseDecl { path: "B".into(), alias: Some("Bsys".into()), span: Span::new(10, 25) },
            ],
        }];

        let (_map, diags) = resolve_modules(&mut program, &file_systems);
        let errors: Vec<_> = diags.iter().filter(|d| d.severity == Severity::Error).collect();
        assert!(errors.is_empty(), "no conflicts expected: {:?}", errors);
    }
}
