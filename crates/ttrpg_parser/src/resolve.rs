//! Module resolution: validates imports, detects global name collisions,
//! computes per-system visibility, and desugars `TypeExpr::Qualified`.
//!
//! Runs after parsing/lowering, before checking.

use std::collections::{HashMap, HashSet};

use ttrpg_ast::ast::*;
use ttrpg_ast::diagnostic::Diagnostic;
use ttrpg_ast::module::{ImportInfo, ModuleMap, SystemInfo};
use ttrpg_ast::name::Name;
use ttrpg_ast::{Span, Spanned};

#[cfg(test)]
use ttrpg_ast::FileId;

/// Per-file metadata extracted by `parse_multi` before calling `resolve_modules`.
#[derive(Clone)]
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
    let mut system_decls: HashMap<Name, Vec<DeclOwnership>> = HashMap::new();

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
        let mut seen_names: HashMap<(Namespace, Name), Span> = HashMap::new();

        for owned in decl_list {
            for (ns, name) in &owned.names {
                // Variants allow multi-owner: the same variant name can appear
                // in multiple enums and the checker resolves via expected-type
                // hints or qualified syntax.
                if *ns == Namespace::Variant {
                    info.variants.insert(name.clone());
                } else if let Some(&prev_span) = seen_names.get(&(*ns, name.clone())) {
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
                        Namespace::Variant => unreachable!(),
                    }
                }
            }
        }

        module_map.systems.insert(sys_name.clone(), info);
    }

    // Step 3: Collect per-file use declarations and associate with systems
    // All uses in a file apply to ALL system blocks in that file.
    // Per-system imports = union of uses from all files containing it.
    let mut system_imports: HashMap<Name, Vec<(ImportInfo, Span)>> = HashMap::new();

    for file_info in file_systems {
        for use_decl in &file_info.use_decls {
            let import = ImportInfo {
                system_name: Name::from(use_decl.path.clone()),
                alias: use_decl.alias.clone(),
                span: use_decl.span,
            };
            for sys_name in &file_info.system_names {
                system_imports
                    .entry(Name::from(sys_name.clone()))
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
        let mut aliases: HashMap<Name, (Name, Span)> = HashMap::new();
        let mut deduped_imports: Vec<ImportInfo> = Vec::new();

        // Pre-collect ALL valid import target systems so alias shadow
        // checking is order-independent (not just "previously accepted").
        let all_import_targets: HashSet<Name> = imports.iter()
            .filter_map(|(import, _)| {
                if !module_map.systems.contains_key(&import.system_name) { return None; }
                if import.system_name == *sys_name { return None; }
                Some(import.system_name.clone())
            })
            .collect();

        for (import, _span) in imports {
            // Check target exists
            if !module_map.systems.contains_key(&import.system_name) {
                diagnostics.push(Diagnostic::error(
                    format!("unknown system \"{}\"", import.system_name),
                    import.span,
                ).with_help(format!(
                    "\"{}\" is not defined in the loaded files; \
                     load the file that defines it in the same `load` command",
                    import.system_name
                )));
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

                // Check alias vs imported names from ALL import targets
                // (order-independent: uses pre-collected target set, not
                // just previously processed imports)
                let mut shadowed_system = None;
                for target in &all_import_targets {
                    if let Some(sys_info) = module_map.systems.get(target.as_str()) {
                        if system_has_name(sys_info, alias) {
                            shadowed_system = Some(target.to_string());
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
    desugar_qualified_types(program, &module_map, &mut diagnostics);

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
    names: Vec<(Namespace, Name)>,
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
            DeclKind::Table(t) => {
                names.push((Namespace::Function, t.name.clone()));
            }
            DeclKind::Unit(u) => {
                names.push((Namespace::Type, u.name.clone()));
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
    // Variants are excluded: multi-owner variants are allowed across systems
    // and disambiguated by the checker via expected-type hints or qualified syntax.
    let namespaces: &[(Namespace, &str)] = &[
        (Namespace::Type, "type"),
        (Namespace::Function, "function"),
        (Namespace::Condition, "condition"),
        (Namespace::Event, "event"),
        (Namespace::Option, "option"),
    ];

    for &(ns, ns_label) in namespaces {
        let mut name_owners: HashMap<&str, Vec<&str>> = HashMap::new();

        for (sys_name, sys_info) in &module_map.systems {
            let names: &HashSet<Name> = match ns {
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
                let owners_list = sorted_owners
                    .iter()
                    .map(|o| format!("\"{}\"", o))
                    .collect::<Vec<_>>()
                    .join(", ");
                diagnostics.push(Diagnostic::error(
                    format!(
                        "duplicate {} \"{}\": defined in {}",
                        ns_label, name, owners_list
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
    diagnostics: &mut Vec<Diagnostic>,
) {
    // Build alias → system_name map per system from validated imports
    let mut system_aliases: HashMap<Name, HashMap<Name, Name>> = HashMap::new();
    for (sys_name, sys_info) in &module_map.systems {
        for import in &sys_info.imports {
            if let Some(ref alias) = import.alias {
                system_aliases
                    .entry(sys_name.clone())
                    .or_default()
                    .insert(alias.clone(), import.system_name.clone());
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
    current_system: &Name,
    aliases: Option<&HashMap<Name, Name>>,
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
            for clause in &mut c.clauses {
                if let ConditionClause::Modify(m) = clause {
                    desugar_modify_stmts(&mut m.body, current_system, aliases, module_map, diagnostics);
                }
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
        DeclKind::Table(t) => {
            desugar_type_expr(&mut t.return_type, current_system, aliases, module_map, diagnostics);
            for p in &mut t.params {
                desugar_type_expr(&mut p.ty, current_system, aliases, module_map, diagnostics);
            }
        }
        DeclKind::Unit(u) => {
            for f in &mut u.fields {
                desugar_type_expr(&mut f.ty, current_system, aliases, module_map, diagnostics);
            }
        }
        DeclKind::Option(o) => {
            if let Some(ref mut clauses) = o.when_enabled {
                for m in clauses {
                    desugar_modify_stmts(&mut m.body, current_system, aliases, module_map, diagnostics);
                }
            }
        }
        DeclKind::Move(_) => {}
    }
}

/// Desugar qualified types inside modify statement bodies (recursing into if branches).
fn desugar_modify_stmts(
    stmts: &mut [ModifyStmt],
    current_system: &Name,
    aliases: Option<&HashMap<Name, Name>>,
    module_map: &ModuleMap,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for stmt in stmts {
        match stmt {
            ModifyStmt::Let { ty, .. } => {
                if let Some(ref mut ty_expr) = ty {
                    desugar_type_expr(ty_expr, current_system, aliases, module_map, diagnostics);
                }
            }
            ModifyStmt::If { then_body, else_body, .. } => {
                desugar_modify_stmts(then_body, current_system, aliases, module_map, diagnostics);
                if let Some(ref mut else_stmts) = else_body {
                    desugar_modify_stmts(else_stmts, current_system, aliases, module_map, diagnostics);
                }
            }
            ModifyStmt::ParamOverride { .. } | ModifyStmt::ResultOverride { .. } => {}
        }
    }
}

/// Desugar a single `TypeExpr::Qualified` to `TypeExpr::Named`.
fn desugar_type_expr(
    texpr: &mut Spanned<TypeExpr>,
    current_system: &Name,
    aliases: Option<&HashMap<Name, Name>>,
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
                name: Name::from(name),
                decls,
            }),
            Span::dummy(),
        )
    }

    fn make_enum(name: &str, variants: &[&str]) -> Spanned<DeclKind> {
        Spanned::new(
            DeclKind::Enum(EnumDecl {
                name: Name::from(name),
                ordered: false,
                variants: variants
                    .iter()
                    .map(|v| EnumVariant {
                        name: Name::from(*v),
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
                name: Name::from(name),
                params: vec![],
                return_type: Spanned::new(TypeExpr::Int, Span::dummy()),
                body: Spanned::new(vec![], Span::dummy()),
                synthetic: false,
            }),
            Span::dummy(),
        )
    }

    fn make_condition(name: &str) -> Spanned<DeclKind> {
        Spanned::new(
            DeclKind::Condition(ConditionDecl {
                name: Name::from(name),
                params: vec![],
                receiver_name: Name::from("bearer"),
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
    fn cross_system_shared_variant_allowed() {
        // Multi-owner variants: same variant name in different enums across
        // systems is allowed — the checker disambiguates via expected-type
        // hints or qualified syntax.
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
        assert!(errors.is_empty(), "multi-owner variants should not be errors: {:?}", errors);
    }

    #[test]
    fn cross_system_three_way_collision_lists_all_owners() {
        let mut program = make_program(vec![
            make_system("A", vec![make_enum("Ability", &["STR"])]),
            make_system("B", vec![make_enum("Ability", &["DEX"])]),
            make_system("C", vec![make_enum("Ability", &["CON"])]),
        ]);
        let file_systems = vec![FileSystemInfo {
            system_names: vec!["A".into(), "B".into(), "C".into()],
            use_decls: vec![],
        }];

        let (_map, diags) = resolve_modules(&mut program, &file_systems);
        let errors: Vec<_> = diags.iter().filter(|d| d.severity == Severity::Error).collect();
        assert_eq!(errors.len(), 1);
        let msg = &errors[0].message;
        assert!(msg.contains("\"A\""), "should mention system A: {}", msg);
        assert!(msg.contains("\"B\""), "should mention system B: {}", msg);
        assert!(msg.contains("\"C\""), "should mention system C: {}", msg);
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
                span: Span::new(FileId(0), 0, 7),
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
                span: Span::new(FileId(0), 0, 4),
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
                UseDecl { path: "A".into(), alias: Some("X".into()), span: Span::new(FileId(0), 0, 10) },
                UseDecl { path: "B".into(), alias: Some("X".into()), span: Span::new(FileId(0), 20, 30) },
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
                    UseDecl { path: "A".into(), alias: Some("X".into()), span: Span::new(FileId(0), 0, 10) },
                ],
            },
            FileSystemInfo {
                system_names: vec!["Main".into()],
                use_decls: vec![
                    UseDecl { path: "A".into(), alias: Some("X".into()), span: Span::new(FileId(0), 50, 60) },
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
                span: Span::new(FileId(0), 0, 10),
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
                    span: Span::new(FileId(0), 0, 5),
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
                span: Span::new(FileId(0), 0, 10),
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
                span: Span::new(FileId(0), 0, 10),
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
                UseDecl { path: "A".into(), alias: None, span: Span::new(FileId(0), 0, 5) },
                UseDecl { path: "B".into(), alias: Some("Foo".into()), span: Span::new(FileId(0), 10, 25) },
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
                UseDecl { path: "A".into(), alias: None, span: Span::new(FileId(0), 0, 5) },
                UseDecl { path: "B".into(), alias: Some("fire".into()), span: Span::new(FileId(0), 10, 25) },
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
                UseDecl { path: "A".into(), alias: None, span: Span::new(FileId(0), 0, 5) },
                UseDecl { path: "B".into(), alias: Some("Stunned".into()), span: Span::new(FileId(0), 10, 25) },
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
                span: Span::new(FileId(0), 0, 10),
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
                UseDecl { path: "A".into(), alias: None, span: Span::new(FileId(0), 0, 5) },
                UseDecl { path: "B".into(), alias: Some("Bsys".into()), span: Span::new(FileId(0), 10, 25) },
            ],
        }];

        let (_map, diags) = resolve_modules(&mut program, &file_systems);
        let errors: Vec<_> = diags.iter().filter(|d| d.severity == Severity::Error).collect();
        assert!(errors.is_empty(), "no conflicts expected: {:?}", errors);
    }

    // ── Load order independence tests ──────────────────────────────────

    /// Helper: run resolve_modules with the given file_systems and return
    /// whether any errors were produced (ignoring message text / ordering).
    fn has_errors(program: &mut Program, file_systems: &[FileSystemInfo]) -> bool {
        let (_map, diags) = resolve_modules(program, file_systems);
        diags.iter().any(|d| d.severity == Severity::Error)
    }

    #[test]
    fn alias_shadow_cross_file_order_independent() {
        // Regression: alias shadow check must detect conflict regardless of
        // which file's use-declaration is processed first.
        //
        // File A: use "Lib" as foo  +  system "Main" { ... }
        // File B: use "Utils"       +  system "Main" { ... }
        // Utils exports function "foo" → alias "foo" shadows it.
        let program_items = vec![
            make_system("Lib", vec![make_derive("bar")]),
            make_system("Utils", vec![make_derive("foo")]),
            make_system("Main", vec![make_derive("main_fn")]),
        ];

        // Order A: alias file first, bare import second
        let mut p1 = make_program(program_items.clone());
        let fs_order_a = vec![
            FileSystemInfo {
                system_names: vec!["Main".into()],
                use_decls: vec![UseDecl {
                    path: "Lib".into(),
                    alias: Some("foo".into()),
                    span: Span::new(FileId(0), 0, 10),
                }],
            },
            FileSystemInfo {
                system_names: vec!["Main".into()],
                use_decls: vec![UseDecl {
                    path: "Utils".into(),
                    alias: None,
                    span: Span::new(FileId(1), 0, 10),
                }],
            },
        ];
        let has_a = has_errors(&mut p1, &fs_order_a);

        // Order B: bare import first, alias file second
        let mut p2 = make_program(program_items.clone());
        let fs_order_b = vec![
            FileSystemInfo {
                system_names: vec!["Main".into()],
                use_decls: vec![UseDecl {
                    path: "Utils".into(),
                    alias: None,
                    span: Span::new(FileId(0), 0, 10),
                }],
            },
            FileSystemInfo {
                system_names: vec!["Main".into()],
                use_decls: vec![UseDecl {
                    path: "Lib".into(),
                    alias: Some("foo".into()),
                    span: Span::new(FileId(1), 0, 10),
                }],
            },
        ];
        let has_b = has_errors(&mut p2, &fs_order_b);

        assert!(has_a, "order A (alias first) should detect shadow");
        assert!(has_b, "order B (alias second) should detect shadow");
    }

    #[test]
    fn alias_shadow_cross_file_both_aliased() {
        // Both imports are aliased and come from different files.
        // use "A" as foo  (file 1)  — A has no "foo"
        // use "B" as bar  (file 2)  — B exports "foo"
        // Alias "foo" shadows B's function "foo".
        let program_items = vec![
            make_system("A", vec![make_derive("alpha")]),
            make_system("B", vec![make_derive("foo")]),
            make_system("Main", vec![make_derive("main_fn")]),
        ];

        // Order: alias "foo" first, alias "bar" second
        let mut p1 = make_program(program_items.clone());
        let fs1 = vec![
            FileSystemInfo {
                system_names: vec!["Main".into()],
                use_decls: vec![UseDecl {
                    path: "A".into(),
                    alias: Some("foo".into()),
                    span: Span::new(FileId(0), 0, 10),
                }],
            },
            FileSystemInfo {
                system_names: vec!["Main".into()],
                use_decls: vec![UseDecl {
                    path: "B".into(),
                    alias: Some("bar".into()),
                    span: Span::new(FileId(1), 0, 10),
                }],
            },
        ];
        let has1 = has_errors(&mut p1, &fs1);

        // Reversed order
        let mut p2 = make_program(program_items.clone());
        let fs2 = vec![
            FileSystemInfo {
                system_names: vec!["Main".into()],
                use_decls: vec![UseDecl {
                    path: "B".into(),
                    alias: Some("bar".into()),
                    span: Span::new(FileId(0), 0, 10),
                }],
            },
            FileSystemInfo {
                system_names: vec!["Main".into()],
                use_decls: vec![UseDecl {
                    path: "A".into(),
                    alias: Some("foo".into()),
                    span: Span::new(FileId(1), 0, 10),
                }],
            },
        ];
        let has2 = has_errors(&mut p2, &fs2);

        assert!(has1, "order 1 should detect alias 'foo' shadows B's function");
        assert!(has2, "order 2 should detect alias 'foo' shadows B's function");
    }

    #[test]
    fn alias_shadow_variant_cross_file_order_independent() {
        // Alias shadows an enum variant from another imported system,
        // regardless of file order.
        let program_items = vec![
            make_system("Lib", vec![make_derive("bar")]),
            make_system("Types", vec![make_enum("DamageType", &["fire", "cold"])]),
            make_system("Main", vec![make_derive("main_fn")]),
        ];

        let make_fs = |alias_first: bool| -> Vec<FileSystemInfo> {
            let alias_file = FileSystemInfo {
                system_names: vec!["Main".into()],
                use_decls: vec![UseDecl {
                    path: "Lib".into(),
                    alias: Some("fire".into()),
                    span: Span::new(FileId(0), 0, 10),
                }],
            };
            let bare_file = FileSystemInfo {
                system_names: vec!["Main".into()],
                use_decls: vec![UseDecl {
                    path: "Types".into(),
                    alias: None,
                    span: Span::new(FileId(1), 0, 10),
                }],
            };
            if alias_first {
                vec![alias_file, bare_file]
            } else {
                vec![bare_file, alias_file]
            }
        };

        let mut p1 = make_program(program_items.clone());
        let mut p2 = make_program(program_items.clone());
        assert!(has_errors(&mut p1, &make_fs(true)), "alias first: should detect shadow");
        assert!(has_errors(&mut p2, &make_fs(false)), "alias second: should detect shadow");
    }

    #[test]
    fn collision_detection_both_system_orderings() {
        // Hazard: detect_cross_system_collisions iterates a HashMap.
        // This test ensures collision is detected regardless of which
        // system is iterated first (by testing both program orderings).
        let items_ab = vec![
            make_system("Alpha", vec![make_enum("Color", &["red"])]),
            make_system("Beta", vec![make_enum("Color", &["blue"])]),
        ];
        let items_ba = vec![
            make_system("Beta", vec![make_enum("Color", &["blue"])]),
            make_system("Alpha", vec![make_enum("Color", &["red"])]),
        ];

        let mut p1 = make_program(items_ab);
        let mut p2 = make_program(items_ba);
        let fs = vec![FileSystemInfo {
            system_names: vec!["Alpha".into(), "Beta".into()],
            use_decls: vec![],
        }];

        assert!(has_errors(&mut p1, &fs), "A-then-B ordering should detect collision");
        assert!(has_errors(&mut p2, &fs), "B-then-A ordering should detect collision");
    }

    #[test]
    fn collision_detection_across_files_order_independent() {
        // Systems defined in separate files — collision must fire
        // regardless of which file comes first.
        let items = vec![
            make_system("X", vec![make_derive("shared_fn")]),
            make_system("Y", vec![make_derive("shared_fn")]),
        ];

        let mut p1 = make_program(items.clone());
        let fs_xy = vec![
            FileSystemInfo { system_names: vec!["X".into()], use_decls: vec![] },
            FileSystemInfo { system_names: vec!["Y".into()], use_decls: vec![] },
        ];
        let mut p2 = make_program(items.clone());
        let fs_yx = vec![fs_xy[1].clone(), fs_xy[0].clone()];

        assert!(has_errors(&mut p1, &fs_xy), "X-first should detect function collision");
        assert!(has_errors(&mut p2, &fs_yx), "Y-first should detect function collision");
    }

    #[test]
    fn merged_system_file_order_collects_all_decls() {
        // Hazard: if the system registry iterates files in order and
        // short-circuits, a later file's declarations could be missed.
        // System "Core" is split across two files. Verify both orderings
        // produce the same SystemInfo.
        let items = vec![
            make_system("Core", vec![make_enum("Ability", &["STR", "DEX"])]),
            make_system("Core", vec![make_derive("modifier")]),
        ];

        let mut p1 = make_program(items.clone());
        let fs1 = vec![
            FileSystemInfo { system_names: vec!["Core".into()], use_decls: vec![] },
            FileSystemInfo { system_names: vec!["Core".into()], use_decls: vec![] },
        ];
        let (map1, _) = resolve_modules(&mut p1, &fs1);

        let mut p2 = make_program(vec![items[1].clone(), items[0].clone()]);
        let fs2 = vec![fs1[1].clone(), fs1[0].clone()];
        let (map2, _) = resolve_modules(&mut p2, &fs2);

        let core1 = map1.systems.get("Core").unwrap();
        let core2 = map2.systems.get("Core").unwrap();

        assert!(core1.types.contains("Ability") && core1.functions.contains("modifier"),
            "order 1 should have both type and function");
        assert!(core2.types.contains("Ability") && core2.functions.contains("modifier"),
            "order 2 should have both type and function");
        assert_eq!(core1.variants, core2.variants,
            "variants should be identical regardless of file order");
    }

    #[test]
    fn visibility_union_order_independent() {
        // Hazard: if visibility computation short-circuits or depends on
        // import processing order, some names could be invisible.
        // System "Main" imports "Lib" (types) and "Utils" (functions)
        // from separate files.
        let items = vec![
            make_system("Lib", vec![make_enum("Color", &["red", "blue"])]),
            make_system("Utils", vec![make_derive("helper")]),
            make_system("Main", vec![make_derive("main_fn")]),
        ];

        let make_fs = |lib_first: bool| -> Vec<FileSystemInfo> {
            let lib_file = FileSystemInfo {
                system_names: vec!["Main".into()],
                use_decls: vec![UseDecl {
                    path: "Lib".into(),
                    alias: None,
                    span: Span::new(FileId(0), 0, 10),
                }],
            };
            let utils_file = FileSystemInfo {
                system_names: vec!["Main".into()],
                use_decls: vec![UseDecl {
                    path: "Utils".into(),
                    alias: None,
                    span: Span::new(FileId(1), 0, 10),
                }],
            };
            if lib_first {
                vec![lib_file, utils_file]
            } else {
                vec![utils_file, lib_file]
            }
        };

        // Both orderings must produce the same visibility
        let mut p1 = make_program(items.clone());
        let (map1, d1) = resolve_modules(&mut p1, &make_fs(true));
        assert!(!d1.iter().any(|d| d.severity == Severity::Error), "lib-first: {:?}", d1);

        let mut p2 = make_program(items.clone());
        let (map2, d2) = resolve_modules(&mut p2, &make_fs(false));
        assert!(!d2.iter().any(|d| d.severity == Severity::Error), "utils-first: {:?}", d2);

        let main1 = map1.systems.get("Main").unwrap();
        let main2 = map2.systems.get("Main").unwrap();
        assert_eq!(main1.imports.len(), main2.imports.len(),
            "import count should be the same regardless of file order");
    }

    #[test]
    fn no_false_positive_when_alias_is_clean() {
        // Alias doesn't match any imported name — no error regardless of order.
        let program_items = vec![
            make_system("Lib", vec![make_derive("bar")]),
            make_system("Utils", vec![make_derive("baz")]),
            make_system("Main", vec![make_derive("main_fn")]),
        ];

        let mut p1 = make_program(program_items.clone());
        let fs1 = vec![
            FileSystemInfo {
                system_names: vec!["Main".into()],
                use_decls: vec![UseDecl {
                    path: "Lib".into(),
                    alias: Some("L".into()),
                    span: Span::new(FileId(0), 0, 10),
                }],
            },
            FileSystemInfo {
                system_names: vec!["Main".into()],
                use_decls: vec![UseDecl {
                    path: "Utils".into(),
                    alias: None,
                    span: Span::new(FileId(1), 0, 10),
                }],
            },
        ];
        assert!(!has_errors(&mut p1, &fs1), "clean alias should not produce errors");

        // Reversed
        let mut p2 = make_program(program_items.clone());
        let fs2 = vec![fs1[1].clone(), fs1[0].clone()];
        assert!(!has_errors(&mut p2, &fs2), "reversed clean alias should not produce errors");
    }
}
