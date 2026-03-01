use ttrpg_ast::ast::{
    ArmBody, DeclKind, ElseBranch, ExprKind, FieldDef, ForIterable, GuardKind, TopLevel, TypeExpr,
};
use ttrpg_ast::{Name, Spanned};

use crate::effect::FieldPathSegment;
use crate::state::EntityRef;
use crate::value::Value;
use crate::Env;

use super::dispatch::eval_expr;

// ── Helpers ────────────────────────────────────────────────────

/// Returns a human-readable type name for error messages.
pub(crate) fn type_name(val: &Value) -> &'static str {
    match val {
        Value::Int(_) => "Int",
        Value::Float(_) => "Float",
        Value::Bool(_) => "Bool",
        Value::Str(_) => "String",
        Value::None => "None",
        Value::DiceExpr(_) => "DiceExpr",
        Value::RollResult(_) => "RollResult",
        Value::List(_) => "List",
        Value::Set(_) => "Set",
        Value::Map(_) => "Map",
        Value::Option(_) => "Option",
        Value::Struct { .. } => "Struct",
        Value::Entity(_) => "Entity",
        Value::EnumVariant { .. } => "EnumVariant",
        Value::Position(_) => "Position",
        Value::Condition { .. } => "Condition",
        Value::Invocation(_) => "Invocation",
        Value::EnumNamespace(_) => "EnumNamespace",
        Value::ModuleAlias(_) => "ModuleAlias",
    }
}

/// Walk `program.items` to find optional group field definitions by name,
/// scoped to a specific entity type.
pub(super) fn find_optional_group_fields<'a>(
    env: &'a Env,
    entity_type: Option<&str>,
    group_name: &str,
) -> Option<&'a [FieldDef]> {
    let entity_type = entity_type?;
    for item in &env.interp.program.items {
        if let TopLevel::System(system) = &item.node {
            for decl in &system.decls {
                if let DeclKind::Entity(entity_decl) = &decl.node {
                    if entity_decl.name == entity_type {
                        for group in &entity_decl.optional_groups {
                            if group.name == group_name {
                                if group.is_external_ref {
                                    return find_group_decl_fields(env, group_name);
                                }
                                return Some(group.fields.as_slice());
                            }
                        }
                    }
                }
            }
        }
    }
    None
}

pub(super) fn find_group_decl_fields<'a>(env: &'a Env, group_name: &str) -> Option<&'a [FieldDef]> {
    for item in &env.interp.program.items {
        if let TopLevel::System(system) = &item.node {
            for decl in &system.decls {
                if let DeclKind::Group(group_decl) = &decl.node {
                    if group_decl.name == group_name {
                        return Some(group_decl.fields.as_slice());
                    }
                }
            }
        }
    }
    None
}

/// Look up the `FieldDef` for the first field segment of a mutation path on an entity.
///
/// Handles both base fields and fields inside optional groups. For a path like
/// `[Field("Spellcasting"), Field("spell_slots"), Index(3)]`, this returns the
/// `FieldDef` for `spell_slots` inside the `Spellcasting` group and the remaining
/// path `[Index(3)]`.
fn find_field_def_and_remaining<'a>(
    env: &'a Env,
    entity_type: &str,
    path: &[FieldPathSegment],
) -> Option<(&'a FieldDef, usize)> {
    if path.is_empty() {
        return None;
    }
    let first_name = match &path[0] {
        FieldPathSegment::Field(name) => name,
        _ => return None,
    };

    for item in &env.interp.program.items {
        if let TopLevel::System(system) = &item.node {
            for decl in &system.decls {
                if let DeclKind::Entity(entity_decl) = &decl.node {
                    if entity_decl.name != entity_type {
                        continue;
                    }
                    // Check base fields
                    if let Some(field) = entity_decl.fields.iter().find(|f| f.name == *first_name) {
                        return Some((field, 1));
                    }
                    // Check if first segment is a group name
                    if let Some(group) = entity_decl
                        .optional_groups
                        .iter()
                        .find(|g| g.name == *first_name)
                    {
                        let group_fields: &[FieldDef] = if group.is_external_ref {
                            match find_group_decl_fields(env, first_name) {
                                Some(fields) => fields,
                                None => return None,
                            }
                        } else {
                            group.fields.as_slice()
                        };
                        // Next segment should be a field within the group
                        if let Some(FieldPathSegment::Field(field_name)) = path.get(1) {
                            if let Some(field) = group_fields.iter().find(|f| f.name == *field_name)
                            {
                                return Some((field, 2));
                            }
                        }
                    }
                }
            }
        }
    }
    None
}

/// Walk remaining path segments through a `TypeExpr` to find resource bounds at the leaf.
///
/// For `map<int, resource(0..=9)>` with path `[Index(3)]`, this returns the resource
/// bounds `(0, 9)` expressions. For non-resource leaves, returns `None`.
///
/// Also traverses `Named` struct types by looking up their field definitions in the
/// program, so paths like `stats.spell_slots[1]` resolve correctly when `stats` is a
/// user-defined struct containing a resource map.
fn extract_resource_bounds_from_type<'a>(
    ty: &'a TypeExpr,
    path: &[FieldPathSegment],
    items: &'a [Spanned<TopLevel>],
) -> Option<(&'a Spanned<ExprKind>, &'a Spanned<ExprKind>)> {
    if path.is_empty() {
        if let TypeExpr::Resource(min, max) = ty {
            return Some((min, max));
        }
        return None;
    }
    match (&path[0], ty) {
        (FieldPathSegment::Index(_), TypeExpr::Map(_, val_type)) => {
            extract_resource_bounds_from_type(&val_type.node, &path[1..], items)
        }
        (FieldPathSegment::Index(_), TypeExpr::List(elem_type)) => {
            extract_resource_bounds_from_type(&elem_type.node, &path[1..], items)
        }
        (FieldPathSegment::Field(field_name), TypeExpr::Named(struct_name)) => {
            // Look up the struct declaration and find the field's type
            let field = find_struct_field(items, struct_name, field_name)?;
            extract_resource_bounds_from_type(&field.ty.node, &path[1..], items)
        }
        _ => None,
    }
}

/// Collect `(field_name, default_expr)` pairs for all fields with defaults in a struct.
pub(super) fn find_struct_defaults(env: &Env, struct_name: &str) -> Vec<(Name, Spanned<ExprKind>)> {
    for item in &env.interp.program.items {
        if let TopLevel::System(system) = &item.node {
            for decl in &system.decls {
                let fields = match &decl.node {
                    DeclKind::Struct(s) if s.name == struct_name => &s.fields,
                    DeclKind::Unit(u) if u.name == struct_name => &u.fields,
                    _ => continue,
                };
                return fields
                    .iter()
                    .filter_map(|f| f.default.as_ref().map(|d| (f.name.clone(), d.clone())))
                    .collect();
            }
        }
    }
    Vec::new()
}

/// Find a field definition within a named struct declaration.
fn find_struct_field<'a>(
    items: &'a [Spanned<TopLevel>],
    struct_name: &str,
    field_name: &str,
) -> Option<&'a FieldDef> {
    for item in items {
        if let TopLevel::System(system) = &item.node {
            for decl in &system.decls {
                if let DeclKind::Struct(s) = &decl.node {
                    if s.name == struct_name {
                        return s.fields.iter().find(|f| f.name == field_name);
                    }
                }
            }
        }
    }
    None
}

/// Collect all identifier names referenced in an expression tree.
fn collect_idents(expr: &Spanned<ExprKind>, out: &mut Vec<Name>) {
    match &expr.node {
        ExprKind::Ident(name) => out.push(name.clone()),
        ExprKind::UnaryOp { operand, .. } => collect_idents(operand, out),
        ExprKind::BinOp { lhs, rhs, .. } => {
            collect_idents(lhs, out);
            collect_idents(rhs, out);
        }
        ExprKind::FieldAccess { object, .. } => collect_idents(object, out),
        ExprKind::Index { object, index } => {
            collect_idents(object, out);
            collect_idents(index, out);
        }
        ExprKind::Call { callee, args } => {
            collect_idents(callee, out);
            for arg in args {
                collect_idents(&arg.value, out);
            }
        }
        ExprKind::Paren(inner) => collect_idents(inner, out),
        ExprKind::ListLit(elems) => {
            for elem in elems {
                collect_idents(elem, out);
            }
        }
        ExprKind::MapLit(entries) => {
            for (key, value) in entries {
                collect_idents(key, out);
                collect_idents(value, out);
            }
        }
        ExprKind::If {
            condition,
            then_block,
            else_branch,
        } => {
            collect_idents(condition, out);
            collect_idents_block(then_block, out);
            if let Some(eb) = else_branch {
                match eb {
                    ElseBranch::Block(block) => collect_idents_block(block, out),
                    ElseBranch::If(expr) => collect_idents(expr, out),
                }
            }
        }
        ExprKind::IfLet {
            scrutinee,
            then_block,
            else_branch,
            ..
        } => {
            collect_idents(scrutinee, out);
            collect_idents_block(then_block, out);
            if let Some(eb) = else_branch {
                match eb {
                    ElseBranch::Block(block) => collect_idents_block(block, out),
                    ElseBranch::If(expr) => collect_idents(expr, out),
                }
            }
        }
        ExprKind::PatternMatch { scrutinee, arms } => {
            collect_idents(scrutinee, out);
            for arm in arms {
                collect_idents_arm_body(&arm.body, out);
            }
        }
        ExprKind::GuardMatch { arms } => {
            for arm in arms {
                if let GuardKind::Expr(expr) = &arm.guard {
                    collect_idents(expr, out);
                }
                collect_idents_arm_body(&arm.body, out);
            }
        }
        ExprKind::StructLit { fields, base, .. } => {
            for field in fields {
                collect_idents(&field.value, out);
            }
            if let Some(base) = base {
                collect_idents(base, out);
            }
        }
        ExprKind::For { iterable, body, .. } => {
            match iterable {
                ForIterable::Collection(expr) => collect_idents(expr, out),
                ForIterable::Range { start, end, .. } => {
                    collect_idents(start, out);
                    collect_idents(end, out);
                }
            }
            collect_idents_block(body, out);
        }
        ExprKind::ListComprehension {
            element,
            iterable,
            filter,
            ..
        } => {
            match iterable {
                ForIterable::Collection(expr) => collect_idents(expr, out),
                ForIterable::Range { start, end, .. } => {
                    collect_idents(start, out);
                    collect_idents(end, out);
                }
            }
            collect_idents(element, out);
            if let Some(f) = filter {
                collect_idents(f, out);
            }
        }
        ExprKind::Has { entity, .. } => {
            collect_idents(entity, out);
        }
        _ => {}
    }
}

fn collect_idents_block(block: &ttrpg_ast::ast::Block, out: &mut Vec<Name>) {
    use ttrpg_ast::ast::StmtKind;
    for stmt in &block.node {
        match &stmt.node {
            StmtKind::Let { value, .. } => collect_idents(value, out),
            StmtKind::Assign { value, .. } => collect_idents(value, out),
            StmtKind::Expr(expr) => collect_idents(expr, out),
            StmtKind::Grant { entity, .. } => collect_idents(entity, out),
            StmtKind::Revoke { entity, .. } => collect_idents(entity, out),
            StmtKind::Emit { args, .. } => {
                for arg in args {
                    collect_idents(&arg.value, out);
                }
            }
        }
    }
}

fn collect_idents_arm_body(body: &ArmBody, out: &mut Vec<Name>) {
    match body {
        ArmBody::Expr(expr) => collect_idents(expr, out),
        ArmBody::Block(block) => collect_idents_block(block, out),
    }
}

/// Try to evaluate a resource bound expression to a Value.
///
/// First attempts normal expression evaluation (handles literals and in-scope vars).
/// If that fails, collects all identifiers from the expression, resolves any that are
/// entity fields, injects them into a temporary scope, and retries evaluation.
fn eval_bound_expr(
    env: &mut Env,
    entity: &EntityRef,
    expr: &Spanned<ExprKind>,
    group_prefix: &[FieldPathSegment],
) -> Option<Value> {
    // Try normal evaluation first (handles literals, in-scope variables, derives)
    if let Ok(val) = eval_expr(env, expr) {
        return Some(val);
    }
    // Collect identifiers and try to resolve them as entity fields
    let mut idents = Vec::new();
    collect_idents(expr, &mut idents);

    let mut bindings = Vec::new();
    for name in &idents {
        if env.lookup(name).is_none() {
            // First try reading the field at the group-qualified path
            // (e.g. CombatantCore.max_hp for a resource inside CombatantCore)
            let resolved = if !group_prefix.is_empty() {
                let mut full_path = group_prefix.to_vec();
                full_path.push(FieldPathSegment::Field(name.clone()));
                crate::adapter::read_at_path(env.state, entity, &full_path)
            } else {
                None
            };
            // Fall back to top-level field lookup
            let resolved = resolved.or_else(|| env.state.read_field(entity, name));
            if let Some(val) = resolved {
                bindings.push((name.clone(), val));
            }
        }
    }
    if bindings.is_empty() {
        return None;
    }

    // Push a temporary scope with entity field values and retry
    env.push_scope();
    for (name, val) in bindings {
        env.bind(name, val);
    }
    let result = eval_expr(env, expr).ok();
    env.pop_scope();
    result
}

/// Look up resource bounds for a mutation path on an entity.
///
/// Returns evaluated `(min, max)` Values if the leaf of the path is a resource type.
/// Clones bound expressions before evaluation to avoid borrow conflicts with `env`.
pub(super) fn resolve_resource_bounds(
    env: &mut Env,
    entity: &EntityRef,
    path: &[FieldPathSegment],
) -> Option<(Value, Value)> {
    let entity_type = env.state.entity_type_name(entity)?;
    // Look up the field def and extract resource bounds from the type expression.
    // Clone the bound expressions so we can release the borrow on env.interp.program
    // before calling eval_bound_expr (which needs &mut env).
    let (bound_exprs, group_prefix) = {
        let (field_def, consumed) = find_field_def_and_remaining(env, &entity_type, path)?;
        let remaining = &path[consumed..];
        let (min_expr, max_expr) = extract_resource_bounds_from_type(
            &field_def.ty.node,
            remaining,
            &env.interp.program.items,
        )?;
        // When the field is inside a group (consumed > 1), the first path
        // segment is the group name. Bound expressions reference sibling
        // fields within the same group, so we need to qualify lookups
        // with the group prefix.
        let prefix = if consumed > 1 { &path[..1] } else { &[] };
        ((min_expr.clone(), max_expr.clone()), prefix.to_vec())
    };
    let min_val = eval_bound_expr(env, entity, &bound_exprs.0, &group_prefix)?;
    let max_val = eval_bound_expr(env, entity, &bound_exprs.1, &group_prefix)?;
    Some((min_val, max_val))
}

pub(crate) fn resolve_resource_bounds_pub(
    env: &mut Env,
    entity: &EntityRef,
    path: &[FieldPathSegment],
) -> Option<(Value, Value)> {
    resolve_resource_bounds(env, entity, path)
}
