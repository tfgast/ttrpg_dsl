//! Include expansion: copies declarative clauses from source conditions
//! into conditions that use `include` directives.
//!
//! Runs after parsing and move lowering, before type-checking.
//! Replaces `ConditionClause::Include` variants with concrete
//! `Modify`/`Suppress`/`SuppressModify` clauses copied from the source.

use ttrpg_ast::Spanned;
use ttrpg_ast::ast::*;
use ttrpg_ast::diagnostic::Diagnostic;
use ttrpg_ast::name::Name;

/// Expand all `include` directives in condition declarations.
///
/// For each `ConditionClause::Include(inc)` found:
/// 1. Look up `inc.source_condition` in the program's condition index
/// 2. Filter source clauses by `inc.kind`
/// 3. Clone matching clauses, set `included_from`, remap receiver name, substitute params
/// 4. Replace the `Include` variant with the expanded clauses
///
/// Must be called after `build_index()` so `program.conditions` is populated.
pub fn expand_includes(mut program: Program, diags: &mut Vec<Diagnostic>) -> Program {
    // Collect all include directives with their expansion info.
    // We need to gather expansion data first, then mutate, to avoid borrow conflicts.
    struct Expansion {
        /// Index into program.items
        item_idx: usize,
        /// Index into system.decls
        decl_idx: usize,
        /// The condition's receiver_name (for remapping)
        child_receiver_name: Name,
        /// Clause index within the condition
        clause_idx: usize,
        /// The include directive
        include: IncludeClause,
    }

    let mut expansions: Vec<Expansion> = Vec::new();

    for (item_idx, item) in program.items.iter().enumerate() {
        if let TopLevel::System(system) = &item.node {
            for (decl_idx, decl) in system.decls.iter().enumerate() {
                if let DeclKind::Condition(c) = &decl.node {
                    for (clause_idx, clause) in c.clauses.iter().enumerate() {
                        if let ConditionClause::Include(inc) = clause {
                            expansions.push(Expansion {
                                item_idx,
                                decl_idx,
                                child_receiver_name: c.receiver_name.clone(),
                                clause_idx,
                                include: inc.clone(),
                            });
                        }
                    }
                }
            }
        }
    }

    if expansions.is_empty() {
        return program;
    }

    // Process expansions in reverse order so clause indices stay valid
    expansions.sort_by(|a, b| {
        a.item_idx
            .cmp(&b.item_idx)
            .then(a.decl_idx.cmp(&b.decl_idx))
            .then(a.clause_idx.cmp(&b.clause_idx))
            .reverse()
    });

    for exp in expansions {
        let inc = &exp.include;

        // Look up source condition
        let source_decl = match program.conditions.get(&inc.source_condition) {
            Some(d) => d.clone(),
            None => {
                diags.push(Diagnostic::error(
                    format!(
                        "include references unknown condition `{}`",
                        inc.source_condition
                    ),
                    inc.span,
                ));
                continue;
            }
        };

        // Build param substitution map: source_param_name -> IncludeArgValue
        let param_map: Vec<(&Name, &IncludeArgValue)> =
            inc.args.iter().map(|a| (&a.name, &a.value)).collect();

        // Filter source clauses by kind and clone them
        let mut new_clauses: Vec<ConditionClause> = Vec::new();
        for clause in &source_decl.clauses {
            match (&inc.kind, clause) {
                (IncludeKind::Modify, ConditionClause::Modify(m)) => {
                    let mut cloned = m.clone();
                    cloned.included_from = Some(inc.span);
                    remap_modify_receiver(
                        &mut cloned,
                        &source_decl.receiver_name,
                        &exp.child_receiver_name,
                    );
                    substitute_modify_params(&mut cloned, &source_decl.params, &param_map);
                    new_clauses.push(ConditionClause::Modify(cloned));
                }
                (IncludeKind::Suppress, ConditionClause::Suppress(s)) => {
                    let mut cloned = s.clone();
                    cloned.included_from = Some(inc.span);
                    remap_suppress_receiver(
                        &mut cloned,
                        &source_decl.receiver_name,
                        &exp.child_receiver_name,
                    );
                    substitute_suppress_params(&mut cloned, &source_decl.params, &param_map);
                    new_clauses.push(ConditionClause::Suppress(cloned));
                }
                (IncludeKind::SuppressModify, ConditionClause::SuppressModify(sm)) => {
                    let mut cloned = sm.clone();
                    cloned.included_from = Some(inc.span);
                    remap_suppress_modify_receiver(
                        &mut cloned,
                        &source_decl.receiver_name,
                        &exp.child_receiver_name,
                    );
                    substitute_suppress_modify_params(&mut cloned, &source_decl.params, &param_map);
                    new_clauses.push(ConditionClause::SuppressModify(cloned));
                }
                _ => {} // wrong kind, skip
            }
        }

        // Replace the Include clause with expanded clauses in the condition
        let system = match &mut program.items[exp.item_idx].node {
            TopLevel::System(s) => s,
            _ => continue,
        };
        let cond = match &mut system.decls[exp.decl_idx].node {
            DeclKind::Condition(c) => c,
            _ => continue,
        };
        cond.clauses.remove(exp.clause_idx);
        for (i, clause) in new_clauses.into_iter().enumerate() {
            cond.clauses.insert(exp.clause_idx + i, clause);
        }
    }

    // Rebuild index so ModifyClauseIds are assigned to expanded clauses
    program.build_index();
    program
}

// ── Receiver remapping ─────────────────────────────────────────

fn remap_modify_receiver(clause: &mut ModifyClause, source_name: &Name, child_name: &Name) {
    if source_name == child_name {
        return;
    }
    // Remap bindings that reference the source receiver
    for binding in &mut clause.bindings {
        remap_binding_expr(&mut binding.value, source_name, child_name);
    }
    // Remap body statements
    for stmt in &mut clause.body {
        remap_modify_stmt(stmt, source_name, child_name);
    }
}

fn remap_suppress_receiver(clause: &mut SuppressClause, source_name: &Name, child_name: &Name) {
    if source_name == child_name {
        return;
    }
    for binding in &mut clause.bindings {
        remap_binding_expr(&mut binding.value, source_name, child_name);
    }
}

fn remap_suppress_modify_receiver(
    clause: &mut SuppressModifyClause,
    source_name: &Name,
    child_name: &Name,
) {
    if source_name == child_name {
        return;
    }
    for binding in &mut clause.bindings {
        remap_binding_expr(&mut binding.value, source_name, child_name);
    }
}

fn remap_binding_expr(
    value: &mut Option<Spanned<ExprKind>>,
    source_name: &Name,
    child_name: &Name,
) {
    if let Some(expr) = value {
        remap_expr(&mut expr.node, source_name, child_name);
    }
}

fn remap_expr(expr: &mut ExprKind, source_name: &Name, child_name: &Name) {
    match expr {
        ExprKind::Ident(name) if name == source_name => {
            *name = child_name.clone();
        }
        ExprKind::FieldAccess { object, .. } => {
            remap_expr(&mut object.node, source_name, child_name);
        }
        ExprKind::Index { object, index } => {
            remap_expr(&mut object.node, source_name, child_name);
            remap_expr(&mut index.node, source_name, child_name);
        }
        ExprKind::Call { callee, args } => {
            remap_expr(&mut callee.node, source_name, child_name);
            for arg in args {
                remap_expr(&mut arg.value.node, source_name, child_name);
            }
        }
        ExprKind::BinOp { lhs, rhs, .. } => {
            remap_expr(&mut lhs.node, source_name, child_name);
            remap_expr(&mut rhs.node, source_name, child_name);
        }
        ExprKind::UnaryOp { operand, .. } => {
            remap_expr(&mut operand.node, source_name, child_name);
        }
        ExprKind::Paren(inner) => {
            remap_expr(&mut inner.node, source_name, child_name);
        }
        ExprKind::If {
            condition,
            then_block,
            else_branch,
        } => {
            remap_expr(&mut condition.node, source_name, child_name);
            remap_block(then_block, source_name, child_name);
            if let Some(ElseBranch::Block(b)) = else_branch {
                remap_block(b, source_name, child_name);
            } else if let Some(ElseBranch::If(e)) = else_branch {
                remap_expr(&mut e.node, source_name, child_name);
            }
        }
        _ => {}
    }
}

fn remap_block(block: &mut Block, source_name: &Name, child_name: &Name) {
    for stmt in &mut block.node {
        remap_stmt(&mut stmt.node, source_name, child_name);
    }
}

fn remap_stmt(stmt: &mut StmtKind, source_name: &Name, child_name: &Name) {
    match stmt {
        StmtKind::Let { value, .. } => {
            remap_expr(&mut value.node, source_name, child_name);
        }
        StmtKind::Assign { value, .. } => {
            remap_expr(&mut value.node, source_name, child_name);
        }
        StmtKind::Expr(e) => {
            remap_expr(&mut e.node, source_name, child_name);
        }
        _ => {}
    }
}

fn remap_modify_stmt(stmt: &mut ModifyStmt, source_name: &Name, child_name: &Name) {
    match stmt {
        ModifyStmt::Let { value, .. } => {
            remap_expr(&mut value.node, source_name, child_name);
        }
        ModifyStmt::ParamOverride { value, .. } => {
            remap_expr(&mut value.node, source_name, child_name);
        }
        ModifyStmt::ResultOverride { value, .. } => {
            remap_expr(&mut value.node, source_name, child_name);
        }
        ModifyStmt::If {
            condition,
            then_body,
            else_body,
            ..
        } => {
            remap_expr(&mut condition.node, source_name, child_name);
            for s in then_body {
                remap_modify_stmt(s, source_name, child_name);
            }
            if let Some(else_stmts) = else_body {
                for s in else_stmts {
                    remap_modify_stmt(s, source_name, child_name);
                }
            }
        }
        ModifyStmt::CostOverride { .. } => {}
    }
}

// ── Param substitution ─────────────────────────────────────────

fn substitute_modify_params(
    clause: &mut ModifyClause,
    source_params: &[Param],
    param_map: &[(&Name, &IncludeArgValue)],
) {
    let source_param_names: Vec<&Name> = source_params.iter().map(|p| &p.name).collect();
    for binding in &mut clause.bindings {
        substitute_binding_expr(&mut binding.value, &source_param_names, param_map);
    }
    for stmt in &mut clause.body {
        substitute_modify_stmt(stmt, &source_param_names, param_map);
    }
}

fn substitute_suppress_params(
    clause: &mut SuppressClause,
    source_params: &[Param],
    param_map: &[(&Name, &IncludeArgValue)],
) {
    let source_param_names: Vec<&Name> = source_params.iter().map(|p| &p.name).collect();
    for binding in &mut clause.bindings {
        substitute_binding_expr(&mut binding.value, &source_param_names, param_map);
    }
}

fn substitute_suppress_modify_params(
    clause: &mut SuppressModifyClause,
    source_params: &[Param],
    param_map: &[(&Name, &IncludeArgValue)],
) {
    let source_param_names: Vec<&Name> = source_params.iter().map(|p| &p.name).collect();
    for binding in &mut clause.bindings {
        substitute_binding_expr(&mut binding.value, &source_param_names, param_map);
    }
}

fn substitute_binding_expr(
    value: &mut Option<Spanned<ExprKind>>,
    source_param_names: &[&Name],
    param_map: &[(&Name, &IncludeArgValue)],
) {
    if let Some(expr) = value {
        substitute_expr(&mut expr.node, source_param_names, param_map);
    }
}

fn substitute_expr(
    expr: &mut ExprKind,
    source_param_names: &[&Name],
    param_map: &[(&Name, &IncludeArgValue)],
) {
    match expr {
        ExprKind::Ident(name) if source_param_names.contains(&&*name) => {
            // Find mapping
            if let Some((_, value)) = param_map.iter().find(|(n, _)| **n == *name) {
                match value {
                    IncludeArgValue::Name(new_name) => {
                        *name = new_name.clone();
                    }
                    IncludeArgValue::Literal(lit) => {
                        *expr = lit.clone();
                    }
                }
            }
            // If no mapping found, leave as-is (will use child's own param if named the same)
        }
        ExprKind::FieldAccess { object, .. } => {
            substitute_expr(&mut object.node, source_param_names, param_map);
        }
        ExprKind::Index { object, index } => {
            substitute_expr(&mut object.node, source_param_names, param_map);
            substitute_expr(&mut index.node, source_param_names, param_map);
        }
        ExprKind::Call { callee, args } => {
            substitute_expr(&mut callee.node, source_param_names, param_map);
            for arg in args {
                substitute_expr(&mut arg.value.node, source_param_names, param_map);
            }
        }
        ExprKind::BinOp { lhs, rhs, .. } => {
            substitute_expr(&mut lhs.node, source_param_names, param_map);
            substitute_expr(&mut rhs.node, source_param_names, param_map);
        }
        ExprKind::UnaryOp { operand, .. } => {
            substitute_expr(&mut operand.node, source_param_names, param_map);
        }
        ExprKind::Paren(inner) => {
            substitute_expr(&mut inner.node, source_param_names, param_map);
        }
        ExprKind::If {
            condition,
            then_block,
            else_branch,
            ..
        } => {
            substitute_expr(&mut condition.node, source_param_names, param_map);
            substitute_block(then_block, source_param_names, param_map);
            if let Some(ElseBranch::Block(b)) = else_branch {
                substitute_block(b, source_param_names, param_map);
            } else if let Some(ElseBranch::If(e)) = else_branch {
                substitute_expr(&mut e.node, source_param_names, param_map);
            }
        }
        _ => {}
    }
}

fn substitute_block(
    block: &mut Block,
    source_param_names: &[&Name],
    param_map: &[(&Name, &IncludeArgValue)],
) {
    for stmt in &mut block.node {
        substitute_stmt(&mut stmt.node, source_param_names, param_map);
    }
}

fn substitute_stmt(
    stmt: &mut StmtKind,
    source_param_names: &[&Name],
    param_map: &[(&Name, &IncludeArgValue)],
) {
    match stmt {
        StmtKind::Let { value, .. } => {
            substitute_expr(&mut value.node, source_param_names, param_map);
        }
        StmtKind::Assign { value, .. } => {
            substitute_expr(&mut value.node, source_param_names, param_map);
        }
        StmtKind::Expr(e) => {
            substitute_expr(&mut e.node, source_param_names, param_map);
        }
        _ => {}
    }
}

fn substitute_modify_stmt(
    stmt: &mut ModifyStmt,
    source_param_names: &[&Name],
    param_map: &[(&Name, &IncludeArgValue)],
) {
    match stmt {
        ModifyStmt::Let { value, .. } => {
            substitute_expr(&mut value.node, source_param_names, param_map);
        }
        ModifyStmt::ParamOverride { value, .. } => {
            substitute_expr(&mut value.node, source_param_names, param_map);
        }
        ModifyStmt::ResultOverride { value, .. } => {
            substitute_expr(&mut value.node, source_param_names, param_map);
        }
        ModifyStmt::If {
            condition,
            then_body,
            else_body,
            ..
        } => {
            substitute_expr(&mut condition.node, source_param_names, param_map);
            for s in then_body {
                substitute_modify_stmt(s, source_param_names, param_map);
            }
            if let Some(else_stmts) = else_body {
                for s in else_stmts {
                    substitute_modify_stmt(s, source_param_names, param_map);
                }
            }
        }
        ModifyStmt::CostOverride { .. } => {}
    }
}
