use super::*;

pub(super) fn advance_block(
    frame: &mut Frame,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    sp: &dyn StateProvider,
    eh: &mut dyn EffectHandler,
    tracker: &MutationTracker,
) -> Advance {
    let Frame::Block {
        stmts,
        index,
        result,
        expr_cache,
        awaiting_fn,
        awaiting_error,
    } = frame
    else {
        unreachable!()
    };

    // Handle error from a child frame dispatched via awaiting_fn.
    if let Some(err) = awaiting_error.take() {
        awaiting_fn.take();
        env.pop_scope();
        return Advance::Error(err);
    }

    // Handle completed child frame for a statement dispatched
    // via FunctionEval or ExprEval.
    if let Some(awaiting) = awaiting_fn.take() {
        let value = std::mem::replace(result, Value::Void);
        match awaiting {
            AwaitingFn::ExprStmt => {
                *result = value;
            }
            AwaitingFn::LetBinding { name } => {
                env.bind(name, value);
            }
            AwaitingFn::Assign { target, op, span } => {
                // RHS was evaluated by FunctionEval. Apply
                // the assignment via AssignContext, collecting
                // any mutation effects to yield.
                let rhs = value;
                let collected = {
                    let mut ctx = FrameAssignCtx {
                        env,
                        core,
                        state: sp,
                        handler: &mut *eh,
                        collected: Vec::new(),
                    };
                    if let Err(e) =
                        crate::eval::exec_assign_with_rhs(&mut ctx, &target, op, rhs, span)
                    {
                        env.pop_scope();
                        return Advance::Error(e);
                    }
                    ctx.collected
                };
                // Yield collected mutation effects via MutationYield.
                if let Some(effect) = collected.into_iter().next() {
                    *awaiting_fn = Some(AwaitingFn::AssignYield);
                    return Advance::Push(Frame::MutationYield {
                        effect,
                        pending: None,
                        span,
                    });
                }
            }
            AwaitingFn::AssignYield => {
                // MutationYield child completed — just advance.
            }
            AwaitingFn::Return => {
                env.return_value = Some(value.clone());
                env.pop_scope();
                return Advance::Pop(value);
            }
        }
        *index += 1;
        expr_cache.clear();
        if let Some(ret) = env.return_value.clone() {
            env.pop_scope();
            return Advance::Pop(ret);
        }
        return Advance::Continue;
    }

    // Push scope on first entry (before first statement).
    // Guard with expr_cache.is_empty() so we don't push a second scope when
    // re-entering after an expr_cache child (entity eval for WithBudget, etc.)
    // completes without advancing the statement index.
    if *index == 0 && expr_cache.is_empty() {
        env.push_scope();
    }

    // All statements processed.
    if *index >= stmts.len() {
        env.pop_scope();
        return Advance::Pop(result.clone());
    }

    // Check for early return (set by a previous statement in this block).
    // This must come AFTER the "all stmts processed" check so that blocks
    // with no statements always return Void, matching the recursive
    // evaluator's `eval_block` which only checks return_value inside the
    // statement loop (i.e., after at least one statement has run).
    // Only check return_value when we're not in the middle of an expr_cache
    // multi-step evaluation.  A `return` inside a nested expression (e.g. a
    // match arm block within a MapLit that is the entity expression of a
    // with_budget) sets return_value, but the recursive interpreter continues
    // evaluating the expression and only checks return_value after the full
    // statement completes.  Skipping the check when expr_cache is non-empty
    // matches that behaviour.
    if expr_cache.is_empty() {
        if let Some(ret) = env.return_value.clone() {
            env.pop_scope();
            return Advance::Pop(ret);
        }
    }

    // Evaluate the current statement.
    let stmt = stmts[*index].clone();

    // Record coverage hit for this statement.
    if let Some(ref cov) = core.coverage
        && !stmt.span.is_dummy()
    {
        cov.borrow_mut()
            .hit_spans
            .insert((stmt.span.file.0, stmt.span.start));
    }

    // ── Path-independent native dispatch ────────────────
    // These statements have no sub-expressions that could
    // yield, so they are dispatched directly without child frames.

    // Return(None): bare `return;` — no expression to evaluate.
    if let StmtKind::Return(None) = &stmt.node {
        env.return_value = Some(Value::Void);
        env.pop_scope();
        return Advance::Pop(Value::Void);
    }

    // WithCostPayer: eval entity via expr_cache, push CostPayerGuard.
    if let StmtKind::WithCostPayer {
        entity: ref entity_expr,
        body: ref body_block,
        ..
    } = stmt.node
    {
        if expr_cache.is_empty() {
            // Push ExprEval for entity expression; result goes to expr_cache.
            match compile_expr_to_frame(entity_expr, core) {
                Ok(frame) => return Advance::Push(frame),
                Err(e) => {
                    env.pop_scope();
                    return Advance::Error(e);
                }
            }
        }
        // Entity value cached — extract and push CostPayerGuard.
        let entity_val = expr_cache[0].clone();
        match entity_val {
            Value::Entity(payer) => {
                let prev = env.cost_payer;
                env.cost_payer = Some(payer);
                expr_cache.clear();
                *awaiting_fn = Some(AwaitingFn::ExprStmt);
                return Advance::Push(Frame::CostPayerGuard {
                    saved_payer: prev,
                    body: Some(body_block.clone()),
                    child_result: None,
                });
            }
            _ => {
                env.pop_scope();
                return Advance::Error(RuntimeError::with_span(
                    "with_cost_payer: expected entity value",
                    entity_expr.span,
                ));
            }
        }
    }

    // WithBudget: eval entity + budget fields via expr_cache, push BudgetGuard.
    if let StmtKind::WithBudget {
        entity: ref entity_expr,
        budget_fields: ref budget_field_exprs,
        body: ref body_stmts,
        span: wb_span,
    } = stmt.node
    {
        let needed = 1 + budget_field_exprs.len();
        if expr_cache.len() < needed {
            // Evaluate next expression: entity first, then budget fields.
            let next_expr = if expr_cache.is_empty() {
                entity_expr
            } else {
                &budget_field_exprs[expr_cache.len() - 1].1
            };
            match compile_expr_to_frame(next_expr, core) {
                Ok(frame) => return Advance::Push(frame),
                Err(e) => {
                    env.pop_scope();
                    return Advance::Error(e);
                }
            }
        }
        // All values cached — build BudgetGuard.
        let actor = match &expr_cache[0] {
            Value::Entity(r) => *r,
            _ => {
                env.pop_scope();
                return Advance::Error(RuntimeError::with_span(
                    "with_budget: expected entity value",
                    entity_expr.span,
                ));
            }
        };
        let mut budget = BTreeMap::new();
        for (i, (name, _)) in budget_field_exprs.iter().enumerate() {
            budget.insert(name.node.clone(), expr_cache[1 + i].clone());
        }
        let prev_budget = sp.read_turn_budget(&actor);
        expr_cache.clear();
        *awaiting_fn = Some(AwaitingFn::ExprStmt);
        return Advance::Push(Frame::BudgetGuard {
            actor,
            budget,
            saved_budget: prev_budget,
            body: Some(body_stmts.clone()),
            child_result: None,
            pending: None,
            phase: BudgetGuardPhase::Provision,
            span: wb_span,
        });
    }

    // WithBudgets: eval specs via expr_cache, push MultiBudgetGuard.
    if let StmtKind::WithBudgets {
        specs: ref specs_expr,
        body: ref body_stmts,
        span: wb_span,
        ..
    } = stmt.node
    {
        if expr_cache.is_empty() {
            match compile_expr_to_frame(specs_expr, core) {
                Ok(frame) => return Advance::Push(frame),
                Err(e) => {
                    env.pop_scope();
                    return Advance::Error(e);
                }
            }
        }
        // Specs value cached — parse and build MultiBudgetGuard.
        let spec_list = match &expr_cache[0] {
            Value::List(items) => items.clone(),
            _ => {
                env.pop_scope();
                return Advance::Error(RuntimeError::with_span(
                    "with_budgets: expected list of BudgetSpec",
                    specs_expr.span,
                ));
            }
        };
        let entries = match parse_budget_spec_entries(&spec_list, specs_expr.span) {
            Ok(e) => e,
            Err(e) => {
                env.pop_scope();
                return Advance::Error(e);
            }
        };
        let mut snapshots: Vec<(EntityRef, Option<BTreeMap<Name, Value>>)> =
            Vec::with_capacity(entries.len());
        for (actor, _) in &entries {
            snapshots.push((*actor, sp.read_turn_budget(actor)));
        }
        expr_cache.clear();
        *awaiting_fn = Some(AwaitingFn::ExprStmt);
        return Advance::Push(Frame::MultiBudgetGuard {
            entries,
            saved_budgets: snapshots,
            provision_index: 0,
            phase: MultiBudgetPhase::Provisioning,
            body: Some(body_stmts.clone()),
            child_result: None,
            pending: None,
            span: wb_span,
        });
    }

    // Grant: eval entity + field inits + defaults via expr_cache,
    // then push GrantRevokeGate.
    if let StmtKind::Grant {
        entity: ref entity_expr,
        group_name: ref gname,
        fields: ref field_inits,
    } = stmt.node
    {
        // Phase 1: entity expression.
        if expr_cache.is_empty() {
            match compile_expr_to_frame(entity_expr, core) {
                Ok(frame) => return Advance::Push(frame),
                Err(e) => {
                    env.pop_scope();
                    return Advance::Error(e);
                }
            }
        }
        // Phase 2: field init expressions.
        if expr_cache.len() < 1 + field_inits.len() {
            let idx = expr_cache.len() - 1;
            match compile_expr_to_frame(&field_inits[idx].value, core) {
                Ok(frame) => return Advance::Push(frame),
                Err(e) => {
                    env.pop_scope();
                    return Advance::Error(e);
                }
            }
        }
        // Phase 3: compute defaults list (needs entity_ref from cache[0]).
        let entity_ref = match &expr_cache[0] {
            Value::Entity(r) => *r,
            _ => {
                env.pop_scope();
                return Advance::Error(RuntimeError::with_span(
                    "grant: expected entity value",
                    entity_expr.span,
                ));
            }
        };
        let entity_type = sp.entity_type_name(&entity_ref);
        let defaults: Vec<_> = crate::eval::find_optional_group_fields_in(
            &core.program,
            entity_type.as_deref(),
            gname,
        )
        .into_iter()
        .flatten()
        .filter_map(|fd| {
            // Skip fields that have explicit inits.
            if field_inits.iter().any(|fi| fi.name == fd.name) {
                return None;
            }
            fd.default.clone().map(|d| (fd.name.clone(), d))
        })
        .collect();

        let total_needed = 1 + field_inits.len() + defaults.len();
        if expr_cache.len() < total_needed {
            let def_idx = expr_cache.len() - 1 - field_inits.len();
            match compile_expr_to_frame(&defaults[def_idx].1, core) {
                Ok(frame) => return Advance::Push(frame),
                Err(e) => {
                    env.pop_scope();
                    return Advance::Error(e);
                }
            }
        }
        // All values cached — build GrantGroup effect.
        let mut fields = BTreeMap::new();
        for (i, init) in field_inits.iter().enumerate() {
            fields.insert(init.name.clone(), expr_cache[1 + i].clone());
        }
        for (i, (name, _)) in defaults.iter().enumerate() {
            fields.insert(name.clone(), expr_cache[1 + field_inits.len() + i].clone());
        }
        let struct_val = Value::Struct {
            name: gname.clone(),
            fields,
        };
        let effect = Effect::GrantGroup {
            entity: entity_ref,
            group_name: gname.clone(),
            fields: struct_val,
        };
        expr_cache.clear();
        *awaiting_fn = Some(AwaitingFn::ExprStmt);
        return Advance::Push(Frame::GrantRevokeGate {
            effect,
            pending: None,
            span: stmt.span,
        });
    }

    // Revoke: eval entity via expr_cache, push GrantRevokeGate.
    if let StmtKind::Revoke {
        entity: ref entity_expr,
        group_name: ref gname,
    } = stmt.node
    {
        if expr_cache.is_empty() {
            match compile_expr_to_frame(entity_expr, core) {
                Ok(frame) => return Advance::Push(frame),
                Err(e) => {
                    env.pop_scope();
                    return Advance::Error(e);
                }
            }
        }
        let entity_ref = match &expr_cache[0] {
            Value::Entity(r) => *r,
            _ => {
                env.pop_scope();
                return Advance::Error(RuntimeError::with_span(
                    "revoke: expected entity value",
                    entity_expr.span,
                ));
            }
        };
        let effect = Effect::RevokeGroup {
            entity: entity_ref,
            group_name: gname.clone(),
        };
        expr_cache.clear();
        *awaiting_fn = Some(AwaitingFn::ExprStmt);
        return Advance::Push(Frame::GrantRevokeGate {
            effect,
            pending: None,
            span: stmt.span,
        });
    }

    // Frame-based dispatch: try specialized frames for
    // function calls, emit statements, and resumable expressions.
    match try_frame_dispatch_stmt(core, env, sp, &mut *eh, tracker, &stmt) {
        Ok(Some((fn_frame, awaiting))) => {
            *awaiting_fn = Some(awaiting);
            return Advance::Push(fn_frame);
        }
        Err(e) => {
            env.pop_scope();
            return Advance::Error(e);
        }
        Ok(None) => {} // fall through
    }

    // Intercept emit statements for frame-based dispatch.
    if let StmtKind::Emit {
        event_name: ref ev_name,
        args: ref emit_args,
        span: emit_span,
    } = stmt.node
    {
        let emit_frame = Frame::EmitEval {
            event_name: ev_name.clone(),
            args: emit_args.clone(),
            arg_index: 0,
            span: emit_span,
            phase: EmitEvalPhase::Args,
            param_map: BTreeMap::new(),
            all_fields: BTreeMap::new(),
            param_defaults: Vec::new(),
            field_defaults: Vec::new(),
            default_index: 0,
            saved_emit_depth: env.emit_depth,
            saved_lifecycle: env.in_lifecycle_block,
            scope_pushed: false,
            child_result: None,
        };
        // EmitEval produces Void; treat like an expr stmt.
        *awaiting_fn = Some(AwaitingFn::ExprStmt);
        return Advance::Push(emit_frame);
    }

    // Let/Assign/Expr with non-call expressions: compile to
    // ExprEval frame for step-based evaluation.
    if let Some((rhs_expr, awaiting)) = extract_resumable_expr(&stmt) {
        if let Some(work) = crate::expr_eval::compile_expr(&rhs_expr, &core.type_env, &core.program)
        {
            *awaiting_fn = Some(awaiting);
            return Advance::Push(Frame::ExprEval {
                work,
                operands: Vec::new(),
                pc: 0,
                child_result: None,
                scope_depth: 0,
            });
        }
        // compile_expr returned None — the expression contains
        // constructs that can't be compiled (e.g. unknown unit
        // suffix, entity spread, etc.).  Return a RuntimeError
        // instead of panicking so the step-based path matches the
        // recursive interpreter's error behaviour.
        env.pop_scope();
        return Advance::Error(RuntimeError::with_span(
            "expression could not be compiled for step-based evaluation",
            rhs_expr.span,
        ));
    }

    // All StmtKind variants are dispatched above:
    // - Return(None), WithCostPayer, WithBudget, WithBudgets,
    //   Grant, Revoke: native dispatch (path-independent)
    // - Expr/Let/Assign/Return(Some) with call: try_frame_dispatch_stmt
    // - Emit: EmitEval frame
    // - Expr/Let/Assign/Return(Some) non-call: extract_resumable_expr
    //
    // If we reach here, a new StmtKind variant was added without
    // a corresponding native dispatch path.
    {
        env.pop_scope();
        Advance::Error(RuntimeError::with_span(
            "async Block: undispatched statement variant \
             (missing native frame dispatch)",
            stmt.span,
        ))
    }
}

pub(super) fn advance_for_loop(
    frame: &mut Frame,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    _sp: &dyn StateProvider,
    _eh: &mut dyn EffectHandler,
    _tracker: &MutationTracker,
) -> Advance {
    let Frame::ForLoop {
        items,
        index,
        pattern,
        body,
        child_result,
    } = frame
    else {
        unreachable!()
    };

    // Handle completed child Block frame.
    if let Some(result) = child_result.take() {
        env.pop_scope();
        match result {
            Ok(_) => {
                // Check for early return.
                if env.return_value.is_some() {
                    return Advance::Pop(Value::Void);
                }
                *index += 1;
                return Advance::Continue;
            }
            Err(e) => return Advance::Error(e),
        }
    }

    // Iterate: find next matching item.
    while *index < items.len() {
        let item = &items[*index];
        let mut bindings = rustc_hash::FxHashMap::default();
        if crate::eval::match_pattern(&core.type_env, pattern, item, &mut bindings) {
            env.push_scope();
            for (name, val) in bindings {
                env.bind(name, val);
            }
            return Advance::Push(Frame::Block {
                stmts: body.clone(),
                index: 0,
                result: Value::Void,
                expr_cache: Vec::new(),
                awaiting_fn: None,
                awaiting_error: None,
            });
        }
        // Pattern didn't match — skip this item.
        *index += 1;
    }

    // All items processed.
    Advance::Pop(Value::Void)
}

pub(super) fn advance_list_comp(
    frame: &mut Frame,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    _sp: &dyn StateProvider,
    _eh: &mut dyn EffectHandler,
    _tracker: &MutationTracker,
) -> Advance {
    let Frame::ListComp {
        items,
        index,
        pattern,
        element,
        filter,
        collected,
        phase,
        span,
        child_result,
    } = frame
    else {
        unreachable!()
    };

    // Handle child frame result based on current phase.
    if let Some(result) = child_result.take() {
        match result {
            Err(e) => {
                env.pop_scope();
                return Advance::Error(e);
            }
            Ok(val) => match phase {
                ListCompPhase::FilterDone => {
                    match val {
                        Value::Bool(true) => {
                            // Filter passed — evaluate element expression.
                            *phase = ListCompPhase::ElementDone;
                            return compile_expr_push(element, core);
                        }
                        Value::Bool(false) => {
                            // Filter failed — skip item, pop scope.
                            env.pop_scope();
                            *index += 1;
                            *phase = ListCompPhase::TryMatch;
                            return Advance::Continue;
                        }
                        _ => {
                            env.pop_scope();
                            return Advance::Error(RuntimeError::with_span(
                                "list comprehension filter must be bool",
                                *span,
                            ));
                        }
                    }
                }
                ListCompPhase::ElementDone => {
                    collected.push(val);
                    env.pop_scope();
                    *index += 1;
                    *phase = ListCompPhase::TryMatch;
                    return Advance::Continue;
                }
                _ => {} // TryMatch doesn't have child results
            },
        }
    }

    // Iterate: find next matching item.
    while *index < items.len() {
        let item = &items[*index];
        let mut bindings = rustc_hash::FxHashMap::default();
        if crate::eval::match_pattern(&core.type_env, pattern, item, &mut bindings) {
            env.push_scope();
            for (name, val) in bindings {
                env.bind(name, val);
            }
            if let Some(filter_expr) = filter {
                // Evaluate filter expression.
                *phase = ListCompPhase::FilterDone;
                return compile_expr_push(filter_expr, core);
            }
            // No filter — evaluate element directly.
            *phase = ListCompPhase::ElementDone;
            return compile_expr_push(element, core);
        }
        // Pattern didn't match — skip.
        *index += 1;
    }

    // All items processed.
    let result = std::mem::take(collected);
    Advance::Pop(Value::List(result))
}

pub(super) fn advance_expr_entry(
    frame: &mut Frame,
    core: &RuntimeCore,
    _env: &mut ExecEnv,
    _sp: &dyn StateProvider,
    _eh: &mut dyn EffectHandler,
    _tracker: &MutationTracker,
) -> Advance {
    let Frame::ExprEntry { result, expr } = frame else {
        unreachable!()
    };

    if let Some(r) = result.take() {
        return match r {
            Ok(v) => Advance::Pop(v),
            Err(e) => Advance::Error(e),
        };
    }
    match expr.take() {
        Some(ref e) => compile_expr_push(e, core),
        None => Advance::Error(RuntimeError::new("ExprEntry frame has no expression")),
    }
}

pub(super) fn advance_fill_defaults(
    frame: &mut Frame,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    _sp: &dyn StateProvider,
    _eh: &mut dyn EffectHandler,
    _tracker: &MutationTracker,
) -> Advance {
    let Frame::FillDefaults {
        params,
        index,
        child_result,
    } = frame
    else {
        unreachable!()
    };

    // Handle child ExprEval result (default expr evaluated).
    if let Some(val) = child_result.take() {
        let param = &params[*index];
        env.bind(param.name.clone(), val);
        *index += 1;
        return Advance::Continue;
    }

    // All defaults resolved — pop.
    if *index >= params.len() {
        return Advance::Pop(Value::Void);
    }

    let param = &mut params[*index];

    if let Some(val) = param.provided_value.take() {
        // Already provided by the caller — just bind.
        env.bind(param.name.clone(), val);
        *index += 1;
        Advance::Continue
    } else if let Some(ref default_expr) = param.default_expr {
        // Push child frame to evaluate the default expression.
        compile_expr_push(default_expr, core)
    } else {
        // Missing required parameter.
        Advance::Error(RuntimeError::new(format!(
            "missing required argument '{}'",
            param.name
        )))
    }
}
