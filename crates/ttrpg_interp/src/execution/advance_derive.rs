use super::*;

pub(super) fn advance_binding_check(
    frame: &mut Frame,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    sp: &dyn StateProvider,
    _eh: &mut dyn EffectHandler,
    _tracker: &MutationTracker,
) -> Advance {
    let Frame::BindingCheck {
        bindings,
        bound_params,
        scope_bindings,
        scope_mode,
        index,
        child_result,
        scope_pushed,
    } = frame
    else {
        unreachable!()
    };

    // Helper: pop scope if Owned mode.
    let cleanup = |env: &mut ExecEnv, pushed: &mut bool, mode: BindingScopeMode| {
        if mode == BindingScopeMode::Owned && *pushed {
            env.pop_scope();
            *pushed = false;
        }
    };

    // Init: push scope for Owned mode on first entry.
    if *scope_mode == BindingScopeMode::Owned && !*scope_pushed {
        env.push_scope();
        for (name, val) in scope_bindings.iter() {
            env.bind(name.clone(), val.clone());
        }
        *scope_pushed = true;
    }

    // Handle child ExprEval result.
    if let Some(result) = child_result.take() {
        match result {
            Err(e) => {
                cleanup(env, scope_pushed, *scope_mode);
                return Advance::Error(e);
            }
            Ok(val) => {
                let binding = &bindings[*index];
                let param_val = bound_params
                    .iter()
                    .find(|(n, _)| *n == binding.name)
                    .map(|(_, v)| v);
                // param_val must exist — we checked before pushing ExprEval.
                if let Some(pv) = param_val {
                    if !crate::eval::value_eq(sp, pv, &val) {
                        cleanup(env, scope_pushed, *scope_mode);
                        return Advance::Pop(Value::Bool(false));
                    }
                }
                *index += 1;
                return Advance::Continue;
            }
        }
    }

    // All bindings checked — success.
    if *index >= bindings.len() {
        cleanup(env, scope_pushed, *scope_mode);
        return Advance::Pop(Value::Bool(true));
    }

    let binding = &bindings[*index];

    // Param lookup.
    let _param_val = match bound_params.iter().find(|(n, _)| *n == binding.name) {
        Some((_, val)) => val,
        None => {
            cleanup(env, scope_pushed, *scope_mode);
            return Advance::Pop(Value::Bool(false));
        }
    };

    // Wildcard binding (value == None): skip.
    let expr = match &binding.value {
        Some(expr) => expr,
        None => {
            *index += 1;
            return Advance::Continue;
        }
    };

    // Push ExprEval child for binding expression.
    compile_expr_push(expr, core)
}

pub(super) fn advance_derive_eval(
    frame: &mut Frame,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    sp: &dyn StateProvider,
    eh: &mut dyn EffectHandler,
    _tracker: &MutationTracker,
) -> Advance {
    let Frame::DeriveEval {
        name,
        args,
        is_table,
        base_value,
        phase,
        bound_args,
        modifiers,
        body,
        pending_modify_effect,
        phase1_params,
        phase2_result,
        fn_info_cache,
        pending,
        modify_walker,
        collect_state,
        pre_fill_params,
        should_apply_skipped,
        should_apply_result,
    } = frame
    else {
        unreachable!()
    };

    match phase {
        DeriveEvalPhase::Init => {
            if *is_table && pre_fill_params.is_none() {
                // Tables are pure lookups — dispatch directly
                // via AssignContext.
                // (Only when args are fully resolved; if pre_fill_params
                // is set, defaults need evaluation first via FillDefaults.)
                let n = name.clone();
                let a = args.clone();
                let mut ctx = FrameAssignCtx {
                    env,
                    core,
                    state: sp,
                    handler: &mut *eh,
                    collected: Vec::new(),
                };
                let result = crate::call::dispatch_table_exec(&mut ctx, &n, a, Span::dummy());
                return match result {
                    Ok(val) => Advance::Pop(val),
                    Err(e) => Advance::Error(e),
                };
            }

            // Use pre-built fill_params if available (from ExprWork
            // dispatch path with named-arg mapping already done).
            // When pre_fill_params is set, fn_info_cache and body
            // are already populated by the dispatch function.
            let fill_params = if let Some(pfp) = pre_fill_params.take() {
                args.clear();
                pfp
            } else {
                // Derive/mechanic: look up decl and type info.
                let fn_decl = match core
                    .program
                    .derives
                    .get(name.as_ref())
                    .or_else(|| core.program.mechanics.get(name.as_ref()))
                {
                    Some(d) => d.clone(),
                    None => {
                        return Advance::Error(RuntimeError::new(format!(
                            "undefined derive/mechanic '{name}'"
                        )));
                    }
                };

                let fi = match core.type_env.lookup_fn(name.as_ref()) {
                    Some(fi) => fi.clone(),
                    None => {
                        return Advance::Error(RuntimeError::new(format!(
                            "internal error: no type info for '{name}'"
                        )));
                    }
                };

                // ── Inline arg mapping (pure data transform) ────
                if args.len() > fi.params.len() {
                    return Advance::Error(RuntimeError::new(format!(
                        "too many arguments: '{}' takes {} params, got {}",
                        name,
                        fi.params.len(),
                        args.len()
                    )));
                }

                let mut fp: Vec<DefaultParam> = Vec::new();
                let arg_count = args.len();
                for (i, param) in fi.params.iter().enumerate() {
                    if i < arg_count {
                        fp.push(DefaultParam {
                            name: param.name.clone(),
                            provided_value: Some(args[i].clone()),
                            default_expr: None,
                        });
                    } else if param.has_default {
                        let default_expr = fn_decl
                            .params
                            .get(i)
                            .and_then(|p| p.default.as_ref())
                            .cloned();
                        fp.push(DefaultParam {
                            name: param.name.clone(),
                            provided_value: None,
                            default_expr,
                        });
                    } else {
                        return Advance::Error(RuntimeError::new(format!(
                            "missing required argument '{}' for '{}'",
                            param.name, name
                        )));
                    }
                }
                args.clear();

                *body = Some(fn_decl.body.clone());
                *fn_info_cache = Some(fi);
                fp
            };
            *phase = DeriveEvalPhase::DefaultsDone;

            // Push FillDefaults to resolve all params (provided +
            // defaults). It binds each into the current scope.
            if fill_params.iter().any(|p| p.default_expr.is_some()) {
                return Advance::Push(Frame::FillDefaults {
                    params: fill_params,
                    index: 0,
                    child_result: None,
                });
            }

            // No defaults — bind provided args directly and continue.
            let mapped: Vec<(Name, Value)> = fill_params
                .into_iter()
                .filter_map(|p| p.provided_value.map(|v| (p.name, v)))
                .collect();
            *bound_args = Some(mapped);
            Advance::Continue
        }

        DeriveEvalPhase::DefaultsDone => {
            // FillDefaults completed (or skipped). Collect bound
            // args from scope bindings if FillDefaults ran.
            let fi = fn_info_cache
                .as_ref()
                .expect("DeriveEval: fn_info_cache must be set by Init");

            // If bound_args isn't set, FillDefaults ran and bindings
            // are in the current scope. Collect them by param name.
            if bound_args.is_none() {
                let mut mapped = Vec::new();
                for param in &fi.params {
                    if let Some(val) = env.scopes.last().and_then(|s| s.bindings.get(&param.name)) {
                        mapped.push((param.name.clone(), val.clone()));
                    }
                }
                *bound_args = Some(mapped);
            }

            // Tables with defaults: now that args are resolved,
            // dispatch the table lookup directly (tables have no body).
            if *is_table {
                let resolved_args: Vec<Value> = bound_args
                    .as_ref()
                    .expect("bound_args populated during BindArgs phase")
                    .iter()
                    .map(|(_, v)| v.clone())
                    .collect();
                let n = name.clone();
                let mut ctx = FrameAssignCtx {
                    env,
                    core,
                    state: sp,
                    handler: &mut *eh,
                    collected: Vec::new(),
                };
                let result =
                    crate::call::dispatch_table_exec(&mut ctx, &n, resolved_args, Span::dummy());
                return match result {
                    Ok(val) => Advance::Pop(val),
                    Err(e) => Advance::Error(e),
                };
            }

            *phase = DeriveEvalPhase::CollectModifiers;
            Advance::Continue
        }

        DeriveEvalPhase::CollectModifiers => {
            use crate::effect::ModifySource;
            use std::collections::HashSet;
            use ttrpg_ast::ast::{ConditionClause, ModifyTarget};

            let fi = fn_info_cache
                .as_ref()
                .expect("DeriveEval: fn_info_cache must be set");
            let ba = bound_args.clone().unwrap_or_default();
            let fn_name = name.as_str();

            let mut collected_direct: Vec<(u64, OwnedModifier)> = Vec::new();
            let mut candidates: Vec<CollectCandidate> = Vec::new();
            let mut seen_condition_ids: HashSet<u64> = HashSet::new();
            let mut suppressions_list: Vec<NativeSuppressModify> = Vec::new();

            // 1. For each entity-typed param, query conditions.
            for (i, param_info) in fi.params.iter().enumerate() {
                if !param_info.ty.is_entity() {
                    continue;
                }
                let entity_ref = match &ba[i].1 {
                    Value::Entity(e) => *e,
                    _ => continue,
                };
                let conditions = match sp.read_conditions(&entity_ref) {
                    Some(c) => c,
                    None => {
                        return Advance::Error(RuntimeError::new(format!(
                            "read_conditions returned None for entity {entity_ref:?} — host state out of sync",
                        )));
                    }
                };
                let stacking_winners =
                    crate::pipeline::compute_stacking_winners(&conditions, &core.program);

                for condition in &conditions {
                    if !seen_condition_ids.insert(condition.id) {
                        continue;
                    }
                    if !stacking_winners.contains(&condition.id) {
                        continue;
                    }
                    let cond_decl = match core.program.conditions.get(condition.name.as_str()) {
                        Some(d) => d,
                        None => continue,
                    };

                    for clause_item in &cond_decl.clauses {
                        if let ConditionClause::SuppressModify(sm) = clause_item {
                            suppressions_list.push(NativeSuppressModify {
                                clause: sm.clone(),
                                bearer: Value::Entity(condition.bearer),
                                receiver_name: cond_decl.receiver_name.clone(),
                                condition_params: condition.params.clone(),
                            });
                            continue;
                        }

                        let clause = match clause_item {
                            ConditionClause::Modify(c) => c,
                            _ => continue,
                        };

                        match &clause.target {
                            ModifyTarget::Named(n) if n == fn_name => {}
                            ModifyTarget::Selector(_) => {
                                match core.type_env.selector_matches.get(&clause.id) {
                                    Some(set) if set.contains(fn_name) => {}
                                    _ => continue,
                                }
                            }
                            ModifyTarget::Cost(_) => continue,
                            _ => continue,
                        }

                        let owned_mod = owned_modifier_from_condition(condition, cond_decl, clause);

                        if clause.bindings.is_empty() {
                            collected_direct.push((condition.gained_at, owned_mod));
                        } else {
                            // Build scope bindings for Owned mode.
                            let mut scope_bindings =
                                build_condition_scope_bindings(cond_decl, condition);
                            for (pname, pval) in &ba {
                                scope_bindings.push((pname.clone(), pval.clone()));
                            }

                            let frame = Frame::BindingCheck {
                                bindings: clause.bindings.clone(),
                                bound_params: ba.clone(),
                                scope_bindings,
                                scope_mode: BindingScopeMode::Owned,
                                index: 0,
                                child_result: None,
                                scope_pushed: false,
                            };
                            candidates.push(CollectCandidate {
                                frame: Some(frame),
                                caller_scope: Vec::new(), // Owned mode
                                gained_at: condition.gained_at,
                                modifier: Some(owned_mod),
                            });
                        }
                    }
                }
            }

            let condition_count = candidates.len();

            // 2. Query enabled options and check their modify clauses.
            let mut enabled_options = sp.read_enabled_options();
            let option_order = &core.program.option_order;
            enabled_options.sort_by_key(|opt_name| {
                option_order
                    .iter()
                    .position(|o| *o == opt_name.as_str())
                    .unwrap_or(usize::MAX)
            });

            let mut option_mods_direct: Vec<OwnedModifier> = Vec::new();

            for opt_name in &enabled_options {
                let opt_decl = match core.program.options.get(opt_name.as_str()) {
                    Some(decl) => decl,
                    None => continue,
                };
                let clauses = match &opt_decl.when_enabled {
                    Some(clauses) => clauses,
                    None => continue,
                };

                for clause in clauses {
                    match &clause.target {
                        ModifyTarget::Named(n) if n == fn_name => {}
                        ModifyTarget::Selector(_) => {
                            match core.type_env.selector_matches.get(&clause.id) {
                                Some(set) if set.contains(fn_name) => {}
                                _ => continue,
                            }
                        }
                        ModifyTarget::Cost(_) => continue,
                        _ => continue,
                    }

                    let owned_mod = OwnedModifier {
                        source: ModifySource::Option(opt_name.clone()),
                        clause: clause.clone(),
                        bearer: None,
                        receiver_name: None,
                        condition_params: BTreeMap::new(),
                        condition_id: None,
                        condition_state_fields: BTreeMap::new(),
                        should_apply_body: None,
                    };

                    if clause.bindings.is_empty() {
                        option_mods_direct.push(owned_mod);
                    } else {
                        let scope_bindings: Vec<(Name, Value)> = ba.clone();
                        let frame = Frame::BindingCheck {
                            bindings: clause.bindings.clone(),
                            bound_params: ba.clone(),
                            scope_bindings,
                            scope_mode: BindingScopeMode::Owned,
                            index: 0,
                            child_result: None,
                            scope_pushed: false,
                        };
                        candidates.push(CollectCandidate {
                            frame: Some(frame),
                            caller_scope: Vec::new(), // Owned mode
                            gained_at: u64::MAX,      // sentinel for options
                            modifier: Some(owned_mod),
                        });
                    }
                }
            }

            if candidates.is_empty() && suppressions_list.is_empty() {
                // Fast path: no binding checks and no suppressions needed.
                collected_direct.sort_by_key(|(g, _)| *g);
                let mut result: Vec<OwnedModifier> =
                    collected_direct.into_iter().map(|(_, m)| m).collect();
                result.extend(option_mods_direct);
                if result.is_empty() {
                    *modifiers = result;
                    *phase = DeriveEvalPhase::PushBody;
                } else {
                    *phase1_params = bound_args.clone();
                    let has_should_apply = result.iter().any(|m| m.should_apply_body.is_some());
                    *modifiers = result;
                    *phase = if has_should_apply {
                        DeriveEvalPhase::ShouldApplyGate(0)
                    } else {
                        DeriveEvalPhase::ApplyPhase1(0)
                    };
                }
                Advance::Continue
            } else if candidates.is_empty() {
                // No binding checks but have suppressions — go to CollectDone.
                *collect_state = Some(Box::new(ModifierCollectState {
                    candidates: Vec::new(),
                    collected: collected_direct,
                    index: 0,
                    condition_count: 0,
                    option_modifiers: option_mods_direct,
                    suppressions: suppressions_list,
                    suppress_candidates: Vec::new(),
                    suppress_index: 0,
                    suppressed: HashSet::new(),
                    child_result: None,
                    scope_pushed: false,
                }));
                *phase = DeriveEvalPhase::CollectDone;
                Advance::Continue
            } else {
                *collect_state = Some(Box::new(ModifierCollectState {
                    candidates,
                    collected: collected_direct,
                    index: 0,
                    condition_count,
                    option_modifiers: option_mods_direct,
                    suppressions: suppressions_list,
                    suppress_candidates: Vec::new(),
                    suppress_index: 0,
                    suppressed: HashSet::new(),
                    child_result: None,
                    scope_pushed: false,
                }));
                *phase = DeriveEvalPhase::CollectCheck;
                Advance::Continue
            }
        }

        DeriveEvalPhase::CollectCheck => {
            let cs = collect_state
                .as_mut()
                .expect("DeriveEval::CollectCheck: collect_state must be set");

            match advance_collect_check(cs, env, true) {
                Err(e) => Advance::Error(e),
                Ok(CollectCheckAction::PushChild(frame)) => Advance::Push(*frame),
                Ok(CollectCheckAction::Done) => {
                    *phase = DeriveEvalPhase::CollectDone;
                    Advance::Continue
                }
            }
        }

        DeriveEvalPhase::CollectDone => {
            use ttrpg_ast::ast::SelectorPredicate;

            let cs = collect_state
                .as_mut()
                .expect("DeriveEval::CollectDone: collect_state must be set");

            // Sort condition modifiers by gained_at, build result.
            cs.collected.sort_by_key(|(g, _)| *g);
            let mut result: Vec<OwnedModifier> = std::mem::take(&mut cs.collected)
                .into_iter()
                .map(|(_, m)| m)
                .collect();
            result.extend(std::mem::take(&mut cs.option_modifiers));

            // Build suppression candidates.
            let fi = fn_info_cache
                .as_ref()
                .expect("DeriveEval: fn_info_cache must be set");
            let ba = bound_args.clone().unwrap_or_default();
            let mut immediately_suppressed: std::collections::HashSet<usize> =
                std::collections::HashSet::new();
            let mut suppress_candidates: Vec<SuppressCandidate> = Vec::new();

            for (mod_idx, modifier) in result.iter().enumerate() {
                for sup in &cs.suppressions {
                    let preds_match = sup.clause.predicates.iter().all(|pred| match pred {
                        SelectorPredicate::Tag(tag) => modifier.clause.tags.contains(tag),
                        SelectorPredicate::Returns(type_expr) => {
                            if let Some(fn_i) = core.type_env.functions.get(fi.name.as_str()) {
                                let resolved = core.type_env.resolve_type(type_expr);
                                fn_i.return_type == resolved
                            } else {
                                false
                            }
                        }
                        SelectorPredicate::HasParam { name: pname, ty } => {
                            fi.params.iter().any(|p| {
                                if p.name != *pname {
                                    return false;
                                }
                                if let Some(te) = ty {
                                    let resolved = core.type_env.resolve_type(te);
                                    p.ty == resolved
                                } else {
                                    true
                                }
                            })
                        }
                    });

                    if !preds_match {
                        continue;
                    }

                    if sup.clause.bindings.is_empty() {
                        immediately_suppressed.insert(mod_idx);
                        break; // no need to check other suppressions
                    }

                    // Build Caller-mode scope for this suppression.
                    let mut caller_scope = Vec::new();
                    caller_scope.push((sup.receiver_name.clone(), sup.bearer.clone()));
                    for (pname, pval) in &sup.condition_params {
                        caller_scope.push((pname.clone(), pval.clone()));
                    }

                    let frame = Frame::BindingCheck {
                        bindings: sup.clause.bindings.clone(),
                        bound_params: ba.clone(),
                        scope_bindings: Vec::new(),
                        scope_mode: BindingScopeMode::Caller,
                        index: 0,
                        child_result: None,
                        scope_pushed: false,
                    };

                    suppress_candidates.push(SuppressCandidate {
                        frame: Some(frame),
                        caller_scope,
                        modifier_index: mod_idx,
                    });
                }
            }

            // Apply immediate suppressions.
            if !immediately_suppressed.is_empty() {
                cs.suppressed = immediately_suppressed;
            }

            if suppress_candidates.is_empty() {
                // No binding-check suppressions needed — filter and finish.
                if !cs.suppressed.is_empty() {
                    let suppressed = &cs.suppressed;
                    result = result
                        .into_iter()
                        .enumerate()
                        .filter(|(i, _)| !suppressed.contains(i))
                        .map(|(_, m)| m)
                        .collect();
                }

                *collect_state = None;
                if result.is_empty() {
                    *modifiers = result;
                    *phase = DeriveEvalPhase::PushBody;
                } else {
                    *phase1_params = bound_args.clone();
                    let has_should_apply = result.iter().any(|m| m.should_apply_body.is_some());
                    *modifiers = result;
                    *phase = if has_should_apply {
                        DeriveEvalPhase::ShouldApplyGate(0)
                    } else {
                        DeriveEvalPhase::ApplyPhase1(0)
                    };
                }
                Advance::Continue
            } else {
                // Store result for later filtering, switch to SuppressCheck.
                cs.suppress_candidates = suppress_candidates;
                cs.suppress_index = 0;
                cs.child_result = None;
                cs.scope_pushed = false;
                // Store result temporarily in modifiers for later retrieval.
                *modifiers = result;
                *phase = DeriveEvalPhase::SuppressCheck;
                Advance::Continue
            }
        }

        DeriveEvalPhase::SuppressCheck => {
            let cs = collect_state
                .as_mut()
                .expect("DeriveEval::SuppressCheck: collect_state must be set");

            // Process previous child result (if any).
            if let Some(result) = cs.child_result.take() {
                if cs.scope_pushed {
                    env.pop_scope();
                    cs.scope_pushed = false;
                }
                match result {
                    Ok(Value::Bool(true)) => {
                        let mod_idx = cs.suppress_candidates[cs.suppress_index].modifier_index;
                        cs.suppressed.insert(mod_idx);
                    }
                    Ok(Value::Bool(false)) => { /* not suppressed */ }
                    Ok(other) => {
                        return Advance::Error(RuntimeError::new(format!(
                            "BindingCheck returned non-Bool: {other:?}",
                        )));
                    }
                    Err(e) => return Advance::Error(e),
                }
                cs.suppress_index += 1;
            }

            // Skip candidates whose modifier is already suppressed.
            while cs.suppress_index < cs.suppress_candidates.len() {
                let mod_idx = cs.suppress_candidates[cs.suppress_index].modifier_index;
                if cs.suppressed.contains(&mod_idx) {
                    cs.suppress_index += 1;
                } else {
                    break;
                }
            }

            if cs.suppress_index >= cs.suppress_candidates.len() {
                // Done: filter suppressed modifiers.
                let suppressed = std::mem::take(&mut cs.suppressed);
                let result: Vec<OwnedModifier> = std::mem::take(modifiers)
                    .into_iter()
                    .enumerate()
                    .filter(|(i, _)| !suppressed.contains(i))
                    .map(|(_, m)| m)
                    .collect();

                *collect_state = None;
                if result.is_empty() {
                    *modifiers = result;
                    *phase = DeriveEvalPhase::PushBody;
                } else {
                    *phase1_params = bound_args.clone();
                    let has_should_apply = result.iter().any(|m| m.should_apply_body.is_some());
                    *modifiers = result;
                    *phase = if has_should_apply {
                        DeriveEvalPhase::ShouldApplyGate(0)
                    } else {
                        DeriveEvalPhase::ApplyPhase1(0)
                    };
                }
                Advance::Continue
            } else {
                // Push caller scope and BindingCheck child.
                let candidate = &mut cs.suppress_candidates[cs.suppress_index];
                env.push_scope();
                for (n, v) in &candidate.caller_scope {
                    env.bind(n.clone(), v.clone());
                }
                cs.scope_pushed = true;
                let child_frame = candidate
                    .frame
                    .take()
                    .expect("SuppressCheck: frame already taken");
                Advance::Push(child_frame)
            }
        }

        DeriveEvalPhase::ApplyPhase1(idx) => {
            if *idx >= modifiers.len() {
                // All Phase 1 modifiers applied — update bound_args.
                *bound_args = phase1_params.take();
                *phase = DeriveEvalPhase::PushBody;
                return Advance::Continue;
            }

            // Set up scope for this modifier (mirrors
            // apply_phase1_modifier_native scope setup).
            let modifier = &modifiers[*idx];
            let params = phase1_params.take().unwrap_or_default();

            env.push_scope();
            bind_modifier_context(env, modifier);
            for (n, val) in &params {
                env.bind(n.clone(), val.clone());
            }

            // Store params for walker to update.
            *phase1_params = Some(params);

            // Init walker with Phase1 mode.
            *modify_walker = Some(Box::new(ModifyStmtWalker::new(
                modifier.clause.body.clone(),
                ModifyWalkerMode::Phase1,
            )));
            *phase = DeriveEvalPhase::ExecPhase1Modify(*idx);
            Advance::Continue
        }

        DeriveEvalPhase::ExecPhase1Modify(idx) => {
            let walker = modify_walker
                .as_mut()
                .expect("ExecPhase1Modify without walker");
            let p1 = phase1_params
                .as_mut()
                .expect("ExecPhase1Modify without phase1_params");

            match walker.step(core) {
                WalkerStep::PushExpr(frame) => Advance::Push(frame),
                WalkerStep::Bind(n, val) => {
                    env.bind(n, val);
                    Advance::Continue
                }
                WalkerStep::ParamOverride(n, val) => {
                    // Update params vec and env binding.
                    if let Some(param) = p1.iter_mut().find(|(pn, _)| *pn == n) {
                        param.1 = val;
                        env.bind(n, param.1.clone());
                    }
                    Advance::Continue
                }
                WalkerStep::EnterBody => {
                    env.push_scope();
                    Advance::Continue
                }
                WalkerStep::ExitBody => {
                    env.pop_scope();
                    // Phase 1: rebind all params after branch.
                    for (n, val) in p1.iter() {
                        env.bind(n.clone(), val.clone());
                    }
                    walker.exit_body();
                    Advance::Continue
                }
                WalkerStep::Complete => {
                    *phase = DeriveEvalPhase::Phase1ModifyDone(*idx);
                    Advance::Continue
                }
                WalkerStep::Continue => Advance::Continue,
                WalkerStep::Error(e) => {
                    env.pop_scope();
                    *modify_walker = None;
                    Advance::Error(e)
                }
                // Not produced in Phase1 mode.
                WalkerStep::CostOverride { .. }
                | WalkerStep::ResultOverride(..)
                | WalkerStep::ResultParamOverride(..) => {
                    unreachable!("Phase1 walker produced non-Phase1 step")
                }
            }
        }

        DeriveEvalPhase::Phase1ModifyDone(idx) => {
            // Pop the modifier scope.
            env.pop_scope();
            *modify_walker = None;

            // Detect changes.
            let old_params = bound_args.clone().unwrap_or_default();
            let new_params = phase1_params.as_ref().cloned().unwrap_or_default();
            let changes = crate::pipeline::collect_param_changes(&old_params, &new_params);

            if !changes.is_empty() {
                *pending_modify_effect = Some(Effect::ModifyApplied {
                    source: modifiers[*idx].source.clone(),
                    target_fn: name.clone(),
                    phase: Phase::Phase1,
                    changes,
                    tags: modifiers[*idx].clause.tags.clone(),
                });
                *phase = DeriveEvalPhase::YieldPhase1(*idx);
            } else {
                *phase = DeriveEvalPhase::ApplyPhase1(*idx + 1);
            }
            Advance::Continue
        }

        DeriveEvalPhase::YieldPhase1(idx) => {
            let effect = pending_modify_effect
                .take()
                .expect("YieldPhase1 entered without pending effect");
            *phase = DeriveEvalPhase::AwaitPhase1Ack(*idx);
            Advance::Yield(effect)
        }

        DeriveEvalPhase::AwaitPhase1Ack(idx) => {
            // ModifyApplied is informational — discard the response.
            let _ = pending.take();
            *phase = DeriveEvalPhase::ApplyPhase1(*idx + 1);
            Advance::Continue
        }

        DeriveEvalPhase::PushBody => {
            let fn_body = match body.take() {
                Some(b) => b,
                None => {
                    return Advance::Error(RuntimeError::new(format!(
                        "DeriveEval '{name}': body missing in PushBody",
                    )));
                }
            };
            let final_bound = bound_args.clone().unwrap_or_default();
            *phase = DeriveEvalPhase::BodyDone;
            Advance::Push(Frame::FunctionEval {
                name: name.clone(),
                args: final_bound,
                default_params: Vec::new(),
                body: Some(fn_body),
                defaults_done: false,
                child_result: None,
            })
        }

        DeriveEvalPhase::BodyDone => {
            if let Some(body_val) = base_value.take() {
                if modifiers.is_empty() {
                    // No modifiers — return body value directly.
                    return Advance::Pop(body_val);
                }
                // Start Phase 2 modifier loop.
                *phase2_result = Some(body_val);
                *phase = DeriveEvalPhase::ApplyPhase2(0);
                return Advance::Continue;
            }
            Advance::Error(RuntimeError::new(format!(
                "DeriveEval '{name}': BodyDone but no base_value"
            )))
        }

        DeriveEvalPhase::ApplyPhase2(idx) => {
            if *idx >= modifiers.len() {
                // All Phase 2 modifiers applied — pop with result.
                let val = phase2_result.take().unwrap_or(Value::Void);
                return Advance::Pop(val);
            }

            let modifier = &modifiers[*idx];

            // Skip modifiers with no phase2 stmts.
            if !crate::pipeline::has_phase2_stmts(&modifier.clause.body) {
                *phase = DeriveEvalPhase::ApplyPhase2(*idx + 1);
                return Advance::Continue;
            }

            let result_val = phase2_result.take().unwrap_or(Value::Void);

            // Set up scope (mirrors apply_phase2_modifier_native).
            env.push_scope();
            bind_modifier_context(env, modifier);
            for (n, val) in bound_args.as_deref().unwrap_or(&[]) {
                env.bind(n.clone(), val.clone());
            }

            env.bind(Name::from("result"), result_val.clone());

            // Store result for walker to update.
            *phase2_result = Some(result_val.clone());
            // Snapshot old result for change detection in Phase2ModifyDone.
            *base_value = Some(result_val);

            // Init walker with Phase2 mode.
            *modify_walker = Some(Box::new(ModifyStmtWalker::new(
                modifier.clause.body.clone(),
                ModifyWalkerMode::Phase2,
            )));
            *phase = DeriveEvalPhase::ExecPhase2Modify(*idx);
            Advance::Continue
        }

        DeriveEvalPhase::ExecPhase2Modify(idx) => {
            let walker = modify_walker
                .as_mut()
                .expect("ExecPhase2Modify without walker");
            let result = phase2_result
                .as_mut()
                .expect("ExecPhase2Modify without phase2_result");

            match walker.step(core) {
                WalkerStep::PushExpr(frame) => Advance::Push(frame),
                WalkerStep::Bind(n, val) => {
                    env.bind(n, val);
                    Advance::Continue
                }
                WalkerStep::ResultParamOverride(val) => {
                    // result = expr
                    *result = val;
                    env.bind(Name::from("result"), result.clone());
                    Advance::Continue
                }
                WalkerStep::ResultOverride(field, val) => {
                    // result.field = expr
                    match result {
                        Value::Struct { fields, .. } => {
                            fields.insert(field, val);
                        }
                        Value::RollResult(rr) => {
                            apply_roll_result_field(rr, field.as_str(), val);
                        }
                        _ => {}
                    }
                    env.bind(Name::from("result"), result.clone());
                    Advance::Continue
                }
                WalkerStep::EnterBody => {
                    env.push_scope();
                    Advance::Continue
                }
                WalkerStep::ExitBody => {
                    env.pop_scope();
                    // Phase 2: rebind result after branch.
                    env.bind(Name::from("result"), result.clone());
                    walker.exit_body();
                    Advance::Continue
                }
                WalkerStep::Complete => {
                    *phase = DeriveEvalPhase::Phase2ModifyDone(*idx);
                    Advance::Continue
                }
                WalkerStep::Continue => Advance::Continue,
                WalkerStep::Error(e) => {
                    env.pop_scope();
                    *modify_walker = None;
                    Advance::Error(e)
                }
                // Not produced in Phase2 mode.
                WalkerStep::CostOverride { .. } | WalkerStep::ParamOverride(..) => {
                    unreachable!("Phase2 walker produced non-Phase2 step")
                }
            }
        }

        DeriveEvalPhase::Phase2ModifyDone(idx) => {
            // Pop the modifier scope.
            env.pop_scope();
            *modify_walker = None;

            // Detect changes using the snapshot saved in
            // ApplyPhase2 (stored in base_value).
            let fi = fn_info_cache
                .as_ref()
                .expect("DeriveEval: fn_info_cache must be set");
            let old_result = base_value.take().unwrap_or(Value::Void);
            let new_result = phase2_result.clone().unwrap_or(Value::Void);
            let changes = crate::pipeline::collect_result_changes(&old_result, &new_result, fi);

            if !changes.is_empty() {
                *pending_modify_effect = Some(Effect::ModifyApplied {
                    source: modifiers[*idx].source.clone(),
                    target_fn: name.clone(),
                    phase: Phase::Phase2,
                    changes,
                    tags: modifiers[*idx].clause.tags.clone(),
                });
                *phase = DeriveEvalPhase::YieldPhase2(*idx);
            } else {
                *phase = DeriveEvalPhase::ApplyPhase2(*idx + 1);
            }
            Advance::Continue
        }

        DeriveEvalPhase::YieldPhase2(idx) => {
            let effect = pending_modify_effect
                .take()
                .expect("YieldPhase2 entered without pending effect");
            *phase = DeriveEvalPhase::AwaitPhase2Ack(*idx);
            Advance::Yield(effect)
        }

        DeriveEvalPhase::AwaitPhase2Ack(idx) => {
            // ModifyApplied is informational — discard the response.
            let _ = pending.take();
            *phase = DeriveEvalPhase::ApplyPhase2(*idx + 1);
            Advance::Continue
        }

        // ── should_apply gate ─────────────────────────────────────
        DeriveEvalPhase::ShouldApplyGate(idx) => {
            let idx = *idx;
            // Skip modifiers without a should_apply body.
            if idx >= modifiers.len() {
                // All gates evaluated — filter out skipped modifiers and proceed.
                if !should_apply_skipped.is_empty() {
                    let skipped = std::mem::take(should_apply_skipped);
                    let kept: Vec<OwnedModifier> = std::mem::take(modifiers)
                        .into_iter()
                        .enumerate()
                        .filter(|(i, _)| !skipped.contains(i))
                        .map(|(_, m)| m)
                        .collect();
                    *modifiers = kept;
                }
                if modifiers.is_empty() {
                    *phase = DeriveEvalPhase::PushBody;
                } else {
                    *phase = DeriveEvalPhase::ApplyPhase1(0);
                }
                return Advance::Continue;
            }

            if modifiers[idx].should_apply_body.is_none() {
                *phase = DeriveEvalPhase::ShouldApplyGate(idx + 1);
                return Advance::Continue;
            }

            let modifier = &modifiers[idx];
            let sa_body = modifier.should_apply_body.clone().unwrap();

            // Push scope: receiver, condition params, MUTABLE live state, function params.
            env.push_scope();
            helpers::bind_modifier_context(env, modifier);

            // Re-bind state as MUTABLE from live condition state (not snapshot).
            if let (Some(Value::Entity(bearer_ref)), Some(cond_id)) =
                (&modifier.bearer, modifier.condition_id)
            {
                if let Some(conditions) = sp.read_conditions(bearer_ref) {
                    if let Some(live_cond) = conditions.iter().find(|c| c.id == cond_id) {
                        if !live_cond.state_fields.is_empty() {
                            env.bind(
                                Name::from("state"),
                                Value::Struct {
                                    name: Name::from("state"),
                                    fields: live_cond.state_fields.clone(),
                                },
                            );
                        }
                    }
                }
            }

            // Bind target function params from bound_args.
            if let Some(ba) = bound_args.as_ref() {
                for (param_name, param_val) in ba {
                    env.bind(param_name.clone(), param_val.clone());
                }
            }

            *phase = DeriveEvalPhase::AwaitShouldApply(idx);
            Advance::Push(Frame::Block {
                stmts: sa_body.node,
                index: 0,
                result: Value::Void,
                expr_cache: Vec::new(),
                awaiting_fn: None,
                awaiting_error: None,
            })
        }

        DeriveEvalPhase::AwaitShouldApply(idx) => {
            let idx = *idx;
            match should_apply_result.take() {
                Some(Ok(value)) => {
                    // Read back mutated state from scope before popping.
                    let mut final_state = None;
                    if let Some(Value::Struct { fields, .. }) = env
                        .scopes
                        .last()
                        .and_then(|s| s.bindings.get(&Name::from("state")))
                        .cloned()
                    {
                        final_state = Some(fields);
                    }
                    env.pop_scope();
                    env.return_value = None;

                    // Determine if the modifier should be skipped.
                    let should_run = matches!(value, Value::Bool(true));
                    if !should_run {
                        should_apply_skipped.push(idx);
                    }

                    // If state was mutated, emit SetConditionState.
                    if let Some(fields) = final_state {
                        if !fields.is_empty() {
                            let cond_id = modifiers[idx].condition_id;
                            let bearer = modifiers[idx].bearer.clone();
                            if let (Some(cond_id), Some(Value::Entity(bearer_ref))) =
                                (cond_id, bearer)
                            {
                                // Update the snapshot on the modifier for subsequent phases.
                                modifiers[idx].condition_state_fields = fields.clone();
                                let effect = Effect::SetConditionState {
                                    target: bearer_ref,
                                    condition_id: cond_id,
                                    fields,
                                };
                                *phase = DeriveEvalPhase::YieldShouldApplyState(idx);
                                return Advance::Push(Frame::MutationYield {
                                    effect,
                                    pending: None,
                                    span: Span::default(),
                                });
                            }
                        }
                    }

                    *phase = DeriveEvalPhase::ShouldApplyGate(idx + 1);
                    Advance::Continue
                }
                Some(Err(e)) => {
                    env.pop_scope();
                    env.return_value = None;
                    Advance::Error(e)
                }
                None => {
                    env.pop_scope();
                    Advance::Error(RuntimeError::new(
                        "internal error: AwaitShouldApply completed without result",
                    ))
                }
            }
        }

        DeriveEvalPhase::YieldShouldApplyState(idx) => {
            let idx = *idx;
            // MutationYield completed — advance to next gate.
            *phase = DeriveEvalPhase::ShouldApplyGate(idx + 1);
            Advance::Continue
        }
    }
}

pub(super) fn advance_function_eval(
    frame: &mut Frame,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    _sp: &dyn StateProvider,
    _eh: &mut dyn EffectHandler,
    _tracker: &MutationTracker,
) -> Advance {
    let Frame::FunctionEval {
        name,
        args,
        default_params,
        body,
        defaults_done,
        child_result,
    } = frame
    else {
        unreachable!()
    };

    // Phase 3: child Block completed — clean up and return.
    // (body is None when Block was already pushed)
    if let Some(result) = child_result.take() {
        if body.is_none() {
            // Block child completed.
            env.pop_scope();
            env.return_value = None;
            return match result {
                Ok(val) => Advance::Pop(val),
                Err(e) => Advance::Error(e),
            };
        }
        // FillDefaults child completed (body still present).
        // Fall through to Phase 2.
        if let Err(e) = result {
            env.pop_scope();
            return Advance::Error(e);
        }
    }

    // Phase 2: defaults done — push Block for body.
    if *defaults_done {
        if let Some(block) = body.take() {
            return Advance::Push(Frame::Block {
                stmts: block.node,
                index: 0,
                result: Value::Void,
                expr_cache: Vec::new(),
                awaiting_fn: None,
                awaiting_error: None,
            });
        }
        return Advance::Error(RuntimeError::new(format!(
            "FunctionEval '{name}': no body after defaults"
        )));
    }

    // Phase 1: push scope, bind args, then evaluate defaults.
    if body.is_some() {
        // Record function entry for coverage.
        if let Some(ref cov) = core.coverage {
            cov.borrow_mut().hit_functions.insert(name.to_string());
        }
        env.push_scope();
        for (pname, pval) in args.drain(..) {
            env.bind(pname, pval);
        }

        if default_params.is_empty() {
            // No defaults to evaluate — go straight to body.
            *defaults_done = true;
            return Advance::Continue;
        }

        // Build FillDefaults params from default_params.
        let fill_params: Vec<DefaultParam> = default_params
            .drain(..)
            .map(|(dname, dexpr)| DefaultParam {
                name: dname,
                provided_value: None,
                default_expr: Some(dexpr),
            })
            .collect();

        *defaults_done = true;
        return Advance::Push(Frame::FillDefaults {
            params: fill_params,
            index: 0,
            child_result: None,
        });
    }

    // No body and no child result — shouldn't happen.
    Advance::Error(RuntimeError::new(format!(
        "FunctionEval '{name}': no body and no result"
    )))
}
