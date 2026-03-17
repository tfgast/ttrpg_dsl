use super::*;

pub(super) fn advance_cost_eval(
    frame: &mut Frame,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    sp: &dyn StateProvider,
    _eh: &mut dyn EffectHandler,
    _tracker: &MutationTracker,
) -> Advance {
    let Frame::CostEval {
        cost,
        actor,
        action_name,
        call_span,
        phase,
        effective_cost,
        pending,
        abort_value,
        modifiers,
        pending_modify_effect,
        modify_walker,
        modify_old_tokens,
        modify_old_free,
        collect_state,
        should_apply_skipped,
        should_apply_result,
    } = frame
    else {
        unreachable!()
    };

    let tokens = effective_cost.as_ref().map_or(&cost.tokens, |c| &c.tokens);
    let expected_tokens: Vec<String> = core
        .type_env
        .valid_cost_tokens()
        .into_iter()
        .map(|n| n.to_string())
        .collect();

    match phase {
        CostEvalPhase::CollectModifiers => {
            // Build candidates for binding checks.
            use ttrpg_ast::ast::{ConditionClause, ModifyTarget};

            let conditions = match sp.read_conditions(actor) {
                Some(c) => c,
                None => {
                    *phase = CostEvalPhase::BudgetPreCheck(0);
                    return Advance::Continue;
                }
            };

            let stacking_winners =
                crate::pipeline::compute_stacking_winners(&conditions, &core.program);

            let mut collected_direct: Vec<(u64, OwnedModifier)> = Vec::new();
            let mut candidates: Vec<CollectCandidate> = Vec::new();

            for condition in &conditions {
                if !stacking_winners.contains(&condition.id) {
                    continue;
                }
                let cond_decl = match core.program.conditions.get(condition.name.as_str()) {
                    Some(d) => d,
                    None => continue,
                };
                for clause_item in &cond_decl.clauses {
                    let clause = match clause_item {
                        ConditionClause::Modify(c) => c,
                        _ => continue,
                    };
                    match &clause.target {
                        ModifyTarget::Cost(name) if name == action_name.as_str() => {}
                        _ => continue,
                    }

                    let owned_mod = owned_modifier_from_condition(condition, cond_decl, clause);

                    if clause.bindings.is_empty() {
                        collected_direct.push((condition.gained_at, owned_mod));
                    } else {
                        // Capture bound_params from current env before scope push.
                        let bound_params: Vec<(Name, Value)> = clause
                            .bindings
                            .iter()
                            .filter_map(|b| {
                                env.lookup(&b.name).cloned().map(|v| (b.name.clone(), v))
                            })
                            .collect();

                        let caller_scope = build_condition_scope_bindings(cond_decl, condition);

                        let frame = Frame::BindingCheck {
                            bindings: clause.bindings.clone(),
                            bound_params,
                            scope_bindings: Vec::new(),
                            scope_mode: BindingScopeMode::Caller,
                            index: 0,
                            child_result: None,
                            scope_pushed: false,
                        };

                        candidates.push(CollectCandidate {
                            frame: Some(frame),
                            caller_scope,
                            gained_at: condition.gained_at,
                            modifier: Some(owned_mod),
                        });
                    }
                }
            }

            if candidates.is_empty() {
                // All matches were direct (no binding checks needed).
                collected_direct.sort_by_key(|(g, _)| *g);
                *modifiers = collected_direct.into_iter().map(|(_, m)| m).collect();
                if modifiers.is_empty() {
                    *phase = CostEvalPhase::BudgetPreCheck(0);
                } else {
                    let has_sa = modifiers.iter().any(|m| m.should_apply_body.is_some());
                    *phase = if has_sa {
                        CostEvalPhase::ShouldApplyGate(0)
                    } else {
                        CostEvalPhase::ApplyModifier(0)
                    };
                }
            } else {
                *collect_state = Some(Box::new(ModifierCollectState {
                    candidates,
                    collected: collected_direct,
                    index: 0,
                    condition_count: 0, // not used for CostEval
                    option_modifiers: Vec::new(),
                    suppressions: Vec::new(),
                    suppress_candidates: Vec::new(),
                    suppress_index: 0,
                    suppressed: std::collections::HashSet::new(),
                    child_result: None,
                    scope_pushed: false,
                }));
                *phase = CostEvalPhase::CollectCheck;
            }
            Advance::Continue
        }

        CostEvalPhase::CollectCheck => {
            let cs = collect_state
                .as_mut()
                .expect("CostEval::CollectCheck: collect_state must be set");

            match advance_collect_check(cs, env, false) {
                Err(e) => Advance::Error(e),
                Ok(CollectCheckAction::PushChild(frame)) => Advance::Push(*frame),
                Ok(CollectCheckAction::Done) => {
                    let mut collected = std::mem::take(&mut cs.collected);
                    collected.sort_by_key(|(g, _)| *g);
                    *modifiers = collected.into_iter().map(|(_, m)| m).collect();
                    *collect_state = None;
                    if modifiers.is_empty() {
                        *phase = CostEvalPhase::BudgetPreCheck(0);
                    } else {
                        *phase = CostEvalPhase::ApplyModifier(0);
                    }
                    Advance::Continue
                }
            }
        }

        CostEvalPhase::ApplyModifier(idx) => {
            if *idx >= modifiers.len() {
                // All modifiers applied — emit events then
                // check if cost was made free.
                if modifiers.is_empty() {
                    *phase = CostEvalPhase::BudgetPreCheck(0);
                } else {
                    if effective_cost.as_ref().is_some_and(|c| c.free) {
                        return Advance::Pop(Value::Void);
                    }
                    *phase = CostEvalPhase::BudgetPreCheck(0);
                }
                return Advance::Continue;
            }

            // Set up scope for this modifier (mirrors
            // apply_single_cost_modifier_native scope setup).
            let modifier = &modifiers[*idx];

            // Save old cost state for change detection.
            let eff = effective_cost.as_ref().unwrap_or(cost);
            *modify_old_tokens = eff.tokens.iter().map(|t| t.node.to_string()).collect();
            *modify_old_free = eff.free;

            env.push_scope();
            bind_modifier_context(env, modifier);

            // Init walker with the modifier body.
            *modify_walker = Some(Box::new(ModifyStmtWalker::new(
                modifier.clause.body.clone(),
                ModifyWalkerMode::Cost,
            )));
            *phase = CostEvalPhase::ExecCostModify(*idx);
            Advance::Continue
        }

        CostEvalPhase::ExecCostModify(idx) => {
            let walker = modify_walker
                .as_mut()
                .expect("ExecCostModify without walker");

            match walker.step(core) {
                WalkerStep::PushExpr(frame) => Advance::Push(frame),
                WalkerStep::Bind(name, val) => {
                    env.bind(name, val);
                    Advance::Continue
                }
                WalkerStep::CostOverride { tokens: t, free: f } => {
                    let eff = effective_cost.get_or_insert_with(|| cost.clone());
                    eff.tokens = t;
                    eff.free = f;
                    Advance::Continue
                }
                WalkerStep::EnterBody => {
                    // Walker already pushed stack and set body.
                    // Parent just manages scope.
                    env.push_scope();
                    Advance::Continue
                }
                WalkerStep::ExitBody => {
                    env.pop_scope();
                    // Cost mode: no rebinding needed after If body.
                    walker.exit_body();
                    Advance::Continue
                }
                WalkerStep::Complete => {
                    *phase = CostEvalPhase::CostModifyDone(*idx);
                    Advance::Continue
                }
                WalkerStep::Continue => Advance::Continue,
                WalkerStep::Error(e) => {
                    // Clean up scope before propagating.
                    env.pop_scope();
                    *modify_walker = None;
                    Advance::Error(e)
                }
                // These are not produced in Cost mode.
                WalkerStep::ParamOverride(..)
                | WalkerStep::ResultOverride(..)
                | WalkerStep::ResultParamOverride(..) => {
                    unreachable!("Cost walker produced non-cost step")
                }
            }
        }

        CostEvalPhase::CostModifyDone(idx) => {
            // Pop the modifier scope.
            env.pop_scope();
            *modify_walker = None;

            // Detect changes and build ModifyApplied effect.
            let eff = effective_cost.as_ref().unwrap_or(cost);
            let new_tokens: Vec<String> = eff.tokens.iter().map(|t| t.node.to_string()).collect();

            if *modify_old_free != eff.free || *modify_old_tokens != new_tokens {
                let old_desc = if *modify_old_free {
                    "free".to_string()
                } else {
                    modify_old_tokens.join(", ")
                };
                let new_desc = if eff.free {
                    "free".to_string()
                } else {
                    new_tokens.join(", ")
                };
                let changes = vec![crate::effect::FieldChange {
                    name: Name::from("cost"),
                    old: Value::Str(old_desc),
                    new: Value::Str(new_desc),
                }];
                *pending_modify_effect = Some(Effect::ModifyApplied {
                    source: modifiers[*idx].source.clone(),
                    target_fn: Name::from(action_name.as_str()),
                    phase: Phase::Phase1,
                    changes,
                    tags: modifiers[*idx].clause.tags.clone(),
                });
                *phase = CostEvalPhase::YieldModifyApplied(*idx);
            } else {
                *phase = CostEvalPhase::ApplyModifier(*idx + 1);
            }
            Advance::Continue
        }

        CostEvalPhase::YieldModifyApplied(idx) => {
            // Yield the pending ModifyApplied effect to the host.
            let effect = pending_modify_effect
                .take()
                .expect("YieldModifyApplied entered without pending effect");
            *phase = CostEvalPhase::AwaitModifyAck(*idx);
            Advance::Yield(effect)
        }

        CostEvalPhase::AwaitModifyAck(idx) => {
            // ModifyApplied is informational — we don't check the response.
            let _ = pending.take();
            *phase = CostEvalPhase::ApplyModifier(*idx + 1);
            Advance::Continue
        }

        CostEvalPhase::BudgetPreCheck(idx) => {
            if *idx >= tokens.len() {
                // All tokens checked — proceed to deduction.
                *phase = CostEvalPhase::Deduction(0);
                return Advance::Continue;
            }

            let payer = env.cost_payer.unwrap_or(env.turn_actor.unwrap_or(*actor));

            if let Some(budget) = sp.read_turn_budget(&payer) {
                let token = &tokens[*idx];
                let budget_field = match core.type_env.resolve_cost_token(&token.node) {
                    Some(f) => f,
                    None => {
                        return Advance::Error(RuntimeError::with_span(
                            format!(
                                "internal error: unknown cost token '{}'; \
                                 expected one of: {}",
                                token.node,
                                expected_tokens.join(", ")
                            ),
                            token.span,
                        ));
                    }
                };

                if let Some(current) = budget.get(&budget_field) {
                    let current_int = match current {
                        Value::Int(v) => *v,
                        other => {
                            return Advance::Error(RuntimeError::with_span(
                                format!(
                                    "budget field '{budget_field}' has non-integer value: {other:?}",
                                ),
                                token.span,
                            ));
                        }
                    };
                    if current_int < 1 {
                        // Insufficient budget — yield RequiresCheck
                        let effect = Effect::RequiresCheck {
                            action: action_name.clone(),
                            passed: false,
                            reason: Some(format!(
                                "insufficient budget: {budget_field} requires 1 \
                                 but {budget_field} has {current_int}",
                            )),
                        };
                        *phase = CostEvalPhase::AwaitBudgetCheck(*idx);
                        return Advance::Yield(effect);
                    }
                }
            }
            // Budget OK for this token or no budget provisioned
            *phase = CostEvalPhase::BudgetPreCheck(*idx + 1);
            Advance::Continue
        }

        CostEvalPhase::AwaitBudgetCheck(idx) => {
            let response = match pending.take() {
                Some(r) => r,
                None => return Advance::Continue,
            };
            match response {
                Response::Acknowledged | Response::Override(Value::Bool(false)) => {
                    // Budget check failed — abort action.
                    Advance::Pop(abort_value.clone())
                }
                Response::Override(Value::Bool(true)) => {
                    // Host allows overdraft — continue pre-check.
                    *phase = CostEvalPhase::BudgetPreCheck(*idx + 1);
                    Advance::Continue
                }
                other => Advance::Error(RuntimeError::with_span(
                    format!(
                        "protocol error: expected Acknowledged or \
                         Override(Bool) for RequiresCheck, got {other:?}"
                    ),
                    *call_span,
                )),
            }
        }

        CostEvalPhase::Deduction(idx) => {
            if *idx >= tokens.len() {
                // All tokens deducted — cost succeeded.
                return Advance::Pop(Value::Void);
            }

            let payer = env.cost_payer.unwrap_or(env.turn_actor.unwrap_or(*actor));
            let token = &tokens[*idx];
            let budget_field = match core.type_env.resolve_cost_token(&token.node) {
                Some(f) => f,
                None => {
                    return Advance::Error(RuntimeError::with_span(
                        format!(
                            "internal error: unknown cost token '{}'; \
                             expected one of: {}",
                            token.node,
                            expected_tokens.join(", ")
                        ),
                        token.span,
                    ));
                }
            };

            let effect = Effect::DeductCost {
                actor: payer,
                token: token.node.clone(),
                budget_field,
            };
            *phase = CostEvalPhase::AwaitDeduction(*idx);
            Advance::Yield(effect)
        }

        CostEvalPhase::AwaitDeduction(idx) => {
            let response = match pending.take() {
                Some(r) => r,
                None => return Advance::Continue,
            };
            match response {
                Response::Acknowledged | Response::Vetoed => {
                    // Proceed to next token.
                    *phase = CostEvalPhase::Deduction(*idx + 1);
                    Advance::Continue
                }
                Response::Override(Value::Str(ref replacement)) => {
                    // Validate replacement token.
                    if core.type_env.resolve_cost_token(replacement).is_none() {
                        return Advance::Error(RuntimeError::with_span(
                            format!(
                                "invalid cost override '{}'; expected one of: {}",
                                replacement,
                                expected_tokens.join(", ")
                            ),
                            *call_span,
                        ));
                    }
                    *phase = CostEvalPhase::Deduction(*idx + 1);
                    Advance::Continue
                }
                other => Advance::Error(RuntimeError::with_span(
                    format!(
                        "protocol error: expected Acknowledged, Override(Str), \
                         or Vetoed for DeductCost, got {other:?}"
                    ),
                    *call_span,
                )),
            }
        }

        // ── should_apply gate ─────────────────────────────────────
        CostEvalPhase::ShouldApplyGate(idx) => {
            let idx = *idx;
            if idx >= modifiers.len() {
                // All gates evaluated — filter out skipped modifiers.
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
                    *phase = CostEvalPhase::BudgetPreCheck(0);
                } else {
                    *phase = CostEvalPhase::ApplyModifier(0);
                }
                return Advance::Continue;
            }

            if modifiers[idx].should_apply_body.is_none() {
                *phase = CostEvalPhase::ShouldApplyGate(idx + 1);
                return Advance::Continue;
            }

            let modifier = &modifiers[idx];
            let sa_body = modifier.should_apply_body.clone().unwrap();

            env.push_scope();
            helpers::bind_modifier_context(env, modifier);

            // Re-bind state as MUTABLE from live condition.
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

            *phase = CostEvalPhase::AwaitShouldApply(idx);
            Advance::Push(Frame::Block {
                stmts: sa_body.node,
                index: 0,
                result: Value::Void,
                expr_cache: Vec::new(),
                awaiting_fn: None,
                awaiting_error: None,
            })
        }

        CostEvalPhase::AwaitShouldApply(idx) => {
            let idx = *idx;
            match should_apply_result.take() {
                Some(Ok(value)) => {
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

                    let should_run = matches!(value, Value::Bool(true));
                    if !should_run {
                        should_apply_skipped.push(idx);
                    }

                    if let Some(fields) = final_state {
                        if !fields.is_empty() {
                            let cond_id = modifiers[idx].condition_id;
                            let bearer = modifiers[idx].bearer.clone();
                            if let (Some(cond_id), Some(Value::Entity(bearer_ref))) =
                                (cond_id, bearer)
                            {
                                modifiers[idx].condition_state_fields = fields.clone();
                                let effect = Effect::SetConditionState {
                                    target: bearer_ref,
                                    condition_id: cond_id,
                                    fields,
                                };
                                *phase = CostEvalPhase::YieldShouldApplyState(idx);
                                return Advance::Push(Frame::MutationYield {
                                    effect,
                                    pending: None,
                                    span: Span::default(),
                                });
                            }
                        }
                    }

                    *phase = CostEvalPhase::ShouldApplyGate(idx + 1);
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
                        "internal error: CostEval AwaitShouldApply completed without result",
                    ))
                }
            }
        }

        CostEvalPhase::YieldShouldApplyState(idx) => {
            let idx = *idx;
            *phase = CostEvalPhase::ShouldApplyGate(idx + 1);
            Advance::Continue
        }
    }
}

pub(super) fn advance_budget_guard(
    frame: &mut Frame,
    _core: &RuntimeCore,
    _env: &mut ExecEnv,
    _sp: &dyn StateProvider,
    _eh: &mut dyn EffectHandler,
    _tracker: &MutationTracker,
) -> Advance {
    let Frame::BudgetGuard {
        actor,
        budget,
        saved_budget,
        body,
        child_result,
        pending,
        phase,
        span,
    } = frame
    else {
        unreachable!()
    };

    match phase {
        BudgetGuardPhase::Provision => {
            if let Some(response) = pending.take() {
                match response {
                    Response::Vetoed => {
                        return Advance::Error(RuntimeError::with_span(
                            "with_budget: ProvisionBudget was vetoed by host",
                            *span,
                        ));
                    }
                    _ => {
                        *phase = BudgetGuardPhase::Body;
                        return Advance::Continue;
                    }
                }
            }
            // Yield the provision effect.
            Advance::Yield(Effect::ProvisionBudget {
                actor: *actor,
                budget: budget.clone(),
            })
        }

        BudgetGuardPhase::Body => {
            if let Some(result) = child_result.take() {
                // Body completed — transition to restore.
                *child_result = Some(result);
                *phase = BudgetGuardPhase::Restore;
                return Advance::Continue;
            }

            // Push Block for body.
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

            Advance::Error(RuntimeError::with_span(
                "BudgetGuard: no body and no result",
                *span,
            ))
        }

        BudgetGuardPhase::Restore => {
            if let Some(_response) = pending.take() {
                // Restore acknowledged — return body result.
                return match child_result.take() {
                    Some(Ok(val)) => Advance::Pop(val),
                    Some(Err(e)) => Advance::Error(e),
                    None => Advance::Pop(Value::Void),
                };
            }
            // Yield the restore effect.
            match saved_budget {
                Some(old) => Advance::Yield(Effect::ProvisionBudget {
                    actor: *actor,
                    budget: old.clone(),
                }),
                None => Advance::Yield(Effect::ClearBudget { actor: *actor }),
            }
        }
    }
}

pub(super) fn advance_multi_budget_guard(
    frame: &mut Frame,
    _core: &RuntimeCore,
    _env: &mut ExecEnv,
    _sp: &dyn StateProvider,
    _eh: &mut dyn EffectHandler,
    _tracker: &MutationTracker,
) -> Advance {
    let Frame::MultiBudgetGuard {
        entries,
        saved_budgets,
        provision_index,
        phase,
        body,
        child_result,
        pending,
        span,
    } = frame
    else {
        unreachable!()
    };

    match phase {
        MultiBudgetPhase::Provisioning => {
            if let Some(response) = pending.take() {
                match response {
                    Response::Vetoed => {
                        // Roll back already-provisioned budgets.
                        if *provision_index > 0 {
                            *phase = MultiBudgetPhase::Rollback { index: 0 };
                            return Advance::Continue;
                        }
                        return Advance::Error(RuntimeError::with_span(
                            "with_budgets: ProvisionBudget was vetoed by host",
                            *span,
                        ));
                    }
                    _ => {
                        *provision_index += 1;
                        // Fall through to check if more to provision.
                    }
                }
            }

            if *provision_index >= entries.len() {
                // All provisioned — transition to body.
                *phase = MultiBudgetPhase::Body;
                return Advance::Continue;
            }

            // Yield next ProvisionBudget.
            let (actor, budget) = &entries[*provision_index];
            Advance::Yield(Effect::ProvisionBudget {
                actor: *actor,
                budget: budget.clone(),
            })
        }

        MultiBudgetPhase::Rollback { index } => {
            if let Some(_response) = pending.take() {
                *index += 1;
                // Fall through to check if done.
            }

            // Rollback in reverse: indices 0..provision_index-1
            // already provisioned, restore in reverse.
            if *index >= *provision_index {
                return Advance::Error(RuntimeError::with_span(
                    "with_budgets: ProvisionBudget was vetoed by host",
                    *span,
                ));
            }

            let restore_idx = *provision_index - 1 - *index;
            let (actor, ref prev) = saved_budgets[restore_idx];
            match prev {
                Some(old) => Advance::Yield(Effect::ProvisionBudget {
                    actor,
                    budget: old.clone(),
                }),
                None => Advance::Yield(Effect::ClearBudget { actor }),
            }
        }

        MultiBudgetPhase::Body => {
            // Body completed — transition to Restoring.
            if let Some(result) = child_result.take() {
                *phase = MultiBudgetPhase::Restoring { index: 0 };
                // Stash result back for use in Restoring.
                *child_result = Some(result);
                return Advance::Continue;
            }

            // Push Block for body.
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

            Advance::Error(RuntimeError::with_span(
                "MultiBudgetGuard: no body and no result",
                *span,
            ))
        }

        MultiBudgetPhase::Restoring { index } => {
            if let Some(_response) = pending.take() {
                *index += 1;
                // Fall through to check if done.
            }

            if *index >= saved_budgets.len() {
                // All budgets restored. Return body result.
                return match child_result.take() {
                    Some(Ok(val)) => Advance::Pop(val),
                    Some(Err(e)) => Advance::Error(e),
                    None => Advance::Pop(Value::Void),
                };
            }

            // Restore in reverse order.
            let restore_idx = saved_budgets.len() - 1 - *index;
            let (actor, ref prev) = saved_budgets[restore_idx];
            match prev {
                Some(old) => Advance::Yield(Effect::ProvisionBudget {
                    actor,
                    budget: old.clone(),
                }),
                None => Advance::Yield(Effect::ClearBudget { actor }),
            }
        }
    }
}

pub(super) fn advance_cost_payer_guard(
    frame: &mut Frame,
    _core: &RuntimeCore,
    env: &mut ExecEnv,
    _sp: &dyn StateProvider,
    _eh: &mut dyn EffectHandler,
    _tracker: &MutationTracker,
) -> Advance {
    let Frame::CostPayerGuard {
        saved_payer,
        body,
        child_result,
    } = frame
    else {
        unreachable!()
    };

    // Phase 2: body completed — restore cost_payer and return.
    if let Some(result) = child_result.take() {
        env.cost_payer = *saved_payer;
        return match result {
            Ok(val) => Advance::Pop(val),
            Err(e) => Advance::Error(e),
        };
    }

    // Phase 1: push Block for body.
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

    Advance::Error(RuntimeError::new("CostPayerGuard: no body and no result"))
}
