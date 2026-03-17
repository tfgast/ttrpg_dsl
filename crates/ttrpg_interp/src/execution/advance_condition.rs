use super::*;

pub(super) fn advance_condition_materialize(
    frame: &mut Frame,
    core: &RuntimeCore,
    _env: &mut ExecEnv,
    _sp: &dyn StateProvider,
    _eh: &mut dyn EffectHandler,
    _tracker: &MutationTracker,
) -> Advance {
    let Frame::ConditionMaterialize {
        name,
        params,
        index,
        child_result,
    } = frame
    else {
        unreachable!()
    };

    // Handle child ExprEval result (default expr evaluated).
    if let Some(val) = child_result.take() {
        // Store value in the param slot for later collection.
        params[*index].provided_value = Some(val);
        *index += 1;
        return Advance::Continue;
    }

    // All params resolved — build and pop Condition value.
    if *index >= params.len() {
        let mut args = std::collections::BTreeMap::new();
        for param in params.drain(..) {
            if let Some(val) = param.provided_value {
                args.insert(param.name, val);
            }
        }
        return Advance::Pop(Value::Condition {
            name: name.clone(),
            args,
        });
    }

    let param = &mut params[*index];

    if let Some(val) = param.provided_value.take() {
        // Already provided — re-store and advance.
        params[*index].provided_value = Some(val);
        *index += 1;
        Advance::Continue
    } else if let Some(ref default_expr) = param.default_expr {
        // Push child frame to evaluate the default expression.
        Advance::Push(compile_expr_to_frame(default_expr, core))
    } else {
        // Condition param without default — skip it.
        *index += 1;
        Advance::Continue
    }
}

pub(super) fn advance_condition_apply_gate(
    frame: &mut Frame,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    _sp: &dyn StateProvider,
    _eh: &mut dyn EffectHandler,
    _tracker: &MutationTracker,
) -> Advance {
    let Frame::ConditionApplyGate {
        target,
        condition_name,
        params,
        duration,
        source,
        tags,
        token,
        pending,
        state_defaults,
        state_defaults_idx,
        state_fields_acc,
        state_expr_cache,
        default_scope_pushed,
    } = frame
    else {
        unreachable!()
    };

    // Handle ExprEval child result for state default.
    if *default_scope_pushed && let Some(val) = state_expr_cache.pop() {
        env.pop_scope();
        *default_scope_pushed = false;
        if let Some(defaults) = state_defaults
            && *state_defaults_idx < defaults.len()
        {
            let (ref field_name, _) = defaults[*state_defaults_idx];
            state_fields_acc.insert(field_name.clone(), val);
            *state_defaults_idx += 1;
        }
        // Continue to check if more defaults need evaluation.
    }

    // Phase 2: evaluate state field defaults one at a time.
    if let Some(defaults) = state_defaults {
        if *state_defaults_idx >= defaults.len() {
            // All defaults evaluated — transition to ConditionOnApply.
            let target = *target;
            let cond_name = condition_name.clone();
            let duration = duration.clone();
            let source = source.clone();
            let tags = tags.clone();
            let token = *token;
            let params = params.clone();
            let fields = std::mem::take(state_fields_acc);
            let saved_token = env.current_condition_token;
            *frame = Frame::ConditionOnApply {
                target,
                condition_name: cond_name,
                params,
                duration,
                source,
                tags,
                token,
                state_fields: fields,
                clause_index: 0,
                child_result: None,
                saved_condition_token: saved_token,
            };
            return Advance::Continue;
        }

        let (_, ref field_expr) = defaults[*state_defaults_idx];

        // Push scope with condition params for default evaluation.
        env.push_scope();
        for (pname, pval) in params.iter() {
            env.bind(pname.clone(), pval.clone());
        }
        *default_scope_pushed = true;

        return Advance::Push(compile_expr_to_frame(field_expr, core));
    }

    // Phase 1: gate response handling.
    if let Some(response) = pending.take() {
        match response {
            Response::Vetoed => Advance::Pop(Value::Option(None)),
            Response::Acknowledged => {
                // Gate passed — collect state field defaults to
                // evaluate, then advance to Phase 2.
                let cond_name = condition_name.as_str();
                let defaults: Vec<(Name, Spanned<ExprKind>)> =
                    if let Some(decl) = core.program.conditions.get(cond_name) {
                        decl.state_fields
                            .iter()
                            .map(|sf| (sf.name.clone(), sf.default.clone()))
                            .collect()
                    } else {
                        Vec::new()
                    };
                *state_defaults = Some(defaults);
                *state_defaults_idx = 0;
                Advance::Continue
            }
            other => Advance::Error(RuntimeError::new(format!(
                "protocol error: unexpected response \
                     for ConditionApplyGate: {other:?}"
            ))),
        }
    } else {
        // First advance — emit the gate effect.
        let params_map: BTreeMap<Name, Value> = params.iter().cloned().collect();
        let tags_set: BTreeSet<Name> = tags.iter().cloned().collect();
        Advance::Yield(Effect::ConditionApplyGate {
            target: *target,
            condition: condition_name.clone(),
            params: params_map,
            duration: duration.clone(),
            invocation: env.current_invocation_id,
            source: source.clone(),
            tags: tags_set,
        })
    }
}

pub(super) fn advance_condition_on_apply(
    frame: &mut Frame,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    _sp: &dyn StateProvider,
    _eh: &mut dyn EffectHandler,
    _tracker: &MutationTracker,
) -> Advance {
    let Frame::ConditionOnApply {
        target,
        condition_name,
        params,
        duration,
        source,
        tags,
        token,
        state_fields,
        clause_index,
        child_result,
        saved_condition_token,
    } = frame
    else {
        unreachable!()
    };

    // Handle completed child Block (on_apply body).
    if let Some(result) = child_result.take() {
        match result {
            Ok(_) => {
                // Read back mutated state from scope before
                // we pop it (the Block already popped its own
                // scope, but we bound state in OUR scope).
                if let Some(Value::Struct { fields, .. }) = env
                    .scopes
                    .last()
                    .and_then(|s| s.bindings.get(&Name::from("state")))
                    .cloned()
                {
                    *state_fields = fields;
                }
                env.pop_scope();
                env.return_value = None; // clear early-return flag
                *clause_index += 1;
                return Advance::Continue;
            }
            Err(e) => {
                env.pop_scope();
                // Cleanup lifecycle state.
                env.in_lifecycle_block -= 1;
                env.lifecycle_condition_stack.pop();
                env.current_condition_token = *saved_condition_token;
                return Advance::Error(e);
            }
        }
    }

    // First entry at clause_index 0: set up lifecycle context.
    if *clause_index == 0 {
        env.in_lifecycle_block += 1;
        env.lifecycle_condition_stack.push(token.0);
        env.current_condition_token = Some(*token);
    }

    // Find the next on_apply clause to execute.
    let decl = core.program.conditions.get(condition_name.as_str());
    if let Some(decl) = decl {
        while *clause_index < decl.clauses.len() {
            if let ttrpg_ast::ast::ConditionClause::OnApply(lb) = &decl.clauses[*clause_index] {
                // Set up scope for this on_apply block.
                env.push_scope();
                env.bind(decl.receiver_name.clone(), Value::Entity(*target));
                for (pname, pval) in params.iter() {
                    env.bind(pname.clone(), pval.clone());
                }
                // Bind state fields as a mutable struct.
                if !state_fields.is_empty() {
                    env.bind(
                        Name::from("state"),
                        Value::Struct {
                            name: Name::from("state"),
                            fields: state_fields.clone(),
                        },
                    );
                }
                // Push Block frame for the on_apply body.
                return Advance::Push(Frame::Block {
                    stmts: lb.body.node.clone(),
                    index: 0,
                    result: Value::Void,
                    expr_cache: Vec::new(),
                    awaiting_fn: None,
                    awaiting_error: None,
                });
            }
            *clause_index += 1;
        }
    }

    // All on_apply clauses processed (or none exist).
    // Cleanup lifecycle state.
    env.in_lifecycle_block -= 1;
    env.lifecycle_condition_stack.pop();
    env.current_condition_token = *saved_condition_token;

    // Transition to ConditionActivate.
    let target = *target;
    let condition_name = condition_name.clone();
    let params = params.clone();
    let duration = duration.clone();
    let source = source.clone();
    let tags = tags.clone();
    let token = *token;
    let final_state = std::mem::take(state_fields);
    *frame = Frame::ConditionActivate {
        target,
        condition_name,
        params,
        duration,
        source,
        tags,
        token,
        state_fields: final_state,
        pending: None,
    };
    Advance::Continue
}

pub(super) fn advance_condition_activate(
    frame: &mut Frame,
    _core: &RuntimeCore,
    env: &mut ExecEnv,
    _sp: &dyn StateProvider,
    _eh: &mut dyn EffectHandler,
    _tracker: &MutationTracker,
) -> Advance {
    let Frame::ConditionActivate {
        target,
        condition_name,
        params,
        duration,
        source,
        tags,
        token,
        state_fields,
        pending,
    } = frame
    else {
        unreachable!()
    };

    if let Some(response) = pending.take() {
        let token_val = *token;
        match response {
            Response::Acknowledged | Response::Override(_) => Advance::Pop(Value::Option(Some(
                Box::new(Value::Int(token_val.0 as i64)),
            ))),
            Response::Vetoed => Advance::Pop(Value::Option(None)),
            other => Advance::Error(RuntimeError::new(format!(
                "protocol error: unsupported response \
                 for ApplyCondition: {other:?}"
            ))),
        }
    } else {
        // First advance — build and yield the ApplyCondition effect.
        let params_map: BTreeMap<Name, Value> = params.iter().cloned().collect();
        let tags_set: BTreeSet<Name> = tags.iter().cloned().collect();
        let final_state = std::mem::take(state_fields);
        let effect = Effect::ApplyCondition {
            target: *target,
            condition: condition_name.clone(),
            params: params_map,
            duration: duration.clone(),
            invocation: env.current_invocation_id,
            source: source.clone(),
            tags: tags_set,
            condition_id: token.0,
            state_fields: final_state,
        };
        Advance::Yield(effect)
    }
}

pub(super) fn advance_condition_handler_epilogue(
    frame: &mut Frame,
    _core: &RuntimeCore,
    env: &mut ExecEnv,
    _sp: &dyn StateProvider,
    _eh: &mut dyn EffectHandler,
    _tracker: &MutationTracker,
) -> Advance {
    let Frame::ConditionHandlerEpilogue {
        target,
        instance_id,
        original_state,
        block_stmts,
        child_result,
        awaiting_yield,
    } = frame
    else {
        unreachable!()
    };

    // Phase 3: MutationYield child completed — done.
    if *awaiting_yield {
        if let Some(Err(e)) = child_result.take() {
            return Advance::Error(e);
        }
        return Advance::Pop(Value::Void);
    }

    // Phase 1: push Block on first advance.
    if let Some(stmts) = block_stmts.take() {
        return Advance::Push(Frame::Block {
            stmts,
            index: 0,
            result: Value::Void,
            expr_cache: Vec::new(),
            awaiting_fn: None,
            awaiting_error: None,
        });
    }

    // Phase 2: Block completed — do epilogue.
    if let Some(result) = child_result.take() {
        if let Err(e) = result {
            env.pop_scope();
            return Advance::Error(e);
        }

        // Read back mutated state from scope before popping.
        // The scope was pushed by EmitConditionHandlers and is
        // still active (Block used its own inner scope).
        let mut final_state = None;
        if !original_state.is_empty()
            && let Some(Value::Struct { fields, .. }) = env
                .scopes
                .last()
                .and_then(|s| s.bindings.get(&Name::from("state")))
                .cloned()
        {
            final_state = Some(fields);
        }

        env.pop_scope();
        env.return_value = None;

        // Yield SetConditionState if state has fields (matching
        // recursive path which writes back unconditionally when
        // state is non-empty).
        if let Some(fields) = final_state
            && !fields.is_empty()
        {
            let effect = Effect::SetConditionState {
                target: *target,
                condition_id: *instance_id,
                fields,
            };
            *awaiting_yield = true;
            return Advance::Push(Frame::MutationYield {
                effect,
                pending: None,
                span: Span::default(),
            });
        }

        return Advance::Pop(Value::Void);
    }

    // Should not reach here — block_stmts and child_result
    // are the only two phases.
    Advance::Pop(Value::Void)
}

pub(super) fn advance_condition_removal_loop(
    frame: &mut Frame,
    _core: &RuntimeCore,
    _env: &mut ExecEnv,
    _sp: &dyn StateProvider,
    _eh: &mut dyn EffectHandler,
    _tracker: &MutationTracker,
) -> Advance {
    let Frame::ConditionRemovalLoop {
        instances,
        index,
        first_error,
        revoke_invocation,
        child_result,
        awaiting_revoke,
    } = frame
    else {
        unreachable!()
    };

    // Handle completed MutationYield child (RevokeInvocation).
    if *awaiting_revoke {
        if let Some(Err(e)) = child_result.take()
            && first_error.is_none()
        {
            *first_error = Some(e);
        }
        // Return deferred error or success.
        return if let Some(err) = first_error.take() {
            Advance::Error(err)
        } else {
            Advance::Pop(Value::Void)
        };
    }

    // Handle completed child (ConditionRemovalGate or ConditionOnRemove).
    if let Some(result) = child_result.take() {
        match result {
            Ok(_) => {
                // Child completed successfully; advance index.
                *index += 1;
                return Advance::Continue;
            }
            Err(e) => {
                // Deferred error: stash and continue to next instance.
                if first_error.is_none() {
                    *first_error = Some(e);
                }
                *index += 1;
                return Advance::Continue;
            }
        }
    }

    // Push ConditionRemovalGate for the next instance.
    if *index < instances.len() {
        let (inst_target, inst) = &instances[*index];
        return Advance::Push(Frame::ConditionRemovalGate {
            target: *inst_target,
            condition_name: inst.name.clone(),
            instance_id: inst.id,
            pending: None,
        });
    }

    // All instances processed. Yield RevokeInvocation if needed.
    if let Some(inv_id) = revoke_invocation.take() {
        let effect = Effect::RevokeInvocation { invocation: inv_id };
        *awaiting_revoke = true;
        return Advance::Push(Frame::MutationYield {
            effect,
            pending: None,
            span: Span::default(),
        });
    }

    // Return deferred error or success.
    if let Some(err) = first_error.take() {
        Advance::Error(err)
    } else {
        Advance::Pop(Value::Void)
    }
}

pub(super) fn advance_condition_removal_gate(
    frame: &mut Frame,
    _core: &RuntimeCore,
    env: &mut ExecEnv,
    sp: &dyn StateProvider,
    _eh: &mut dyn EffectHandler,
    _tracker: &MutationTracker,
) -> Advance {
    let Frame::ConditionRemovalGate {
        target,
        condition_name,
        instance_id,
        pending,
    } = frame
    else {
        unreachable!()
    };

    if let Some(response) = pending.take() {
        match response {
            Response::Vetoed => {
                // Host vetoed removal — skip this instance.
                Advance::Pop(Value::Void)
            }
            Response::Acknowledged => {
                // Gate passed — transition to ConditionOnRemove.
                // Read the instance's state fields and params from game state.
                let inst_target = *target;
                let inst_id = *instance_id;
                let cond_name = condition_name.clone();
                let conditions = sp.read_conditions(&inst_target).unwrap_or_default();
                let (state_fields, params) = conditions
                    .iter()
                    .find(|c| c.id == inst_id)
                    .map(|c| (c.state_fields.clone(), c.params.clone()))
                    .unwrap_or_default();
                let saved_token = env.current_condition_token;
                *frame = Frame::ConditionOnRemove {
                    target: inst_target,
                    condition_name: cond_name,
                    instance_id: inst_id,
                    params,
                    state_fields,
                    clause_index: 0,
                    child_result: None,
                    saved_condition_token: saved_token,
                    lifecycle_setup: false,
                    on_remove_error: None,
                    cleanup_step: 0,
                };
                Advance::Continue
            }
            other => Advance::Error(RuntimeError::new(format!(
                "protocol error: unexpected response \
                     for ConditionRemovalGate: {other:?}"
            ))),
        }
    } else {
        // First advance — emit the gate effect.
        Advance::Yield(Effect::ConditionRemovalGate {
            target: *target,
            condition: condition_name.clone(),
            id: *instance_id,
        })
    }
}

pub(super) fn advance_condition_on_remove(
    frame: &mut Frame,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    _sp: &dyn StateProvider,
    _eh: &mut dyn EffectHandler,
    _tracker: &MutationTracker,
) -> Advance {
    let Frame::ConditionOnRemove {
        target,
        condition_name,
        instance_id,
        params,
        state_fields,
        clause_index,
        child_result,
        saved_condition_token,
        lifecycle_setup,
        on_remove_error,
        cleanup_step,
    } = frame
    else {
        unreachable!()
    };

    // ── Cleanup phase: yield effects sequentially ──
    if *cleanup_step > 0 {
        // Handle MutationYield child completion.
        if let Some(result) = child_result.take() {
            if let Err(e) = result
                && on_remove_error.is_none()
            {
                *on_remove_error = Some(e);
            }
            *cleanup_step += 1;
            return Advance::Continue;
        }

        match *cleanup_step {
            1 => {
                // Yield SetConditionState if state has fields.
                if !state_fields.is_empty() {
                    let effect = Effect::SetConditionState {
                        target: *target,
                        condition_id: *instance_id,
                        fields: std::mem::take(state_fields),
                    };
                    return Advance::Push(Frame::MutationYield {
                        effect,
                        pending: None,
                        span: Span::default(),
                    });
                }
                // No state to set — skip to next step.
                *cleanup_step = 2;
                return Advance::Continue;
            }
            2 => {
                // Always yield RemoveCondition.
                let effect = Effect::RemoveCondition {
                    target: *target,
                    condition: condition_name.clone(),
                    params: None,
                    id: Some(*instance_id),
                };
                return Advance::Push(Frame::MutationYield {
                    effect,
                    pending: None,
                    span: Span::default(),
                });
            }
            3 => {
                // Always yield RemoveSuspensionSource.
                let effect = Effect::RemoveSuspensionSource {
                    entity: *target,
                    source_id: *instance_id,
                };
                return Advance::Push(Frame::MutationYield {
                    effect,
                    pending: None,
                    span: Span::default(),
                });
            }
            _ => {
                // All cleanup effects yielded. Propagate error or pop.
                return if let Some(err) = on_remove_error.take() {
                    Advance::Error(err)
                } else {
                    Advance::Pop(Value::Void)
                };
            }
        }
    }

    // ── Clause execution phase ──

    // Handle completed child Block (on_remove body).
    if let Some(result) = child_result.take() {
        match result {
            Ok(_) => {
                // Read back mutated state from scope.
                if let Some(Value::Struct { fields, .. }) = env
                    .scopes
                    .last()
                    .and_then(|s| s.bindings.get(&Name::from("state")))
                    .cloned()
                {
                    *state_fields = fields;
                }
                env.pop_scope();
                env.return_value = None;
                *clause_index += 1;
                return Advance::Continue;
            }
            Err(e) => {
                env.pop_scope();
                env.return_value = None;
                // Stash error but continue — we must still emit RemoveCondition.
                if on_remove_error.is_none() {
                    *on_remove_error = Some(e);
                }
                *clause_index += 1;
                // Skip remaining on_remove clauses; fall through to cleanup.
                // Set clause_index past all clauses so the loop below exits.
                *clause_index = usize::MAX;
                return Advance::Continue;
            }
        }
    }

    // Set up lifecycle context on first entry.
    if !*lifecycle_setup {
        *lifecycle_setup = true;
        env.in_lifecycle_block += 1;
        env.lifecycle_condition_stack.push(*instance_id);
        env.current_condition_token = Some(ConditionToken(*instance_id));
    }

    // Find the next on_remove clause to execute.
    let decl = core.program.conditions.get(condition_name.as_str());
    if let Some(decl) = decl {
        while *clause_index < decl.clauses.len() {
            if let ttrpg_ast::ast::ConditionClause::OnRemove(lb) = &decl.clauses[*clause_index] {
                // Set up scope for this on_remove block.
                env.push_scope();
                env.bind(decl.receiver_name.clone(), Value::Entity(*target));
                for (pname, pval) in params.iter() {
                    env.bind(pname.clone(), pval.clone());
                }
                // Bind state fields as a mutable struct.
                if !state_fields.is_empty() {
                    env.bind(
                        Name::from("state"),
                        Value::Struct {
                            name: Name::from("state"),
                            fields: state_fields.clone(),
                        },
                    );
                }
                // Push Block frame for the on_remove body.
                return Advance::Push(Frame::Block {
                    stmts: lb.body.node.clone(),
                    index: 0,
                    result: Value::Void,
                    expr_cache: Vec::new(),
                    awaiting_fn: None,
                    awaiting_error: None,
                });
            }
            *clause_index += 1;
        }
    }

    // All on_remove clauses processed (or none exist / error skipped rest).
    // Cleanup lifecycle state.
    env.in_lifecycle_block -= 1;
    env.lifecycle_condition_stack.pop();
    env.current_condition_token = *saved_condition_token;

    // Transition to cleanup phase — yield effects sequentially.
    *cleanup_step = 1;
    Advance::Continue
}
