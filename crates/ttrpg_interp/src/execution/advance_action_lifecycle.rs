use super::*;

pub(super) fn advance_action_lifecycle(
    frame: &mut Frame,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    _sp: &dyn StateProvider,
    _eh: &mut dyn EffectHandler,
    _tracker: &MutationTracker,
) -> Advance {
    let Frame::ActionLifecycle {
        name,
        actor,
        action_kind,
        call_span,
        has_return_type,
        inv_id,
        requires,
        cost,
        resolve,
        receiver_name,
        bindings,
        default_params,
        step,
        pending,
        body_result,
        cost_aborted,
        saved_turn_actor,
        saved_invocation,
    } = frame
    else {
        unreachable!()
    };

    match step {
        ActionStep::EmitStarted => {
            let effect = Effect::ActionStarted {
                name: name.clone(),
                kind: action_kind.clone(),
                actor: *actor,
                params: bindings.iter().map(|(_, v)| v.clone()).collect(),
            };
            *step = ActionStep::AwaitGate;
            Advance::Yield(effect)
        }

        ActionStep::AwaitGate => {
            let response = match pending.take() {
                Some(r) => r,
                None => return Advance::Continue,
            };

            match response {
                Response::Acknowledged => {
                    *saved_turn_actor = env.turn_actor.take();
                    *saved_invocation = env.current_invocation_id.take();
                    env.turn_actor = Some(*actor);
                    env.current_invocation_id = Some(*inv_id);
                    env.push_scope();

                    env.bind(receiver_name.clone(), Value::Entity(*actor));
                    for (pname, pval) in bindings.drain(..) {
                        env.bind(pname, pval);
                    }

                    // Always flow through the frame-based state machine
                    // (EvalRequires → EvalCost → RunResolve), even on the
                    // sync path. This eliminates the RunPipeline bridge.
                    *step = ActionStep::EvalRequires;

                    // Push FillDefaults if there are defaults to evaluate.
                    if !default_params.is_empty() {
                        let fill_params: Vec<DefaultParam> = default_params
                            .drain(..)
                            .map(|(name, expr)| DefaultParam {
                                name,
                                provided_value: None,
                                default_expr: Some(expr),
                            })
                            .collect();
                        return Advance::Push(Frame::FillDefaults {
                            params: fill_params,
                            index: 0,
                            child_result: None,
                        });
                    }

                    Advance::Continue
                }

                Response::Vetoed => {
                    *step = ActionStep::EmitVetoedCompleted;
                    Advance::Continue
                }

                other => {
                    *body_result = Some(Err(RuntimeError::with_span(
                        format!(
                            "protocol error: expected Acknowledged or Vetoed \
                             for ActionStarted, got {other:?}"
                        ),
                        *call_span,
                    )));
                    *step = ActionStep::EmitVetoedCompleted;
                    Advance::Continue
                }
            }
        }

        ActionStep::EmitVetoedCompleted => {
            let outcome = if body_result.as_ref().is_some_and(|r| r.is_err()) {
                ActionOutcome::Failed
            } else {
                ActionOutcome::Vetoed
            };
            let inv = if outcome == ActionOutcome::Vetoed {
                None
            } else {
                Some(*inv_id)
            };
            let effect = Effect::ActionCompleted {
                name: name.clone(),
                actor: *actor,
                outcome,
                invocation: inv,
            };
            *step = ActionStep::AwaitVetoedAck;
            Advance::Yield(effect)
        }

        ActionStep::AwaitVetoedAck => {
            let _ = pending.take();
            if let Some(Err(e)) = body_result.take() {
                return Advance::Error(e);
            }
            let abort = if *has_return_type {
                Value::Option(None)
            } else {
                Value::Void
            };
            Advance::Pop(abort)
        }

        ActionStep::EvalRequires => {
            if let Some(req_expr) = requires.as_ref() {
                // Push ExprEval for the requires expression.
                *step = ActionStep::AwaitRequiresEval;
                Advance::Push(compile_expr_to_frame(req_expr, core))
            } else {
                // No requires clause, skip to cost evaluation
                *step = ActionStep::EvalCost;
                Advance::Continue
            }
        }

        ActionStep::AwaitRequiresEval => {
            // ExprEval child completed with the requires
            // expression result.
            let val = body_result.take().unwrap_or(Ok(Value::Bool(true)));
            match val {
                Ok(Value::Bool(passed)) => {
                    let effect = Effect::RequiresCheck {
                        action: name.clone(),
                        passed,
                        reason: None,
                    };
                    *body_result = Some(Ok(Value::Bool(passed)));
                    *step = ActionStep::AwaitRequires;
                    Advance::Yield(effect)
                }
                Ok(other) => {
                    let req_span = requires.as_ref().map_or(*call_span, |r| r.span);
                    Advance::Error(RuntimeError::with_span(
                        format!("requires clause must evaluate to Bool, got {other:?}"),
                        req_span,
                    ))
                }
                Err(e) => Advance::Error(e),
            }
        }

        ActionStep::AwaitRequires => {
            let response = match pending.take() {
                Some(r) => r,
                None => return Advance::Continue,
            };
            let original_passed = match body_result.take() {
                Some(Ok(Value::Bool(b))) => b,
                _ => false,
            };

            let effective_passed = match response {
                Response::Override(Value::Bool(b)) => b,
                Response::Acknowledged => original_passed,
                other => {
                    return Advance::Error(RuntimeError::with_span(
                        format!(
                            "protocol error: expected Acknowledged or \
                             Override(Bool) for RequiresCheck, got {other:?}"
                        ),
                        *call_span,
                    ));
                }
            };

            if effective_passed {
                *step = ActionStep::EvalCost;
                Advance::Continue
            } else {
                let abort = if *has_return_type {
                    Value::Option(None)
                } else {
                    Value::Void
                };
                *body_result = Some(Ok(abort));
                *step = ActionStep::EmitCompleted;
                Advance::Continue
            }
        }

        ActionStep::EvalCost => {
            // Check if cost exists and is not free.
            if let Some(c) = cost.as_ref()
                && !c.free
            {
                // Use Bool(false) as a universal abort sentinel:
                // CostEval pops Void on success, Bool(false) on abort.
                // receive_child_result detects this and sets cost_aborted.
                let abort = Value::Bool(false);
                *step = ActionStep::AwaitCostEval;
                return Advance::Push(Frame::CostEval {
                    cost: c.clone(),
                    actor: *actor,
                    action_name: name.clone(),
                    call_span: *call_span,
                    phase: CostEvalPhase::CollectModifiers,
                    effective_cost: Some(c.clone()),
                    pending: None,
                    abort_value: abort,
                    modifiers: Vec::new(),
                    pending_modify_effect: None,
                    modify_hooks_result: None,
                    modify_walker: None,
                    modify_old_tokens: Vec::new(),
                    modify_old_free: false,
                    collect_state: None,
                });
            }
            // No cost or cost is free — skip to resolve.
            *step = ActionStep::RunResolve;
            Advance::Continue
        }

        ActionStep::AwaitCostEval => {
            // CostEval child completed. Check if it aborted.
            if *cost_aborted {
                // Cost check failed — skip resolve, emit completed.
                if body_result.is_none() {
                    let abort = if *has_return_type {
                        Value::Option(None)
                    } else {
                        Value::Void
                    };
                    *body_result = Some(Ok(abort));
                }
                *step = ActionStep::EmitCompleted;
            } else {
                // Cost succeeded — proceed to resolve.
                body_result.take();
                *step = ActionStep::RunResolve;
            }
            Advance::Continue
        }

        ActionStep::RunResolve => {
            // Push a Block frame for the resolve body. The Block
            // frame iterates statements one at a time, bridging
            // each through the recursive evaluator.
            Advance::Push(Frame::Block {
                stmts: resolve.node.clone(),
                index: 0,
                result: Value::Void,
                expr_cache: Vec::new(),
                awaiting_fn: None,
                awaiting_error: None,
            })
        }

        ActionStep::EmitCompleted => {
            // Clear return_value from body (previously done in
            // RunResolve when it ran the block synchronously).
            env.return_value = None;
            let outcome = if *cost_aborted {
                ActionOutcome::Failed
            } else {
                match body_result {
                    Some(Ok(_)) => ActionOutcome::Succeeded,
                    Some(Err(_)) => ActionOutcome::Failed,
                    None => ActionOutcome::Succeeded,
                }
            };
            let effect = Effect::ActionCompleted {
                name: name.clone(),
                actor: *actor,
                outcome,
                invocation: Some(*inv_id),
            };
            *step = ActionStep::AwaitCompletedAck;
            Advance::Yield(effect)
        }

        ActionStep::AwaitCompletedAck => {
            let _ = pending.take();
            env.pop_scope();
            env.turn_actor = saved_turn_actor.take();
            env.current_invocation_id = saved_invocation.take();

            match body_result.take() {
                Some(Ok(val)) => Advance::Pop(val),
                Some(Err(e)) => Advance::Error(e),
                None => Advance::Pop(Value::Void),
            }
        }
    }
}

pub(super) fn advance_call_setup(
    frame: &mut Frame,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    sp: &dyn StateProvider,
    _eh: &mut dyn EffectHandler,
    _tracker: &MutationTracker,
) -> Advance {
    let Frame::CallSetup {
        target,
        arg_exprs,
        arg_index,
        evaluated,
        child_result,
        awaiting_child,
        span,
    } = frame
    else {
        unreachable!()
    };

    // Phase 3: pass-through — target frame completed.
    if *awaiting_child {
        return match child_result.take() {
            Some(Ok(val)) => Advance::Pop(val),
            Some(Err(e)) => Advance::Error(e),
            None => Advance::Error(RuntimeError::with_span(
                "CallSetup: awaiting child but no result",
                *span,
            )),
        };
    }

    // Phase 1: collect child result from previous arg eval.
    if let Some(res) = child_result.take() {
        match res {
            Ok(val) => {
                evaluated.push(val);
                *arg_index += 1;
            }
            Err(e) => return Advance::Error(e),
        }
    }

    // Phase 1: push ExprEval for next arg.
    if *arg_index < arg_exprs.len() {
        return Advance::Push(compile_expr_to_frame(&arg_exprs[*arg_index], core));
    }

    // Phase 2: all args evaluated — build and push target frame.
    let values = std::mem::take(evaluated);
    let call_span = *span;
    *awaiting_child = true;

    match target {
        CallTarget::ApplyCondition { span: ac_span } => {
            let ac_span = *ac_span;
            // Lifecycle guard
            if env.in_lifecycle_block > 0 {
                return Advance::Error(RuntimeError::with_span(
                    "apply_condition() cannot be called inside on_apply/on_remove blocks",
                    ac_span,
                ));
            }
            // Extract arguments
            let (target_ref, cond_name, cond_args, duration) =
                match (values.first(), values.get(1), values.get(2)) {
                    (
                        Some(Value::Entity(t)),
                        Some(Value::Condition { name: cn, args: ca }),
                        Some(dur),
                    ) => (*t, cn.clone(), ca.clone(), dur.clone()),
                    (Some(Value::Entity(t)), Some(Value::Str(cn)), Some(dur)) => {
                        (*t, Name::from(cn.as_str()), BTreeMap::new(), dur.clone())
                    }
                    _ => {
                        return Advance::Error(RuntimeError::with_span(
                            "apply_condition: invalid arguments",
                            ac_span,
                        ));
                    }
                };
            let source = values
                .get(3)
                .cloned()
                .unwrap_or_else(crate::value::effect_source_unknown);
            let tags: Vec<Name> = core
                .type_env
                .conditions
                .get(&cond_name)
                .map(|info| info.tags.iter().cloned().collect())
                .unwrap_or_default();
            let token = match core.alloc_condition_id() {
                Ok(id) => ConditionToken(id),
                Err(e) => return Advance::Error(e),
            };
            let params: Vec<(Name, Value)> = cond_args.into_iter().collect();
            Advance::Push(Frame::ConditionApplyGate {
                target: target_ref,
                condition_name: cond_name,
                params,
                duration,
                source,
                tags,
                token,
                pending: None,
                state_defaults: None,
                state_defaults_idx: 0,
                state_fields_acc: BTreeMap::new(),
                state_expr_cache: Vec::new(),
                default_scope_pushed: false,
            })
        }
        CallTarget::RemoveCondition { span: rc_span } => {
            let rc_span = *rc_span;
            if env.in_lifecycle_block > 0 {
                return Advance::Error(RuntimeError::with_span(
                    "remove_condition() cannot be called inside on_apply/on_remove blocks",
                    rc_span,
                ));
            }
            let (target_ref, instances) = match (values.first(), values.get(1)) {
                (Some(Value::Entity(t)), Some(Value::Condition { name: cn, args: ca })) => {
                    let conditions = sp.read_conditions(t).unwrap_or_default();
                    let matching: Vec<_> = conditions
                        .into_iter()
                        .filter(|c| c.name == *cn && c.params == *ca)
                        .collect();
                    (*t, matching)
                }
                (Some(Value::Entity(t)), Some(Value::Str(cn))) => {
                    let conditions = sp.read_conditions(t).unwrap_or_default();
                    let name = Name::from(cn.as_str());
                    let matching: Vec<_> =
                        conditions.into_iter().filter(|c| c.name == name).collect();
                    (*t, matching)
                }
                (Some(Value::Entity(t)), Some(Value::Struct { name, fields }))
                    if name == "ActiveCondition" =>
                {
                    let cond_id = match fields.get("id") {
                        Some(Value::Int(id)) if *id >= 0 => *id as u64,
                        Some(Value::Int(_)) => {
                            return Advance::Error(RuntimeError::with_span(
                                "ActiveCondition id must be non-negative",
                                rc_span,
                            ));
                        }
                        _ => {
                            return Advance::Error(RuntimeError::with_span(
                                "ActiveCondition missing 'id' field",
                                rc_span,
                            ));
                        }
                    };
                    let conditions = sp.read_conditions(t).unwrap_or_default();
                    let matching: Vec<_> =
                        conditions.into_iter().filter(|c| c.id == cond_id).collect();
                    (*t, matching)
                }
                _ => {
                    return Advance::Error(RuntimeError::with_span(
                        "remove_condition: invalid arguments",
                        rc_span,
                    ));
                }
            };
            let mut sorted: Vec<(EntityRef, ActiveCondition)> =
                instances.into_iter().map(|c| (target_ref, c)).collect();
            sorted.sort_by_key(|(_, c)| c.gained_at);
            Advance::Push(Frame::ConditionRemovalLoop {
                instances: sorted,
                index: 0,
                first_error: None,
                revoke_invocation: None,
                child_result: None,
                awaiting_revoke: false,
            })
        }
        CallTarget::Revoke { span: rv_span } => {
            let rv_span = *rv_span;
            if env.in_lifecycle_block > 0 {
                return Advance::Error(RuntimeError::with_span(
                    "revoke() cannot be called inside on_apply/on_remove blocks",
                    rv_span,
                ));
            }
            let arg = match values.first() {
                Some(v) => v,
                None => {
                    return Advance::Error(RuntimeError::with_span(
                        "revoke: missing argument",
                        rv_span,
                    ));
                }
            };
            let inv_id = match arg {
                Value::Invocation(id) => *id,
                Value::Option(Some(inner)) => match inner.as_ref() {
                    Value::Invocation(id) => *id,
                    _ => {
                        return Advance::Error(RuntimeError::with_span(
                            "revoke: expected Invocation argument",
                            rv_span,
                        ));
                    }
                },
                Value::Option(None) | Value::Void => {
                    // No-op: nothing to revoke.
                    return Advance::Push(Frame::ConditionRemovalLoop {
                        instances: Vec::new(),
                        index: 0,
                        first_error: None,
                        revoke_invocation: None,
                        child_result: None,
                        awaiting_revoke: false,
                    });
                }
                _ => {
                    return Advance::Error(RuntimeError::with_span(
                        "revoke: expected Invocation argument",
                        rv_span,
                    ));
                }
            };
            let entities = sp.all_entities();
            let mut matching: Vec<(EntityRef, ActiveCondition)> = Vec::new();
            for entity in &entities {
                if let Some(conditions) = sp.read_conditions(entity) {
                    for cond in conditions {
                        if cond.invocation == Some(inv_id) {
                            matching.push((*entity, cond));
                        }
                    }
                }
            }
            matching.sort_by_key(|(_, c)| c.gained_at);
            Advance::Push(Frame::ConditionRemovalLoop {
                instances: matching,
                index: 0,
                first_error: None,
                revoke_invocation: Some(inv_id),
                child_result: None,
                awaiting_revoke: false,
            })
        }
        CallTarget::Function {
            callee,
            body,
            slot_mapping,
            param_names,
            default_params: fn_defaults,
        } => {
            // Map evaluated values to (name, value) pairs using slot_mapping.
            let mut slot_values: Vec<Option<Value>> = vec![None; param_names.len()];
            for (arg_idx, val) in values.into_iter().enumerate() {
                slot_values[slot_mapping[arg_idx]] = Some(val);
            }
            let mut evaluated_args: Vec<(Name, Value)> = Vec::new();
            let mut remaining_defaults: Vec<(Name, Spanned<ExprKind>)> = Vec::new();
            for (i, dp) in fn_defaults.iter().enumerate() {
                if let Some(val) = slot_values[i].take() {
                    evaluated_args.push((param_names[i].clone(), val));
                } else if let Some(ref expr) = dp.default_expr {
                    remaining_defaults.push((param_names[i].clone(), expr.clone()));
                } else {
                    return Advance::Error(RuntimeError::with_span(
                        format!(
                            "missing required argument '{}' for '{}'",
                            param_names[i], callee
                        ),
                        call_span,
                    ));
                }
            }
            Advance::Push(Frame::FunctionEval {
                name: callee.clone(),
                args: evaluated_args,
                default_params: remaining_defaults,
                body: Some(body.clone()),
                defaults_done: false,
                child_result: None,
            })
        }
    }
}
