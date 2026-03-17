use super::*;

pub(super) fn advance_roll_dice_waiting(
    frame: &mut Frame,
    _core: &RuntimeCore,
    _env: &mut ExecEnv,
    _sp: &dyn StateProvider,
    _eh: &mut dyn EffectHandler,
    _tracker: &MutationTracker,
) -> Advance {
    let Frame::RollDiceWaiting {
        dice_expr,
        span,
        pending,
    } = frame
    else {
        unreachable!()
    };
    if let Some(response) = pending.take() {
        // Host responded — extract the roll result.
        match response {
            Response::Rolled(rr) => Advance::Pop(Value::RollResult(rr)),
            Response::Override(Value::RollResult(rr)) => Advance::Pop(Value::RollResult(rr)),
            other => Advance::Error(RuntimeError::with_span(
                format!(
                    "protocol error: expected Rolled or Override(RollResult) \
                     for RollDice, got {other:?}"
                ),
                *span,
            )),
        }
    } else {
        // First advance — emit the RollDice effect.
        Advance::Yield(Effect::RollDice {
            expr: dice_expr.clone(),
        })
    }
}

pub(super) fn advance_prompt_waiting(
    frame: &mut Frame,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    _sp: &dyn StateProvider,
    _eh: &mut dyn EffectHandler,
    _tracker: &MutationTracker,
) -> Advance {
    let Frame::PromptWaiting {
        prompt_name,
        params,
        return_type,
        hint,
        suggest,
        default_block,
        span,
        pending,
        child_result,
        phase,
        suggest_expr,
        default_params,
    } = frame
    else {
        unreachable!()
    };
    match phase {
        PromptPhase::EvalDefaults => {
            // Handle FillDefaults child result.
            if let Some(result) = child_result.take() {
                if let Err(e) = result {
                    return Advance::Error(e);
                }
                // FillDefaults completed. Collect bound params from scope.
                // FillDefaults binds values into scope by name.
                // We need to rebuild params from scope bindings.
                if let Some(scope) = env.scopes.last() {
                    for dp in default_params.drain(..) {
                        if let Some(val) = scope.bindings.get(&dp.name) {
                            params.push((dp.name, val.clone()));
                        }
                    }
                }
                *phase = PromptPhase::EvalSuggest;
                return Advance::Continue;
            }

            if default_params.iter().any(|p| p.default_expr.is_some()) {
                // Push FillDefaults to evaluate param defaults.
                // Phase stays at EvalDefaults so child_result is handled here.
                env.push_scope();
                // Bind already-provided params so defaults can reference them.
                for (pn, pv) in params.iter() {
                    env.bind(pn.clone(), pv.clone());
                }
                let fill = std::mem::take(default_params);
                return Advance::Push(Frame::FillDefaults {
                    params: fill,
                    index: 0,
                    child_result: None,
                });
            }

            // No defaults to evaluate — convert default_params to params.
            for dp in default_params.drain(..) {
                if let Some(val) = dp.provided_value {
                    params.push((dp.name, val));
                }
            }
            *phase = PromptPhase::EvalSuggest;
            Advance::Continue
        }

        PromptPhase::EvalSuggest => {
            // Handle suggest ExprEval child result.
            if let Some(result) = child_result.take() {
                match result {
                    Ok(val) => {
                        env.pop_scope();
                        *suggest = Some(val);
                    }
                    Err(e) => {
                        env.pop_scope();
                        return Advance::Error(e);
                    }
                }
                *phase = PromptPhase::EmitPrompt;
                return Advance::Continue;
            }

            if let Some(expr) = suggest_expr.take() {
                // Push scope and bind params for suggest evaluation.
                // Phase stays at EvalSuggest so child_result is handled here.
                env.push_scope();
                for (pn, pv) in params.iter() {
                    env.bind(pn.clone(), pv.clone());
                }
                return compile_expr_push(&expr, core);
            }

            // No suggest expression — skip to emit.
            *phase = PromptPhase::EmitPrompt;
            Advance::Continue
        }

        PromptPhase::EmitPrompt => {
            *phase = PromptPhase::AwaitResponse;
            Advance::Yield(Effect::ResolvePrompt {
                name: prompt_name.clone(),
                params: params.clone(),
                return_type: return_type.clone(),
                hint: hint.clone(),
                suggest: suggest.take(),
                has_default: default_block.is_some(),
            })
        }

        PromptPhase::AwaitResponse => {
            if let Some(response) = pending.take() {
                match response {
                    Response::PromptResult(val) => Advance::Pop(val),
                    Response::Override(val) => Advance::Pop(val),
                    Response::UseDefault => {
                        if let Some(block) = default_block.take() {
                            env.push_scope();
                            for (pn, pv) in params.drain(..) {
                                env.bind(pn, pv);
                            }
                            *phase = PromptPhase::RunningDefault;
                            Advance::Push(Frame::Block {
                                stmts: block.node,
                                index: 0,
                                result: Value::Void,
                                expr_cache: Vec::new(),
                                awaiting_fn: None,
                                awaiting_error: None,
                            })
                        } else {
                            Advance::Error(RuntimeError::with_span(
                                "prompt: UseDefault response but no default block",
                                *span,
                            ))
                        }
                    }
                    other => Advance::Error(RuntimeError::with_span(
                        format!(
                            "protocol error: expected PromptResult, Override, \
                             or UseDefault for ResolvePrompt, got {other:?}"
                        ),
                        *span,
                    )),
                }
            } else {
                // Waiting for host response — should not be called
                // without a pending response in AwaitResponse phase.
                Advance::Error(RuntimeError::with_span(
                    "prompt: AwaitResponse but no pending response",
                    *span,
                ))
            }
        }

        PromptPhase::RunningDefault => {
            // UseDefault Block child completed.
            if let Some(result) = child_result.take() {
                env.pop_scope();
                return match result {
                    Ok(val) => Advance::Pop(val),
                    Err(e) => Advance::Error(e),
                };
            }
            Advance::Error(RuntimeError::with_span(
                "prompt: RunningDefault but no child result",
                *span,
            ))
        }
    }
}

pub(super) fn advance_spawn_entity(
    frame: &mut Frame,
    _core: &RuntimeCore,
    _env: &mut ExecEnv,
    _sp: &dyn StateProvider,
    _eh: &mut dyn EffectHandler,
    _tracker: &MutationTracker,
) -> Advance {
    let Frame::SpawnEntity {
        entity_type,
        base_fields,
        groups,
        phase,
        pending,
        entity_ref,
        span,
    } = frame
    else {
        unreachable!()
    };
    match phase {
        SpawnPhase::Defaults => {
            // Field defaults are evaluated by the caller before
            // constructing this frame. Transition to Spawned.
            *phase = SpawnPhase::Spawned;
            Advance::Continue
        }

        SpawnPhase::Spawned => {
            if let Some(response) = pending.take() {
                match response {
                    Response::EntitySpawned(r) => {
                        *entity_ref = Some(r);
                        *phase = SpawnPhase::GrantingGroups { index: 0 };
                        Advance::Continue
                    }
                    Response::Vetoed => Advance::Error(RuntimeError::with_span(
                        format!(
                            "entity construction for `{entity_type}` \
                                 was vetoed by host"
                        ),
                        *span,
                    )),
                    other => Advance::Error(RuntimeError::with_span(
                        format!(
                            "protocol error: expected EntitySpawned for \
                             SpawnEntity, got {other:?}"
                        ),
                        *span,
                    )),
                }
            } else {
                // Emit SpawnEntity effect.
                let fields: FxHashMap<Name, Value> = base_fields.drain(..).collect();
                Advance::Yield(Effect::SpawnEntity {
                    entity_type: entity_type.clone(),
                    fields,
                })
            }
        }

        SpawnPhase::GrantingGroups { index } => {
            if let Some(_response) = pending.take() {
                // Previous GrantGroup acknowledged; advance.
                *index += 1;
                return Advance::Continue;
            }

            if *index >= groups.len() {
                let r = entity_ref.expect("entity_ref must be set after Spawned");
                return Advance::Pop(Value::Entity(r));
            }

            let r = entity_ref.expect("entity_ref must be set after Spawned");
            let group = &groups[*index];
            Advance::Yield(Effect::GrantGroup {
                entity: r,
                group_name: group.group_name.clone(),
                fields: Value::Struct {
                    name: group.group_name.clone(),
                    fields: group.fields.clone(),
                },
            })
        }
    }
}

pub(super) fn advance_mutation_yield(
    frame: &mut Frame,
    _core: &RuntimeCore,
    _env: &mut ExecEnv,
    _sp: &dyn StateProvider,
    _eh: &mut dyn EffectHandler,
    _tracker: &MutationTracker,
) -> Advance {
    let Frame::MutationYield {
        effect,
        pending,
        span,
    } = frame
    else {
        unreachable!()
    };
    if let Some(response) = pending.take() {
        match response {
            Response::Acknowledged | Response::Override(_) | Response::Vetoed => {
                Advance::Pop(Value::Void)
            }
            other => Advance::Error(RuntimeError::with_span(
                format!("protocol error: unsupported response for mutation effect: {other:?}"),
                *span,
            )),
        }
    } else {
        Advance::Yield(effect.clone())
    }
}

pub(super) fn advance_grant_revoke_gate(
    frame: &mut Frame,
    _core: &RuntimeCore,
    _env: &mut ExecEnv,
    _sp: &dyn StateProvider,
    _eh: &mut dyn EffectHandler,
    _tracker: &MutationTracker,
) -> Advance {
    let Frame::GrantRevokeGate {
        effect,
        pending,
        span,
    } = frame
    else {
        unreachable!()
    };
    if let Some(response) = pending.take() {
        match response {
            Response::Vetoed => {
                let label = match effect {
                    Effect::GrantGroup { group_name, .. } => {
                        format!("grant {group_name} was vetoed by host")
                    }
                    Effect::RevokeGroup { group_name, .. } => {
                        format!("revoke {group_name} was vetoed by host")
                    }
                    _ => "grant/revoke was vetoed by host".to_string(),
                };
                Advance::Error(RuntimeError::with_span(label, *span))
            }
            _ => Advance::Pop(Value::Void),
        }
    } else {
        Advance::Yield(effect.clone())
    }
}
