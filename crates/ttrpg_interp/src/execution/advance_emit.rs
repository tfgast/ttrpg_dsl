use super::*;

pub(super) fn advance_emit_eval(
    frame: &mut Frame,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    sp: &dyn StateProvider,
    _eh: &mut dyn EffectHandler,
    _tracker: &MutationTracker,
) -> Advance {
    let Frame::EmitEval {
        event_name,
        args,
        arg_index,
        span,
        phase,
        param_map,
        all_fields,
        param_defaults,
        field_defaults,
        default_index,
        saved_emit_depth,
        saved_lifecycle,
        scope_pushed,
        child_result,
    } = frame
    else {
        unreachable!()
    };

    // Handle child results based on phase.
    if let Some(result) = child_result.take() {
        match phase {
            EmitEvalPhase::Args => {
                // ExprEval child completed for arg evaluation.
                match result {
                    Ok(val) => {
                        let arg = &args[*arg_index];
                        if let Some(ref name) = arg.name {
                            param_map.insert(name.clone(), val);
                        }
                        *arg_index += 1;
                        // Continue to evaluate next arg or transition.
                    }
                    Err(e) => return Advance::Error(e),
                }
            }
            EmitEvalPhase::ParamDefaults => {
                // ExprEval child completed for param default.
                match result {
                    Ok(val) => {
                        let (ref pname, _) = param_defaults[*default_index];
                        param_map.insert(pname.clone(), val);
                        *default_index += 1;
                    }
                    Err(e) => return Advance::Error(e),
                }
            }
            EmitEvalPhase::FieldDefaults => {
                // ExprEval child completed for field default.
                match result {
                    Ok(val) => {
                        let (ref fname, _) = field_defaults[*default_index];
                        all_fields.insert(fname.clone(), val);
                        *default_index += 1;
                    }
                    Err(e) => {
                        if *scope_pushed {
                            env.pop_scope();
                            *scope_pushed = false;
                        }
                        return Advance::Error(e);
                    }
                }
            }
            EmitEvalPhase::Ready => {
                // EmitHooks/EmitConditionHandlers child returned.
                env.emit_depth = *saved_emit_depth;
                env.in_lifecycle_block = *saved_lifecycle;
                return match result {
                    Ok(_) => Advance::Pop(Value::Void),
                    Err(e) => Advance::Error(e),
                };
            }
        }
    }

    match phase {
        EmitEvalPhase::Args => {
            // 1. Check emit depth limit (only on first entry).
            if *arg_index == 0 && env.emit_depth >= crate::MAX_EMIT_DEPTH {
                return Advance::Error(RuntimeError::with_span(
                    format!(
                        "emit depth limit ({}) exceeded — possible \
                         circular emit chain",
                        crate::MAX_EMIT_DEPTH
                    ),
                    *span,
                ));
            }

            // 3. Evaluate arg expressions one at a time via child frames.
            if *arg_index < args.len() {
                return compile_expr_push(&args[*arg_index].value, core);
            }

            // All args evaluated — look up EventDecl and collect defaults.
            // 2. Look up EventDecl
            let event_decl = match core.program.events.get(event_name) {
                Some(d) => d.clone(),
                None => {
                    return Advance::Error(RuntimeError::with_span(
                        format!("undefined event '{event_name}'"),
                        *span,
                    ));
                }
            };

            // 4. Collect defaults for missing params
            *param_defaults = event_decl
                .params
                .iter()
                .filter_map(|p| {
                    if param_map.contains_key(&p.name) {
                        None
                    } else {
                        p.default.clone().map(|d| (p.name.clone(), d))
                    }
                })
                .collect();

            // Collect field defaults
            *field_defaults = event_decl
                .fields
                .iter()
                .filter_map(|f| f.default.clone().map(|d| (f.name.clone(), d)))
                .collect();

            *default_index = 0;
            *phase = EmitEvalPhase::ParamDefaults;
            Advance::Continue
        }

        EmitEvalPhase::ParamDefaults => {
            // Fill defaults for missing params, one at a time.
            if *default_index >= param_defaults.len() {
                // All param defaults filled — transition to
                // FieldDefaults. Push a scope with params bound.
                *all_fields = param_map.clone();
                env.push_scope();
                *scope_pushed = true;
                for (name, val) in param_map.iter() {
                    env.bind(name.clone(), val.clone());
                }
                *default_index = 0;
                *phase = EmitEvalPhase::FieldDefaults;
                return Advance::Continue;
            }

            let (_, ref default_expr) = param_defaults[*default_index];
            compile_expr_push(default_expr, core)
        }

        EmitEvalPhase::FieldDefaults => {
            // Evaluate derived fields with params in scope.
            if *default_index >= field_defaults.len() {
                // Pop the scope we pushed for field evaluation.
                if *scope_pushed {
                    env.pop_scope();
                    *scope_pushed = false;
                }
                *phase = EmitEvalPhase::Ready;
                return Advance::Continue;
            }

            let (ref fname, ref default_expr) = field_defaults[*default_index];
            if all_fields.contains_key(fname) {
                // Already present (from params) — skip.
                *default_index += 1;
                return Advance::Continue;
            }

            compile_expr_push(default_expr, core)
        }

        EmitEvalPhase::Ready => {
            // 5. Construct payload
            let payload = Value::Struct {
                name: Name::from(format!("__event_{event_name}")),
                fields: std::mem::take(all_fields),
            };

            // 6. Find matching hooks and condition handlers.
            // These are pure queries — no Interpreter needed.
            let candidates = sp.entities_in_play();

            let hook_result = crate::event::find_matching_hooks(
                &core.program,
                &core.type_env,
                sp,
                event_name,
                &payload,
                &candidates,
            );
            let hooks = match hook_result {
                Ok(hr) => hr.hooks,
                Err(e) => return Advance::Error(e),
            };

            let cond_result = crate::event::find_matching_condition_handlers(
                &core.program,
                &core.type_env,
                sp,
                event_name,
                &payload,
                &candidates,
            );
            let cond_handlers = match cond_result {
                Ok(cr) => cr.handlers,
                Err(e) => return Advance::Error(e),
            };

            // Save depth/lifecycle counters
            *saved_emit_depth = env.emit_depth;
            *saved_lifecycle = env.in_lifecycle_block;

            // Convert event::HookInfo -> execution::HookInfo
            let exec_hooks: Vec<crate::execution::HookInfo> = hooks
                .into_iter()
                .map(|h| crate::execution::HookInfo {
                    hook_name: h.name,
                    actor: h.target,
                })
                .collect();

            // Convert event::ConditionHandlerInfo -> execution::ConditionHandlerInfo
            let exec_handlers: Vec<crate::execution::ConditionHandlerInfo> = cond_handlers
                .into_iter()
                .map(|h| crate::execution::ConditionHandlerInfo {
                    target: h.bearer,
                    condition_name: h.condition_name,
                    instance_id: h.instance_id,
                    handler_index: h.clause_index,
                })
                .collect();

            if exec_hooks.is_empty() && exec_handlers.is_empty() {
                // No hooks or condition handlers — fast path.
                // No depth/lifecycle changes needed since nobody
                // ran. Just complete.
                return Advance::Pop(Value::Void);
            }

            // Push EmitHooks frame (it will handle hooks, then
            // push EmitConditionHandlers when done).
            // EmitHooks increments emit_depth and clears
            // in_lifecycle_block; this frame restores them
            // when it receives the child result.
            Advance::Push(Frame::EmitHooks {
                hooks: exec_hooks,
                condition_handlers: exec_handlers,
                index: 0,
                payload,
                initialized: false,
                child_result: None,
            })
        }
    }
}

pub(super) fn advance_emit_hooks(
    frame: &mut Frame,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    _sp: &dyn StateProvider,
    _eh: &mut dyn EffectHandler,
    _tracker: &MutationTracker,
) -> Advance {
    let Frame::EmitHooks {
        hooks,
        condition_handlers,
        index,
        payload,
        initialized,
        child_result,
    } = frame
    else {
        unreachable!()
    };

    // Handle completed child ActionLifecycle (hook execution).
    if let Some(result) = child_result.take() {
        match result {
            Ok(_) => {
                *index += 1;
                // Fall through to dispatch next hook.
            }
            Err(e) => return Advance::Error(e),
        }
    }

    // First entry: set up emit_depth and clear in_lifecycle_block.
    if !*initialized {
        *initialized = true;
        env.emit_depth += 1;
        env.in_lifecycle_block = 0;
    }

    // Dispatch hooks one at a time.
    if *index < hooks.len() {
        let hook_info = &hooks[*index];
        let hook_decl = match core.program.hooks.get(&hook_info.hook_name) {
            Some(d) => d.clone(),
            None => {
                return Advance::Error(RuntimeError::new(format!(
                    "undefined hook '{}'",
                    hook_info.hook_name
                )));
            }
        };

        let inv_id = match core.alloc_invocation_id() {
            Ok(id) => InvocationId(id),
            Err(e) => return Advance::Error(e),
        };

        return Advance::Push(Frame::ActionLifecycle {
            name: hook_decl.name.clone(),
            actor: hook_info.actor,
            action_kind: ActionKind::Hook {
                event: hook_decl.trigger.event_name.clone(),
                trigger: payload.clone(),
            },
            call_span: Span::default(),
            has_return_type: false,
            inv_id,
            requires: None,
            cost: None,
            resolve: hook_decl.resolve.clone(),
            receiver_name: hook_decl.receiver_name.clone(),
            bindings: vec![(Name::from("trigger"), payload.clone())],
            default_params: Vec::new(),
            step: ActionStep::EmitStarted,
            pending: None,
            body_result: None,
            cost_aborted: false,
            saved_turn_actor: None,
            saved_invocation: None,
        });
    }

    // All hooks dispatched. Push EmitConditionHandlers if any,
    // otherwise complete.
    let handlers = std::mem::take(condition_handlers);
    if handlers.is_empty() {
        Advance::Pop(Value::Void)
    } else {
        let p = payload.clone();
        Advance::Push(Frame::EmitConditionHandlers {
            handlers,
            index: 0,
            payload: p,
            child_result: None,
        })
    }
}

pub(super) fn advance_emit_condition_handlers(
    frame: &mut Frame,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    sp: &dyn StateProvider,
    _eh: &mut dyn EffectHandler,
    _tracker: &MutationTracker,
) -> Advance {
    let Frame::EmitConditionHandlers {
        handlers,
        index,
        payload,
        child_result,
    } = frame
    else {
        unreachable!()
    };

    // Handle completed child ConditionHandlerEpilogue.
    if let Some(result) = child_result.take() {
        match result {
            Ok(_) => {
                *index += 1;
                // Fall through to dispatch next handler.
            }
            Err(e) => return Advance::Error(e),
        }
    }

    // Dispatch handlers one at a time.
    while *index < handlers.len() {
        let handler_info = &handlers[*index];
        let bearer = handler_info.target;

        // 1. Look up condition declaration.
        let decl = match core
            .program
            .conditions
            .get(handler_info.condition_name.as_str())
        {
            Some(d) => d.clone(),
            None => {
                return Advance::Error(RuntimeError::new(format!(
                    "undefined condition '{}' in event handler",
                    handler_info.condition_name
                )));
            }
        };

        // 2. Verify condition still exists on bearer (snapshot safety).
        let cond_instance = {
            let conditions = sp.read_conditions(&bearer).unwrap_or_default();
            match conditions
                .into_iter()
                .find(|c| c.id == handler_info.instance_id)
            {
                Some(c) => c,
                None => {
                    // Condition was removed — skip.
                    *index += 1;
                    continue;
                }
            }
        };

        // 3. Get the on-event clause body.
        let clause_body = match decl.clauses.get(handler_info.handler_index) {
            Some(ttrpg_ast::ast::ConditionClause::OnEvent(oe)) => oe.body.clone(),
            _ => {
                *index += 1;
                continue;
            }
        };

        // Snapshot current state for delta detection.
        let original_state = cond_instance.state_fields.clone();

        // 4. Push scope with proper bindings.
        env.push_scope();
        env.bind(decl.receiver_name.clone(), Value::Entity(bearer));
        env.bind("self".into(), cond_instance.to_value());
        for (pname, pval) in &cond_instance.params {
            env.bind(pname.clone(), pval.clone());
        }
        if !cond_instance.state_fields.is_empty() {
            env.bind(
                Name::from("state"),
                Value::Struct {
                    name: Name::from("state"),
                    fields: cond_instance.state_fields.clone(),
                },
            );
        }
        env.bind(Name::from("trigger"), payload.clone());

        // Push ConditionHandlerEpilogue as child. On its first
        // advance it pushes the Block; when the Block completes
        // it reads back state, pops scope, emits effects, and
        // pops itself. Its result then comes back here.
        return Advance::Push(Frame::ConditionHandlerEpilogue {
            target: bearer,
            instance_id: handler_info.instance_id,
            original_state,
            block_stmts: Some(clause_body.node),
            child_result: None,
            awaiting_yield: false,
        });
    }

    // All handlers dispatched.
    Advance::Pop(Value::Void)
}
