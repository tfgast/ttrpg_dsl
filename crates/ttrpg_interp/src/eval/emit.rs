use std::collections::BTreeMap;

use ttrpg_ast::Name;
use ttrpg_ast::Span;
use ttrpg_ast::ast::{Arg, ConditionClause};

use crate::RuntimeError;
use crate::action;
use crate::effect::Effect;
use crate::event::{self, ConditionHandlerInfo};
use crate::value::Value;
use crate::{Env, MAX_EMIT_DEPTH};

use super::dispatch::eval_expr;

/// Evaluate an `emit EventName(param: expr, ...)` statement.
///
/// Steps:
/// 1. Check emit depth limit
/// 2. Look up the EventDecl from the program
/// 3. Evaluate arg expressions, build param map
/// 4. Fill defaults for missing params
/// 5. Evaluate derived fields (event field defaults) with params in scope
/// 6. Construct payload as a struct value
/// 7. Find matching hooks via `event::find_matching_hooks`
/// 8. Execute each matching hook inline
pub(crate) fn eval_emit(
    env: &mut Env,
    event_name: &Name,
    args: &[Arg],
    span: Span,
) -> Result<(), RuntimeError> {
    // 1. Check emit depth limit
    if env.emit_depth >= MAX_EMIT_DEPTH {
        return Err(RuntimeError::with_span(
            format!("emit depth limit ({MAX_EMIT_DEPTH}) exceeded — possible circular emit chain"),
            span,
        ));
    }

    // 2. Look up EventDecl
    let event_decl = env
        .interp
        .program
        .events
        .get(event_name)
        .ok_or_else(|| RuntimeError::with_span(format!("undefined event '{event_name}'"), span))?
        .clone();

    // 2. Evaluate arg expressions, build param map
    let mut param_map = BTreeMap::new();
    for arg in args {
        let val = eval_expr(env, &arg.value)?;
        if let Some(ref name) = arg.name {
            param_map.insert(name.clone(), val);
        }
    }

    // 3. Fill defaults for missing params
    let defaults: Vec<_> = event_decl
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
    for (name, default_expr) in &defaults {
        let val = eval_expr(env, default_expr)?;
        param_map.insert(name.clone(), val);
    }

    // 4. Evaluate derived fields with params in scope
    env.push_scope();
    for (name, val) in &param_map {
        env.bind(name.clone(), val.clone());
    }

    let mut all_fields = param_map.clone();
    let field_defaults: Vec<_> = event_decl
        .fields
        .iter()
        .filter_map(|f| f.default.clone().map(|d| (f.name.clone(), d)))
        .collect();
    for (name, default_expr) in &field_defaults {
        if !all_fields.contains_key(name) {
            match eval_expr(env, default_expr) {
                Ok(val) => {
                    all_fields.insert(name.clone(), val);
                }
                Err(e) => {
                    env.pop_scope();
                    return Err(e);
                }
            }
        }
    }
    env.pop_scope();

    // 5. Construct payload
    let payload = Value::Struct {
        name: Name::from(format!("__event_{event_name}")),
        fields: all_fields,
    };

    // 6. Get candidates and find matching hooks (off-board entities excluded)
    let candidates = env.state.entities_in_play();
    let hook_result =
        event::find_matching_hooks(env.interp, env.state, event_name, &payload, &candidates)?;

    // 7. Execute each matching hook inline (with depth tracking)
    // Save and restore in_lifecycle_block so that hooks triggered via emit
    // inside a lifecycle block can freely call apply_condition/remove_condition/revoke.
    let saved_lifecycle = env.in_lifecycle_block;
    env.in_lifecycle_block = 0;
    env.emit_depth += 1;
    let result = (|| {
        for hook_info in hook_result.hooks {
            let hook_decl = env
                .interp
                .program
                .hooks
                .get(&hook_info.name)
                .ok_or_else(|| {
                    RuntimeError::with_span(format!("undefined hook '{}'", hook_info.name), span)
                })?
                .clone();

            action::execute_hook(env, &hook_decl, hook_info.target, payload.clone(), span)?;
        }

        // 8. Execute condition event handlers (after hooks, seeing post-hook state)
        let cond_result = event::find_matching_condition_handlers(
            env.interp,
            env.state,
            event_name,
            &payload,
            &candidates,
        )?;
        for handler_info in cond_result.handlers {
            execute_condition_event_handler(env, &handler_info, payload.clone(), span)?;
        }

        Ok(())
    })();
    env.emit_depth -= 1;
    env.in_lifecycle_block = saved_lifecycle;

    result
}

/// Execute a single condition event handler.
///
/// Follows the condition handler execution pattern:
/// 1. Look up condition declaration
/// 2. Verify condition still exists on bearer (snapshot safety)
/// 3. Push scope, bind bearer/self/params/state/trigger
/// 4. Execute block body
/// 5. Read back mutated state, pop scope
/// 6. Write back state via Effect::SetConditionState
///
/// No ActionStarted/ActionCompleted — condition handlers are implicit effects
/// of the condition's existence, not actions.
pub(crate) fn execute_condition_event_handler(
    env: &mut Env,
    handler_info: &ConditionHandlerInfo,
    trigger_payload: Value,
    span: Span,
) -> Result<(), RuntimeError> {
    let bearer = handler_info.bearer;

    // 1. Look up condition declaration
    let decl = env
        .interp
        .program
        .conditions
        .get(handler_info.condition_name.as_str())
        .ok_or_else(|| {
            RuntimeError::with_span(
                format!(
                    "undefined condition '{}' in event handler",
                    handler_info.condition_name
                ),
                span,
            )
        })?
        .clone();

    // 2. Verify condition still exists on bearer (snapshot safety — may have been
    //    removed by a previous hook or handler in this emit cycle)
    let cond_instance = {
        let conditions = env.state.read_conditions(&bearer).unwrap_or_default();
        match conditions
            .into_iter()
            .find(|c| c.id == handler_info.instance_id)
        {
            Some(c) => c,
            None => return Ok(()), // condition was removed, skip silently
        }
    };

    // Get the on-event clause body
    let clause_body = match decl.clauses.get(handler_info.clause_index) {
        Some(ConditionClause::OnEvent(oe)) => oe.body.clone(),
        _ => return Ok(()),
    };

    // Thread state through execution
    let mut current_state = if cond_instance.state_fields.is_empty() {
        None
    } else {
        Some(cond_instance.state_fields.clone())
    };

    // 3. Push scope and bind variables
    env.push_scope();
    env.bind(decl.receiver_name.clone(), Value::Entity(bearer));
    env.bind("self".into(), cond_instance.to_value());
    for (pname, pval) in &cond_instance.params {
        env.bind(pname.clone(), pval.clone());
    }
    if let Some(ref state_fields) = current_state {
        env.bind(
            Name::from("state"),
            Value::Struct {
                name: Name::from("state"),
                fields: state_fields.clone(),
            },
        );
    }
    env.bind(Name::from("trigger"), trigger_payload);

    // 4. Execute block body
    let result = super::eval_block(env, &clause_body);

    // 5. Read back mutated state before popping scope
    if current_state.is_some()
        && let Some(Value::Struct { fields, .. }) = env.lookup(&Name::from("state")).cloned()
    {
        current_state = Some(fields);
    }
    env.pop_scope();
    env.return_value = None;
    result?;

    // 6. Write back state via Effect::SetConditionState
    if let Some(final_state) = current_state
        && !final_state.is_empty()
    {
        let effect = Effect::SetConditionState {
            target: bearer,
            condition_id: cond_instance.id,
            fields: final_state,
        };
        env.emit(effect);
    }

    Ok(())
}
