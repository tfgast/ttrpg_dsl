use std::collections::BTreeMap;

use ttrpg_ast::ast::Arg;
use ttrpg_ast::Name;
use ttrpg_ast::Span;

use crate::action;
use crate::event;
use crate::value::Value;
use crate::{Env, MAX_EMIT_DEPTH};
use crate::RuntimeError;

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
            format!(
                "emit depth limit ({}) exceeded — possible circular emit chain",
                MAX_EMIT_DEPTH
            ),
            span,
        ));
    }

    // 2. Look up EventDecl
    let event_decl = env
        .interp
        .program
        .events
        .get(event_name)
        .ok_or_else(|| {
            RuntimeError::with_span(format!("undefined event '{}'", event_name), span)
        })?
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
            let val = eval_expr(env, &default_expr)?;
            all_fields.insert(name.clone(), val);
        }
    }
    env.pop_scope();

    // 5. Construct payload
    let payload = Value::Struct {
        name: Name::from(format!("__event_{}", event_name)),
        fields: all_fields,
    };

    // 6. Get candidates and find matching hooks
    let candidates = env.state.all_entities();
    let hook_result =
        event::find_matching_hooks(env.interp, env.state, event_name, &payload, &candidates)?;

    // 7. Execute each matching hook inline (with depth tracking)
    env.emit_depth += 1;
    let result = (|| {
        for hook_info in hook_result.hooks {
            let hook_decl = env
                .interp
                .program
                .hooks
                .get(&hook_info.name)
                .ok_or_else(|| {
                    RuntimeError::with_span(
                        format!("undefined hook '{}'", hook_info.name),
                        span,
                    )
                })?
                .clone();

            action::execute_hook(env, &hook_decl, hook_info.target, payload.clone(), span)?;
        }
        Ok(())
    })();
    env.emit_depth -= 1;

    result
}
