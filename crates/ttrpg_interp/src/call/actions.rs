use ttrpg_ast::ast::{Arg, Param};
use ttrpg_ast::{Name, Span};
use ttrpg_checker::env::ParamInfo;

use crate::action::execute_action;
use crate::value::Value;
use crate::Env;
use crate::RuntimeError;

use super::args::bind_args;

// ── Action dispatch ────────────────────────────────────────────

/// Dispatch an action call from within DSL code (nested action calls from resolve blocks).
///
/// Extracts the receiver EntityRef from the effective argument list (receiver as first param,
/// mirroring the checker's effective_params construction) and delegates to the action pipeline.
pub(super) fn dispatch_action(
    env: &mut Env,
    fn_info: &ttrpg_checker::env::FnInfo,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    let name = &fn_info.name;

    // Look up action declaration and clone what we need before borrowing env mutably
    let action_decl = env
        .interp
        .program
        .actions
        .get(name.as_str())
        .ok_or_else(|| {
            RuntimeError::with_span(
                format!("internal error: no declaration found for action '{}'", name),
                call_span,
            )
        })?;
    let action_decl = action_decl.clone();
    let ast_params = action_decl.params.clone();
    let receiver_type = action_decl.receiver_type.clone();

    // Get receiver info (actions always have a receiver)
    let receiver_info = fn_info
        .receiver
        .as_ref()
        .ok_or_else(|| {
            RuntimeError::with_span(
                format!("internal error: action '{}' has no receiver info", name),
                call_span,
            )
        })?
        .clone();

    // Build effective parameter list: receiver as first param, then regular params.
    // This mirrors the checker's effective_params construction (check_expr.rs).
    let effective_params: Vec<ParamInfo> = {
        let mut params = vec![receiver_info.clone()];
        params.extend(fn_info.params.iter().cloned());
        params
    };

    // Build aligned AST params with placeholder for receiver (for default evaluation).
    // The receiver has has_default: false, so bind_args won't evaluate a default for it.
    let effective_ast_params: Vec<Param> = {
        let mut params = vec![Param {
            name: receiver_info.name.clone(),
            ty: receiver_type,
            default: None,
            with_groups: vec![],
            span: call_span,
        }];
        params.extend(ast_params);
        params
    };

    // Bind all arguments (receiver + regular params)
    let bound = bind_args(
        &effective_params,
        args,
        Some(&effective_ast_params),
        env,
        call_span,
    )?;

    // Extract receiver EntityRef from the first bound argument
    let actor = match &bound[0].1 {
        Value::Entity(entity_ref) => *entity_ref,
        other => {
            return Err(RuntimeError::with_span(
                format!(
                    "action '{}' receiver '{}' must be an entity, got {:?}",
                    name, receiver_info.name, other
                ),
                call_span,
            ));
        }
    };

    // Remaining bound arguments (skip receiver) are the action's regular params
    let action_args: Vec<(Name, Value)> = bound[1..].to_vec();

    execute_action(env, &action_decl, actor, action_args, call_span)
}

/// Dispatch an action via method-call syntax: `entity.ActionName(args)`.
///
/// The receiver entity is already evaluated (the `object` value). Remaining
/// arguments are bound against the action's declared params (not including
/// the receiver). This desugars to the same `execute_action` pipeline.
pub(super) fn dispatch_action_method(
    env: &mut Env,
    fn_info: &ttrpg_checker::env::FnInfo,
    receiver: Value,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    let name = &fn_info.name;

    let action_decl = env
        .interp
        .program
        .actions
        .get(name.as_str())
        .ok_or_else(|| {
            RuntimeError::with_span(
                format!("internal error: no declaration found for action '{}'", name),
                call_span,
            )
        })?
        .clone();
    let ast_params = action_decl.params.clone();

    // Extract EntityRef from receiver value
    let actor = match &receiver {
        Value::Entity(entity_ref) => *entity_ref,
        other => {
            return Err(RuntimeError::with_span(
                format!(
                    "action '{}' receiver must be an entity, got {:?}",
                    name, other
                ),
                call_span,
            ));
        }
    };

    // Bind remaining arguments against the action's regular params (not receiver)
    let bound = bind_args(&fn_info.params, args, Some(&ast_params), env, call_span)?;

    execute_action(env, &action_decl, actor, bound, call_span)
}
