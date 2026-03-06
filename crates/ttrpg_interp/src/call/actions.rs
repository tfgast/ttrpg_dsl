use ttrpg_ast::ast::{Arg, Param, WithClause};
use ttrpg_ast::{Name, Span};
use ttrpg_checker::env::ParamInfo;

use crate::action::execute_action;
use crate::select_action_overload;
use crate::value::Value;
use crate::Env;
use crate::RuntimeError;

use super::args::bind_args;

// ── Action dispatch ────────────────────────────────────────────

/// Look up the action overloads by name and select the best match for the given entity.
fn resolve_action_decl(
    env: &Env,
    name: &str,
    entity_type: Option<&Name>,
    call_span: Span,
) -> Result<ttrpg_ast::ast::ActionDecl, RuntimeError> {
    let overloads = env.interp.program.actions.get(name).ok_or_else(|| {
        RuntimeError::with_span(
            format!("internal error: no declaration found for action '{name}'"),
            call_span,
        )
    })?;

    select_action_overload(overloads, entity_type)
        .cloned()
        .ok_or_else(|| {
            RuntimeError::with_span(
                format!(
                    "no matching overload for action '{}' on entity type '{}'",
                    name,
                    entity_type.map_or("unknown", |n| n.as_str())
                ),
                call_span,
            )
        })
}

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

    // Get receiver info (actions always have a receiver)
    let receiver_info = fn_info
        .receiver
        .as_ref()
        .ok_or_else(|| {
            RuntimeError::with_span(
                format!("internal error: action '{name}' has no receiver info"),
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

    // We need to bind args first to get the receiver value, then resolve the overload.
    // Use a temporary placeholder action decl for the receiver type in AST params.
    // The receiver has has_default: false, so bind_args won't evaluate a default for it.

    // For now, build AST params from the fn_info (we'll get the real AST params after resolving).
    // We need the receiver type from fn_info for the placeholder.
    let placeholder_receiver_type = ttrpg_ast::Spanned::new(
        ttrpg_ast::ast::TypeExpr::Named(Name::from("entity")),
        call_span,
    );

    let effective_ast_params: Vec<Param> = {
        let mut params = vec![Param {
            name: receiver_info.name.clone(),
            ty: placeholder_receiver_type,
            default: None,
            with_groups: WithClause::default(),
            span: call_span,
        }];
        // We need the real AST params for default evaluation. Look up overloads to get them.
        // Since we don't know the entity type yet, grab the first overload's params as a
        // starting point — all overloads should have compatible signatures.
        let overloads = env.interp.program.actions.get(name.as_str());
        if let Some(overloads) = overloads {
            params.extend(overloads[0].params.clone());
        }
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

    // Now resolve the correct overload using the actor's entity type
    let entity_type = env.state.entity_type_name(&actor);
    let action_decl = resolve_action_decl(env, name, entity_type.as_ref(), call_span)?;

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

    // Extract EntityRef from receiver value
    let actor = match &receiver {
        Value::Entity(entity_ref) => *entity_ref,
        other => {
            return Err(RuntimeError::with_span(
                format!("action '{name}' receiver must be an entity, got {other:?}"),
                call_span,
            ));
        }
    };

    // Resolve the correct overload using the actor's entity type
    let entity_type = env.state.entity_type_name(&actor);
    let action_decl = resolve_action_decl(env, name, entity_type.as_ref(), call_span)?;
    let ast_params = action_decl.params.clone();

    // Bind remaining arguments against the action's regular params (not receiver).
    // Push receiver into scope first so default expressions can reference it
    // (mirrors dispatch_action which includes receiver in effective_params).
    env.push_scope();
    env.bind(action_decl.receiver_name.clone(), receiver);
    let bound = bind_args(&fn_info.params, args, Some(&ast_params), env, call_span);
    env.pop_scope();
    let bound = bound?;

    execute_action(env, &action_decl, actor, bound, call_span)
}
