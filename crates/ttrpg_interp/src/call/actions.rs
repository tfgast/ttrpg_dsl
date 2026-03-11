use ttrpg_ast::ast::Arg;
use ttrpg_ast::{Name, Span};
use ttrpg_checker::ty::Ty;

use crate::Env;
use crate::RuntimeError;
use crate::action::execute_action;
use crate::eval::eval_expr;
use crate::select_action_overload;
use crate::value::Value;

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
/// Evaluates the receiver argument first to determine the entity type, then selects the
/// correct action overload and binds the remaining arguments against it. This handles
/// overloaded actions with different parameter lists per receiver type (e.g., MeleeAttack
/// on Character vs Monster).
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

    // Step 1: Find and evaluate the receiver argument to determine entity type.
    // The receiver is the first positional arg, or a named arg matching the receiver name.
    let (receiver_idx, receiver_arg) = args
        .iter()
        .enumerate()
        .find(|(_, a)| a.name.is_none())
        .or_else(|| {
            args.iter()
                .enumerate()
                .find(|(_, a)| a.name.as_ref().is_some_and(|n| *n == receiver_info.name))
        })
        .ok_or_else(|| {
            RuntimeError::with_span(
                format!("action '{name}' requires a receiver argument"),
                call_span,
            )
        })?;

    let receiver_val = eval_expr(env, &receiver_arg.value)?;
    let actor = match &receiver_val {
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

    // Step 2: Select the correct overload using the actor's entity type.
    let entity_type = env.state.entity_type_name(&actor);
    let action_decl = resolve_action_decl(env, name, entity_type.as_ref(), call_span)?;

    let recv_ty = entity_type.map_or(Ty::AnyEntity, Ty::Entity);
    let correct_fn_info = env
        .interp
        .type_env
        .lookup_action_overload(name, &recv_ty)
        .ok_or_else(|| {
            RuntimeError::with_span(
                format!(
                    "no matching overload for action '{}' on type '{}'",
                    name,
                    recv_ty.display()
                ),
                call_span,
            )
        })?
        .clone();

    // Step 3: Bind remaining args (excluding receiver) against the correct overload's params.
    let remaining_args: Vec<Arg> = args
        .iter()
        .enumerate()
        .filter(|(i, _)| *i != receiver_idx)
        .map(|(_, a)| a.clone())
        .collect();

    let ast_params = action_decl.params.clone();

    // Push receiver into scope so default expressions can reference it
    env.push_scope();
    env.bind(action_decl.receiver_name.clone(), receiver_val);
    let bound = bind_args(
        &correct_fn_info.params,
        &remaining_args,
        Some(&ast_params),
        env,
        call_span,
    );
    env.pop_scope();
    let bound = bound?;

    execute_action(env, &action_decl, actor, bound, call_span)
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

    // Get the correct overload's FnInfo (params may differ from the representative fn_info)
    let recv_ty = entity_type.map_or(Ty::AnyEntity, Ty::Entity);
    let correct_fn_info = env
        .interp
        .type_env
        .lookup_action_overload(name, &recv_ty)
        .ok_or_else(|| {
            RuntimeError::with_span(
                format!(
                    "no matching overload for action '{}' on type '{}'",
                    name,
                    recv_ty.display()
                ),
                call_span,
            )
        })?
        .clone();

    // Bind remaining arguments against the action's regular params (not receiver).
    // Push receiver into scope first so default expressions can reference it
    // (mirrors dispatch_action which includes receiver in effective_params).
    env.push_scope();
    env.bind(action_decl.receiver_name.clone(), receiver);
    let bound = bind_args(
        &correct_fn_info.params,
        args,
        Some(&ast_params),
        env,
        call_span,
    );
    env.pop_scope();
    let bound = bound?;

    execute_action(env, &action_decl, actor, bound, call_span)
}
