use ttrpg_ast::ast::Arg;
use ttrpg_ast::{Name, Span, Spanned};
use ttrpg_checker::env::ParamInfo;

use crate::effect::{Effect, Response};
use crate::eval::{eval_block, eval_expr};
use crate::pipeline::{collect_modifiers_owned, emit_modify_applied_events, run_phase1, run_phase2};
use crate::value::{value_matches_ty, value_type_display, Value};
use crate::Env;
use crate::RuntimeError;

use super::args::bind_args;

// ── Public entry point for derive/mechanic with pre-evaluated args ──

/// Evaluate a derive or mechanic function with pre-evaluated positional arguments.
///
/// Used by the public API (`Interpreter::evaluate_derive`, `Interpreter::evaluate_mechanic`)
/// where arguments are already `Value`s rather than AST expressions.
pub(crate) fn evaluate_fn_with_values(
    env: &mut Env,
    name: &str,
    args: Vec<Value>,
    call_span: Span,
) -> Result<Value, RuntimeError> {
    let fn_decl = env
        .interp
        .program
        .derives
        .get(name)
        .or_else(|| env.interp.program.mechanics.get(name))
        .ok_or_else(|| {
            RuntimeError::with_span(format!("undefined function '{}'", name), call_span)
        })?;

    let ast_params = fn_decl.params.clone();
    let body = fn_decl.body.clone();

    let fn_info = env
        .interp
        .type_env
        .lookup_fn(name)
        .ok_or_else(|| {
            RuntimeError::with_span(
                format!("internal error: no type info for function '{}'", name),
                call_span,
            )
        })?
        .clone();

    // Map positional args to param names
    if args.len() > fn_info.params.len() {
        return Err(RuntimeError::with_span(
            format!(
                "too many arguments: '{}' takes {} params, got {}",
                name,
                fn_info.params.len(),
                args.len()
            ),
            call_span,
        ));
    }

    let mut bound: Vec<(Name, Value)> = Vec::new();
    for (i, val) in args.into_iter().enumerate() {
        bound.push((fn_info.params[i].name.clone(), val));
    }

    // Fill defaults for missing optional params
    for i in bound.len()..fn_info.params.len() {
        if fn_info.params[i].has_default {
            if let Some(default_expr) = ast_params.get(i).and_then(|p| p.default.as_ref()) {
                env.push_scope();
                for (pname, pval) in &bound {
                    env.bind(pname.clone(), pval.clone());
                }
                let result = eval_expr(env, default_expr);
                env.pop_scope();
                bound.push((fn_info.params[i].name.clone(), result?));
            }
        } else {
            return Err(RuntimeError::with_span(
                format!(
                    "missing required argument '{}' for '{}'",
                    fn_info.params[i].name, name
                ),
                call_span,
            ));
        }
    }

    // Collect modifiers, Phase 1, execute body, Phase 2
    let modifiers = collect_modifiers_owned(env, name, &fn_info, &bound)?;

    let bound = if modifiers.is_empty() {
        bound
    } else {
        run_phase1(env, name, &fn_info, bound, &modifiers)?
    };

    env.push_scope();
    for (param_name, param_val) in &bound {
        env.bind(param_name.clone(), param_val.clone());
    }

    let result = eval_block(env, &body);
    env.pop_scope();

    let val = match result {
        Ok(val) => {
            if modifiers.is_empty() {
                val
            } else {
                run_phase2(env, name, &fn_info, &bound, val, &modifiers)?
            }
        }
        Err(e) => return Err(e),
    };

    // Emit modify_applied events for any condition modifiers that fired
    if !modifiers.is_empty() {
        emit_modify_applied_events(env, &modifiers, name, call_span)?;
    }

    Ok(val)
}

// ── Derive / Mechanic dispatch ─────────────────────────────────

pub(super) fn dispatch_derive_or_mechanic(
    env: &mut Env,
    name: &str,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    // Look up the declaration
    let fn_decl = env
        .interp
        .program
        .derives
        .get(name)
        .or_else(|| env.interp.program.mechanics.get(name))
        .ok_or_else(|| {
            RuntimeError::with_span(
                format!(
                    "internal error: no declaration found for function '{}'",
                    name
                ),
                call_span,
            )
        })?;

    // Clone what we need from the declaration before mutably borrowing env
    let ast_params = fn_decl.params.clone();
    let body = fn_decl.body.clone();

    // Get the FnInfo for parameter type info
    let fn_info = env
        .interp
        .type_env
        .lookup_fn(name)
        .ok_or_else(|| {
            RuntimeError::with_span(
                format!("internal error: no type info for function '{}'", name),
                call_span,
            )
        })?
        .clone();

    // Bind arguments (with access to AST params for default expressions)
    let bound = bind_args(&fn_info.params, args, Some(&ast_params), env, call_span)?;

    // Collect modifiers from conditions and options
    let modifiers = collect_modifiers_owned(env, name, &fn_info, &bound)?;

    // Phase 1: rewrite input parameters
    let bound = if modifiers.is_empty() {
        bound
    } else {
        run_phase1(env, name, &fn_info, bound, &modifiers)?
    };

    // Push scope and bind (possibly modified) parameters
    env.push_scope();
    for (param_name, param_val) in &bound {
        env.bind(param_name.clone(), param_val.clone());
    }

    let result = eval_block(env, &body);
    env.pop_scope();

    // Phase 2: rewrite output result
    let val = match result {
        Ok(val) => {
            if modifiers.is_empty() {
                val
            } else {
                run_phase2(env, name, &fn_info, &bound, val, &modifiers)?
            }
        }
        Err(e) => return Err(e),
    };

    // Emit modify_applied events for any condition modifiers that fired
    if !modifiers.is_empty() {
        emit_modify_applied_events(env, &modifiers, name, call_span)?;
    }

    Ok(val)
}

// ── Table dispatch ─────────────────────────────────────────────

/// Evaluate a table lookup by matching arguments against table entry keys.
pub(super) fn dispatch_table(
    env: &mut Env,
    name: &str,
    param_infos: &[ParamInfo],
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    // Look up the table declaration
    let table_decl = env.interp.program.tables.get(name).ok_or_else(|| {
        RuntimeError::with_span(
            format!("internal error: no declaration found for table '{}'", name),
            call_span,
        )
    })?;
    let ast_params: Vec<ttrpg_ast::ast::Param> = table_decl.params.clone();

    // Bind arguments
    let bound = bind_args(param_infos, args, Some(&ast_params), env, call_span)?;
    let arg_values: Vec<Value> = bound.iter().map(|(_, v)| v.clone()).collect();

    dispatch_table_core(env, name, arg_values, call_span)
}

/// Evaluate a table lookup with pre-evaluated argument values.
pub(crate) fn dispatch_table_with_values(
    env: &mut Env,
    name: &str,
    args: Vec<Value>,
    call_span: Span,
) -> Result<Value, RuntimeError> {
    if !env.interp.program.tables.contains_key(name) {
        return Err(RuntimeError::with_span(
            format!("undefined table '{}'", name),
            call_span,
        ));
    }
    dispatch_table_core(env, name, args, call_span)
}

/// Core table matching logic shared by both dispatch paths.
fn dispatch_table_core(
    env: &mut Env,
    name: &str,
    arg_values: Vec<Value>,
    call_span: Span,
) -> Result<Value, RuntimeError> {
    use ttrpg_ast::ast::TableKey;

    let table_decl = env.interp.program.tables.get(name).ok_or_else(|| {
        RuntimeError::with_span(
            format!("internal error: no declaration found for table '{}'", name),
            call_span,
        )
    })?;
    let entries = table_decl.entries.clone();

    // Try each entry in order
    for entry in &entries {
        let mut matches = true;
        for (key, arg_val) in entry.keys.iter().zip(arg_values.iter()) {
            match &key.node {
                TableKey::Wildcard => {
                    // Always matches
                }
                TableKey::Expr(expr_kind) => {
                    let key_expr = Spanned {
                        node: expr_kind.clone(),
                        span: key.span,
                    };
                    let key_val = eval_expr(env, &key_expr)?;
                    if !crate::eval::value_eq(env.state, &key_val, arg_val) {
                        matches = false;
                        break;
                    }
                }
                TableKey::Range { start, end } => {
                    let start_val = eval_expr(env, start)?;
                    let end_val = eval_expr(env, end)?;
                    match (arg_val, &start_val, &end_val) {
                        (Value::Int(v), Value::Int(lo), Value::Int(hi)) => {
                            if *v < *lo || *v > *hi {
                                matches = false;
                                break;
                            }
                        }
                        _ => {
                            matches = false;
                            break;
                        }
                    }
                }
            }
        }
        if matches {
            return eval_expr(env, &entry.value);
        }
    }

    Err(RuntimeError::with_span(
        format!(
            "no matching entry in table '{}' for arguments: {}",
            name,
            arg_values
                .iter()
                .map(|v| format!("{:?}", v))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        call_span,
    ))
}

// ── Prompt dispatch ────────────────────────────────────────────

pub(super) fn dispatch_prompt(
    env: &mut Env,
    name: &str,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    let prompt_decl = env.interp.program.prompts.get(name).ok_or_else(|| {
        RuntimeError::with_span(
            format!("internal error: no declaration found for prompt '{}'", name),
            call_span,
        )
    })?;

    let hint = prompt_decl.hint.clone();
    let suggest_expr = prompt_decl.suggest.clone();
    let ast_params = prompt_decl.params.clone();

    // Get the FnInfo for parameter info
    let fn_info = env
        .interp
        .type_env
        .lookup_fn(name)
        .ok_or_else(|| {
            RuntimeError::with_span(
                format!("internal error: no type info for prompt '{}'", name),
                call_span,
            )
        })?
        .clone();

    // Bind arguments
    let bound = bind_args(&fn_info.params, args, Some(&ast_params), env, call_span)?;
    let return_type = fn_info.return_type.clone();

    // Evaluate suggest expression if present
    let suggest = match &suggest_expr {
        Some(expr) => {
            // Push scope with params for suggest evaluation
            env.push_scope();
            for (pn, pv) in &bound {
                env.bind(pn.clone(), pv.clone());
            }
            let val = eval_expr(env, expr);
            env.pop_scope();
            Some(val?)
        }
        None => None,
    };

    // Emit ResolvePrompt effect
    let effect = Effect::ResolvePrompt {
        name: Name::from(name),
        params: bound,
        return_type: return_type.clone(),
        hint,
        suggest,
    };
    let response = env.handler.handle(effect);

    match response {
        Response::PromptResult(val) | Response::Override(val) => {
            if !value_matches_ty(&val, &return_type, env.state) {
                return Err(RuntimeError::with_span(
                    format!(
                        "prompt '{}' expected return type {}, got {}",
                        name,
                        return_type.display(),
                        value_type_display(&val),
                    ),
                    call_span,
                ));
            }
            Ok(val)
        }
        _ => Err(RuntimeError::with_span(
            format!(
                "protocol error: expected PromptResult or Override response for ResolvePrompt, got {:?}",
                response
            ),
            call_span,
        )),
    }
}
