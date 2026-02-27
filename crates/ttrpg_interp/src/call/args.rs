use ttrpg_ast::ast::{Arg, Param};
use ttrpg_ast::{Name, Span};
use ttrpg_checker::env::ParamInfo;

use crate::eval::eval_expr;
use crate::value::Value;
use crate::Env;
use crate::RuntimeError;

// ── Argument binding ───────────────────────────────────────────

/// Match call arguments to function parameters.
///
/// `ast_params` provides the AST parameter declarations (with default expressions)
/// when available. For builtins and enum constructors, this is `None`.
///
/// Returns a list of (param_name, value) pairs in parameter declaration order.
pub(super) fn bind_args(
    params: &[ParamInfo],
    args: &[Arg],
    ast_params: Option<&[Param]>,
    env: &mut Env,
    call_span: Span,
) -> Result<Vec<(Name, Value)>, RuntimeError> {
    let mut result: Vec<Option<Value>> = vec![None; params.len()];

    // Pre-pass: determine which slots are claimed by named args so positional
    // assignment knows which slots to skip. This must happen before evaluation
    // so we can evaluate all arguments in source order.
    let mut named_slots = vec![false; params.len()];
    for arg in args {
        if let Some(ref name) = arg.name {
            let pos = params.iter().position(|p| p.name == *name).ok_or_else(|| {
                RuntimeError::with_span(format!("unknown parameter '{}'", name), arg.span)
            })?;
            if named_slots[pos] {
                return Err(RuntimeError::with_span(
                    format!("duplicate argument for parameter '{}'", name),
                    arg.span,
                ));
            }
            named_slots[pos] = true;
        }
    }

    // Single pass: evaluate all arguments in source order, assigning each to
    // its correct parameter slot. This preserves side-effect ordering.
    let mut pos_iter = (0..params.len()).filter(|i| !named_slots[*i]);
    for arg in args {
        if let Some(ref name) = arg.name {
            let pos = params.iter().position(|p| p.name == *name).ok_or_else(|| {
                RuntimeError::with_span(
                    format!("internal: named arg '{}' not found after validation", name),
                    arg.span,
                )
            })?;
            let val = eval_expr(env, &arg.value)?;
            result[pos] = Some(val);
        } else {
            let pos = pos_iter.next().ok_or_else(|| {
                RuntimeError::with_span("too many positional arguments", arg.span)
            })?;
            let val = eval_expr(env, &arg.value)?;
            result[pos] = Some(val);
        }
    }

    // Pass 3: Fill defaults for unbound optional params.
    // Default expressions may reference earlier parameters (e.g., `f(a: Int, b: Int = a)`),
    // so we push a temporary scope and bind already-resolved params before evaluating defaults.
    let needs_default_scope = params
        .iter()
        .enumerate()
        .any(|(i, p)| result[i].is_none() && p.has_default);

    if needs_default_scope {
        env.push_scope();
        // Bind all already-resolved params into the scope so defaults can reference them
        for (i, param) in params.iter().enumerate() {
            if let Some(ref val) = result[i] {
                env.bind(param.name.clone(), val.clone());
            }
        }
    }

    // Collect bound params, popping scope on any exit path.
    let outcome = fill_defaults(params, &mut result, ast_params, env, call_span);

    if needs_default_scope {
        env.pop_scope();
    }

    outcome
}

/// Inner loop for pass 3 of `bind_args`: fill default values for unbound params.
///
/// Extracted so that `bind_args` can unconditionally pop_scope after this returns,
/// even on error paths.
fn fill_defaults(
    params: &[ParamInfo],
    result: &mut [Option<Value>],
    ast_params: Option<&[Param]>,
    env: &mut Env,
    call_span: Span,
) -> Result<Vec<(Name, Value)>, RuntimeError> {
    let mut bound = Vec::with_capacity(params.len());
    for (i, param) in params.iter().enumerate() {
        match result[i].take() {
            Some(val) => bound.push((param.name.clone(), val)),
            None => {
                if param.has_default {
                    let default_val = if let Some(ast_ps) = ast_params {
                        if let Some(ast_param) = ast_ps.get(i) {
                            if let Some(ref default_expr) = ast_param.default {
                                let val = eval_expr(env, default_expr)?;
                                // Bind this default into scope so later defaults can see it
                                env.bind(param.name.clone(), val.clone());
                                val
                            } else {
                                return Err(RuntimeError::with_span(
                                    format!(
                                        "internal error: parameter '{}' has_default but no default expression",
                                        param.name
                                    ),
                                    call_span,
                                ));
                            }
                        } else {
                            return Err(RuntimeError::with_span(
                                format!(
                                    "internal error: parameter index {} out of range for '{}'",
                                    i, param.name
                                ),
                                call_span,
                            ));
                        }
                    } else {
                        return Err(RuntimeError::with_span(
                            format!(
                                "internal error: no AST params available to evaluate default for '{}'",
                                param.name
                            ),
                            call_span,
                        ));
                    };
                    bound.push((param.name.clone(), default_val));
                } else {
                    return Err(RuntimeError::with_span(
                        format!("missing required argument '{}'", param.name),
                        call_span,
                    ));
                }
            }
        }
    }
    Ok(bound)
}
