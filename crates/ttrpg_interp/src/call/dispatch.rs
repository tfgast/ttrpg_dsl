use std::collections::BTreeMap;

use ttrpg_ast::ast::{Arg, ExprKind};
use ttrpg_ast::{Name, Span, Spanned};
use ttrpg_checker::env::{DeclInfo, FnKind};

use crate::builtins::call_builtin;
use crate::eval::eval_expr;
use crate::value::Value;
use crate::Env;
use crate::RuntimeError;

use super::actions::{dispatch_action, dispatch_action_method};
use super::args::bind_args;
use super::collection_builtins::{
    eval_all, eval_any, eval_append, eval_concat, eval_first, eval_keys, eval_last, eval_len,
    eval_reverse, eval_some, eval_sort, eval_sum, eval_values,
};
use super::functions::{dispatch_derive_or_mechanic, dispatch_prompt, dispatch_table};
use super::methods::eval_method_call;
use super::ordinals::{eval_from_ordinal, eval_ordinal, eval_try_from_ordinal};
use super::variants::construct_enum_variant;

// ── Call dispatch ───────────────────────────────────────────────

/// Evaluate a function call expression.
///
/// Resolves the callee syntactically (function names are not first-class),
/// dispatches based on `FnKind`, and handles enum variant construction.
pub(crate) fn eval_call(
    env: &mut Env,
    callee: &Spanned<ExprKind>,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    match &callee.node {
        // ── Simple identifier: bare enum variant or function name ──
        ExprKind::Ident(name) => {
            // 1. Check if it's a bare enum variant (via resolution table or unique owner).
            //    Variants shadow functions with the same name, matching the
            //    checker's resolution order (check_expr.rs:630).
            let resolved = env
                .interp
                .type_env
                .resolved_variants
                .get(&callee.span)
                .cloned()
                .or_else(|| env.interp.type_env.unique_variant_owner(name).cloned());
            if let Some(enum_name) = resolved {
                return construct_enum_variant(env, &enum_name, name, args, call_span);
            }

            // 2. Check ordinal() / from_ordinal() builtins
            if name == "ordinal" {
                return eval_ordinal(env, args, call_span);
            }
            if name == "from_ordinal" {
                return eval_from_ordinal(env, args, call_span);
            }
            if name == "try_from_ordinal" {
                return eval_try_from_ordinal(env, args, call_span);
            }

            // 3. Check collection builtins
            match name.as_str() {
                "len" => return eval_len(env, args, call_span),
                "keys" => return eval_keys(env, args, call_span),
                "values" => return eval_values(env, args, call_span),
                "first" => return eval_first(env, args, call_span),
                "last" => return eval_last(env, args, call_span),
                "append" => return eval_append(env, args, call_span),
                "concat" => return eval_concat(env, args, call_span),
                "reverse" => return eval_reverse(env, args, call_span),
                "sum" => return eval_sum(env, args, call_span),
                "any" => return eval_any(env, args, call_span),
                "all" => return eval_all(env, args, call_span),
                "sort" => return eval_sort(env, args, call_span),
                "some" => return eval_some(env, args, call_span),
                _ => {}
            }

            // 4. Check if it's a condition with parameters (e.g., Frightened(source: attacker))
            if let Some(cond_decl) = env.interp.program.conditions.get(name.as_str()) {
                let cond_decl = cond_decl.clone();
                // Reuse bind_args for named arg resolution + default materialization
                let param_infos = env
                    .interp
                    .type_env
                    .conditions
                    .get(name.as_str())
                    .map(|ci| ci.params.clone())
                    .unwrap_or_default();
                let bound = bind_args(&param_infos, args, Some(&cond_decl.params), env, call_span)?;
                let cond_args: BTreeMap<Name, Value> = bound.into_iter().collect();
                return Ok(Value::Condition {
                    name: name.clone(),
                    args: cond_args,
                });
            }

            // 4. Check if it's a function (user-defined or builtin)
            if let Some(fn_info) = env.interp.type_env.lookup_fn(name) {
                let fn_info = fn_info.clone();
                return dispatch_fn(env, &fn_info, args, call_span);
            }

            Err(RuntimeError::with_span(
                format!("undefined function '{}'", name),
                call_span,
            ))
        }

        // ── Qualified access: enum constructor (e.g. Duration.rounds(3)) ──
        ExprKind::FieldAccess { object, field } => {
            if let ExprKind::Ident(obj_name) = &object.node {
                if let Some(DeclInfo::Enum(_)) = env.interp.type_env.types.get(obj_name.as_str()) {
                    return construct_enum_variant(env, obj_name, field, args, call_span);
                }
            }
            // Action method call: entity.Action(args)
            if let Some(fn_info) = env.interp.type_env.lookup_fn(field) {
                if fn_info.kind == FnKind::Action {
                    let fn_info = fn_info.clone();
                    let object_val = eval_expr(env, object)?;
                    return dispatch_action_method(env, &fn_info, object_val, args, call_span);
                }
            }
            // Method call: evaluate the object and dispatch
            let object_val = eval_expr(env, object)?;
            eval_method_call(env, object_val, field, args, call_span)
        }

        _ => Err(RuntimeError::with_span(
            "invalid callee expression",
            call_span,
        )),
    }
}

// ── Function dispatch by kind ──────────────────────────────────

fn dispatch_fn(
    env: &mut Env,
    fn_info: &ttrpg_checker::env::FnInfo,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    match fn_info.kind {
        FnKind::Derive => dispatch_derive_or_mechanic(env, &fn_info.name, args, call_span),
        FnKind::Mechanic => dispatch_derive_or_mechanic(env, &fn_info.name, args, call_span),
        FnKind::Prompt => dispatch_prompt(env, &fn_info.name, args, call_span),
        FnKind::Builtin => {
            // Builtins have no defaults — all params are required
            let bound = bind_args(&fn_info.params, args, None, env, call_span)?;
            let arg_values: Vec<Value> = bound.into_iter().map(|(_, v)| v).collect();
            call_builtin(env, &fn_info.name, arg_values, call_span)
        }
        FnKind::Table => dispatch_table(env, &fn_info.name, &fn_info.params, args, call_span),
        FnKind::Action => dispatch_action(env, fn_info, args, call_span),
        FnKind::Reaction | FnKind::Hook => {
            // The checker rejects direct reaction/hook calls; this is unreachable.
            Err(RuntimeError::with_span(
                "internal error: reactions and hooks cannot be called directly",
                call_span,
            ))
        }
    }
}
