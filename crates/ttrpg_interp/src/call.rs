use std::collections::BTreeMap;

use ttrpg_ast::Span;
use ttrpg_ast::Spanned;
use ttrpg_ast::ast::{Arg, ExprKind, Param};
use ttrpg_checker::env::{DeclInfo, FnKind, ParamInfo};

use crate::Env;
use crate::RuntimeError;
use crate::action::execute_action;
use crate::builtins::call_builtin;
use crate::effect::{Effect, Response};
use crate::eval::{eval_block, eval_expr, type_name};
use crate::pipeline::{collect_modifiers_owned, run_phase1, run_phase2};
use crate::value::Value;

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
            // 1. Check if it's a bare enum variant (via variant_to_enum).
            //    Variants shadow functions with the same name, matching the
            //    checker's resolution order (check_expr.rs:630).
            if let Some(enum_name) = env.interp.type_env.variant_to_enum.get(name.as_str()) {
                let enum_name = enum_name.clone();
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
                _ => {}
            }

            // 4. Check if it's a condition with parameters (e.g., Frightened(source: attacker))
            if let Some(cond_decl) = env.interp.program.conditions.get(name.as_str()) {
                let cond_decl = cond_decl.clone();
                // Reuse bind_args for named arg resolution + default materialization
                let param_infos = env.interp.type_env.conditions.get(name.as_str())
                    .map(|ci| ci.params.clone())
                    .unwrap_or_default();
                let bound = bind_args(&param_infos, args, Some(&cond_decl.params), env, call_span)?;
                let cond_args: BTreeMap<String, Value> = bound.into_iter().collect();
                return Ok(Value::Condition { name: name.to_string(), args: cond_args });
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
                if let Some(DeclInfo::Enum(_)) =
                    env.interp.type_env.types.get(obj_name.as_str())
                {
                    return construct_enum_variant(
                        env, obj_name, field, args, call_span,
                    );
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

// ── ordinal / from_ordinal builtins ────────────────────────────

fn eval_ordinal(
    env: &mut Env,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    let val = eval_expr(env, &args[0].value)?;
    match &val {
        Value::EnumVariant { enum_name, variant, .. } => {
            let ordinal = crate::eval::variant_ordinal(env.interp.type_env, enum_name, variant)
                .ok_or_else(|| {
                    RuntimeError::with_span(
                        format!("unknown variant `{}` of enum `{}`", variant, enum_name),
                        call_span,
                    )
                })?;
            Ok(Value::Int(ordinal as i64))
        }
        _ => Err(RuntimeError::with_span(
            format!("ordinal() expects an enum variant, got {}", type_name(&val)),
            call_span,
        )),
    }
}

fn eval_from_ordinal(
    env: &mut Env,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    let ns_val = eval_expr(env, &args[0].value)?;
    let idx_val = eval_expr(env, &args[1].value)?;

    let enum_name = match &ns_val {
        Value::EnumNamespace(name) => name.clone(),
        _ => {
            return Err(RuntimeError::with_span(
                format!("from_ordinal() first argument must be an enum type, got {}", type_name(&ns_val)),
                call_span,
            ));
        }
    };

    let idx = match &idx_val {
        Value::Int(n) => *n,
        _ => {
            return Err(RuntimeError::with_span(
                format!("from_ordinal() second argument must be int, got {}", type_name(&idx_val)),
                call_span,
            ));
        }
    };

    if idx < 0 {
        return Err(RuntimeError::with_span(
            format!("from_ordinal() index must be non-negative, got {}", idx),
            call_span,
        ));
    }

    let info = match env.interp.type_env.types.get(enum_name.as_str()) {
        Some(DeclInfo::Enum(info)) => info,
        _ => {
            return Err(RuntimeError::with_span(
                format!("unknown enum `{}`", enum_name),
                call_span,
            ));
        }
    };

    let idx_usize = idx as usize;
    if idx_usize >= info.variants.len() {
        return Err(RuntimeError::with_span(
            format!(
                "from_ordinal() index {} out of range for enum `{}` (0..{})",
                idx, enum_name, info.variants.len()
            ),
            call_span,
        ));
    }

    let variant = &info.variants[idx_usize];
    if !variant.fields.is_empty() {
        return Err(RuntimeError::with_span(
            format!(
                "from_ordinal() cannot construct variant `{}` of `{}` — it has payload fields",
                variant.name, enum_name
            ),
            call_span,
        ));
    }

    Ok(Value::EnumVariant {
        enum_name,
        variant: variant.name.clone(),
        fields: BTreeMap::new(),
    })
}

fn eval_try_from_ordinal(
    env: &mut Env,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    let ns_val = eval_expr(env, &args[0].value)?;
    let idx_val = eval_expr(env, &args[1].value)?;

    let enum_name = match &ns_val {
        Value::EnumNamespace(name) => name.clone(),
        _ => {
            return Err(RuntimeError::with_span(
                format!("try_from_ordinal() first argument must be an enum type, got {}", type_name(&ns_val)),
                call_span,
            ));
        }
    };

    let idx = match &idx_val {
        Value::Int(n) => *n,
        _ => {
            return Err(RuntimeError::with_span(
                format!("try_from_ordinal() second argument must be int, got {}", type_name(&idx_val)),
                call_span,
            ));
        }
    };

    if idx < 0 {
        return Ok(Value::None);
    }

    let info = match env.interp.type_env.types.get(enum_name.as_str()) {
        Some(DeclInfo::Enum(info)) => info,
        _ => {
            return Err(RuntimeError::with_span(
                format!("unknown enum `{}`", enum_name),
                call_span,
            ));
        }
    };

    let idx_usize = idx as usize;
    if idx_usize >= info.variants.len() {
        return Ok(Value::None);
    }

    let variant = &info.variants[idx_usize];
    if !variant.fields.is_empty() {
        return Ok(Value::None);
    }

    Ok(Value::EnumVariant {
        enum_name,
        variant: variant.name.clone(),
        fields: BTreeMap::new(),
    })
}

// ── Collection builtins ─────────────────────────────────────────

fn eval_len(
    env: &mut Env,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    let val = eval_expr(env, &args[0].value)?;
    match &val {
        Value::List(v) => Ok(Value::Int(v.len() as i64)),
        Value::Set(s) => Ok(Value::Int(s.len() as i64)),
        Value::Map(m) => Ok(Value::Int(m.len() as i64)),
        _ => Err(RuntimeError::with_span(
            format!("len() expects a list, set, or map, got {}", type_name(&val)),
            call_span,
        )),
    }
}

fn eval_keys(
    env: &mut Env,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    let val = eval_expr(env, &args[0].value)?;
    match val {
        Value::Map(m) => Ok(Value::List(m.into_keys().collect())),
        _ => Err(RuntimeError::with_span(
            format!("keys() expects a map, got {}", type_name(&val)),
            call_span,
        )),
    }
}

fn eval_values(
    env: &mut Env,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    let val = eval_expr(env, &args[0].value)?;
    match val {
        Value::Map(m) => Ok(Value::List(m.into_values().collect())),
        _ => Err(RuntimeError::with_span(
            format!("values() expects a map, got {}", type_name(&val)),
            call_span,
        )),
    }
}

fn eval_first(
    env: &mut Env,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    let val = eval_expr(env, &args[0].value)?;
    match val {
        Value::List(v) => Ok(v.into_iter().next()
            .map(|v| Value::Option(Some(Box::new(v))))
            .unwrap_or(Value::None)),
        _ => Err(RuntimeError::with_span(
            format!("first() expects a list, got {}", type_name(&val)),
            call_span,
        )),
    }
}

fn eval_last(
    env: &mut Env,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    let val = eval_expr(env, &args[0].value)?;
    match val {
        Value::List(v) => Ok(v.into_iter().next_back()
            .map(|v| Value::Option(Some(Box::new(v))))
            .unwrap_or(Value::None)),
        _ => Err(RuntimeError::with_span(
            format!("last() expects a list, got {}", type_name(&val)),
            call_span,
        )),
    }
}

fn eval_append(
    env: &mut Env,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    let list_val = eval_expr(env, &args[0].value)?;
    let elem_val = eval_expr(env, &args[1].value)?;
    match list_val {
        Value::List(mut v) => {
            v.push(elem_val);
            Ok(Value::List(v))
        }
        _ => Err(RuntimeError::with_span(
            format!("append() first argument must be a list, got {}", type_name(&list_val)),
            call_span,
        )),
    }
}

fn eval_concat(
    env: &mut Env,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    let first_val = eval_expr(env, &args[0].value)?;
    let second_val = eval_expr(env, &args[1].value)?;
    match (first_val, &second_val) {
        (Value::List(mut a), Value::List(b)) => {
            a.extend(b.iter().cloned());
            Ok(Value::List(a))
        }
        (Value::List(_), _) => Err(RuntimeError::with_span(
            format!("concat() second argument must be a list, got {}", type_name(&second_val)),
            call_span,
        )),
        (ref other, _) => Err(RuntimeError::with_span(
            format!("concat() expects two lists, got {} and {}", type_name(other), type_name(&second_val)),
            call_span,
        )),
    }
}

fn eval_reverse(
    env: &mut Env,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    let val = eval_expr(env, &args[0].value)?;
    match val {
        Value::List(mut v) => {
            v.reverse();
            Ok(Value::List(v))
        }
        _ => Err(RuntimeError::with_span(
            format!("reverse() expects a list, got {}", type_name(&val)),
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
            RuntimeError::with_span(
                format!("undefined function '{}'", name),
                call_span,
            )
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

    let mut bound: Vec<(String, Value)> = Vec::new();
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
                let default_val = eval_expr(env, default_expr)?;
                env.pop_scope();
                bound.push((fn_info.params[i].name.clone(), default_val));
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

    match result {
        Ok(val) => {
            if modifiers.is_empty() {
                Ok(val)
            } else {
                run_phase2(env, name, &fn_info, &bound, val, &modifiers)
            }
        }
        Err(e) => Err(e),
    }
}

// ── Derive / Mechanic dispatch ─────────────────────────────────

fn dispatch_derive_or_mechanic(
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
                format!("internal error: no declaration found for function '{}'", name),
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
    match result {
        Ok(val) => {
            if modifiers.is_empty() {
                Ok(val)
            } else {
                run_phase2(env, name, &fn_info, &bound, val, &modifiers)
            }
        }
        Err(e) => Err(e),
    }
}

// ── Table dispatch ─────────────────────────────────────────────

/// Evaluate a table lookup by matching arguments against table entry keys.
fn dispatch_table(
    env: &mut Env,
    name: &str,
    param_infos: &[ParamInfo],
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    use ttrpg_ast::ast::TableKey;

    // Look up the table declaration
    let table_decl = env
        .interp
        .program
        .tables
        .get(name)
        .ok_or_else(|| {
            RuntimeError::with_span(
                format!("internal error: no declaration found for table '{}'", name),
                call_span,
            )
        })?;
    let entries = table_decl.entries.clone();
    let ast_params: Vec<Param> = table_decl.params.clone();

    // Bind arguments
    let bound = bind_args(param_infos, args, Some(&ast_params), env, call_span)?;
    let arg_values: Vec<Value> = bound.iter().map(|(_, v)| v.clone()).collect();

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

// ── Action dispatch ────────────────────────────────────────────

/// Dispatch an action call from within DSL code (nested action calls from resolve blocks).
///
/// Extracts the receiver EntityRef from the effective argument list (receiver as first param,
/// mirroring the checker's effective_params construction) and delegates to the action pipeline.
fn dispatch_action(
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
    let action_args: Vec<(String, Value)> = bound[1..].to_vec();

    execute_action(env, &action_decl, actor, action_args, call_span)
}

// ── Prompt dispatch ────────────────────────────────────────────

fn dispatch_prompt(
    env: &mut Env,
    name: &str,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    let prompt_decl = env
        .interp
        .program
        .prompts
        .get(name)
        .ok_or_else(|| {
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
    let param_values: Vec<Value> = bound.iter().map(|(_, v)| v.clone()).collect();

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
        name: name.to_string(),
        params: param_values,
        hint,
        suggest,
    };
    let response = env.handler.handle(effect);

    match response {
        Response::PromptResult(val) => Ok(val),
        Response::Override(val) => Ok(val),
        _ => Err(RuntimeError::with_span(
            format!(
                "protocol error: expected PromptResult or Override response for ResolvePrompt, got {:?}",
                response
            ),
            call_span,
        )),
    }
}

// ── Enum variant construction ──────────────────────────────────

fn construct_enum_variant(
    env: &mut Env,
    enum_name: &str,
    variant_name: &str,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    let enum_info = match env.interp.type_env.types.get(enum_name) {
        Some(DeclInfo::Enum(info)) => info.clone(),
        _ => {
            return Err(RuntimeError::with_span(
                format!("internal error: '{}' is not an enum", enum_name),
                call_span,
            ));
        }
    };

    let variant_info = enum_info
        .variants
        .iter()
        .find(|v| v.name == variant_name)
        .ok_or_else(|| {
            RuntimeError::with_span(
                format!("enum '{}' has no variant '{}'", enum_name, variant_name),
                call_span,
            )
        })?;

    if variant_info.fields.is_empty() && args.is_empty() {
        return Ok(Value::EnumVariant {
            enum_name: enum_name.to_string(),
            variant: variant_name.to_string(),
            fields: BTreeMap::new(),
        });
    }

    // Build ParamInfo from variant fields for bind_args (no defaults for enum fields)
    let param_infos: Vec<ParamInfo> = variant_info
        .fields
        .iter()
        .map(|(name, ty)| ParamInfo {
            name: name.clone(),
            ty: ty.clone(),
            has_default: false,
            with_groups: vec![],
        })
        .collect();

    let bound = bind_args(&param_infos, args, None, env, call_span)?;

    let mut fields = BTreeMap::new();
    for (name, val) in bound {
        fields.insert(name, val);
    }

    Ok(Value::EnumVariant {
        enum_name: enum_name.to_string(),
        variant: variant_name.to_string(),
        fields,
    })
}

// ── Argument binding ───────────────────────────────────────────

/// Match call arguments to function parameters.
///
/// `ast_params` provides the AST parameter declarations (with default expressions)
/// when available. For builtins and enum constructors, this is `None`.
///
/// Returns a list of (param_name, value) pairs in parameter declaration order.
fn bind_args(
    params: &[ParamInfo],
    args: &[Arg],
    ast_params: Option<&[Param]>,
    env: &mut Env,
    call_span: Span,
) -> Result<Vec<(String, Value)>, RuntimeError> {
    let mut result: Vec<Option<Value>> = vec![None; params.len()];

    // Pre-pass: determine which slots are claimed by named args so positional
    // assignment knows which slots to skip. This must happen before evaluation
    // so we can evaluate all arguments in source order.
    let mut named_slots = vec![false; params.len()];
    for arg in args {
        if let Some(ref name) = arg.name {
            let pos = params
                .iter()
                .position(|p| p.name == *name)
                .ok_or_else(|| {
                    RuntimeError::with_span(
                        format!("unknown parameter '{}'", name),
                        arg.span,
                    )
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
            let pos = params.iter().position(|p| p.name == *name).unwrap();
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
) -> Result<Vec<(String, Value)>, RuntimeError> {
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

// ── Method dispatch ─────────────────────────────────────────────

fn eval_method_call(
    env: &mut Env,
    object: Value,
    method: &str,
    args: &[Arg],
    span: Span,
) -> Result<Value, RuntimeError> {
    match &object {
        Value::Option(_) | Value::None => eval_option_method(env, object, method, args, span),
        _ => Err(RuntimeError::with_span(
            format!("type {} has no methods", crate::eval::type_name(&object)),
            span,
        )),
    }
}

fn eval_option_method(
    env: &mut Env,
    value: Value,
    method: &str,
    args: &[Arg],
    span: Span,
) -> Result<Value, RuntimeError> {
    match method {
        "unwrap" => {
            match value {
                Value::Option(Some(inner)) => Ok(*inner),
                Value::Option(None) | Value::None => Err(RuntimeError::with_span(
                    "called unwrap() on a none value",
                    span,
                )),
                _ => unreachable!(),
            }
        }
        "unwrap_or" => {
            let default_val = eval_expr(env, &args[0].value)?;
            match value {
                Value::Option(Some(inner)) => Ok(*inner),
                Value::Option(None) | Value::None => Ok(default_val),
                _ => unreachable!(),
            }
        }
        _ => Err(RuntimeError::with_span(
            format!(
                "option type has no method `{}`; available methods: unwrap, unwrap_or",
                method
            ),
            span,
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::{BTreeMap, HashMap};

    use ttrpg_ast::Span;
    use ttrpg_ast::ast::*;
    use ttrpg_checker::env::{
        EnumInfo, FnInfo, FnKind, ParamInfo, TypeEnv, VariantInfo,
    };
    use ttrpg_checker::ty::Ty;

    use crate::effect::{Effect, EffectHandler, Response};
    use crate::state::{ActiveCondition, EntityRef, StateProvider};
    use crate::value::{DiceExpr, PositionValue, RollResult, duration_variant_with};
    use crate::Interpreter;

    // ── Test infrastructure ────────────────────────────────────

    struct ScriptedHandler {
        script: std::collections::VecDeque<Response>,
        log: Vec<Effect>,
    }

    impl ScriptedHandler {
        fn new() -> Self {
            ScriptedHandler {
                script: std::collections::VecDeque::new(),
                log: Vec::new(),
            }
        }

        fn with_responses(responses: Vec<Response>) -> Self {
            ScriptedHandler {
                script: responses.into(),
                log: Vec::new(),
            }
        }
    }

    impl EffectHandler for ScriptedHandler {
        fn handle(&mut self, effect: Effect) -> Response {
            self.log.push(effect);
            self.script.pop_front().unwrap_or(Response::Acknowledged)
        }
    }

    struct TestState {
        fields: HashMap<(u64, String), Value>,
        conditions: HashMap<u64, Vec<ActiveCondition>>,
        turn_budgets: HashMap<u64, BTreeMap<String, Value>>,
        enabled_options: Vec<String>,
    }

    impl TestState {
        fn new() -> Self {
            TestState {
                fields: HashMap::new(),
                conditions: HashMap::new(),
                turn_budgets: HashMap::new(),
                enabled_options: Vec::new(),
            }
        }
    }

    impl StateProvider for TestState {
        fn read_field(&self, entity: &EntityRef, field: &str) -> Option<Value> {
            self.fields.get(&(entity.0, field.to_string())).cloned()
        }
        fn read_conditions(&self, entity: &EntityRef) -> Option<Vec<ActiveCondition>> {
            self.conditions.get(&entity.0).cloned()
        }
        fn read_turn_budget(&self, entity: &EntityRef) -> Option<BTreeMap<String, Value>> {
            self.turn_budgets.get(&entity.0).cloned()
        }
        fn read_enabled_options(&self) -> Vec<String> {
            self.enabled_options.clone()
        }
        fn position_eq(&self, a: &Value, b: &Value) -> bool {
            if let (Value::Position(pa), Value::Position(pb)) = (a, b) {
                if let (Some(a), Some(b)) = (
                    pa.0.downcast_ref::<(i64, i64)>(),
                    pb.0.downcast_ref::<(i64, i64)>(),
                ) {
                    return a == b;
                }
            }
            false
        }
        fn distance(&self, a: &Value, b: &Value) -> Option<i64> {
            if let (Value::Position(pa), Value::Position(pb)) = (a, b) {
                if let (Some(a), Some(b)) = (
                    pa.0.downcast_ref::<(i64, i64)>(),
                    pb.0.downcast_ref::<(i64, i64)>(),
                ) {
                    return Some(((a.0 - b.0).abs()).max((a.1 - b.1).abs()));
                }
            }
            None
        }
    }

    fn dummy_span() -> Span {
        Span::dummy()
    }

    fn spanned<T>(node: T) -> Spanned<T> {
        Spanned::new(node, dummy_span())
    }

    fn make_env<'a, 'p>(
        state: &'a TestState,
        handler: &'a mut ScriptedHandler,
        interp: &'a Interpreter<'p>,
    ) -> Env<'a, 'p> {
        Env::new(state, handler, interp)
    }

    /// Build a program with a single system block containing the given declarations.
    fn program_with_decls(decls: Vec<DeclKind>) -> Program {
        let mut program = Program {
            items: vec![spanned(TopLevel::System(SystemBlock {
                name: "Test".into(),
                decls: decls.into_iter().map(spanned).collect(),
            }))],
            ..Default::default()
        };
        program.build_index();
        program
    }

    /// Build a type env with builtins registered.
    fn type_env_with_builtins() -> TypeEnv {
        let mut env = TypeEnv::new();
        for builtin in ttrpg_checker::builtins::register_builtins() {
            env.builtins.insert(builtin.name.clone(), builtin);
        }
        env
    }

    // ── Derive call tests ──────────────────────────────────────

    #[test]
    fn derive_call_arithmetic_body() {
        // derive add_bonus(base: Int, bonus: Int) -> Int { base + bonus }
        let program = program_with_decls(vec![DeclKind::Derive(FnDecl {
            name: "add_bonus".into(),
            params: vec![
                Param {
                    name: "base".into(),
                    ty: spanned(TypeExpr::Int),
                    default: None,
                    with_groups: vec![],
                    span: dummy_span(),
                },
                Param {
                    name: "bonus".into(),
                    ty: spanned(TypeExpr::Int),
                    default: None,
                    with_groups: vec![],
                    span: dummy_span(),
                },
            ],
            return_type: spanned(TypeExpr::Int),
            body: spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::BinOp {
                op: BinOp::Add,
                lhs: Box::new(spanned(ExprKind::Ident("base".into()))),
                rhs: Box::new(spanned(ExprKind::Ident("bonus".into()))),
            })))]),
            synthetic: false,
        })]);

        let mut type_env = TypeEnv::new();
        type_env.functions.insert(
            "add_bonus".into(),
            FnInfo {
                name: "add_bonus".into(),
                kind: FnKind::Derive,
                params: vec![
                    ParamInfo { name: "base".into(), ty: Ty::Int, has_default: false, with_groups: vec![] },
                    ParamInfo { name: "bonus".into(), ty: Ty::Int, has_default: false, with_groups: vec![] },
                ],
                return_type: Ty::Int,
                receiver: None,
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // Call: add_bonus(10, 5)
        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("add_bonus".into()))),
            args: vec![
                Arg { name: None, value: spanned(ExprKind::IntLit(10)), span: dummy_span() },
                Arg { name: None, value: spanned(ExprKind::IntLit(5)), span: dummy_span() },
            ],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        assert_eq!(result, Value::Int(15));
    }

    #[test]
    fn derive_call_with_named_args() {
        // derive add_bonus(base: Int, bonus: Int) -> Int { base + bonus }
        let program = program_with_decls(vec![DeclKind::Derive(FnDecl {
            name: "add_bonus".into(),
            params: vec![
                Param {
                    name: "base".into(),
                    ty: spanned(TypeExpr::Int),
                    default: None,
                    with_groups: vec![],
                    span: dummy_span(),
                },
                Param {
                    name: "bonus".into(),
                    ty: spanned(TypeExpr::Int),
                    default: None,
                    with_groups: vec![],
                    span: dummy_span(),
                },
            ],
            return_type: spanned(TypeExpr::Int),
            body: spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::BinOp {
                op: BinOp::Add,
                lhs: Box::new(spanned(ExprKind::Ident("base".into()))),
                rhs: Box::new(spanned(ExprKind::Ident("bonus".into()))),
            })))]),
            synthetic: false,
        })]);

        let mut type_env = TypeEnv::new();
        type_env.functions.insert(
            "add_bonus".into(),
            FnInfo {
                name: "add_bonus".into(),
                kind: FnKind::Derive,
                params: vec![
                    ParamInfo { name: "base".into(), ty: Ty::Int, has_default: false, with_groups: vec![] },
                    ParamInfo { name: "bonus".into(), ty: Ty::Int, has_default: false, with_groups: vec![] },
                ],
                return_type: Ty::Int,
                receiver: None,
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // Call: add_bonus(bonus: 3, base: 7) — reversed named args
        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("add_bonus".into()))),
            args: vec![
                Arg { name: Some("bonus".into()), value: spanned(ExprKind::IntLit(3)), span: dummy_span() },
                Arg { name: Some("base".into()), value: spanned(ExprKind::IntLit(7)), span: dummy_span() },
            ],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        assert_eq!(result, Value::Int(10));
    }

    #[test]
    fn derive_call_with_default_value() {
        // derive add_bonus(base: Int, bonus: Int = 5) -> Int { base + bonus }
        let program = program_with_decls(vec![DeclKind::Derive(FnDecl {
            name: "add_bonus".into(),
            params: vec![
                Param {
                    name: "base".into(),
                    ty: spanned(TypeExpr::Int),
                    default: None,
                    with_groups: vec![],
                    span: dummy_span(),
                },
                Param {
                    name: "bonus".into(),
                    ty: spanned(TypeExpr::Int),
                    default: Some(spanned(ExprKind::IntLit(5))),
                    with_groups: vec![],
                    span: dummy_span(),
                },
            ],
            return_type: spanned(TypeExpr::Int),
            body: spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::BinOp {
                op: BinOp::Add,
                lhs: Box::new(spanned(ExprKind::Ident("base".into()))),
                rhs: Box::new(spanned(ExprKind::Ident("bonus".into()))),
            })))]),
            synthetic: false,
        })]);

        let mut type_env = TypeEnv::new();
        type_env.functions.insert(
            "add_bonus".into(),
            FnInfo {
                name: "add_bonus".into(),
                kind: FnKind::Derive,
                params: vec![
                    ParamInfo { name: "base".into(), ty: Ty::Int, has_default: false, with_groups: vec![] },
                    ParamInfo { name: "bonus".into(), ty: Ty::Int, has_default: true, with_groups: vec![] },
                ],
                return_type: Ty::Int,
                receiver: None,
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // Call: add_bonus(10) — bonus defaults to 5
        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("add_bonus".into()))),
            args: vec![
                Arg { name: None, value: spanned(ExprKind::IntLit(10)), span: dummy_span() },
            ],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        assert_eq!(result, Value::Int(15));
    }

    // ── Mechanic call tests ────────────────────────────────────

    #[test]
    fn mechanic_call_with_roll_emits_roll_dice() {
        // mechanic attack_roll(bonus: Int) -> RollResult { roll(2d6 + bonus) }
        // We simulate this as: body = roll(2d6 + bonus)
        // Since roll is a builtin, the body calls roll(DiceExpr)
        // For simplicity, body is: roll(2d6 + bonus) which needs DiceLit + Add + roll
        // Let's simplify: body just calls roll on a dice literal

        let program = program_with_decls(vec![DeclKind::Mechanic(FnDecl {
            name: "attack_roll".into(),
            params: vec![],
            return_type: spanned(TypeExpr::RollResult),
            body: spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::Call {
                callee: Box::new(spanned(ExprKind::Ident("roll".into()))),
                args: vec![Arg {
                    name: None,
                    value: spanned(ExprKind::DiceLit {
                        count: 2,
                        sides: 6,
                        filter: None,
                    }),
                    span: dummy_span(),
                }],
            })))]),
            synthetic: false,
        })]);

        let mut type_env = type_env_with_builtins();
        type_env.functions.insert(
            "attack_roll".into(),
            FnInfo {
                name: "attack_roll".into(),
                kind: FnKind::Mechanic,
                params: vec![],
                return_type: Ty::RollResult,
                receiver: None,
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();

        let roll_result = RollResult {
            expr: DiceExpr { count: 2, sides: 6, filter: None, modifier: 0 },
            dice: vec![4, 5],
            kept: vec![4, 5],
            modifier: 0,
            total: 9,
            unmodified: 9,
        };
        let mut handler = ScriptedHandler::with_responses(vec![
            Response::Rolled(roll_result.clone()),
        ]);
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("attack_roll".into()))),
            args: vec![],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        assert_eq!(result, Value::RollResult(roll_result));

        // Verify that RollDice effect was emitted
        assert_eq!(handler.log.len(), 1);
        assert!(matches!(&handler.log[0], Effect::RollDice { expr } if expr.count == 2 && expr.sides == 6));
    }

    // ── Prompt call tests ──────────────────────────────────────

    #[test]
    fn prompt_call_emits_resolve_prompt() {
        let program = program_with_decls(vec![DeclKind::Prompt(PromptDecl {
            name: "ask_target".into(),
            params: vec![],
            return_type: spanned(TypeExpr::Int),
            hint: Some("Choose a target".into()),
            suggest: None,
        })]);

        let mut type_env = TypeEnv::new();
        type_env.functions.insert(
            "ask_target".into(),
            FnInfo {
                name: "ask_target".into(),
                kind: FnKind::Prompt,
                params: vec![],
                return_type: Ty::Int,
                receiver: None,
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::with_responses(vec![
            Response::PromptResult(Value::Int(42)),
        ]);
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("ask_target".into()))),
            args: vec![],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        assert_eq!(result, Value::Int(42));

        // Verify ResolvePrompt was emitted with hint
        assert_eq!(handler.log.len(), 1);
        match &handler.log[0] {
            Effect::ResolvePrompt { name, hint, .. } => {
                assert_eq!(name, "ask_target");
                assert_eq!(*hint, Some("Choose a target".to_string()));
            }
            _ => panic!("expected ResolvePrompt"),
        }
    }

    #[test]
    fn prompt_call_with_suggest() {
        // prompt pick_value(default: Int) -> Int { hint: "pick", suggest: default + 1 }
        let program = program_with_decls(vec![DeclKind::Prompt(PromptDecl {
            name: "pick_value".into(),
            params: vec![Param {
                name: "default_val".into(),
                ty: spanned(TypeExpr::Int),
                default: None,
                with_groups: vec![],
                span: dummy_span(),
            }],
            return_type: spanned(TypeExpr::Int),
            hint: Some("pick".into()),
            suggest: Some(spanned(ExprKind::BinOp {
                op: BinOp::Add,
                lhs: Box::new(spanned(ExprKind::Ident("default_val".into()))),
                rhs: Box::new(spanned(ExprKind::IntLit(1))),
            })),
        })]);

        let mut type_env = TypeEnv::new();
        type_env.functions.insert(
            "pick_value".into(),
            FnInfo {
                name: "pick_value".into(),
                kind: FnKind::Prompt,
                params: vec![ParamInfo {
                    name: "default_val".into(),
                    ty: Ty::Int,
                    has_default: false,
                    with_groups: vec![],
                }],
                return_type: Ty::Int,
                receiver: None,
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::with_responses(vec![
            Response::PromptResult(Value::Int(100)),
        ]);
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("pick_value".into()))),
            args: vec![Arg {
                name: None,
                value: spanned(ExprKind::IntLit(10)),
                span: dummy_span(),
            }],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        assert_eq!(result, Value::Int(100));

        // Verify suggest was evaluated: default_val(10) + 1 = 11
        match &handler.log[0] {
            Effect::ResolvePrompt { suggest, params, .. } => {
                assert_eq!(*suggest, Some(Value::Int(11)));
                assert_eq!(params, &[Value::Int(10)]);
            }
            _ => panic!("expected ResolvePrompt"),
        }
    }

    // ── Builtin tests ──────────────────────────────────────────

    #[test]
    fn builtin_floor_test() {
        let program = program_with_decls(vec![]);
        let type_env = type_env_with_builtins();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("floor".into()))),
            args: vec![Arg {
                name: None,
                value: spanned(ExprKind::BinOp {
                    op: BinOp::Div,
                    lhs: Box::new(spanned(ExprKind::IntLit(7))),
                    rhs: Box::new(spanned(ExprKind::IntLit(2))),
                }),
                span: dummy_span(),
            }],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        assert_eq!(result, Value::Int(3)); // floor(3.5) = 3
    }

    #[test]
    fn builtin_ceil_test() {
        let program = program_with_decls(vec![]);
        let type_env = type_env_with_builtins();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("ceil".into()))),
            args: vec![Arg {
                name: None,
                value: spanned(ExprKind::BinOp {
                    op: BinOp::Div,
                    lhs: Box::new(spanned(ExprKind::IntLit(7))),
                    rhs: Box::new(spanned(ExprKind::IntLit(2))),
                }),
                span: dummy_span(),
            }],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        assert_eq!(result, Value::Int(4)); // ceil(3.5) = 4
    }

    #[test]
    fn builtin_min_max_test() {
        let program = program_with_decls(vec![]);
        let type_env = type_env_with_builtins();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // min(3, 7)
        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("min".into()))),
            args: vec![
                Arg { name: None, value: spanned(ExprKind::IntLit(3)), span: dummy_span() },
                Arg { name: None, value: spanned(ExprKind::IntLit(7)), span: dummy_span() },
            ],
        });
        assert_eq!(crate::eval::eval_expr(&mut env, &expr).unwrap(), Value::Int(3));

        // max(3, 7)
        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("max".into()))),
            args: vec![
                Arg { name: None, value: spanned(ExprKind::IntLit(3)), span: dummy_span() },
                Arg { name: None, value: spanned(ExprKind::IntLit(7)), span: dummy_span() },
            ],
        });
        assert_eq!(crate::eval::eval_expr(&mut env, &expr).unwrap(), Value::Int(7));
    }

    #[test]
    fn builtin_distance_test() {
        use std::sync::Arc;

        let program = program_with_decls(vec![]);
        let type_env = type_env_with_builtins();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let pos_a = Value::Position(PositionValue(Arc::new((0i64, 0i64))));
        let pos_b = Value::Position(PositionValue(Arc::new((3i64, 4i64))));

        // Bind positions as local variables to pass to distance()
        env.bind("pos_a".into(), pos_a);
        env.bind("pos_b".into(), pos_b);

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("distance".into()))),
            args: vec![
                Arg { name: None, value: spanned(ExprKind::Ident("pos_a".into())), span: dummy_span() },
                Arg { name: None, value: spanned(ExprKind::Ident("pos_b".into())), span: dummy_span() },
            ],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        assert_eq!(result, Value::Int(4)); // Chebyshev distance: max(|3|, |4|) = 4
    }

    #[test]
    fn builtin_multiply_dice_test() {
        let program = program_with_decls(vec![]);
        let type_env = type_env_with_builtins();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // multiply_dice(2d6, 3) → 6d6
        env.bind("dice".into(), Value::DiceExpr(DiceExpr {
            count: 2, sides: 6, filter: None, modifier: 0,
        }));

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("multiply_dice".into()))),
            args: vec![
                Arg { name: None, value: spanned(ExprKind::Ident("dice".into())), span: dummy_span() },
                Arg { name: None, value: spanned(ExprKind::IntLit(3)), span: dummy_span() },
            ],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        match result {
            Value::DiceExpr(d) => {
                assert_eq!(d.count, 6);
                assert_eq!(d.sides, 6);
            }
            _ => panic!("expected DiceExpr"),
        }
    }

    #[test]
    fn builtin_multiply_dice_zero_factor_error() {
        let program = program_with_decls(vec![]);
        let type_env = type_env_with_builtins();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("dice".into(), Value::DiceExpr(DiceExpr {
            count: 2, sides: 6, filter: None, modifier: 0,
        }));

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("multiply_dice".into()))),
            args: vec![
                Arg { name: None, value: spanned(ExprKind::Ident("dice".into())), span: dummy_span() },
                Arg { name: None, value: spanned(ExprKind::IntLit(0)), span: dummy_span() },
            ],
        });
        let err = crate::eval::eval_expr(&mut env, &expr).unwrap_err();
        assert!(err.message.contains("positive"));
    }

    #[test]
    fn builtin_roll_test() {
        let program = program_with_decls(vec![]);
        let type_env = type_env_with_builtins();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();

        let roll_result = RollResult {
            expr: DiceExpr { count: 1, sides: 20, filter: None, modifier: 5 },
            dice: vec![15],
            kept: vec![15],
            modifier: 5,
            total: 20,
            unmodified: 15,
        };
        let mut handler = ScriptedHandler::with_responses(vec![
            Response::Rolled(roll_result.clone()),
        ]);
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("dice".into(), Value::DiceExpr(DiceExpr {
            count: 1, sides: 20, filter: None, modifier: 5,
        }));

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("roll".into()))),
            args: vec![Arg {
                name: None,
                value: spanned(ExprKind::Ident("dice".into())),
                span: dummy_span(),
            }],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        assert_eq!(result, Value::RollResult(roll_result));
    }

    #[test]
    fn builtin_roll_override_response() {
        let program = program_with_decls(vec![]);
        let type_env = type_env_with_builtins();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();

        let override_result = RollResult {
            expr: DiceExpr { count: 1, sides: 20, filter: None, modifier: 0 },
            dice: vec![20],
            kept: vec![20],
            modifier: 0,
            total: 20,
            unmodified: 20,
        };
        let mut handler = ScriptedHandler::with_responses(vec![
            Response::Override(Value::RollResult(override_result.clone())),
        ]);
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("dice".into(), Value::DiceExpr(DiceExpr {
            count: 1, sides: 20, filter: None, modifier: 0,
        }));

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("roll".into()))),
            args: vec![Arg {
                name: None,
                value: spanned(ExprKind::Ident("dice".into())),
                span: dummy_span(),
            }],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        assert_eq!(result, Value::RollResult(override_result));
    }

    #[test]
    fn builtin_apply_condition_emits_effect() {
        let program = program_with_decls(vec![]);
        let type_env = type_env_with_builtins();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("target".into(), Value::Entity(EntityRef(1)));
        env.bind("cond".into(), Value::Condition { name: "Prone".into(), args: BTreeMap::new() });
        env.bind("dur".into(), {
            let mut f = BTreeMap::new();
            f.insert("count".into(), Value::Int(3));
            duration_variant_with("rounds", f)
        });

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("apply_condition".into()))),
            args: vec![
                Arg { name: None, value: spanned(ExprKind::Ident("target".into())), span: dummy_span() },
                Arg { name: None, value: spanned(ExprKind::Ident("cond".into())), span: dummy_span() },
                Arg { name: None, value: spanned(ExprKind::Ident("dur".into())), span: dummy_span() },
            ],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        assert_eq!(result, Value::None);

        assert_eq!(handler.log.len(), 1);
        match &handler.log[0] {
            Effect::ApplyCondition { target, condition, .. } => {
                assert_eq!(target.0, 1);
                assert_eq!(condition, "Prone");
            }
            _ => panic!("expected ApplyCondition effect"),
        }
    }

    #[test]
    fn builtin_remove_condition_emits_effect() {
        let program = program_with_decls(vec![]);
        let type_env = type_env_with_builtins();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("target".into(), Value::Entity(EntityRef(2)));
        env.bind("cond".into(), Value::Condition { name: "Stunned".into(), args: BTreeMap::new() });

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("remove_condition".into()))),
            args: vec![
                Arg { name: None, value: spanned(ExprKind::Ident("target".into())), span: dummy_span() },
                Arg { name: None, value: spanned(ExprKind::Ident("cond".into())), span: dummy_span() },
            ],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        assert_eq!(result, Value::None);

        assert_eq!(handler.log.len(), 1);
        match &handler.log[0] {
            Effect::RemoveCondition { target, condition, .. } => {
                assert_eq!(target.0, 2);
                assert_eq!(condition, "Stunned");
            }
            _ => panic!("expected RemoveCondition effect"),
        }
    }

    // ── Enum variant construction tests ────────────────────────

    #[test]
    fn enum_variant_qualified_construction() {
        let program = program_with_decls(vec![]);
        let mut type_env = TypeEnv::new();
        type_env.types.insert(
            "Duration".into(),
            ttrpg_checker::env::DeclInfo::Enum(EnumInfo {
                name: "Duration".into(),
                ordered: false,
                variants: vec![
                    VariantInfo { name: "rounds".into(), fields: vec![("value".into(), Ty::Int)] },
                    VariantInfo { name: "indefinite".into(), fields: vec![] },
                ],
            }),
        );
        type_env.variant_to_enum.insert("rounds".into(), "Duration".into());
        type_env.variant_to_enum.insert("indefinite".into(), "Duration".into());

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // Duration.rounds(3)
        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::FieldAccess {
                object: Box::new(spanned(ExprKind::Ident("Duration".into()))),
                field: "rounds".into(),
            })),
            args: vec![Arg {
                name: None,
                value: spanned(ExprKind::IntLit(3)),
                span: dummy_span(),
            }],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        match result {
            Value::EnumVariant { enum_name, variant, fields } => {
                assert_eq!(enum_name, "Duration");
                assert_eq!(variant, "rounds");
                assert_eq!(fields.get("value"), Some(&Value::Int(3)));
            }
            _ => panic!("expected EnumVariant, got {:?}", result),
        }
    }

    #[test]
    fn enum_variant_bare_construction() {
        let program = program_with_decls(vec![]);
        let mut type_env = TypeEnv::new();
        type_env.types.insert(
            "Duration".into(),
            ttrpg_checker::env::DeclInfo::Enum(EnumInfo {
                name: "Duration".into(),
                ordered: false,
                variants: vec![
                    VariantInfo { name: "rounds".into(), fields: vec![("value".into(), Ty::Int)] },
                    VariantInfo { name: "indefinite".into(), fields: vec![] },
                ],
            }),
        );
        type_env.variant_to_enum.insert("rounds".into(), "Duration".into());
        type_env.variant_to_enum.insert("indefinite".into(), "Duration".into());

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // rounds(5) — bare enum variant call
        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("rounds".into()))),
            args: vec![Arg {
                name: None,
                value: spanned(ExprKind::IntLit(5)),
                span: dummy_span(),
            }],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        match result {
            Value::EnumVariant { enum_name, variant, fields } => {
                assert_eq!(enum_name, "Duration");
                assert_eq!(variant, "rounds");
                assert_eq!(fields.get("value"), Some(&Value::Int(5)));
            }
            _ => panic!("expected EnumVariant, got {:?}", result),
        }
    }

    // ── Error case tests ───────────────────────────────────────

    #[test]
    fn missing_required_arg_error() {
        let program = program_with_decls(vec![DeclKind::Derive(FnDecl {
            name: "identity".into(),
            params: vec![Param {
                name: "x".into(),
                ty: spanned(TypeExpr::Int),
                default: None,
                with_groups: vec![],
                span: dummy_span(),
            }],
            return_type: spanned(TypeExpr::Int),
            body: spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::Ident("x".into()))))]),
            synthetic: false,
        })]);

        let mut type_env = TypeEnv::new();
        type_env.functions.insert(
            "identity".into(),
            FnInfo {
                name: "identity".into(),
                kind: FnKind::Derive,
                params: vec![ParamInfo { name: "x".into(), ty: Ty::Int, has_default: false, with_groups: vec![] }],
                return_type: Ty::Int,
                receiver: None,
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // Call with no arguments
        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("identity".into()))),
            args: vec![],
        });
        let err = crate::eval::eval_expr(&mut env, &expr).unwrap_err();
        assert!(err.message.contains("missing required argument"));
    }

    #[test]
    fn multiply_dice_overflow_error() {
        let program = program_with_decls(vec![]);
        let type_env = type_env_with_builtins();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("dice".into(), Value::DiceExpr(DiceExpr {
            count: u32::MAX, sides: 6, filter: None, modifier: 0,
        }));

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("multiply_dice".into()))),
            args: vec![
                Arg { name: None, value: spanned(ExprKind::Ident("dice".into())), span: dummy_span() },
                Arg { name: None, value: spanned(ExprKind::IntLit(2)), span: dummy_span() },
            ],
        });
        let err = crate::eval::eval_expr(&mut env, &expr).unwrap_err();
        assert!(err.message.contains("overflow"));
    }

    #[test]
    fn builtin_dice_basic() {
        let program = program_with_decls(vec![]);
        let type_env = type_env_with_builtins();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // dice(2, 6) → 2d6
        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("dice".into()))),
            args: vec![
                Arg { name: None, value: spanned(ExprKind::IntLit(2)), span: dummy_span() },
                Arg { name: None, value: spanned(ExprKind::IntLit(6)), span: dummy_span() },
            ],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        match result {
            Value::DiceExpr(d) => {
                assert_eq!(d.count, 2);
                assert_eq!(d.sides, 6);
                assert!(d.filter.is_none());
                assert_eq!(d.modifier, 0);
            }
            _ => panic!("expected DiceExpr, got {:?}", result),
        }
    }

    #[test]
    fn builtin_dice_zero_count() {
        let program = program_with_decls(vec![]);
        let type_env = type_env_with_builtins();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // dice(0, 8) → 0d8 (valid)
        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("dice".into()))),
            args: vec![
                Arg { name: None, value: spanned(ExprKind::IntLit(0)), span: dummy_span() },
                Arg { name: None, value: spanned(ExprKind::IntLit(8)), span: dummy_span() },
            ],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        match result {
            Value::DiceExpr(d) => {
                assert_eq!(d.count, 0);
                assert_eq!(d.sides, 8);
            }
            _ => panic!("expected DiceExpr, got {:?}", result),
        }
    }

    #[test]
    fn builtin_dice_negative_count_error() {
        let program = program_with_decls(vec![]);
        let type_env = type_env_with_builtins();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("dice".into()))),
            args: vec![
                Arg { name: None, value: spanned(ExprKind::IntLit(-1)), span: dummy_span() },
                Arg { name: None, value: spanned(ExprKind::IntLit(6)), span: dummy_span() },
            ],
        });
        let err = crate::eval::eval_expr(&mut env, &expr).unwrap_err();
        assert!(err.message.contains("non-negative"));
    }

    #[test]
    fn builtin_dice_zero_sides_error() {
        let program = program_with_decls(vec![]);
        let type_env = type_env_with_builtins();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("dice".into()))),
            args: vec![
                Arg { name: None, value: spanned(ExprKind::IntLit(2)), span: dummy_span() },
                Arg { name: None, value: spanned(ExprKind::IntLit(0)), span: dummy_span() },
            ],
        });
        let err = crate::eval::eval_expr(&mut env, &expr).unwrap_err();
        assert!(err.message.contains("at least 1"));
    }

    #[test]
    fn builtin_dice_composable_with_modifier() {
        let program = program_with_decls(vec![]);
        let type_env = type_env_with_builtins();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // dice(3, 8) + 5 → 3d8+5
        let expr = spanned(ExprKind::BinOp {
            op: BinOp::Add,
            lhs: Box::new(spanned(ExprKind::Call {
                callee: Box::new(spanned(ExprKind::Ident("dice".into()))),
                args: vec![
                    Arg { name: None, value: spanned(ExprKind::IntLit(3)), span: dummy_span() },
                    Arg { name: None, value: spanned(ExprKind::IntLit(8)), span: dummy_span() },
                ],
            })),
            rhs: Box::new(spanned(ExprKind::IntLit(5))),
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        match result {
            Value::DiceExpr(d) => {
                assert_eq!(d.count, 3);
                assert_eq!(d.sides, 8);
                assert_eq!(d.modifier, 5);
            }
            _ => panic!("expected DiceExpr, got {:?}", result),
        }
    }

    #[test]
    fn invalid_callee_expression_error() {
        let program = program_with_decls(vec![]);
        let type_env = TypeEnv::new();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // Try to call a literal: 42()
        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::IntLit(42))),
            args: vec![],
        });
        let err = crate::eval::eval_expr(&mut env, &expr).unwrap_err();
        assert!(err.message.contains("invalid callee"));
    }

    // ── Action dispatch tests ─────────────────────────────────────

    /// Helper: build an action declaration and matching FnInfo for testing.
    fn action_test_setup() -> (Program, TypeEnv) {
        // action Attack on actor: Character (target: Character) { resolve { actor } }
        let program = program_with_decls(vec![DeclKind::Action(ActionDecl {
            name: "Attack".into(),
            receiver_name: "actor".into(),
            receiver_type: spanned(TypeExpr::Named("Character".into())),
            receiver_with_groups: vec![],
            params: vec![Param {
                name: "target".into(),
                ty: spanned(TypeExpr::Named("Character".into())),
                default: None,
                with_groups: vec![],
                span: dummy_span(),
            }],
            cost: None,
            requires: None,
            resolve: spanned(vec![spanned(StmtKind::Expr(spanned(
                ExprKind::Ident("actor".into()),
            )))]),
            trigger_text: None,
            synthetic: false,
        })]);

        let mut type_env = TypeEnv::new();
        type_env.functions.insert(
            "Attack".into(),
            FnInfo {
                name: "Attack".into(),
                kind: FnKind::Action,
                params: vec![ParamInfo {
                    name: "target".into(),
                    ty: Ty::Entity("Character".into()),
                    has_default: false,
                    with_groups: vec![],
                }],
                return_type: Ty::Unit,
                receiver: Some(ParamInfo {
                    name: "actor".into(),
                    ty: Ty::Entity("Character".into()),
                    has_default: false,
                    with_groups: vec![],
                }),
            },
        );

        (program, type_env)
    }

    #[test]
    fn action_call_extracts_receiver_positional() {
        let (program, type_env) = action_test_setup();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("warrior".into(), Value::Entity(EntityRef(1)));
        env.bind("goblin".into(), Value::Entity(EntityRef(2)));

        // Call: Attack(warrior, goblin) — positional args
        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("Attack".into()))),
            args: vec![
                Arg {
                    name: None,
                    value: spanned(ExprKind::Ident("warrior".into())),
                    span: dummy_span(),
                },
                Arg {
                    name: None,
                    value: spanned(ExprKind::Ident("goblin".into())),
                    span: dummy_span(),
                },
            ],
        });

        // Action executes: resolve block returns actor entity
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        assert_eq!(result, Value::Entity(EntityRef(1)));
    }

    #[test]
    fn action_call_extracts_receiver_named() {
        let (program, type_env) = action_test_setup();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("warrior".into(), Value::Entity(EntityRef(1)));
        env.bind("goblin".into(), Value::Entity(EntityRef(2)));

        // Call: Attack(target: goblin, actor: warrior) — named args, reversed order
        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("Attack".into()))),
            args: vec![
                Arg {
                    name: Some("target".into()),
                    value: spanned(ExprKind::Ident("goblin".into())),
                    span: dummy_span(),
                },
                Arg {
                    name: Some("actor".into()),
                    value: spanned(ExprKind::Ident("warrior".into())),
                    span: dummy_span(),
                },
            ],
        });

        // Action executes: resolve block returns actor entity
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        assert_eq!(result, Value::Entity(EntityRef(1)));
    }

    #[test]
    fn action_call_missing_receiver_error() {
        let (program, type_env) = action_test_setup();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("goblin".into(), Value::Entity(EntityRef(2)));

        // Call: Attack(target: goblin) — missing receiver
        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("Attack".into()))),
            args: vec![Arg {
                name: Some("target".into()),
                value: spanned(ExprKind::Ident("goblin".into())),
                span: dummy_span(),
            }],
        });

        let err = crate::eval::eval_expr(&mut env, &expr).unwrap_err();
        assert!(
            err.message.contains("missing required argument"),
            "Expected missing argument error, got: {}",
            err.message
        );
    }

    // ── Default parameter dependency tests ──────────────────────

    #[test]
    fn derive_default_references_earlier_param() {
        // derive add(a: Int, b: Int = a) -> Int { a + b }
        let program = program_with_decls(vec![DeclKind::Derive(FnDecl {
            name: "add".into(),
            params: vec![
                Param {
                    name: "a".into(),
                    ty: spanned(TypeExpr::Int),
                    default: None,
                    with_groups: vec![],
                    span: dummy_span(),
                },
                Param {
                    name: "b".into(),
                    ty: spanned(TypeExpr::Int),
                    default: Some(spanned(ExprKind::Ident("a".into()))),
                    with_groups: vec![],
                    span: dummy_span(),
                },
            ],
            return_type: spanned(TypeExpr::Int),
            body: spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::BinOp {
                op: BinOp::Add,
                lhs: Box::new(spanned(ExprKind::Ident("a".into()))),
                rhs: Box::new(spanned(ExprKind::Ident("b".into()))),
            })))]),
            synthetic: false,
        })]);

        let mut type_env = TypeEnv::new();
        type_env.functions.insert(
            "add".into(),
            FnInfo {
                name: "add".into(),
                kind: FnKind::Derive,
                params: vec![
                    ParamInfo { name: "a".into(), ty: Ty::Int, has_default: false, with_groups: vec![] },
                    ParamInfo { name: "b".into(), ty: Ty::Int, has_default: true, with_groups: vec![] },
                ],
                return_type: Ty::Int,
                receiver: None,
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // Call: add(7) — b defaults to a (7), result = 7 + 7 = 14
        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("add".into()))),
            args: vec![
                Arg { name: None, value: spanned(ExprKind::IntLit(7)), span: dummy_span() },
            ],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        assert_eq!(result, Value::Int(14));
    }

    #[test]
    fn derive_chained_defaults_reference_earlier_defaults() {
        // derive f(a: Int, b: Int = a, c: Int = b) -> Int { c }
        let program = program_with_decls(vec![DeclKind::Derive(FnDecl {
            name: "f".into(),
            params: vec![
                Param {
                    name: "a".into(),
                    ty: spanned(TypeExpr::Int),
                    default: None,
                    with_groups: vec![],
                    span: dummy_span(),
                },
                Param {
                    name: "b".into(),
                    ty: spanned(TypeExpr::Int),
                    default: Some(spanned(ExprKind::Ident("a".into()))),
                    with_groups: vec![],
                    span: dummy_span(),
                },
                Param {
                    name: "c".into(),
                    ty: spanned(TypeExpr::Int),
                    default: Some(spanned(ExprKind::Ident("b".into()))),
                    with_groups: vec![],
                    span: dummy_span(),
                },
            ],
            return_type: spanned(TypeExpr::Int),
            body: spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::Ident("c".into()))))]),
            synthetic: false,
        })]);

        let mut type_env = TypeEnv::new();
        type_env.functions.insert(
            "f".into(),
            FnInfo {
                name: "f".into(),
                kind: FnKind::Derive,
                params: vec![
                    ParamInfo { name: "a".into(), ty: Ty::Int, has_default: false, with_groups: vec![] },
                    ParamInfo { name: "b".into(), ty: Ty::Int, has_default: true, with_groups: vec![] },
                    ParamInfo { name: "c".into(), ty: Ty::Int, has_default: true, with_groups: vec![] },
                ],
                return_type: Ty::Int,
                receiver: None,
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // Call: f(5) — b defaults to a (5), c defaults to b (5)
        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("f".into()))),
            args: vec![
                Arg { name: None, value: spanned(ExprKind::IntLit(5)), span: dummy_span() },
            ],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        assert_eq!(result, Value::Int(5));
    }

    // ── Prompt Override response tests ──────────────────────────

    #[test]
    fn prompt_call_accepts_override_response() {
        let program = program_with_decls(vec![DeclKind::Prompt(PromptDecl {
            name: "ask_target".into(),
            params: vec![],
            return_type: spanned(TypeExpr::Int),
            hint: Some("Choose a target".into()),
            suggest: None,
        })]);

        let mut type_env = TypeEnv::new();
        type_env.functions.insert(
            "ask_target".into(),
            FnInfo {
                name: "ask_target".into(),
                kind: FnKind::Prompt,
                params: vec![],
                return_type: Ty::Int,
                receiver: None,
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        // GM overrides the prompt with a specific value
        let mut handler = ScriptedHandler::with_responses(vec![
            Response::Override(Value::Int(99)),
        ]);
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("ask_target".into()))),
            args: vec![],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        assert_eq!(result, Value::Int(99));
    }

    #[test]
    fn prompt_call_rejects_invalid_response() {
        let program = program_with_decls(vec![DeclKind::Prompt(PromptDecl {
            name: "ask_target".into(),
            params: vec![],
            return_type: spanned(TypeExpr::Int),
            hint: None,
            suggest: None,
        })]);

        let mut type_env = TypeEnv::new();
        type_env.functions.insert(
            "ask_target".into(),
            FnInfo {
                name: "ask_target".into(),
                kind: FnKind::Prompt,
                params: vec![],
                return_type: Ty::Int,
                receiver: None,
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        // Invalid: Acknowledged is not valid for ResolvePrompt
        let mut handler = ScriptedHandler::with_responses(vec![Response::Acknowledged]);
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("ask_target".into()))),
            args: vec![],
        });
        let err = crate::eval::eval_expr(&mut env, &expr).unwrap_err();
        assert!(
            err.message.contains("protocol error"),
            "Expected protocol error, got: {}",
            err.message
        );
    }

    // ── Condition response validation tests ─────────────────────

    #[test]
    fn apply_condition_rejects_invalid_response() {
        let program = program_with_decls(vec![]);
        let type_env = type_env_with_builtins();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        // Invalid: Rolled is not valid for ApplyCondition
        let roll_result = RollResult {
            expr: DiceExpr { count: 1, sides: 20, filter: None, modifier: 0 },
            dice: vec![10],
            kept: vec![10],
            modifier: 0,
            total: 10,
            unmodified: 10,
        };
        let mut handler = ScriptedHandler::with_responses(vec![
            Response::Rolled(roll_result),
        ]);
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("target".into(), Value::Entity(EntityRef(1)));
        env.bind("cond".into(), Value::Condition { name: "Prone".into(), args: BTreeMap::new() });
        env.bind("dur".into(), {
            let mut f = BTreeMap::new();
            f.insert("count".into(), Value::Int(3));
            duration_variant_with("rounds", f)
        });

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("apply_condition".into()))),
            args: vec![
                Arg { name: None, value: spanned(ExprKind::Ident("target".into())), span: dummy_span() },
                Arg { name: None, value: spanned(ExprKind::Ident("cond".into())), span: dummy_span() },
                Arg { name: None, value: spanned(ExprKind::Ident("dur".into())), span: dummy_span() },
            ],
        });
        let err = crate::eval::eval_expr(&mut env, &expr).unwrap_err();
        assert!(
            err.message.contains("protocol error"),
            "Expected protocol error, got: {}",
            err.message
        );
    }

    #[test]
    fn apply_condition_accepts_vetoed_response() {
        let program = program_with_decls(vec![]);
        let type_env = type_env_with_builtins();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::with_responses(vec![Response::Vetoed]);
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("target".into(), Value::Entity(EntityRef(1)));
        env.bind("cond".into(), Value::Condition { name: "Prone".into(), args: BTreeMap::new() });
        env.bind("dur".into(), {
            let mut f = BTreeMap::new();
            f.insert("count".into(), Value::Int(3));
            duration_variant_with("rounds", f)
        });

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("apply_condition".into()))),
            args: vec![
                Arg { name: None, value: spanned(ExprKind::Ident("target".into())), span: dummy_span() },
                Arg { name: None, value: spanned(ExprKind::Ident("cond".into())), span: dummy_span() },
                Arg { name: None, value: spanned(ExprKind::Ident("dur".into())), span: dummy_span() },
            ],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        assert_eq!(result, Value::None);
    }

    #[test]
    fn remove_condition_rejects_invalid_response() {
        let program = program_with_decls(vec![]);
        let type_env = type_env_with_builtins();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::with_responses(vec![
            Response::PromptResult(Value::Int(42)),
        ]);
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("target".into(), Value::Entity(EntityRef(2)));
        env.bind("cond".into(), Value::Condition { name: "Stunned".into(), args: BTreeMap::new() });

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("remove_condition".into()))),
            args: vec![
                Arg { name: None, value: spanned(ExprKind::Ident("target".into())), span: dummy_span() },
                Arg { name: None, value: spanned(ExprKind::Ident("cond".into())), span: dummy_span() },
            ],
        });
        let err = crate::eval::eval_expr(&mut env, &expr).unwrap_err();
        assert!(
            err.message.contains("protocol error"),
            "Expected protocol error, got: {}",
            err.message
        );
    }

    #[test]
    fn action_call_non_entity_receiver_error() {
        let (program, type_env) = action_test_setup();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("goblin".into(), Value::Entity(EntityRef(2)));

        // Call: Attack(42, goblin) — non-entity receiver
        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("Attack".into()))),
            args: vec![
                Arg {
                    name: None,
                    value: spanned(ExprKind::IntLit(42)),
                    span: dummy_span(),
                },
                Arg {
                    name: None,
                    value: spanned(ExprKind::Ident("goblin".into())),
                    span: dummy_span(),
                },
            ],
        });

        let err = crate::eval::eval_expr(&mut env, &expr).unwrap_err();
        assert!(
            err.message.contains("must be an entity"),
            "Expected entity error, got: {}",
            err.message
        );
    }

    // ── Resolution order tests ──────────────────────────────────

    #[test]
    fn bare_call_prefers_variant_over_function() {
        // Enum variant "rounds" collides with a function named "rounds".
        // The interpreter should resolve to the variant, matching the checker.
        let program = program_with_decls(vec![DeclKind::Derive(FnDecl {
            name: "rounds".into(),
            params: vec![Param {
                name: "n".into(),
                ty: spanned(TypeExpr::Int),
                default: None,
                with_groups: vec![],
                span: dummy_span(),
            }],
            return_type: spanned(TypeExpr::Int),
            body: spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::IntLit(999))))]),
            synthetic: false,
        })]);

        let mut type_env = TypeEnv::new();
        type_env.functions.insert(
            "rounds".into(),
            FnInfo {
                name: "rounds".into(),
                kind: FnKind::Derive,
                params: vec![ParamInfo { name: "n".into(), ty: Ty::Int, has_default: false, with_groups: vec![] }],
                return_type: Ty::Int,
                receiver: None,
            },
        );
        type_env.types.insert(
            "Duration".into(),
            ttrpg_checker::env::DeclInfo::Enum(EnumInfo {
                name: "Duration".into(),
                ordered: false,
                variants: vec![
                    VariantInfo { name: "rounds".into(), fields: vec![("value".into(), Ty::Int)] },
                ],
            }),
        );
        type_env.variant_to_enum.insert("rounds".into(), "Duration".into());

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // Call: rounds(5) — should resolve to enum variant, not the function
        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("rounds".into()))),
            args: vec![Arg {
                name: None,
                value: spanned(ExprKind::IntLit(5)),
                span: dummy_span(),
            }],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        match result {
            Value::EnumVariant { enum_name, variant, fields } => {
                assert_eq!(enum_name, "Duration");
                assert_eq!(variant, "rounds");
                assert_eq!(fields.get("value"), Some(&Value::Int(5)));
            }
            Value::Int(999) => panic!("resolved to function instead of enum variant"),
            other => panic!("unexpected result: {:?}", other),
        }
    }

    // ── Argument evaluation order tests ─────────────────────────

    #[test]
    fn mixed_args_evaluated_in_source_order() {
        // derive add3(a: Int, b: Int, c: Int) -> Int { a + b + c }
        // Call: add3(roll_a(), c: roll_c(), roll_b())
        // Effects should be emitted in source order: roll_a, roll_c, roll_b
        //
        // We simulate this using mechanic calls that emit RollDice effects.
        // Instead, we use a simpler approach: bind side-effectful expressions as
        // variables and verify ordering through a sequenced approach.
        //
        // Since we need to verify eval order of arg expressions specifically,
        // we'll use a derive whose body just returns a + b + c, and pass
        // expressions that call roll() which emits effects in order.

        let program = program_with_decls(vec![
            DeclKind::Derive(FnDecl {
                name: "sum3".into(),
                params: vec![
                    Param { name: "a".into(), ty: spanned(TypeExpr::Int), default: None, with_groups: vec![], span: dummy_span() },
                    Param { name: "b".into(), ty: spanned(TypeExpr::Int), default: None, with_groups: vec![], span: dummy_span() },
                    Param { name: "c".into(), ty: spanned(TypeExpr::Int), default: None, with_groups: vec![], span: dummy_span() },
                ],
                return_type: spanned(TypeExpr::Int),
                body: spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::BinOp {
                    op: BinOp::Add,
                    lhs: Box::new(spanned(ExprKind::BinOp {
                        op: BinOp::Add,
                        lhs: Box::new(spanned(ExprKind::Ident("a".into()))),
                        rhs: Box::new(spanned(ExprKind::Ident("b".into()))),
                    })),
                    rhs: Box::new(spanned(ExprKind::Ident("c".into()))),
                })))]),
                synthetic: false,
            }),
        ]);

        let mut type_env = type_env_with_builtins();
        type_env.functions.insert(
            "sum3".into(),
            FnInfo {
                name: "sum3".into(),
                kind: FnKind::Derive,
                params: vec![
                    ParamInfo { name: "a".into(), ty: Ty::Int, has_default: false, with_groups: vec![] },
                    ParamInfo { name: "b".into(), ty: Ty::Int, has_default: false, with_groups: vec![] },
                    ParamInfo { name: "c".into(), ty: Ty::Int, has_default: false, with_groups: vec![] },
                ],
                return_type: Ty::Int,
                receiver: None,
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();

        // Three roll responses: 1d4 -> 1, 1d6 -> 2, 1d8 -> 3
        // Call: sum3(roll(1d4), c: roll(1d6), roll(1d8))
        // Source order: roll(1d4), roll(1d6), roll(1d8)
        // Named c=roll(1d6) is second in source but slot [2].
        // Positional roll(1d4) fills slot [0], positional roll(1d8) fills slot [1].
        let mut handler = ScriptedHandler::with_responses(vec![
            Response::Rolled(RollResult {
                expr: DiceExpr { count: 1, sides: 4, filter: None, modifier: 0 },
                dice: vec![1], kept: vec![1], modifier: 0, total: 1, unmodified: 1,
            }),
            Response::Rolled(RollResult {
                expr: DiceExpr { count: 1, sides: 6, filter: None, modifier: 0 },
                dice: vec![2], kept: vec![2], modifier: 0, total: 2, unmodified: 2,
            }),
            Response::Rolled(RollResult {
                expr: DiceExpr { count: 1, sides: 8, filter: None, modifier: 0 },
                dice: vec![3], kept: vec![3], modifier: 0, total: 3, unmodified: 3,
            }),
        ]);
        let mut env = make_env(&state, &mut handler, &interp);

        // sum3(roll(1d4), c: roll(1d6), roll(1d8))
        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("sum3".into()))),
            args: vec![
                Arg {
                    name: None,
                    value: spanned(ExprKind::Call {
                        callee: Box::new(spanned(ExprKind::Ident("roll".into()))),
                        args: vec![Arg {
                            name: None,
                            value: spanned(ExprKind::DiceLit { count: 1, sides: 4, filter: None }),
                            span: dummy_span(),
                        }],
                    }),
                    span: dummy_span(),
                },
                Arg {
                    name: Some("c".into()),
                    value: spanned(ExprKind::Call {
                        callee: Box::new(spanned(ExprKind::Ident("roll".into()))),
                        args: vec![Arg {
                            name: None,
                            value: spanned(ExprKind::DiceLit { count: 1, sides: 6, filter: None }),
                            span: dummy_span(),
                        }],
                    }),
                    span: dummy_span(),
                },
                Arg {
                    name: None,
                    value: spanned(ExprKind::Call {
                        callee: Box::new(spanned(ExprKind::Ident("roll".into()))),
                        args: vec![Arg {
                            name: None,
                            value: spanned(ExprKind::DiceLit { count: 1, sides: 8, filter: None }),
                            span: dummy_span(),
                        }],
                    }),
                    span: dummy_span(),
                },
            ],
        });

        // RollResult gets coerced to Int when used in arithmetic
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        // a=roll(1d4)=1, b=roll(1d8)=3, c=roll(1d6)=2 → 1+3+2 = 6
        assert_eq!(result, Value::Int(6));

        // Effects emitted in source order: 1d4, 1d6, 1d8
        assert_eq!(handler.log.len(), 3);
        match &handler.log[0] {
            Effect::RollDice { expr } => assert_eq!(expr.sides, 4, "first roll should be 1d4"),
            e => panic!("expected RollDice, got {:?}", e),
        }
        match &handler.log[1] {
            Effect::RollDice { expr } => assert_eq!(expr.sides, 6, "second roll should be 1d6"),
            e => panic!("expected RollDice, got {:?}", e),
        }
        match &handler.log[2] {
            Effect::RollDice { expr } => assert_eq!(expr.sides, 8, "third roll should be 1d8"),
            e => panic!("expected RollDice, got {:?}", e),
        }
    }

    // ── Scope balance on error tests ────────────────────────────

    #[test]
    fn prompt_suggest_error_does_not_leak_scope() {
        // prompt with suggest that errors — scope should be balanced after
        let program = program_with_decls(vec![DeclKind::Prompt(PromptDecl {
            name: "bad_suggest".into(),
            params: vec![],
            return_type: spanned(TypeExpr::Int),
            hint: None,
            // suggest: undefined_var (will error)
            suggest: Some(spanned(ExprKind::Ident("undefined_var".into()))),
        })]);

        let mut type_env = TypeEnv::new();
        type_env.functions.insert(
            "bad_suggest".into(),
            FnInfo {
                name: "bad_suggest".into(),
                kind: FnKind::Prompt,
                params: vec![],
                return_type: Ty::Int,
                receiver: None,
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let scope_depth_before = env.scopes.len();

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("bad_suggest".into()))),
            args: vec![],
        });
        let err = crate::eval::eval_expr(&mut env, &expr);
        assert!(err.is_err(), "should fail due to undefined var in suggest");

        // Scope depth should be restored
        assert_eq!(
            env.scopes.len(),
            scope_depth_before,
            "scope leaked after suggest evaluation error"
        );
    }

    #[test]
    fn default_eval_error_does_not_leak_scope() {
        // derive f(a: Int, b: Int = undefined_var) -> Int { a }
        let program = program_with_decls(vec![DeclKind::Derive(FnDecl {
            name: "f".into(),
            params: vec![
                Param {
                    name: "a".into(),
                    ty: spanned(TypeExpr::Int),
                    default: None,
                    with_groups: vec![],
                    span: dummy_span(),
                },
                Param {
                    name: "b".into(),
                    ty: spanned(TypeExpr::Int),
                    // Default expression references an undefined variable
                    default: Some(spanned(ExprKind::Ident("undefined_var".into()))),
                    with_groups: vec![],
                    span: dummy_span(),
                },
            ],
            return_type: spanned(TypeExpr::Int),
            body: spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::Ident("a".into()))))]),
            synthetic: false,
        })]);

        let mut type_env = TypeEnv::new();
        type_env.functions.insert(
            "f".into(),
            FnInfo {
                name: "f".into(),
                kind: FnKind::Derive,
                params: vec![
                    ParamInfo { name: "a".into(), ty: Ty::Int, has_default: false, with_groups: vec![] },
                    ParamInfo { name: "b".into(), ty: Ty::Int, has_default: true, with_groups: vec![] },
                ],
                return_type: Ty::Int,
                receiver: None,
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let scope_depth_before = env.scopes.len();

        // Call: f(5) — b defaults to undefined_var which should error
        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("f".into()))),
            args: vec![Arg {
                name: None,
                value: spanned(ExprKind::IntLit(5)),
                span: dummy_span(),
            }],
        });
        let err = crate::eval::eval_expr(&mut env, &expr);
        assert!(err.is_err(), "should fail due to undefined var in default");

        // Scope depth should be restored
        assert_eq!(
            env.scopes.len(),
            scope_depth_before,
            "scope leaked after default evaluation error"
        );
    }
}
