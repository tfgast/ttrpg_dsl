use std::collections::BTreeMap;

use ttrpg_ast::ast::Arg;
use ttrpg_ast::Span;
use ttrpg_checker::env::DeclInfo;

use crate::eval::{eval_expr, type_name, variant_ordinal};
use crate::value::Value;
use crate::Env;
use crate::RuntimeError;

// ── ordinal / from_ordinal builtins ────────────────────────────

pub(super) fn eval_ordinal(
    env: &mut Env,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    if args.is_empty() {
        return Err(RuntimeError::with_span(
            "ordinal() requires 1 argument",
            call_span,
        ));
    }
    let val = eval_expr(env, &args[0].value)?;
    match &val {
        Value::EnumVariant {
            enum_name, variant, ..
        } => {
            let ordinal = variant_ordinal(env.interp.type_env, enum_name, variant).ok_or_else(
                || {
                    RuntimeError::with_span(
                        format!("unknown variant `{}` of enum `{}`", variant, enum_name),
                        call_span,
                    )
                },
            )?;
            Ok(Value::Int(ordinal as i64))
        }
        _ => Err(RuntimeError::with_span(
            format!(
                "ordinal() expects an enum variant, got {}",
                type_name(&val)
            ),
            call_span,
        )),
    }
}

pub(super) fn eval_from_ordinal(
    env: &mut Env,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    if args.len() < 2 {
        return Err(RuntimeError::with_span(
            "from_ordinal() requires 2 arguments",
            call_span,
        ));
    }
    let ns_val = eval_expr(env, &args[0].value)?;
    let idx_val = eval_expr(env, &args[1].value)?;

    let enum_name = match &ns_val {
        Value::EnumNamespace(name) => name.clone(),
        _ => {
            return Err(RuntimeError::with_span(
                format!(
                    "from_ordinal() first argument must be an enum type, got {}",
                    type_name(&ns_val)
                ),
                call_span,
            ));
        }
    };

    let idx = match &idx_val {
        Value::Int(n) => *n,
        _ => {
            return Err(RuntimeError::with_span(
                format!(
                    "from_ordinal() second argument must be int, got {}",
                    type_name(&idx_val)
                ),
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
                idx,
                enum_name,
                info.variants.len()
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

pub(super) fn eval_try_from_ordinal(
    env: &mut Env,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    if args.len() < 2 {
        return Err(RuntimeError::with_span(
            "try_from_ordinal() requires 2 arguments",
            call_span,
        ));
    }
    let ns_val = eval_expr(env, &args[0].value)?;
    let idx_val = eval_expr(env, &args[1].value)?;

    let enum_name = match &ns_val {
        Value::EnumNamespace(name) => name.clone(),
        _ => {
            return Err(RuntimeError::with_span(
                format!(
                    "try_from_ordinal() first argument must be an enum type, got {}",
                    type_name(&ns_val)
                ),
                call_span,
            ));
        }
    };

    let idx = match &idx_val {
        Value::Int(n) => *n,
        _ => {
            return Err(RuntimeError::with_span(
                format!(
                    "try_from_ordinal() second argument must be int, got {}",
                    type_name(&idx_val)
                ),
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
