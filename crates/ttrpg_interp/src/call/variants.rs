use std::collections::BTreeMap;

use ttrpg_ast::ast::Arg;
use ttrpg_ast::{Name, Span};
use ttrpg_checker::env::{DeclInfo, ParamInfo};

use crate::value::Value;
use crate::Env;
use crate::RuntimeError;

use super::args::bind_args;

// ── Enum variant construction ──────────────────────────────────

pub(super) fn construct_enum_variant(
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
            enum_name: Name::from(enum_name),
            variant: Name::from(variant_name),
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
            with_disjunctive: false,
        })
        .collect();

    let bound = bind_args(&param_infos, args, None, env, call_span)?;

    let mut fields = BTreeMap::new();
    for (name, val) in bound {
        fields.insert(name, val);
    }

    Ok(Value::EnumVariant {
        enum_name: Name::from(enum_name),
        variant: Name::from(variant_name),
        fields,
    })
}
