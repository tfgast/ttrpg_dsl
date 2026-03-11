use std::collections::BTreeMap;

use ttrpg_ast::ast::{Arg, Param};
use ttrpg_ast::{Name, Span};
use ttrpg_checker::env::{DeclInfo, ParamInfo};

use crate::Env;
use crate::RuntimeError;
use crate::value::Value;

use super::args::bind_args;

// ── Enum variant construction ──────────────────────────────────

/// Find the AST field entries for an enum variant, used to evaluate defaults.
fn find_variant_ast_fields(env: &Env, enum_name: &str, variant_name: &str) -> Vec<Param> {
    use ttrpg_ast::ast::{DeclKind, TopLevel};

    for item in &env.interp.program.items {
        if let TopLevel::System(system) = &item.node {
            for decl in &system.decls {
                if let DeclKind::Enum(e) = &decl.node {
                    if e.name == enum_name {
                        for v in &e.variants {
                            if v.name == variant_name {
                                if let Some(ref fields) = v.fields {
                                    return fields
                                        .iter()
                                        .map(|f| Param {
                                            name: f.name.clone(),
                                            ty: f.ty.clone(),
                                            default: f.default.clone(),
                                            with_groups: Default::default(),
                                            span: f.span,
                                        })
                                        .collect();
                                }
                                return Vec::new();
                            }
                        }
                    }
                }
            }
        }
    }
    Vec::new()
}

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
                format!("internal error: '{enum_name}' is not an enum"),
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
                format!("enum '{enum_name}' has no variant '{variant_name}'"),
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

    let has_any_default = variant_info.has_defaults.iter().any(|d| *d);

    // Build ParamInfo from variant fields
    let param_infos: Vec<ParamInfo> = variant_info
        .fields
        .iter()
        .enumerate()
        .map(|(i, (name, ty))| ParamInfo {
            name: name.clone(),
            ty: ty.clone(),
            has_default: variant_info.has_defaults.get(i).copied().unwrap_or(false),
            with_groups: vec![],
            with_disjunctive: false,
        })
        .collect();

    // If any field has a default, look up the AST to get default expressions
    let ast_params = if has_any_default {
        Some(find_variant_ast_fields(env, enum_name, variant_name))
    } else {
        None
    };

    let bound = bind_args(&param_infos, args, ast_params.as_deref(), env, call_span)?;

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
