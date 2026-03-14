mod access;
mod assign;
mod compare;
mod control;
mod dispatch;
pub(crate) mod emit;
mod helpers;
mod ops;

#[cfg(test)]
mod tests;

// Re-export the crate-visible API.
pub(crate) use assign::eval_assign_with_rhs;
pub(crate) use compare::value_eq;
pub(crate) use control::{eval_block, eval_stmt};
pub(crate) use dispatch::eval_expr;
pub(crate) use helpers::{resolve_resource_bounds_pub, try_resolve_variant_from_hint, type_name};
pub(crate) use ops::variant_ordinal;
