mod access;
mod assign;
mod compare;
mod control;
mod dispatch;
mod helpers;
mod ops;

#[cfg(test)]
mod tests;

// Re-export the crate-visible API.
pub(crate) use compare::value_eq;
pub(crate) use control::eval_block;
pub(crate) use dispatch::eval_expr;
pub(crate) use helpers::{resolve_resource_bounds_pub, type_name};
pub(crate) use ops::variant_ordinal;
