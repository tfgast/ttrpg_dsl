mod actions;
mod args;
mod collection_builtins;
mod dispatch;
mod functions;
mod methods;
mod ordinals;
mod variants;

#[cfg(test)]
mod tests;

// Re-export the crate-visible API.
pub(crate) use dispatch::eval_call;
pub(crate) use functions::{dispatch_table_with_values, evaluate_fn_with_values};
