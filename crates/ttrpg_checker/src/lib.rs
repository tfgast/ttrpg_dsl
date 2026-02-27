pub mod builtins;
pub mod check;
mod check_args;
mod check_builtins;
mod check_call;
mod check_control;
mod check_expr;
mod check_has;
mod check_literal;
mod check_method;
mod check_modify;
mod check_pattern;
mod check_stmt;
pub mod collect;
pub mod env;
pub mod scope;
pub mod ty;

use ttrpg_ast::ast::Program;
use ttrpg_ast::diagnostic::Diagnostic;
use ttrpg_ast::module::ModuleMap;

use crate::check::Checker;
use crate::collect::{collect, collect_with_modules};
use crate::env::TypeEnv;

pub struct CheckResult {
    pub diagnostics: Vec<Diagnostic>,
    pub env: TypeEnv,
}

/// Run the checker on a parsed program (single-file, no module constraints).
///
/// Pass 1: collect all declarations into a TypeEnv.
/// Pass 2: check all function/action/reaction/condition bodies.
pub fn check(program: &Program) -> CheckResult {
    let (env, diagnostics) = collect(program);
    run_pass2(program, env, diagnostics, None)
}

/// Run the checker with module awareness.
///
/// Same as `check`, but uses the `ModuleMap` to populate ownership maps
/// and visibility constraints. The checker gates name lookups via
/// `check_name_visible` using the `current_system` context.
pub fn check_with_modules(program: &Program, modules: &ModuleMap) -> CheckResult {
    let (env, diagnostics) = collect_with_modules(program, modules);
    run_pass2(program, env, diagnostics, Some(modules))
}

/// Pass 2: check all function/action/reaction/condition bodies and produce
/// the final [`CheckResult`].
fn run_pass2(
    program: &Program,
    mut env: TypeEnv,
    mut diagnostics: Vec<Diagnostic>,
    modules: Option<&ModuleMap>,
) -> CheckResult {
    let mut checker = Checker::new(&env, modules);
    checker.check_program(program);
    diagnostics.extend(checker.diagnostics);

    // Transfer resolution tables from checker to env for interpreter use.
    // Destructure to move owned fields out, dropping the borrow on `env`.
    let resolved_variants = checker.resolved_variants;
    let resolved_group_aliases = checker.resolved_group_aliases;
    let resolved_lvalue_aliases = checker.resolved_lvalue_aliases;
    let selector_matches = checker.selector_matches;
    env.resolved_variants = resolved_variants;
    env.resolved_group_aliases = resolved_group_aliases;
    env.resolved_lvalue_aliases = resolved_lvalue_aliases;
    env.selector_matches = selector_matches;

    CheckResult { diagnostics, env }
}
