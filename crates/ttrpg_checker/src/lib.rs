pub mod ty;
pub mod env;
pub mod scope;
pub mod builtins;
pub mod collect;
pub mod check;
mod check_expr;
mod check_stmt;
mod check_pattern;
mod check_modify;

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
    // Pass 1: collect declarations
    let (env, mut diagnostics) = collect(program);

    // Pass 2: check bodies
    let mut checker = Checker::new(&env, None);
    checker.check_program(program);
    diagnostics.extend(checker.diagnostics);

    CheckResult { diagnostics, env }
}

/// Run the checker with module awareness.
///
/// Same as `check`, but uses the `ModuleMap` to populate ownership maps
/// and visibility constraints. The checker gates name lookups via
/// `check_name_visible` using the `current_system` context.
pub fn check_with_modules(program: &Program, modules: &ModuleMap) -> CheckResult {
    // Pass 1: collect declarations with module ownership
    let (env, mut diagnostics) = collect_with_modules(program, modules);

    // Pass 2: check bodies with module-aware visibility
    let mut checker = Checker::new(&env, Some(modules));
    checker.check_program(program);
    diagnostics.extend(checker.diagnostics);

    CheckResult { diagnostics, env }
}
