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

use crate::check::Checker;
use crate::collect::collect;
use crate::env::TypeEnv;

pub struct CheckResult {
    pub diagnostics: Vec<Diagnostic>,
    pub env: TypeEnv,
}

/// Run the checker on a parsed program.
///
/// Pass 1: collect all declarations into a TypeEnv.
/// Pass 2: check all function/action/reaction/condition bodies.
pub fn check(program: &Program) -> CheckResult {
    // Pass 1: collect declarations
    let (env, mut diagnostics) = collect(program);

    // Pass 2: check bodies
    let mut checker = Checker::new(&env);
    checker.check_program(program);
    diagnostics.extend(checker.diagnostics);

    CheckResult { diagnostics, env }
}
