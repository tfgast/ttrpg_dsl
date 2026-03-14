#![no_main]

//! Differential fuzzer: generates arbitrary ASTs, then evaluates zero-argument
//! derives, tables, and functions through both the recursive `Interpreter`
//! path and the step-based `Execution` frame stack, asserting results match.

use std::rc::Rc;
use std::sync::Arc;

use arbitrary::Unstructured;
use libfuzzer_sys::fuzz_target;
use ttrpg_ast::ast::Program;
use ttrpg_interp::adapter::StateAdapter;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::execution::Execution;
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::runtime_core::RuntimeCore;
use ttrpg_interp::value::RollResult;
use ttrpg_interp::Interpreter;

/// Deterministic handler: acknowledges gates, rolls all 1s, uses defaults.
struct DeterministicHandler;

impl EffectHandler for DeterministicHandler {
    fn handle(&mut self, effect: Effect) -> Response {
        match &effect {
            Effect::RollDice { expr } => {
                let num_dice: usize = expr.groups.iter().map(|g| g.count as usize).sum();
                let total = num_dice as i64 + expr.modifier;
                Response::Rolled(RollResult {
                    expr: expr.clone(),
                    dice: vec![1; num_dice],
                    kept: vec![1; num_dice],
                    modifier: expr.modifier,
                    total,
                    unmodified: num_dice as i64,
                })
            }
            Effect::ResolvePrompt { suggest, .. } => {
                if let Some(val) = suggest {
                    Response::PromptResult(val.clone())
                } else {
                    Response::UseDefault
                }
            }
            _ => Response::Acknowledged,
        }
    }
}

fuzz_target!(|data: &[u8]| {
    let Ok(program) = Unstructured::new(data).arbitrary::<Program>() else {
        return;
    };

    let mut diags = Vec::new();
    let program = ttrpg_parser::lower_moves(program, &mut diags);

    let check_result = ttrpg_checker::check(&program);
    // Don't filter on errors — the interpreter should handle (or reject)
    // ill-typed programs the same way on both paths.

    let program = Arc::new(program);
    let type_env = Arc::new(check_result.env);

    // Collect zero-argument derives, tables, and functions
    let targets: Vec<&str> = program
        .derives
        .iter()
        .filter(|(_, d)| d.params.is_empty())
        .map(|(name, _)| name.as_ref())
        .chain(
            program
                .tables
                .iter()
                .filter(|(_, t)| t.params.is_empty())
                .map(|(name, _)| name.as_ref()),
        )
        .chain(
            program
                .functions
                .iter()
                .filter(|(_, f)| f.params.is_empty())
                .map(|(name, _)| name.as_ref()),
        )
        .collect();

    if targets.is_empty() {
        return;
    }

    // Build interpreter once (shared across targets)
    let interp = match Interpreter::new(&program, &type_env) {
        Ok(i) => i,
        Err(_) => return,
    };

    for name in targets {
        let is_derive_or_table =
            program.derives.contains_key(name) || program.tables.contains_key(name);

        // ── Path A: Recursive Interpreter ──
        let gs_a = GameState::new();
        let mut handler_a = DeterministicHandler;
        let result_a = if is_derive_or_table {
            interp.evaluate_derive(&gs_a, &mut handler_a, name, vec![])
        } else {
            interp.evaluate_function(&gs_a, &mut handler_a, name, vec![])
        };

        // ── Path B: Step-based Execution ──
        let core = RuntimeCore::new(Arc::clone(&program), Arc::clone(&type_env), 1, 1);
        let gs_b = GameState::new();
        let adapter = StateAdapter::new(gs_b);
        let mut handler_b = DeterministicHandler;

        let exec = if is_derive_or_table {
            match Execution::start_derive(Rc::clone(&core), adapter, name, vec![]) {
                Ok(e) => e,
                Err(_) => continue,
            }
        } else {
            match Execution::start_function(Rc::clone(&core), adapter, name, vec![]) {
                Ok(e) => e,
                Err(_) => continue,
            }
        };

        let result_b = exec.run_with_handler(&mut handler_b);

        // ── Compare ──
        match (&result_a, &result_b) {
            (Ok(va), Ok(vb)) => {
                assert!(
                    va == vb,
                    "DIVERGENCE in '{name}': recursive={va:?}, step={vb:?}"
                );
            }
            (Err(_), Err(_)) => {}
            (Ok(va), Err(eb)) => {
                panic!("DIVERGENCE in '{name}': recursive=Ok({va:?}), step=Err({eb:?})");
            }
            (Err(ea), Ok(vb)) => {
                panic!("DIVERGENCE in '{name}': recursive=Err({ea:?}), step=Ok({vb:?})");
            }
        }
    }
});
