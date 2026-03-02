//! Profiling harness — run under samply or perf.
//!
//! Usage:
//!   cargo build --profile profiling -p ttrpg_cli --example profile_pipeline
//!   samply record target/profiling/examples/profile_pipeline

use ttrpg_ast::diagnostic::Severity;
use ttrpg_ast::FileId;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

static OSE_COMBAT: &str = include_str!("../../../ose/ose_combat.ttrpg");
static DND5E: &str = include_str!("../../../examples/dnd5e_expanded.ttrpg");
static SPEC_FULL: &str = include_str!("../../../spec/v0/04_full_example.ttrpg");

struct NullHandler;

impl EffectHandler for NullHandler {
    fn handle(&mut self, _effect: Effect) -> Response {
        Response::Acknowledged
    }
}

fn run_pipeline(source: &str) {
    // lex + parse
    let (program, diags) = ttrpg_parser::parse(source, FileId::SYNTH);
    assert!(diags.is_empty(), "Parse errors: {diags:?}");

    // lower
    let mut lower_diags = Vec::new();
    let program = ttrpg_parser::lower_moves(program, &mut lower_diags);

    // check
    let result = ttrpg_checker::check(&program);
    assert!(
        result
            .diagnostics
            .iter()
            .all(|d| d.severity != Severity::Error),
        "Check errors: {:?}",
        result.diagnostics
    );

    // interpret a derive if available
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    if let Ok(val) = interp.evaluate_derive(
        &state,
        &mut NullHandler,
        "target_number",
        vec![Value::Int(19), Value::Int(5)],
    ) {
        std::hint::black_box(val);
    }
}

fn main() {
    let iterations: usize = std::env::var("PROFILE_ITERS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(1000);

    eprintln!("Running {iterations} iterations across 3 source files...");

    for i in 0..iterations {
        run_pipeline(OSE_COMBAT);
        run_pipeline(DND5E);
        run_pipeline(SPEC_FULL);
        if (i + 1) % 100 == 0 {
            eprintln!("  iteration {}/{iterations}", i + 1);
        }
    }

    eprintln!("Done.");
}
