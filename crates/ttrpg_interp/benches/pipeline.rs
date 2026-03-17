//! Criterion benchmarks for the core TTRPG DSL pipeline.
//!
//! Workload: `ose/ose_combat.ttrpg` — the full OSE combat system file.
//! Each benchmark isolates a single pipeline stage so regressions are
//! immediately attributable.

use std::sync::Arc;

use criterion::{Criterion, black_box, criterion_group, criterion_main};

use ttrpg_ast::FileId;
use ttrpg_ast::diagnostic::Severity;
use ttrpg_interp::Interpreter;
use ttrpg_interp::adapter::StateAdapter;
use ttrpg_interp::effect::{Effect, EffectHandler, Response, Step};
use ttrpg_interp::execution::Execution;
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::runtime_core::RuntimeCore;
use ttrpg_interp::value::Value;
use ttrpg_lexer::Lexer;

static SOURCE: &str = include_str!("../../../ose/ose_combat.ttrpg");

// ── Helpers ──────────────────────────────────────────────────────

fn parse_source() -> (ttrpg_ast::ast::Program, Vec<ttrpg_ast::Diagnostic>) {
    ttrpg_parser::parse(SOURCE, FileId::SYNTH)
}

fn lower(program: ttrpg_ast::ast::Program) -> ttrpg_ast::ast::Program {
    let mut diags = Vec::new();
    ttrpg_parser::lower_moves(program, &mut diags)
}

fn check(program: &ttrpg_ast::ast::Program) -> ttrpg_checker::CheckResult {
    ttrpg_checker::check(program)
}

struct NullHandler;

impl EffectHandler for NullHandler {
    fn handle(&mut self, _effect: Effect) -> Response {
        Response::Acknowledged
    }
}

// ── Benchmarks ───────────────────────────────────────────────────

fn bench_lex(c: &mut Criterion) {
    c.bench_function("lex_ose_combat", |b| {
        b.iter(|| {
            let lexer = Lexer::new(black_box(SOURCE), FileId::SYNTH);
            let count: usize = lexer.count();
            black_box(count);
        });
    });
}

fn bench_parse(c: &mut Criterion) {
    c.bench_function("parse_ose_combat", |b| {
        b.iter(|| {
            let (program, diags) = parse_source();
            assert!(diags.is_empty());
            black_box(program);
        });
    });
}

fn bench_lower(c: &mut Criterion) {
    let (program, _) = parse_source();

    c.bench_function("lower_ose_combat", |b| {
        b.iter(|| {
            let lowered = lower(program.clone());
            black_box(lowered);
        });
    });
}

fn bench_check(c: &mut Criterion) {
    let (program, _) = parse_source();
    let program = lower(program);

    c.bench_function("check_ose_combat", |b| {
        b.iter(|| {
            let result = check(black_box(&program));
            assert!(
                result
                    .diagnostics
                    .iter()
                    .all(|d| d.severity != Severity::Error)
            );
            black_box(result);
        });
    });
}

fn bench_interpret_derive(c: &mut Criterion) {
    let (program, _) = parse_source();
    let program = lower(program);
    let result = check(&program);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    c.bench_function("interpret_derive_target_number", |b| {
        b.iter(|| {
            let val = interp
                .evaluate_derive(
                    &state,
                    &mut NullHandler,
                    "target_number",
                    vec![Value::Int(19), Value::Int(5)],
                )
                .unwrap();
            black_box(val);
        });
    });
}

fn bench_full_pipeline(c: &mut Criterion) {
    c.bench_function("full_pipeline_ose_combat", |b| {
        b.iter(|| {
            // lex + parse
            let (program, diags) = ttrpg_parser::parse(black_box(SOURCE), FileId::SYNTH);
            assert!(diags.is_empty());

            // lower
            let program = lower(program);

            // check
            let result = check(&program);
            assert!(
                result
                    .diagnostics
                    .iter()
                    .all(|d| d.severity != Severity::Error)
            );

            // interpret a derive
            let interp = Interpreter::new(&program, &result.env).unwrap();
            let state = GameState::new();
            let val = interp
                .evaluate_derive(
                    &state,
                    &mut NullHandler,
                    "target_number",
                    vec![Value::Int(19), Value::Int(5)],
                )
                .unwrap();

            black_box(val);
        });
    });
}

// ── Step-mode benchmarks ─────────────────────────────────────────

fn bench_step_derive(c: &mut Criterion) {
    let (program, _) = parse_source();
    let program = lower(program);
    let result = check(&program);
    let program = Arc::new(program);
    let type_env = Arc::new(result.env);

    c.bench_function("step_derive_target_number", |b| {
        b.iter(|| {
            let state = GameState::new();
            let core = RuntimeCore::new(program.clone(), type_env.clone(), 1, 1);
            let adapter = StateAdapter::new(state);
            let exec = Execution::start_derive(
                core,
                adapter,
                "target_number",
                vec![Value::Int(19), Value::Int(5)],
            )
            .unwrap();
            let val = exec.run_with_handler(&mut NullHandler).unwrap();
            black_box(val);
        });
    });
}

fn bench_step_derive_poll(c: &mut Criterion) {
    let (program, _) = parse_source();
    let program = lower(program);
    let result = check(&program);
    let program = Arc::new(program);
    let type_env = Arc::new(result.env);

    c.bench_function("step_derive_target_number_poll", |b| {
        b.iter(|| {
            let state = GameState::new();
            let core = RuntimeCore::new(program.clone(), type_env.clone(), 1, 1);
            let adapter = StateAdapter::new(state);
            let mut exec = Execution::start_derive(
                core,
                adapter,
                "target_number",
                vec![Value::Int(19), Value::Int(5)],
            )
            .unwrap();
            loop {
                match exec.poll().unwrap() {
                    Step::Done(val) => {
                        black_box(val);
                        break;
                    }
                    Step::Yielded(_effect) => {
                        exec.respond(Response::Acknowledged).unwrap();
                    }
                }
            }
        });
    });
}

criterion_group!(
    benches,
    bench_lex,
    bench_parse,
    bench_lower,
    bench_check,
    bench_interpret_derive,
    bench_step_derive,
    bench_step_derive_poll,
    bench_full_pipeline,
);
criterion_main!(benches);
