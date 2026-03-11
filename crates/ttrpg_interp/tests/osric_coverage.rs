//! OSRIC combined DSL coverage test.
//!
//! Compiles all 9 OSRIC source files, attaches shared coverage tracking,
//! and runs every subsystem's scenario functions to produce a combined
//! coverage report. The report is written to `target/osric_coverage_report.txt`.

use std::cell::RefCell;
use std::rc::Rc;

use ttrpg_ast::diagnostic::MultiSourceMap;
use ttrpg_interp::Interpreter;
use ttrpg_interp::coverage::{self, CoverageData, CoverageSource};

mod osric_common;
use osric_common::*;

#[test]
fn osric_combined_coverage() {
    // 1. Load all 9 OSRIC source files
    let sources = all_osric_sources();

    // 2. Compile through the full pipeline
    let (program, result) = compile_osric_sources(sources.clone());

    // 3. Create shared coverage data and attach to interpreter
    let cov = Rc::new(RefCell::new(CoverageData::new()));
    let mut interp = Interpreter::new(&program, &result.env).unwrap();
    interp.set_coverage(Rc::clone(&cov));

    // 4. Run all scenario functions to exercise DSL code paths
    let state = ttrpg_interp::reference_state::GameState::new();

    run_all_ability(&interp, &state);
    run_all_character(&interp, &state);
    run_all_class(&interp, &state);
    run_all_saves(&interp, &state);
    run_all_equipment(&interp, &state);
    run_all_encumbrance(&interp);
    run_all_conditions(&interp);
    run_all_combat(&interp);
    run_all_initiative(&interp);

    // 5. Build CoverageSource list from the source map
    let sm = MultiSourceMap::new(sources.into_iter().collect());
    let mut cov_sources = Vec::new();
    for i in 0..sm.file_count() {
        if let Some((filename, source, line_starts)) = sm.file_info(i) {
            cov_sources.push(CoverageSource {
                filename: filename.to_string(),
                source: source.to_string(),
                file_id: i as u32,
                line_starts: line_starts.to_vec(),
            });
        }
    }

    // 6. Render and write report
    let report = coverage::render_coverage_report(&cov.borrow(), &cov_sources, &program);

    let out_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../target/osric_coverage_report.txt");
    std::fs::write(&out_path, &report).expect("failed to write coverage report");

    // Print summary to stdout (visible with --nocapture)
    let lines: Vec<&str> = report.lines().collect();
    // Find and print the summary section (last ~20 lines typically)
    let summary_start = lines
        .iter()
        .rposition(|l| l.starts_with("══"))
        .unwrap_or(lines.len().saturating_sub(20));
    for line in &lines[summary_start..] {
        println!("{line}");
    }

    println!("\nFull report: {}", out_path.display());
}
