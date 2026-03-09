//! OSRIC afflictions integration tests — parse/typecheck coverage.
//!
//! Behavioural poison, disease, and insanity tests have been moved to
//! `osric/tests/osric_afflictions.ttrpg-cli`.

use ttrpg_ast::ast::TopLevel;

mod osric_common;
use osric_common::*;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_afflictions() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn osric_afflictions_parses_and_typechecks() {
    let (program, _) = compile_osric_afflictions();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSRIC Afflictions"));
}
