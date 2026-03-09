//! OSRIC falling damage integration tests — parser/typechecker coverage only.
//!
//! Runtime value checks (distance-to-dice lookup, save-for-half behavior, and
//! the <10ft edge case) have been moved to `osric/tests/osric_falling.ttrpg-cli`.

use ttrpg_ast::ast::TopLevel;

mod osric_common;
use osric_common::*;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_falling() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn osric_falling_parses_and_typechecks() {
    let (program, _) = compile_osric_falling();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSRIC Falling"));
}
