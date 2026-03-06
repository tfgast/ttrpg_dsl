//! OSRIC dual-classing integration tests.
//!
//! Verifies the dual-class rules from osric/osric_dualclass.ttrpg:
//! prime requisite lookups, eligibility checks, HP gain logic,
//! old ability usage, and XP forfeit rules.
//!
//! Runtime tests have been moved to a CLI script; only the
//! parse + typecheck smoke test remains here.

use ttrpg_ast::ast::TopLevel;

mod osric_common;
use osric_common::*;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_dualclass() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn osric_dualclass_parses_and_typechecks() {
    let (program, _) = compile_osric_dualclass();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSRIC Dualclass"));
}
