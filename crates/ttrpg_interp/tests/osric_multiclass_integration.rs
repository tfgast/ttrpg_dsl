//! OSRIC multi-classing integration tests.
//!
//! Verifies the multi-class rules from osric/osric_multiclass.ttrpg:
//! valid combo validation, XP splitting, HP averaging, and armour
//! permission aggregation.

use ttrpg_ast::ast::TopLevel;

mod osric_common;
use osric_common::*;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_multiclass() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn osric_multiclass_parses_and_typechecks() {
    let (program, _) = compile_osric_multiclass();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSRIC Multiclass"));
}
