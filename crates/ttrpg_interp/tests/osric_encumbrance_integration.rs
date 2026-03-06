//! OSRIC encumbrance integration test — AST structure verification.
//!
//! All runtime value tests have been moved to
//! `osric/tests/osric_encumbrance.ttrpg-cli`.

use ttrpg_ast::ast::TopLevel;

mod osric_common;
use osric_common::*;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_encumbrance() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn osric_encumbrance_parses_and_typechecks() {
    let (program, _) = compile_osric_encumbrance();
    let has_conditions = program
        .items
        .iter()
        .any(|item| matches!(&item.node, TopLevel::System(sys) if sys.name == "OSRIC Conditions"));
    assert!(has_conditions);
}
