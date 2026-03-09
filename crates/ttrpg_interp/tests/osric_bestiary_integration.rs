//! OSRIC bestiary integration tests.
//!
//! Runtime factory/condition/saving-throw coverage has been moved to
//! `osric/tests/osric_bestiary.ttrpg-cli`.
//!
//! This file retains parse/typecheck coverage for the bestiary modules.

use ttrpg_ast::ast::TopLevel;

mod osric_common;
use osric_common::{all_osric_sources, compile_osric_sources};

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_bestiary() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn osric_bestiary_parses_and_typechecks() {
    let (program, _) = compile_osric_bestiary();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSRIC Bestiary"));
    assert!(system_names.contains(&"OSRIC Monster Traits"));
}
