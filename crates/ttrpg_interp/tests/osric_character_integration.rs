//! OSRIC character integration test.
//!
//! Verifies that osric/osric_character.ttrpg parses, lowers, and type-checks
//! through the full multi-file pipeline (core + ability + character).
//! Runtime derive tests have been moved to CLI scripts.

use ttrpg_ast::ast::TopLevel;

mod osric_common;
use osric_common::*;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_character() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn osric_character_parses_and_typechecks() {
    let (program, _) = compile_osric_character();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSRIC"));
    assert!(system_names.contains(&"OSRIC Ability"));
    assert!(system_names.contains(&"OSRIC Character"));
}
