//! OSRIC magic-user spell integration tests.
//!
//! Runtime derive and spell-resolution coverage has moved to
//! `osric/tests/osric_mu_spells.ttrpg-cli`.
//! This Rust file keeps only pipeline coverage for the real OSRIC sources.

use ttrpg_ast::ast::TopLevel;

mod osric_common;
use osric_common::*;

fn compile_all() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

#[test]
fn osric_mu_spells_parses_and_typechecks() {
    let (program, _) = compile_all();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSRIC MU Spells"));
}
