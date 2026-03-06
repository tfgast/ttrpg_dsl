//! OSRIC encumbrance integration test — AST structure verification.
//!
//! Runtime value tests (effective_str_encumbrance, character_encumbrance,
//! character_movement, character_surprise_adj, update_encumbrance) have been
//! moved to `osric/tests/osric_encumbrance.ttrpg-cli`.
//!
//! This file retains the parse+typecheck test and Dwarf movement tests
//! (which require the Feet unit type not yet supported in CLI spawn).

use ttrpg_ast::ast::TopLevel;
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

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

#[test]
fn character_movement_dwarf_with_encumbrance() {
    let (program, result) = compile_osric_encumbrance();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // Dwarf 90ft base
    let cases = [
        ("Unencumbered", 90), // 90 * 4/4 = 90
        ("Light", 67),        // floor(90 * 3/4) = floor(67.5) = 67
        ("Moderate", 45),     // floor(90 * 2/4) = 45
        ("Heavy", 22),        // floor(90 * 1/4) = floor(22.5) = 22
        ("Overloaded", 0),    // 90 * 0/4 = 0
    ];

    for (tier_name, expected) in cases {
        let char_ref = make_encumbrance_character(
            &mut state,
            &format!("Dwarf-{tier_name}"),
            &standard_abilities(),
            "Dwarf",
            0,
            0,
        );
        apply_encumbrance(&mut state, &char_ref, tier_name);

        let val = interp
            .evaluate_derive(
                &state,
                &mut handler,
                "character_movement",
                vec![Value::Entity(char_ref)],
            )
            .unwrap();
        assert_eq!(
            expect_feet(val, &format!("Dwarf {tier_name}")),
            expected,
            "Dwarf + {tier_name}"
        );
    }
}
