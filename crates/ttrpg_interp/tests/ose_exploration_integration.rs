//! OSE exploration orchestration integration tests.
//!
//! Verifies that ose/ose_exploration.ttrpg parses, lowers, and type-checks
//! through the multi-file pipeline.
//!
//! Runtime derive/mechanic tests have been moved to
//! ose/tests/ose_exploration.ttrpg-cli.

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_ast::diagnostic::Severity;

fn compile_ose_exploration() -> ttrpg_ast::ast::Program {
    let core_source = include_str!("../../../ose/ose_core.ttrpg");
    let exploration_source = include_str!("../../../ose/ose_exploration.ttrpg");

    let sources = vec![
        ("ose/ose_core.ttrpg".to_string(), core_source.to_string()),
        (
            "ose/ose_exploration.ttrpg".to_string(),
            exploration_source.to_string(),
        ),
    ];

    let parse_result = ttrpg_parser::parse_multi(&sources);
    let parse_errors: Vec<_> = parse_result
        .diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .collect();
    assert!(
        parse_errors.is_empty(),
        "parse/lower errors: {:?}",
        parse_errors.iter().map(|d| &d.message).collect::<Vec<_>>()
    );

    let (program, module_map) = parse_result.ok().unwrap();
    let result = ttrpg_checker::check_with_modules(program, module_map);
    let errors: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .collect();
    assert!(
        errors.is_empty(),
        "checker errors: {:?}",
        errors.iter().map(|d| &d.message).collect::<Vec<_>>()
    );

    program.clone()
}

#[test]
fn ose_exploration_parses_and_typechecks() {
    let program = compile_ose_exploration();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSE"));
    assert!(system_names.contains(&"OSE Exploration"));
}

#[test]
fn ose_exploration_has_expected_decls() {
    let program = compile_ose_exploration();

    let mut has_action_enum = false;
    let mut has_phase_enum = false;
    let mut has_action_phase_enum = false;
    let mut has_turn_phases_derive = false;
    let mut has_action_phases_table = false;
    let mut has_skip_phase_derive = false;
    let mut has_wandering_roll = false;

    for item in &program.items {
        if let TopLevel::System(sys) = &item.node
            && sys.name == "OSE Exploration"
        {
            for decl in &sys.decls {
                match &decl.node {
                    DeclKind::Enum(e) if e.name == "ExplorationAction" => {
                        has_action_enum = true;
                        assert_eq!(e.variants.len(), 6);
                    }
                    DeclKind::Enum(e) if e.name == "ExplorationPhase" => {
                        has_phase_enum = true;
                        assert_eq!(e.variants.len(), 6);
                    }
                    DeclKind::Enum(e) if e.name == "ExplorationActionPhase" => {
                        has_action_phase_enum = true;
                        assert_eq!(e.variants.len(), 14);
                    }
                    DeclKind::Const(c) if c.name == "EXPLORATION_TURN_PHASES" => {
                        has_turn_phases_derive = true;
                    }
                    DeclKind::Table(t) if t.name == "exploration_action_phases" => {
                        has_action_phases_table = true;
                    }
                    DeclKind::Derive(d) if d.name == "skip_exploration_phase" => {
                        has_skip_phase_derive = true;
                    }
                    DeclKind::Mechanic(m) if m.name == "wandering_monster_roll" => {
                        has_wandering_roll = true;
                    }
                    _ => {}
                }
            }
        }
    }

    assert!(has_action_enum, "expected ExplorationAction enum");
    assert!(has_phase_enum, "expected ExplorationPhase enum");
    assert!(
        has_action_phase_enum,
        "expected ExplorationActionPhase enum"
    );
    assert!(
        has_turn_phases_derive,
        "expected EXPLORATION_TURN_PHASES const"
    );
    assert!(
        has_action_phases_table,
        "expected exploration_action_phases table"
    );
    assert!(
        has_skip_phase_derive,
        "expected skip_exploration_phase derive"
    );
    assert!(
        has_wandering_roll,
        "expected wandering_monster_roll mechanic"
    );
}
