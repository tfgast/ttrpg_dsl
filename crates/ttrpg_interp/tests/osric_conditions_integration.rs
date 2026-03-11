//! OSRIC conditions integration test — AST structure verification.
//!
//! Behavioural tests (condition modifiers, stacking, removal, cross-entity-type
//! application) have been moved to `osric/tests/osric_conditions.ttrpg-cli`.
//! This file retains only tests that inspect AST structure or use the Rust API
//! directly (condition list inspection).

use std::collections::BTreeMap;

use rustc_hash::FxHashMap;
use ttrpg_ast::Name;
use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::{ConditionArgs, StateProvider, WritableState};
use ttrpg_interp::value::Value;

mod osric_common;
use osric_common::*;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_conditions() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

fn get_conditions_decls(program: &ttrpg_ast::ast::Program) -> &[ttrpg_ast::Spanned<DeclKind>] {
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node
            && sys.name == "OSRIC Conditions"
        {
            return &sys.decls;
        }
    }
    panic!("no system block named 'OSRIC Conditions' found");
}

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn osric_conditions_parses_and_typechecks() {
    let (program, _) = compile_osric_conditions();
    let has_system = program
        .items
        .iter()
        .any(|item| matches!(&item.node, TopLevel::System(sys) if sys.name == "OSRIC Conditions"));
    assert!(has_system, "expected system named 'OSRIC Conditions'");
}

// ── Structure verification ─────────────────────────────────────

#[test]
fn osric_conditions_has_all_conditions() {
    let (program, _) = compile_osric_conditions();
    let decls = get_conditions_decls(&program);
    let conditions: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Condition(c) => Some(&*c.name),
            _ => None,
        })
        .collect();

    let expected = [
        "Prone",
        "Stunned",
        "Staggered",
        "Invisible",
        "Paralyzed",
        "NormalSleep",
        "Sleeping",
        "Fleeing",
        "Surprised",
        "RearAttacked",
        "Concealed",
        "Cover",
        "Charging",
        "ChargeRecovery",
        "Unconscious",
        // Bleeding moved to OSRIC Combat (needs restricted hp access)
        "Dead",
        "Scarred",
        "Coma",
        "Blinded",
        "Confused",
        "Deafened",
        "Grappling",
        "Overborne",
        "Parrying",
        "FourLegged",
        "MultiArmed",
        "EncumbranceState",
        "Charmed",
        "Frightened",
        "Enfeebled",
        "Forgotten",
    ];

    for name in &expected {
        assert!(
            conditions.contains(name),
            "missing condition: {name}. Found: {conditions:?}"
        );
    }
    assert_eq!(
        conditions.len(),
        31,
        "expected 31 conditions, found {}: {:?}",
        conditions.len(),
        conditions
    );
}

#[test]
fn osric_conditions_simple_have_no_params() {
    let (program, _) = compile_osric_conditions();
    let decls = get_conditions_decls(&program);
    let simple = [
        "Prone",
        "Stunned",
        "Staggered",
        "Invisible",
        "Paralyzed",
        "Sleeping",
        "Fleeing",
        "Surprised",
        "RearAttacked",
        "Blinded",
        "Confused",
        "Deafened",
        "Overborne",
    ];

    for item in decls {
        if let DeclKind::Condition(c) = &item.node
            && simple.contains(&&*c.name)
        {
            assert!(
                c.params.is_empty(),
                "condition {} should have no params but has {}",
                c.name,
                c.params.len()
            );
        }
    }
}

#[test]
fn osric_conditions_concealed_has_level_param() {
    let (program, _) = compile_osric_conditions();
    let decls = get_conditions_decls(&program);
    for item in decls {
        if let DeclKind::Condition(c) = &item.node
            && &*c.name == "Concealed"
        {
            assert_eq!(c.params.len(), 1, "Concealed should have 1 param");
            assert_eq!(&*c.params[0].name, "level");
            return;
        }
    }
    panic!("Concealed condition not found");
}

#[test]
fn osric_conditions_cover_has_penalty_param() {
    let (program, _) = compile_osric_conditions();
    let decls = get_conditions_decls(&program);
    for item in decls {
        if let DeclKind::Condition(c) = &item.node
            && &*c.name == "Cover"
        {
            assert_eq!(c.params.len(), 1, "Cover should have 1 param");
            assert_eq!(&*c.params[0].name, "penalty");
            return;
        }
    }
    panic!("Cover condition not found");
}

// ── Rust API: condition list inspection ─────────────────────────

#[test]
fn condition_count_after_apply_and_remove() {
    let (_, _) = compile_osric_conditions();
    let mut state = GameState::new();
    let mut char_fields = FxHashMap::default();
    char_fields.insert(Name::from("name"), Value::Str("Test".to_string()));
    char_fields.insert(
        Name::from("classes"),
        Value::List(vec![class_level_struct("Fighter", 1, 0)]),
    );
    char_fields.insert(Name::from("classing_mode"), classing_mode("Single"));
    char_fields.insert(Name::from("ancestry"), enum_variant("Ancestry", "Human"));
    char_fields.insert(
        Name::from("alignment"),
        enum_variant("Alignment", "TrueNeutral"),
    );
    char_fields.insert(Name::from("abilities"), Value::Map(BTreeMap::new()));
    char_fields.insert(Name::from("max_hp"), Value::Int(10));
    char_fields.insert(Name::from("hp"), Value::Int(10));
    char_fields.insert(Name::from("base_movement"), feet(120));
    char_fields.insert(Name::from("current_weight"), Value::Int(0));

    char_fields.insert(Name::from("saving_throws"), Value::Option(None));
    char_fields.insert(Name::from("wielded_main"), Value::Option(None));
    char_fields.insert(Name::from("wielded_off"), Value::Option(None));
    char_fields.insert(Name::from("worn_armor"), Value::Option(None));
    char_fields.insert(Name::from("worn_shield"), Value::Option(None));
    let entity = state.add_entity("Character", char_fields);

    // Apply three conditions
    state.apply_condition(&entity, "Prone", ConditionArgs::default());
    state.apply_condition(&entity, "Stunned", ConditionArgs::default());
    state.apply_condition(&entity, "Staggered", ConditionArgs::default());
    assert_eq!(state.read_conditions(&entity).unwrap().len(), 3);

    // Remove one
    state.remove_condition(&entity, "Stunned", None);
    let conds = state.read_conditions(&entity).unwrap();
    assert_eq!(conds.len(), 2);
    let names: Vec<_> = conds.iter().map(|c| c.name.to_string()).collect();
    assert!(names.contains(&"Prone".to_string()));
    assert!(names.contains(&"Staggered".to_string()));
    assert!(!names.contains(&"Stunned".to_string()));
}
