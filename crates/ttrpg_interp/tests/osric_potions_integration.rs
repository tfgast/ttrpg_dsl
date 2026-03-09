//! OSRIC potions integration test — parse/typecheck and AST checks only.
//!
//! Runtime coverage for potion healing, DrinkPotion item consumption,
//! PotionSpeed/PotionInvulnerability effects, admixture_result, potion_item,
//! and healing unconscious characters has moved to
//! `osric/tests/osric_potions.ttrpg-cli`.
//! This file retains only compiler-visible structure checks.

use ttrpg_ast::ast::{DeclKind, TopLevel};

mod osric_common;
use osric_common::*;

fn compile_osric() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

fn get_potions_decls(program: &ttrpg_ast::ast::Program) -> &[ttrpg_ast::Spanned<DeclKind>] {
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSRIC Potions" {
                return &sys.decls;
            }
        }
    }
    panic!("no system block named 'OSRIC Potions' found");
}

#[test]
fn osric_potions_parses_and_typechecks() {
    let (program, _) = compile_osric();
    let has_system = program
        .items
        .iter()
        .any(|item| matches!(&item.node, TopLevel::System(sys) if sys.name == "OSRIC Potions"));
    assert!(has_system, "expected system named 'OSRIC Potions'");
}

#[test]
fn osric_potions_has_expected_conditions() {
    let (program, _) = compile_osric();
    let decls = get_potions_decls(&program);
    let conditions: Vec<_> = decls
        .iter()
        .filter_map(|decl| match &decl.node {
            DeclKind::Condition(cond) => Some(cond.name.to_string()),
            _ => None,
        })
        .collect();

    for expected in ["PotionSpeed", "PotionInvulnerability"] {
        assert!(
            conditions.contains(&expected.to_string()),
            "missing condition: {expected}, got {conditions:?}"
        );
    }
}

#[test]
fn osric_potions_has_expected_callable_decls() {
    let (program, _) = compile_osric();
    let decls = get_potions_decls(&program);

    let derives: Vec<_> = decls
        .iter()
        .filter_map(|decl| match &decl.node {
            DeclKind::Derive(derive) => Some(derive.name.to_string()),
            _ => None,
        })
        .collect();
    let functions: Vec<_> = decls
        .iter()
        .filter_map(|decl| match &decl.node {
            DeclKind::Function(function) => Some(function.name.to_string()),
            _ => None,
        })
        .collect();
    let actions: Vec<_> = decls
        .iter()
        .filter_map(|decl| match &decl.node {
            DeclKind::Action(action) => Some(action.name.to_string()),
            _ => None,
        })
        .collect();

    for expected in ["potion_item", "admixture_result"] {
        assert!(
            derives.contains(&expected.to_string()),
            "missing derive: {expected}, got {derives:?}"
        );
    }
    for expected in [
        "resolve_potion_healing",
        "resolve_potion_extra_healing",
        "resolve_potion_speed",
        "resolve_potion_invulnerability",
    ] {
        assert!(
            functions.contains(&expected.to_string()),
            "missing function: {expected}, got {functions:?}"
        );
    }
    assert!(
        actions.contains(&"DrinkPotion".to_string()),
        "missing action: DrinkPotion, got {actions:?}"
    );
}
