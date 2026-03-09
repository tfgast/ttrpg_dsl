//! OSRIC scrolls integration test — parse/typecheck and AST checks.

use ttrpg_ast::ast::{DeclKind, TopLevel};

mod osric_common;
use osric_common::*;

fn compile_osric() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

fn get_scrolls_decls(program: &ttrpg_ast::ast::Program) -> &[ttrpg_ast::Spanned<DeclKind>] {
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSRIC Scrolls" {
                return &sys.decls;
            }
        }
    }
    panic!("no system block named 'OSRIC Scrolls' found");
}

#[test]
fn osric_scrolls_parses_and_typechecks() {
    let (program, _) = compile_osric();
    let has_system = program
        .items
        .iter()
        .any(|item| matches!(&item.node, TopLevel::System(sys) if sys.name == "OSRIC Scrolls"));
    assert!(has_system, "expected system named 'OSRIC Scrolls'");
}

#[test]
fn osric_scrolls_has_expected_conditions() {
    let (program, _) = compile_osric();
    let decls = get_scrolls_decls(&program);
    let conditions: Vec<_> = decls
        .iter()
        .filter_map(|decl| match &decl.node {
            DeclKind::Condition(cond) => Some(cond.name.to_string()),
            _ => None,
        })
        .collect();

    for expected in [
        "ScrollAcidWarding",
        "ScrollDemonWarding",
        "ScrollDevilWarding",
        "ScrollElementalWarding",
        "ScrollLycanthropeWarding",
        "ScrollMagicWarding",
        "ScrollPetrifactionWarding",
        "ScrollPolymorphWarding",
        "ScrollPossessionWarding",
        "ScrollUndeadWarding",
    ] {
        assert!(
            conditions.contains(&expected.to_string()),
            "missing condition: {expected}, got {conditions:?}"
        );
    }
}

#[test]
fn osric_scrolls_has_expected_enums() {
    let (program, _) = compile_osric();
    let decls = get_scrolls_decls(&program);
    let enums: Vec<_> = decls
        .iter()
        .filter_map(|decl| match &decl.node {
            DeclKind::Enum(e) => Some(e.name.to_string()),
            _ => None,
        })
        .collect();

    for expected in [
        "WardingType",
        "WardingRestriction",
        "ScrollFailureEffect",
        "ElementalWardType",
        "LycanthropeWardType",
    ] {
        assert!(
            enums.contains(&expected.to_string()),
            "missing enum: {expected}, got {enums:?}"
        );
    }
}

#[test]
fn osric_scrolls_has_expected_actions() {
    let (program, _) = compile_osric();
    let decls = get_scrolls_decls(&program);
    let actions: Vec<_> = decls
        .iter()
        .filter_map(|decl| match &decl.node {
            DeclKind::Action(action) => Some(action.name.to_string()),
            _ => None,
        })
        .collect();

    for expected in [
        "ReadSpellScroll",
        "ReadWardingScroll",
        "ReadElementalWardingScroll",
        "ReadLycanthropeWardingScroll",
    ] {
        assert!(
            actions.contains(&expected.to_string()),
            "missing action: {expected}, got {actions:?}"
        );
    }
}

#[test]
fn osric_scrolls_has_expected_derives() {
    let (program, _) = compile_osric();
    let decls = get_scrolls_decls(&program);
    let derives: Vec<_> = decls
        .iter()
        .filter_map(|decl| match &decl.node {
            DeclKind::Derive(d) => Some(d.name.to_string()),
            _ => None,
        })
        .collect();

    for expected in [
        "scroll_spell_class",
        "can_use_spell_scroll",
        "scroll_failure_chance",
        "scroll_failure_effect",
        "can_use_warding",
        "warding_def",
        "random_elemental_ward",
        "random_lycanthrope_ward",
        "scroll_reader_progression",
    ] {
        assert!(
            derives.contains(&expected.to_string()),
            "missing derive: {expected}, got {derives:?}"
        );
    }
}
