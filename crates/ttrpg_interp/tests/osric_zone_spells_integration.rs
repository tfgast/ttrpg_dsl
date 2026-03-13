//! OSRIC Zone Spells integration tests.
//!
//! Runtime coverage for zone-keyed condition hooks is in
//! `osric/tests/osric_zone_spells.ttrpg-cli`.
//! This Rust file keeps pipeline coverage for the real OSRIC sources.

use ttrpg_ast::ast::{DeclKind, TopLevel};

mod osric_common;
use osric_common::*;

fn compile_all() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

fn get_decls(program: &ttrpg_ast::ast::Program) -> &[ttrpg_ast::Spanned<DeclKind>] {
    program
        .items
        .iter()
        .find_map(|item| match &item.node {
            TopLevel::System(sys) if sys.name == "OSRIC Zone Spells" => Some(sys.decls.as_slice()),
            _ => None,
        })
        .expect("OSRIC Zone Spells system not found")
}

#[test]
fn osric_zone_spells_parses_and_typechecks() {
    let (program, _) = compile_all();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSRIC Zone Spells"));
}

#[test]
fn osric_zone_spells_has_conditions() {
    let (program, _) = compile_all();
    let decls = get_decls(&program);
    let conditions: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Condition(c) => Some(&*c.name),
            _ => None,
        })
        .collect();
    assert!(
        conditions.contains(&"Silenced"),
        "missing Silenced condition"
    );
    assert!(
        conditions.contains(&"ProtectedFromEvil10Zone"),
        "missing ProtectedFromEvil10Zone condition"
    );
    assert!(
        conditions.contains(&"InsideBladeBarrier"),
        "missing InsideBladeBarrier condition"
    );
}

#[test]
fn osric_zone_spells_has_hooks() {
    let (program, _) = compile_all();
    let decls = get_decls(&program);
    let hooks: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Hook(h) => Some(&*h.name),
            _ => None,
        })
        .collect();
    let expected = [
        "SilenceZoneApply",
        "SilenceZoneRemove",
        "ProtFromEvil10ZoneApply",
        "ProtFromEvil10ZoneRemove",
        "WallOfFireCrossed",
        "BladeBarrierCrossed",
        "BladeBarrierZoneApply",
        "BladeBarrierZoneRemove",
        "GlyphOfWardingTriggered",
    ];
    for name in &expected {
        assert!(hooks.contains(name), "missing hook: {name}");
    }
}

#[test]
fn osric_zone_spells_has_resolve_functions() {
    let (program, _) = compile_all();
    let decls = get_decls(&program);
    let functions: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Function(f) => Some(&*f.name),
            _ => None,
        })
        .collect();
    let expected = [
        "resolve_silence_15",
        "resolve_protection_from_evil_10",
        "resolve_wall_of_fire",
        "resolve_blade_barrier",
        "resolve_glyph_of_warding",
    ];
    for name in &expected {
        assert!(functions.contains(name), "missing resolve function: {name}");
    }
}

#[test]
fn osric_zone_spells_has_glyph_event() {
    let (program, _) = compile_all();
    let decls = get_decls(&program);
    let events: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Event(e) => Some(&*e.name),
            _ => None,
        })
        .collect();
    assert!(
        events.contains(&"GlyphDischarged"),
        "missing GlyphDischarged event"
    );
}

#[test]
fn osric_zone_spells_has_glyph_spell_def() {
    let (program, _) = compile_all();
    let decls = get_decls(&program);
    let consts: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Const(c) => Some(&*c.name),
            _ => None,
        })
        .collect();
    assert!(
        consts.contains(&"GLYPH_OF_WARDING_DEF"),
        "missing GLYPH_OF_WARDING_DEF const"
    );
}
