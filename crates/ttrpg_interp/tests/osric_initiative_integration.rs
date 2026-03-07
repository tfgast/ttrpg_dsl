//! OSRIC initiative integration test — AST structure verification.
//!
//! Behavioural tests (surprise, initiative, segment assignment, spell timing,
//! fighter multi-attacks, movement, CastingSpell condition, BeginCasting action,
//! SpellInterruption hook) have been moved to `osric/tests/osric_initiative.ttrpg-cli`.
//! This file retains only tests that inspect AST structure.

use ttrpg_ast::ast::{DeclKind, TopLevel};

mod osric_common;
use osric_common::*;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_initiative() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

/// Extract all DeclKind items from the "OSRIC Initiative" system block.
fn get_initiative_decls(program: &ttrpg_ast::ast::Program) -> &[ttrpg_ast::Spanned<DeclKind>] {
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSRIC Initiative" {
                return &sys.decls;
            }
        }
    }
    panic!("no system block named 'OSRIC Initiative' found");
}

fn get_spells_decls(program: &ttrpg_ast::ast::Program) -> &[ttrpg_ast::Spanned<DeclKind>] {
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSRIC Spells" {
                return &sys.decls;
            }
        }
    }
    panic!("no system block named 'OSRIC Spells' found");
}

// ══════════════════════════════════════════════════════════════
//  PARSE + TYPECHECK
// ══════════════════════════════════════════════════════════════

#[test]
fn osric_initiative_parses_and_typechecks() {
    let (program, _) = compile_osric_initiative();
    let has_system = program
        .items
        .iter()
        .any(|item| matches!(&item.node, TopLevel::System(sys) if sys.name == "OSRIC Initiative"));
    assert!(has_system, "expected system named 'OSRIC Initiative'");
}

// ══════════════════════════════════════════════════════════════
//  STRUCTURE VERIFICATION
// ══════════════════════════════════════════════════════════════

#[test]
fn initiative_has_declared_action_type_enum() {
    let (program, _) = compile_osric_initiative();
    let decls = get_initiative_decls(&program);
    let enums: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Enum(e) => Some((&*e.name, e.variants.len())),
            _ => None,
        })
        .collect();
    assert!(
        enums.contains(&("DeclaredActionType", 13)),
        "expected DeclaredActionType with 13 variants, got: {enums:?}"
    );
}

#[test]
fn initiative_has_structs() {
    let (program, _) = compile_osric_initiative();
    let decls = get_initiative_decls(&program);
    let structs: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Struct(s) => Some((&*s.name, s.fields.len())),
            _ => None,
        })
        .collect();
    assert!(
        structs.contains(&("InitiativeResult", 5)),
        "missing InitiativeResult with 5 fields"
    );
    assert!(
        structs.contains(&("SurpriseResult", 4)),
        "missing SurpriseResult with 4 fields"
    );
    assert!(
        structs.contains(&("SegmentAction", 3)),
        "missing SegmentAction with 3 fields"
    );
}

#[test]
fn initiative_has_derives() {
    let (program, _) = compile_osric_initiative();
    let decls = get_initiative_decls(&program);
    let derives: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Derive(d) => Some(&*d.name),
            _ => None,
        })
        .collect();
    for expected in &[
        "surprise_duration",
        "free_surprise_segments",
        "wrap_segment",
        "action_segment",
        "missile_init_segment",
        "assign_segment",
        "has_fighter_multi_attack",
        "fighter_attacks_this_round",
        "fighter_attack_segments",
        "spell_effect_segment",
        "is_casting_at_segment",
        "spell_completed_at_segment",
        "acts_first_by_speed",
        "melee_order",
        "movement_per_segment",
        "movement_through_segment",
    ] {
        assert!(derives.contains(expected), "missing derive: {expected}");
    }
}

#[test]
fn initiative_has_mechanics() {
    let (program, _) = compile_osric_initiative();
    let decls = get_initiative_decls(&program);
    let mechanics: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Mechanic(m) => Some(&*m.name),
            _ => None,
        })
        .collect();
    assert!(
        mechanics.contains(&"roll_surprise"),
        "missing roll_surprise"
    );
    assert!(
        mechanics.contains(&"roll_initiative"),
        "missing roll_initiative"
    );
}

#[test]
fn initiative_has_events() {
    let (program, _) = compile_osric_initiative();
    // SpellInterrupted moved to OSRIC Spells module
    let decls = get_spells_decls(&program);
    let events: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Event(e) => Some(&*e.name),
            _ => None,
        })
        .collect();
    assert!(
        events.contains(&"SpellInterrupted"),
        "missing SpellInterrupted event"
    );
}

#[test]
fn initiative_has_conditions() {
    let (program, _) = compile_osric_initiative();
    // CastingSpell moved to OSRIC Spells module
    let decls = get_spells_decls(&program);
    let conditions: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Condition(c) => Some(&*c.name),
            _ => None,
        })
        .collect();
    assert!(
        conditions.contains(&"CastingSpell"),
        "missing CastingSpell condition"
    );
}

#[test]
fn initiative_has_hooks() {
    let (program, _) = compile_osric_initiative();
    // SpellInterruption moved to OSRIC Spells module
    let decls = get_spells_decls(&program);
    let hooks: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Hook(h) => Some(&*h.name),
            _ => None,
        })
        .collect();
    assert!(
        hooks.contains(&"SpellInterruption"),
        "missing SpellInterruption hook"
    );
}

#[test]
fn initiative_has_actions() {
    let (program, _) = compile_osric_initiative();
    // BeginCasting moved to OSRIC Spells module
    let decls = get_spells_decls(&program);
    let actions: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Action(a) => Some(&*a.name),
            _ => None,
        })
        .collect();
    assert!(
        actions.contains(&"BeginCasting"),
        "missing BeginCasting action"
    );
}
