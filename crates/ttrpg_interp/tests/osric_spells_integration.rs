//! OSRIC spell memorisation/casting integration tests.
//!
//! Verifies that osric/osric_spells.ttrpg parses, lowers, and type-checks
//! through the full multi-file pipeline. Exercises AST structure (tables,
//! dispatch derives) and the MemoriseSpell/ForgetSpell/CastSpell action
//! lifecycle.
//!
//! Per-class spell slot progression, WIS bonus, max_spell_level, and
//! has_wis_bonus derives are covered by the CLI runtime script.

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_ast::Name;
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::StateProvider;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

mod osric_common;
use osric_common::*;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_spells() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn osric_spells_parses_and_typechecks() {
    let (program, _) = compile_osric_spells();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSRIC"));
    assert!(system_names.contains(&"OSRIC Classes"));
    assert!(system_names.contains(&"OSRIC Spells"));
}

// ── Table declaration structure ────────────────────────────────

#[test]
fn osric_spells_has_all_tables() {
    let (program, _) = compile_osric_spells();

    let mut table_names = Vec::new();
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSRIC Spells" {
                for decl in &sys.decls {
                    if let DeclKind::Table(t) = &decl.node {
                        table_names.push(t.name.to_string());
                    }
                }
            }
        }
    }

    let expected = [
        "cleric_slots",
        "druid_slots",
        "magic_user_slots",
        "illusionist_slots",
        "wis_bonus_slots",
    ];
    for name in &expected {
        assert!(
            table_names.iter().any(|n| n == name),
            "missing table: {name}, got: {table_names:?}"
        );
    }
    assert_eq!(
        table_names.len(),
        expected.len(),
        "expected {} tables, got: {table_names:?}",
        expected.len()
    );
}

#[test]
fn osric_spells_has_dispatch_derives() {
    let (program, _) = compile_osric_spells();

    let mut derive_names = Vec::new();
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSRIC Spells" {
                for decl in &sys.decls {
                    if let DeclKind::Derive(f) = &decl.node {
                        derive_names.push(f.name.to_string());
                    }
                }
            }
        }
    }

    let expected = [
        "spell_slots_for",
        "max_spell_level",
        "has_wis_bonus",
        "total_spell_slots",
    ];
    for name in &expected {
        assert!(
            derive_names.iter().any(|n| n == name),
            "missing derive: {name}, got: {derive_names:?}"
        );
    }
}

// ═══════════════════════════════════════════════════════════════
//  LIST BUILTIN METHODS: contains, remove_first
//  Tested indirectly through MemoriseSpell/ForgetSpell/CastSpell
//  actions which use .contains() in requires guards and
//  .remove_first() in resolve blocks.
// ═══════════════════════════════════════════════════════════════

// ═══════════════════════════════════════════════════════════════
//  SPELL MEMORISATION / CASTING ACTIONS
// ═══════════════════════════════════════════════════════════════

/// Create a SpellId enum variant value.
fn spell_id(variant: &str) -> Value {
    enum_variant("SpellId", variant)
}

/// Read the Spellcasting group fields from a caster.
/// Returns (memorised SpellId variant names, slots_used[1], slots_used[2]).
fn read_spellcasting(
    state: &GameState,
    entity: &ttrpg_interp::state::EntityRef,
) -> (Vec<String>, i64, i64) {
    let sc = state
        .read_field(entity, "Spellcasting")
        .expect("entity should have Spellcasting group");
    let fields = match &sc {
        Value::Struct { fields, .. } => fields,
        other => panic!("expected Struct for Spellcasting, got {other:?}"),
    };

    // Extract memorised_spells (list of MemorizedSpell structs)
    let spells: Vec<String> = match fields.get::<Name>(&"memorised_spells".into()) {
        Some(Value::List(items)) => items
            .iter()
            .map(|v| match v {
                Value::Struct { fields, .. } => match fields.get::<Name>(&"id".into()) {
                    Some(Value::EnumVariant { variant, .. }) => variant.to_string(),
                    other => panic!("expected SpellId enum in MemorizedSpell.id, got {other:?}"),
                },
                other => {
                    panic!("expected MemorizedSpell struct in memorised_spells, got {other:?}")
                }
            })
            .collect(),
        other => panic!("expected list for memorised_spells, got {other:?}"),
    };

    // Extract slots_used list (index 0 = spell level 1, index 1 = spell level 2)
    let slots_used = match fields.get::<Name>(&"slots_used".into()) {
        Some(Value::List(items)) => items,
        other => panic!("expected list for slots_used, got {other:?}"),
    };

    let used_1 = match slots_used.first() {
        Some(Value::Int(n)) => *n,
        other => panic!("expected int for slots_used[0], got {other:?}"),
    };
    let used_2 = match slots_used.get(1) {
        Some(Value::Int(n)) => *n,
        other => panic!("expected int for slots_used[1], got {other:?}"),
    };

    (spells, used_1, used_2)
}

// ── MemoriseSpell ─────────────────────────────────────────────

#[test]
fn memorise_spell_fills_slot_and_adds_to_list() {
    let ctx = SpellTestContext::cleric("Alaric", 3, &[(1, 2), (2, 1)]);
    let interp = Interpreter::new(&ctx.program, &ctx.check_result.env).unwrap();
    let mut handler = ScriptedHandler::with_responses(vec![]);

    let state = run_action(
        &interp,
        ctx.state,
        &mut handler,
        "MemoriseSpell",
        ctx.caster,
        vec![spell_id("CureLightWounds"), Value::Int(1)],
    );

    let (spells, used_1, _used_2) = read_spellcasting(&state, &ctx.caster);
    assert_eq!(spells, vec!["CureLightWounds"]);
    assert_eq!(used_1, 1);
}

#[test]
fn memorise_spell_fails_when_slots_full() {
    let ctx = SpellTestContext::cleric("Alaric", 3, &[(1, 2), (2, 1)]);
    let interp = Interpreter::new(&ctx.program, &ctx.check_result.env).unwrap();

    // Fill both first-level slots
    let mut handler = ScriptedHandler::with_responses(vec![]);
    let state = run_action(
        &interp,
        ctx.state,
        &mut handler,
        "MemoriseSpell",
        ctx.caster,
        vec![spell_id("CureLightWounds"), Value::Int(1)],
    );
    let mut handler = ScriptedHandler::with_responses(vec![]);
    let state = run_action(
        &interp,
        state,
        &mut handler,
        "MemoriseSpell",
        ctx.caster,
        vec![spell_id("Bless"), Value::Int(1)],
    );

    // Third memorise should fail (only 2 first-level slots)
    let mut handler = ScriptedHandler::with_responses(vec![]);
    let state = run_action(
        &interp,
        state,
        &mut handler,
        "MemoriseSpell",
        ctx.caster,
        vec![spell_id("CauseLightWounds"), Value::Int(1)],
    );

    // Verify requires guard rejected: state unchanged (still 2 spells, slots_used still 2)
    let (spells, used_1, _) = read_spellcasting(&state, &ctx.caster);
    assert_eq!(spells.len(), 2, "no third spell should be memorised");
    assert_eq!(used_1, 2, "slots_used should still be 2");
}

#[test]
fn memorise_same_spell_multiple_times() {
    let ctx = SpellTestContext::cleric("Alaric", 3, &[(1, 2), (2, 1)]);
    let interp = Interpreter::new(&ctx.program, &ctx.check_result.env).unwrap();

    let mut handler = ScriptedHandler::with_responses(vec![]);
    let state = run_action(
        &interp,
        ctx.state,
        &mut handler,
        "MemoriseSpell",
        ctx.caster,
        vec![spell_id("CureLightWounds"), Value::Int(1)],
    );
    let mut handler = ScriptedHandler::with_responses(vec![]);
    let state = run_action(
        &interp,
        state,
        &mut handler,
        "MemoriseSpell",
        ctx.caster,
        vec![spell_id("CureLightWounds"), Value::Int(1)],
    );

    let (spells, used_1, _) = read_spellcasting(&state, &ctx.caster);
    assert_eq!(spells, vec!["CureLightWounds", "CureLightWounds"]);
    assert_eq!(used_1, 2);
}

// ── ForgetSpell ───────────────────────────────────────────────

#[test]
fn forget_spell_removes_spell_and_frees_slot() {
    let ctx = SpellTestContext::cleric("Alaric", 3, &[(1, 2), (2, 1)]);
    let interp = Interpreter::new(&ctx.program, &ctx.check_result.env).unwrap();

    // Memorise then forget
    let mut handler = ScriptedHandler::with_responses(vec![]);
    let state = run_action(
        &interp,
        ctx.state,
        &mut handler,
        "MemoriseSpell",
        ctx.caster,
        vec![spell_id("CureLightWounds"), Value::Int(1)],
    );
    let mut handler = ScriptedHandler::with_responses(vec![]);
    let state = run_action(
        &interp,
        state,
        &mut handler,
        "ForgetSpell",
        ctx.caster,
        vec![spell_id("CureLightWounds"), Value::Int(1)],
    );

    let (spells, used_1, _) = read_spellcasting(&state, &ctx.caster);
    assert!(spells.is_empty(), "spell list should be empty after forget");
    assert_eq!(used_1, 0, "slots_used should be back to 0");
}

#[test]
fn forget_spell_fails_when_not_memorised() {
    let ctx = SpellTestContext::cleric("Alaric", 3, &[(1, 2), (2, 1)]);
    let interp = Interpreter::new(&ctx.program, &ctx.check_result.env).unwrap();

    let mut handler = ScriptedHandler::with_responses(vec![]);
    let state = run_action(
        &interp,
        ctx.state,
        &mut handler,
        "ForgetSpell",
        ctx.caster,
        vec![spell_id("CureLightWounds"), Value::Int(1)],
    );

    // Verify requires guard rejected: state unchanged (empty list, slots_used still 0)
    let (spells, used_1, _) = read_spellcasting(&state, &ctx.caster);
    assert!(spells.is_empty(), "no spells should be in list");
    assert_eq!(used_1, 0, "slots_used should still be 0");
}

#[test]
fn forget_removes_only_first_duplicate() {
    let ctx = SpellTestContext::cleric("Alaric", 3, &[(1, 2), (2, 1)]);
    let interp = Interpreter::new(&ctx.program, &ctx.check_result.env).unwrap();

    // Memorise CLW twice
    let mut handler = ScriptedHandler::with_responses(vec![]);
    let state = run_action(
        &interp,
        ctx.state,
        &mut handler,
        "MemoriseSpell",
        ctx.caster,
        vec![spell_id("CureLightWounds"), Value::Int(1)],
    );
    let mut handler = ScriptedHandler::with_responses(vec![]);
    let state = run_action(
        &interp,
        state,
        &mut handler,
        "MemoriseSpell",
        ctx.caster,
        vec![spell_id("CureLightWounds"), Value::Int(1)],
    );

    // Forget one
    let mut handler = ScriptedHandler::with_responses(vec![]);
    let state = run_action(
        &interp,
        state,
        &mut handler,
        "ForgetSpell",
        ctx.caster,
        vec![spell_id("CureLightWounds"), Value::Int(1)],
    );

    let (spells, used_1, _) = read_spellcasting(&state, &ctx.caster);
    assert_eq!(spells, vec!["CureLightWounds"], "one copy should remain");
    assert_eq!(used_1, 1);
}

// ── CastSpell ─────────────────────────────────────────────────

#[test]
fn cast_spell_expends_slot_and_begins_casting() {
    let ctx = SpellTestContext::cleric("Alaric", 3, &[(1, 2), (2, 1)]);
    let interp = Interpreter::new(&ctx.program, &ctx.check_result.env).unwrap();

    // Memorise a spell first
    let mut handler = ScriptedHandler::with_responses(vec![]);
    let state = run_action(
        &interp,
        ctx.state,
        &mut handler,
        "MemoriseSpell",
        ctx.caster,
        vec![spell_id("CureLightWounds"), Value::Int(1)],
    );

    // Cast it (casting_time = 5 segments)
    let mut handler = ScriptedHandler::with_responses(vec![]);
    let state = run_action(
        &interp,
        state,
        &mut handler,
        "CastSpell",
        ctx.caster,
        vec![spell_id("CureLightWounds"), Value::Int(1), Value::Int(5)],
    );

    // Spell should be removed from memorised list
    let (spells, used_1, _) = read_spellcasting(&state, &ctx.caster);
    assert!(spells.is_empty(), "spell should be expended after casting");
    assert_eq!(used_1, 0, "slots_used should be decremented");

    // CastingSpell condition should be applied (via BeginCasting)
    let conditions = state.read_conditions(&ctx.caster).unwrap_or_default();
    assert!(
        conditions.iter().any(|c| &*c.name == "CastingSpell"),
        "expected CastingSpell condition on caster, got: {:?}",
        conditions.iter().map(|c| &c.name).collect::<Vec<_>>()
    );
}

#[test]
fn cast_spell_fails_when_not_memorised() {
    let ctx = SpellTestContext::cleric("Alaric", 3, &[(1, 2), (2, 1)]);
    let interp = Interpreter::new(&ctx.program, &ctx.check_result.env).unwrap();

    let mut handler = ScriptedHandler::with_responses(vec![]);
    let state = run_action(
        &interp,
        ctx.state,
        &mut handler,
        "CastSpell",
        ctx.caster,
        vec![spell_id("CureLightWounds"), Value::Int(1), Value::Int(5)],
    );

    // Verify requires guard rejected: state unchanged
    let (spells, used_1, _) = read_spellcasting(&state, &ctx.caster);
    assert!(spells.is_empty(), "no spells should be in list");
    assert_eq!(used_1, 0, "slots_used should still be 0");

    // No CastingSpell condition should be applied
    let conditions = state.read_conditions(&ctx.caster).unwrap_or_default();
    assert!(
        !conditions.iter().any(|c| &*c.name == "CastingSpell"),
        "CastingSpell should not be applied when requires fails"
    );
}
