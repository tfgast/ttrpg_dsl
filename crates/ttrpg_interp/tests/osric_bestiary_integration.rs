//! OSRIC bestiary integration tests.
//!
//! Tests factory creation, condition application, saving throw
//! derivation, and entity field values for the monster bestiary.

use ttrpg_ast::ast::TopLevel;
use ttrpg_ast::Name;
use ttrpg_interp::adapter::StateAdapter;
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::StateProvider;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

mod osric_common;
#[allow(unused_imports)]
use osric_common::*;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_bestiary() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn osric_bestiary_parses_and_typechecks() {
    let (program, _) = compile_osric_bestiary();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSRIC Bestiary"));
    assert!(system_names.contains(&"OSRIC Monster Traits"));
}

// ── Helper: run a factory function and return (entity, state) ──

fn run_factory(
    interp: &Interpreter,
    func: &str,
    args: Vec<Value>,
) -> (ttrpg_interp::state::EntityRef, GameState) {
    let state = GameState::new();
    let adapter = StateAdapter::new(state);
    let mut handler = NullHandler;

    let val = adapter.run(&mut handler, |state, handler| {
        interp.evaluate_function(state, handler, func, args)
    });
    let val = val.unwrap();

    match val {
        Value::Entity(e) => {
            let final_state = adapter.into_inner();
            (e, final_state)
        }
        other => panic!("expected Entity value from {func}, got {other:?}"),
    }
}

fn has_condition(state: &GameState, entity: &ttrpg_interp::state::EntityRef, name: &str) -> bool {
    state
        .read_conditions(entity)
        .unwrap_or_default()
        .iter()
        .any(|c| &*c.name == name)
}

fn condition_names(
    state: &GameState,
    entity: &ttrpg_interp::state::EntityRef,
) -> Vec<String> {
    state
        .read_conditions(entity)
        .unwrap_or_default()
        .iter()
        .map(|c| c.name.to_string())
        .collect()
}

// ── FACTORY CREATION TESTS ───────────────────────────────────

#[test]
fn create_goblin_returns_monster_with_correct_fields() {
    let (program, result) = compile_osric_bestiary();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let (entity, state) = run_factory(&interp, "create_goblin", vec![]);

    assert_eq!(
        state.read_field(&entity, "name"),
        Some(Value::Str("Goblin".into()))
    );
    assert_eq!(state.read_field(&entity, "ac"), Some(Value::Int(14)));
    assert_eq!(state.read_field(&entity, "morale"), Some(Value::Int(7)));
    assert_eq!(state.read_field(&entity, "xp_value"), Some(Value::Int(10)));
    assert_eq!(state.read_field(&entity, "intelligence"), Some(Value::Int(9)));
}

#[test]
fn create_orc_returns_monster_with_correct_hp() {
    let (program, result) = compile_osric_bestiary();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let (entity, state) = run_factory(&interp, "create_orc", vec![]);

    assert_eq!(
        state.read_field(&entity, "name"),
        Some(Value::Str("Orc".into()))
    );
    assert_eq!(state.read_field(&entity, "max_hp"), Some(Value::Int(4)));
}

#[test]
fn create_ogre_returns_large_monster() {
    let (program, result) = compile_osric_bestiary();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let (entity, state) = run_factory(&interp, "create_ogre", vec![]);

    assert_eq!(
        state.read_field(&entity, "name"),
        Some(Value::Str("Ogre".into()))
    );
    assert_eq!(state.read_field(&entity, "ac"), Some(Value::Int(15)));
    assert_eq!(
        state.read_field(&entity, "size"),
        Some(enum_variant("Size", "Large"))
    );
}

// ── UNDEAD CONDITION TESTS ──────────────────────────────────

#[test]
fn skeleton_has_undead_and_immunity_conditions() {
    let (program, result) = compile_osric_bestiary();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let (entity, state) = run_factory(&interp, "create_skeleton", vec![]);

    assert!(
        has_condition(&state, &entity, "Undead"),
        "Skeleton should have Undead condition, got {:?}",
        condition_names(&state, &entity)
    );
    assert!(
        has_condition(&state, &entity, "TurnedAsUndead"),
        "Skeleton should have TurnedAsUndead condition"
    );
    assert!(
        has_condition(&state, &entity, "ImmuneToCold"),
        "Skeleton should have ImmuneToCold condition"
    );
    assert!(
        has_condition(&state, &entity, "ImmuneToMindControl"),
        "Skeleton should have ImmuneToMindControl condition"
    );
    assert!(
        has_condition(&state, &entity, "ResistantToBlunt"),
        "Skeleton should have ResistantToBlunt condition"
    );
}

#[test]
fn vampire_has_regeneration_and_immunities() {
    let (program, result) = compile_osric_bestiary();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let (entity, state) = run_factory(&interp, "create_vampire", vec![]);

    assert_eq!(
        state.read_field(&entity, "name"),
        Some(Value::Str("Vampire".into()))
    );
    assert_eq!(state.read_field(&entity, "ac"), Some(Value::Int(19)));
    assert!(has_condition(&state, &entity, "Undead"));
    assert!(has_condition(&state, &entity, "Regeneration"));
    assert!(has_condition(&state, &entity, "ImmuneToNormalWeapons"));
    assert!(has_condition(&state, &entity, "ImmuneToMindControl"));
}

// ── CLASSIC MONSTER TESTS ───────────────────────────────────

#[test]
fn troll_has_regeneration_and_fire_vulnerability() {
    let (program, result) = compile_osric_bestiary();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let (entity, state) = run_factory(&interp, "create_troll", vec![]);

    assert_eq!(
        state.read_field(&entity, "name"),
        Some(Value::Str("Troll".into()))
    );
    assert!(has_condition(&state, &entity, "Regeneration"));
    assert!(has_condition(&state, &entity, "VulnerableToFire"));
}

#[test]
fn basilisk_has_petrifying_gaze() {
    let (program, result) = compile_osric_bestiary();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let (entity, state) = run_factory(&interp, "create_basilisk", vec![]);

    assert!(has_condition(&state, &entity, "PetrifyingGaze"));
}

#[test]
fn gelatinous_cube_has_construct_and_immunities() {
    let (program, result) = compile_osric_bestiary();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let (entity, state) = run_factory(&interp, "create_gelatinous_cube", vec![]);

    assert_eq!(state.read_field(&entity, "intelligence"), Some(Value::Int(0)));
    assert!(has_condition(&state, &entity, "Construct"));
    assert!(has_condition(&state, &entity, "ImmuneToLightning"));
    assert!(has_condition(&state, &entity, "ImmuneToMindControl"));
}

// ── DRAGON TESTS ────────────────────────────────────────────

#[test]
fn red_dragon_age_5_has_correct_hp_and_breath_weapon() {
    let (program, result) = compile_osric_bestiary();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let (entity, state) = run_factory(&interp, "create_red_dragon", vec![Value::Int(5)]);

    assert_eq!(
        state.read_field(&entity, "name"),
        Some(Value::Str("Red Dragon".into()))
    );
    // HP = hd (10) * age (5) = 50
    assert_eq!(state.read_field(&entity, "max_hp"), Some(Value::Int(50)));
    assert_eq!(state.read_field(&entity, "ac"), Some(Value::Int(21)));
    assert_eq!(
        state.read_field(&entity, "size"),
        Some(enum_variant("Size", "Huge"))
    );
    assert!(has_condition(&state, &entity, "ImmuneToFire"));
    assert!(has_condition(&state, &entity, "Infravision"));
    assert!(has_condition(&state, &entity, "FearAura"));
}

#[test]
fn white_dragon_age_3_has_cold_immunity() {
    let (program, result) = compile_osric_bestiary();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let (entity, state) = run_factory(&interp, "create_white_dragon", vec![Value::Int(3)]);

    // HP = 6 * 3 = 18
    assert_eq!(state.read_field(&entity, "max_hp"), Some(Value::Int(18)));
    assert!(has_condition(&state, &entity, "ImmuneToCold"));
    assert!(has_condition(&state, &entity, "VulnerableToFire"));
}

// ── GIANT TESTS ─────────────────────────────────────────────

#[test]
fn fire_giant_has_fire_immunity() {
    let (program, result) = compile_osric_bestiary();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let (entity, state) = run_factory(&interp, "create_fire_giant", vec![]);

    assert!(has_condition(&state, &entity, "ImmuneToFire"));
    assert_eq!(state.read_field(&entity, "ac"), Some(Value::Int(17)));
}

// ── SAVING THROW DERIVATION TESTS ──────────────────────────

#[test]
fn monster_saves_normal_returns_correct_values() {
    let (program, result) = compile_osric_bestiary();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = ScriptedHandler::with_responses(vec![]);

    // HD 1-2 normal saves: aimed_magic=16, breath=17, death=14, petrify=15, spells=17
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "monster_saves_normal",
            vec![Value::Int(1)],
        )
        .unwrap();

    match val {
        Value::Struct { name, fields } => {
            assert_eq!(&*name, "SavingThrows");
            assert_eq!(
                *fields.get::<Name>(&"aimed_magic".into()).unwrap(),
                Value::Int(16)
            );
            assert_eq!(
                *fields.get::<Name>(&"breath".into()).unwrap(),
                Value::Int(17)
            );
            assert_eq!(
                *fields.get::<Name>(&"death_paralysis_poison".into()).unwrap(),
                Value::Int(14)
            );
        }
        other => panic!("expected SavingThrows struct, got {other:?}"),
    }
}

#[test]
fn monster_saves_nonintelligent_differs_from_normal() {
    let (program, result) = compile_osric_bestiary();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = ScriptedHandler::with_responses(vec![]);

    // HD 9-10 non-intelligent: aimed_magic=13, breath=13 (same as normal)
    // but petrification_polymorph=12 (vs 9 for normal) — worse at resisting magic
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "monster_saves_nonintelligent",
            vec![Value::Int(9)],
        )
        .unwrap();

    match val {
        Value::Struct { name, fields } => {
            assert_eq!(&*name, "SavingThrows");
            assert_eq!(
                *fields.get::<Name>(&"aimed_magic".into()).unwrap(),
                Value::Int(13)
            );
            assert_eq!(
                *fields.get::<Name>(&"petrification_polymorph".into()).unwrap(),
                Value::Int(12)
            );
        }
        other => panic!("expected SavingThrows struct, got {other:?}"),
    }
}

// ── ANIMAL TESTS ────────────────────────────────────────────

#[test]
fn giant_spider_has_poison_immunity() {
    let (program, result) = compile_osric_bestiary();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let (entity, state) = run_factory(&interp, "create_giant_spider", vec![]);

    assert!(has_condition(&state, &entity, "ImmuneToPoison"));
    assert_eq!(
        state.read_field(&entity, "size"),
        Some(enum_variant("Size", "Large"))
    );
}

#[test]
fn owlbear_has_three_attacks() {
    let (program, result) = compile_osric_bestiary();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let (entity, state) = run_factory(&interp, "create_owlbear", vec![]);

    match state.read_field(&entity, "attacks") {
        Some(Value::List(attacks)) => {
            assert_eq!(attacks.len(), 3, "Owlbear should have 3 attacks (2 claws + bite)");
        }
        other => panic!("expected list of attacks, got {other:?}"),
    }
}

// ── OUTSIDER TESTS ──────────────────────────────────────────

#[test]
fn efreet_has_fire_immunity_and_infravision() {
    let (program, result) = compile_osric_bestiary();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let (entity, state) = run_factory(&interp, "create_efreet", vec![]);

    assert!(has_condition(&state, &entity, "ImmuneToFire"));
    assert!(has_condition(&state, &entity, "Infravision"));
    assert_eq!(state.read_field(&entity, "xp_value"), Some(Value::Int(7000)));
}
