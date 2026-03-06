//! OSRIC magic-user spell effects integration tests.
//!
//! Tests Magic Missile, Fireball, Sleep resolve functions and SpellDef derives.

use ttrpg_interp::effect::Response;
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::{EntityRef, StateProvider};
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

mod osric_common;
use osric_common::*;

// ── Helpers ─────────────────────────────────────────────────

fn compile_all() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

fn read_monster_hp(state: &GameState, entity: &EntityRef) -> i64 {
    match state
        .read_field(entity, "hp")
        .expect("monster should have hp")
    {
        Value::Int(n) => n,
        other => panic!("expected int for monster hp, got {other:?}"),
    }
}

/// Scripted 1d4 roll returning the given value.
fn roll_1d4(val: i64) -> Response {
    scripted_roll(1, 4, 0, vec![val], vec![val], val, val)
}

// ── Parse + typecheck ──────────────────────────────────────

#[test]
fn osric_mu_spells_parses_and_typechecks() {
    let (program, _) = compile_all();
    let system_names: Vec<_> = program
        .items
        .iter()
        .filter_map(|item| match &item.node {
            ttrpg_ast::ast::TopLevel::System(sys) => Some(sys.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(system_names.contains(&"OSRIC MU Spells"));
}

// ── magic_missile_count derive ─────────────────────────────

#[test]
fn magic_missile_count_scales_correctly() {
    let (program, result) = compile_all();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let cases = [
        (1, 1),
        (2, 1),
        (3, 2),
        (4, 2),
        (5, 3),
        (7, 4),
        (9, 5),
        (11, 6),
    ];

    for (level, expected) in &cases {
        let val = interp
            .evaluate_derive(
                &state,
                &mut handler,
                "magic_missile_count",
                vec![Value::Int(*level)],
            )
            .unwrap();
        assert_eq!(
            expect_int(val, "magic_missile_count"),
            *expected,
            "magic_missile_count({level})"
        );
    }
}

// ── Magic Missile resolve ──────────────────────────────────

#[test]
fn magic_missile_deals_damage_single_target() {
    let mut ctx = SpellTestContext::magic_user("Merlin", 1, &[(1, 1)]);
    let target = ctx.add_target("Orc", "Fighter", 1, 8, 14);
    let interp = Interpreter::new(&ctx.program, &ctx.check_result.env).unwrap();

    // Level 1 MU = 1 missile. Roll 3 on 1d4, +1 = 4 damage.
    let state = run_function_with_rolls(
        &interp,
        ctx.state,
        vec![roll_1d4(3)],
        "resolve_magic_missile",
        vec![
            Value::Entity(ctx.caster),
            Value::List(vec![Value::Entity(target)]),
        ],
    );

    assert_eq!(
        read_hp(&state, &target),
        4,
        "target should take 4 damage (8 - 4 = 4)"
    );
}

#[test]
fn magic_missile_multiple_missiles_same_target() {
    let mut ctx = SpellTestContext::magic_user("Merlin", 5, &[(1, 4), (2, 2), (3, 1)]);
    let target = ctx.add_target("Orc", "Fighter", 1, 30, 14);
    let interp = Interpreter::new(&ctx.program, &ctx.check_result.env).unwrap();

    // Level 5 MU = 3 missiles. Roll 2, 4, 1 on 1d4 => damage 3, 5, 2 = 10 total.
    let state = run_function_with_rolls(
        &interp,
        ctx.state,
        vec![roll_1d4(2), roll_1d4(4), roll_1d4(1)],
        "resolve_magic_missile",
        vec![
            Value::Entity(ctx.caster),
            Value::List(vec![
                Value::Entity(target),
                Value::Entity(target),
                Value::Entity(target),
            ]),
        ],
    );

    assert_eq!(
        read_hp(&state, &target),
        20,
        "target should take 10 total damage (30 - 10 = 20)"
    );
}

#[test]
fn magic_missile_split_across_targets() {
    let mut ctx = SpellTestContext::magic_user("Merlin", 3, &[(1, 2), (2, 1)]);
    let target_a = ctx.add_target("Orc A", "Fighter", 1, 10, 14);
    let target_b = ctx.add_target("Orc B", "Fighter", 1, 10, 14);
    let interp = Interpreter::new(&ctx.program, &ctx.check_result.env).unwrap();

    // Level 3 MU = 2 missiles. Roll 3, 2 on 1d4 => damage 4, 3. One per target.
    let state = run_function_with_rolls(
        &interp,
        ctx.state,
        vec![roll_1d4(3), roll_1d4(2)],
        "resolve_magic_missile",
        vec![
            Value::Entity(ctx.caster),
            Value::List(vec![Value::Entity(target_a), Value::Entity(target_b)]),
        ],
    );

    assert_eq!(
        read_hp(&state, &target_a),
        6,
        "target A should take 4 damage (10 - 4 = 6)"
    );
    assert_eq!(
        read_hp(&state, &target_b),
        7,
        "target B should take 3 damage (10 - 3 = 7)"
    );
}

// ── Fireball resolve ─────────────────────────────────────

#[test]
fn fireball_full_damage_on_failed_save() {
    let mut ctx = SpellTestContext::magic_user("Merlin", 5, &[(1, 4), (2, 2), (3, 1)]);
    let target = ctx.add_target("Orc", "Fighter", 1, 40, 14);
    let interp = Interpreter::new(&ctx.program, &ctx.check_result.env).unwrap();

    // Level 5 MU: 5d6 damage. Script total=18. Save roll=1 (always fails).
    let damage_roll = scripted_roll(5, 6, 0, vec![3, 4, 2, 5, 4], vec![3, 4, 2, 5, 4], 18, 18);
    let state = run_function_with_rolls(
        &interp,
        ctx.state,
        vec![damage_roll, roll_save(1)],
        "resolve_fireball",
        vec![
            Value::Entity(ctx.caster),
            Value::List(vec![Value::Entity(target)]),
        ],
    );

    assert_eq!(
        read_hp(&state, &target),
        22,
        "target should take 18 full damage (40 - 18 = 22)"
    );
}

#[test]
fn fireball_half_damage_on_successful_save() {
    let mut ctx = SpellTestContext::magic_user("Merlin", 5, &[(1, 4), (2, 2), (3, 1)]);
    let target = ctx.add_target("Orc", "Fighter", 1, 40, 14);
    let interp = Interpreter::new(&ctx.program, &ctx.check_result.env).unwrap();

    // Level 5 MU: 5d6 damage. Script total=18. Save roll=20 (always succeeds).
    // Half of 18 = floor(9) = 9 damage.
    let damage_roll = scripted_roll(5, 6, 0, vec![3, 4, 2, 5, 4], vec![3, 4, 2, 5, 4], 18, 18);
    let state = run_function_with_rolls(
        &interp,
        ctx.state,
        vec![damage_roll, roll_save(20)],
        "resolve_fireball",
        vec![
            Value::Entity(ctx.caster),
            Value::List(vec![Value::Entity(target)]),
        ],
    );

    assert_eq!(
        read_hp(&state, &target),
        31,
        "target should take 9 half damage (40 - 9 = 31)"
    );
}

#[test]
fn fireball_multiple_targets_mixed_saves() {
    let mut ctx = SpellTestContext::magic_user("Merlin", 3, &[(1, 2), (2, 1)]);
    let target_a = ctx.add_target("Orc A", "Fighter", 1, 20, 14);
    let target_b = ctx.add_target("Orc B", "Fighter", 1, 20, 14);
    let interp = Interpreter::new(&ctx.program, &ctx.check_result.env).unwrap();

    // Level 3 MU: 3d6 damage = 10. Target A fails save (roll 1), Target B saves (roll 20).
    let damage_roll = scripted_roll(3, 6, 0, vec![3, 4, 3], vec![3, 4, 3], 10, 10);
    let state = run_function_with_rolls(
        &interp,
        ctx.state,
        vec![damage_roll, roll_save(1), roll_save(20)],
        "resolve_fireball",
        vec![
            Value::Entity(ctx.caster),
            Value::List(vec![Value::Entity(target_a), Value::Entity(target_b)]),
        ],
    );

    assert_eq!(
        read_hp(&state, &target_a),
        10,
        "target A should take full 10 damage (20 - 10 = 10)"
    );
    assert_eq!(
        read_hp(&state, &target_b),
        15,
        "target B should take half 5 damage (20 - 5 = 15)"
    );
}

// ── SpellDef ───────────────────────────────────────────────

#[test]
fn fireball_def_has_correct_fields() {
    let (program, result) = compile_all();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "fireball_def", vec![])
        .unwrap();

    let (level, school) = match &val {
        Value::Struct { fields, .. } => (
            expect_int(
                fields
                    .get::<ttrpg_ast::Name>(&"level".into())
                    .cloned()
                    .unwrap(),
                "level",
            ),
            fields
                .get::<ttrpg_ast::Name>(&"school".into())
                .cloned()
                .unwrap(),
        ),
        other => panic!("expected Struct for SpellDef, got {other:?}"),
    };
    assert_eq!(level, 3);
    match school {
        Value::EnumVariant { variant, .. } => assert_eq!(variant.as_str(), "Evocation"),
        other => panic!("expected Evocation variant, got {other:?}"),
    }
}

#[test]
fn magic_missile_def_has_correct_fields() {
    let (program, result) = compile_all();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "magic_missile_def", vec![])
        .unwrap();

    let (level, reversible) = match &val {
        Value::Struct { fields, .. } => (
            expect_int(
                fields
                    .get::<ttrpg_ast::Name>(&"level".into())
                    .cloned()
                    .unwrap(),
                "level",
            ),
            expect_bool(
                fields
                    .get::<ttrpg_ast::Name>(&"reversible".into())
                    .cloned()
                    .unwrap(),
                "reversible",
            ),
        ),
        other => panic!("expected Struct for SpellDef, got {other:?}"),
    };
    assert_eq!(level, 1);
    assert!(!reversible);
}

// ── Sleep ────────────────────────────────────────────────────

fn has_condition(state: &GameState, entity: &ttrpg_interp::state::EntityRef, name: &str) -> bool {
    state
        .read_conditions(entity)
        .unwrap_or_default()
        .iter()
        .any(|c| c.name.as_str() == name)
}

/// Scripted roll for NdM dice (e.g. 4d4, 2d4).
fn roll_nd(count: u32, sides: u32, values: Vec<i64>) -> Response {
    let total: i64 = values.iter().sum();
    scripted_roll(count, sides, 0, values.clone(), values, total, total)
}

#[test]
fn sleep_def_has_correct_fields() {
    let (program, result) = compile_all();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "sleep_def", vec![])
        .unwrap();

    let (level, school) = match &val {
        Value::Struct { fields, .. } => (
            expect_int(
                fields
                    .get::<ttrpg_ast::Name>(&"level".into())
                    .cloned()
                    .unwrap(),
                "level",
            ),
            fields
                .get::<ttrpg_ast::Name>(&"school".into())
                .cloned()
                .unwrap(),
        ),
        other => panic!("expected Struct for SpellDef, got {other:?}"),
    };
    assert_eq!(level, 1);
    match school {
        Value::EnumVariant { variant, .. } => assert_eq!(variant.as_str(), "Enchantment"),
        other => panic!("expected Enchantment variant, got {other:?}"),
    }
}

#[test]
fn sleep_hd_category_classification() {
    let (program, result) = compile_all();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    use ttrpg_interp::value::DiceExpr;

    // (dice_count, dice_sides, modifier) -> expected_category
    let cases = [
        ((0, 4, 0), 0),  // <1 HD (e.g. kobold 1d4 mapped as 0d4)
        ((1, 8, -1), 0), // 1-1 HD
        ((1, 8, 0), 0),  // 1 HD (orc)
        ((1, 8, 1), 1),  // 1+1 HD (hobgoblin)
        ((2, 8, 0), 1),  // 2 HD (gnoll)
        ((2, 8, 1), 2),  // 2+1 HD
        ((3, 8, 0), 2),  // 3 HD
        ((3, 8, 1), 3),  // 3+1 HD
        ((4, 8, 0), 3),  // 4 HD
        ((4, 8, 1), 4),  // 4+1 HD
        ((4, 8, 4), 4),  // 4+4 HD
        ((5, 8, 0), 5),  // 5 HD (immune)
        ((6, 8, 6), 5),  // 6+6 HD troll (immune)
    ];

    for ((count, sides, modifier), expected) in &cases {
        let hd = DiceExpr::single(*count as u32, *sides as u32, None, *modifier);
        let val = interp
            .evaluate_derive(
                &state,
                &mut handler,
                "sleep_hd_category",
                vec![Value::DiceExpr(hd)],
            )
            .unwrap();
        assert_eq!(
            expect_int(val, "sleep_hd_category"),
            *expected,
            "sleep_hd_category({count}d{sides}{modifier:+}) should be {expected}"
        );
    }
}

#[test]
fn sleep_affects_weakest_first_single_category() {
    let mut ctx = SpellTestContext::magic_user("Merlin", 3, &[(1, 2), (2, 1)]);

    // 5 orcs (1 HD each) — all in category 0
    let orcs: Vec<_> = (0..5)
        .map(|i| ctx.add_monster(&format!("Orc {i}"), (1, 8, 0), 4, 14))
        .collect();
    let interp = Interpreter::new(&ctx.program, &ctx.check_result.env).unwrap();

    // Roll 4d4 for category 0 = 3 (put 3 orcs to sleep out of 5)
    let state = run_function_with_rolls(
        &interp,
        ctx.state,
        vec![roll_nd(4, 4, vec![1, 1, 0, 1])],
        "resolve_sleep",
        vec![
            Value::Entity(ctx.caster),
            Value::List(orcs.iter().map(|e| Value::Entity(*e)).collect()),
        ],
    );

    // First 3 should be sleeping, last 2 should not.
    for (i, orc) in orcs.iter().enumerate() {
        let sleeping = has_condition(&state, orc, "Sleeping");
        if i < 3 {
            assert!(sleeping, "Orc {i} should be Sleeping");
        } else {
            assert!(!sleeping, "Orc {i} should NOT be Sleeping");
        }
    }
}

#[test]
fn sleep_multiple_hd_categories() {
    let mut ctx = SpellTestContext::magic_user("Merlin", 5, &[(1, 4), (2, 2), (3, 1)]);

    // Category 0 (<=1 HD): 3 orcs
    let orc0 = ctx.add_monster("Orc 0", (1, 8, 0), 4, 14);
    let orc1 = ctx.add_monster("Orc 1", (1, 8, 0), 4, 14);
    let orc2 = ctx.add_monster("Orc 2", (1, 8, 0), 4, 14);

    // Category 1 (1+ to 2 HD): 2 hobgoblins (1+1 HD)
    let hob0 = ctx.add_monster("Hobgoblin 0", (1, 8, 1), 6, 15);
    let hob1 = ctx.add_monster("Hobgoblin 1", (1, 8, 1), 6, 15);

    // Category 5 (immune): 1 troll (6+6 HD)
    let troll = ctx.add_monster("Troll", (6, 8, 6), 36, 16);

    let targets = [orc0, orc1, orc2, hob0, hob1, troll];
    let interp = Interpreter::new(&ctx.program, &ctx.check_result.env).unwrap();

    // Rolls: 4d4 for cat 0 = 10 (all 3 orcs affected),
    //        2d4 for cat 1 = 3 (both hobgoblins affected)
    let state = run_function_with_rolls(
        &interp,
        ctx.state,
        vec![
            roll_nd(4, 4, vec![3, 3, 2, 2]), // cat 0: 10 affected
            roll_nd(2, 4, vec![2, 1]),       // cat 1: 3 affected
        ],
        "resolve_sleep",
        vec![
            Value::Entity(ctx.caster),
            Value::List(targets.iter().map(|e| Value::Entity(*e)).collect()),
        ],
    );

    assert!(
        has_condition(&state, &orc0, "Sleeping"),
        "orc 0 should sleep"
    );
    assert!(
        has_condition(&state, &orc1, "Sleeping"),
        "orc 1 should sleep"
    );
    assert!(
        has_condition(&state, &orc2, "Sleeping"),
        "orc 2 should sleep"
    );
    assert!(
        has_condition(&state, &hob0, "Sleeping"),
        "hobgoblin 0 should sleep"
    );
    assert!(
        has_condition(&state, &hob1, "Sleeping"),
        "hobgoblin 1 should sleep"
    );
    assert!(
        !has_condition(&state, &troll, "Sleeping"),
        "troll should be immune"
    );
}

#[test]
fn sleep_category_4_zero_or_one() {
    let mut ctx = SpellTestContext::magic_user("Merlin", 1, &[(1, 1)]);
    // Category 4: ogre (4+1 HD)
    let ogre = ctx.add_monster("Ogre", (4, 8, 1), 20, 15);
    let interp = Interpreter::new(&ctx.program, &ctx.check_result.env).unwrap();

    // d2 roll = 1 => 1-1 = 0 affected
    let state = run_function_with_rolls(
        &interp,
        ctx.state,
        vec![scripted_roll(1, 2, 0, vec![1], vec![1], 1, 1)],
        "resolve_sleep",
        vec![
            Value::Entity(ctx.caster),
            Value::List(vec![Value::Entity(ogre)]),
        ],
    );

    assert!(
        !has_condition(&state, &ogre, "Sleeping"),
        "ogre should not sleep (d2=1, 1-1=0)"
    );
}

#[test]
fn sleep_category_4_affects_one() {
    let mut ctx = SpellTestContext::magic_user("Merlin", 2, &[(1, 2)]);
    // Category 4: ogre (4+1 HD)
    let ogre = ctx.add_monster("Ogre", (4, 8, 1), 20, 15);
    let interp = Interpreter::new(&ctx.program, &ctx.check_result.env).unwrap();

    // d2 roll = 2 => 2-1 = 1 affected
    let state = run_function_with_rolls(
        &interp,
        ctx.state,
        vec![scripted_roll(1, 2, 0, vec![2], vec![2], 2, 2)],
        "resolve_sleep",
        vec![
            Value::Entity(ctx.caster),
            Value::List(vec![Value::Entity(ogre)]),
        ],
    );

    assert!(
        has_condition(&state, &ogre, "Sleeping"),
        "ogre should sleep (d2=2, 2-1=1)"
    );
}

#[test]
fn sleep_roll_exceeds_available_targets() {
    let mut ctx = SpellTestContext::magic_user("Merlin", 1, &[(1, 1)]);

    // Only 2 orcs, but 4d4 roll = 12 (more than available)
    let orc0 = ctx.add_monster("Orc 0", (1, 8, 0), 4, 14);
    let orc1 = ctx.add_monster("Orc 1", (1, 8, 0), 4, 14);
    let interp = Interpreter::new(&ctx.program, &ctx.check_result.env).unwrap();

    let state = run_function_with_rolls(
        &interp,
        ctx.state,
        vec![roll_nd(4, 4, vec![3, 3, 3, 3])],
        "resolve_sleep",
        vec![
            Value::Entity(ctx.caster),
            Value::List(vec![Value::Entity(orc0), Value::Entity(orc1)]),
        ],
    );

    assert!(
        has_condition(&state, &orc0, "Sleeping"),
        "orc 0 should sleep"
    );
    assert!(
        has_condition(&state, &orc1, "Sleeping"),
        "orc 1 should sleep"
    );
}

// ── Monster-targeted spells ──────────────────────────────────

#[test]
fn magic_missile_damages_monster() {
    let mut ctx = SpellTestContext::magic_user("Merlin", 1, &[(1, 1)]);
    let orc = ctx.add_monster("Orc", (1, 8, 0), 8, 14);
    let interp = Interpreter::new(&ctx.program, &ctx.check_result.env).unwrap();

    // Level 1 MU = 1 missile. Roll 3 on 1d4, +1 = 4 damage.
    let state = run_function_with_rolls(
        &interp,
        ctx.state,
        vec![roll_1d4(3)],
        "resolve_magic_missile",
        vec![
            Value::Entity(ctx.caster),
            Value::List(vec![Value::Entity(orc)]),
        ],
    );

    assert_eq!(
        read_monster_hp(&state, &orc),
        4,
        "monster should take 4 damage (8 - 4 = 4)"
    );
}

#[test]
fn magic_missile_kills_monster() {
    let mut ctx = SpellTestContext::magic_user("Merlin", 3, &[(1, 2), (2, 1)]);
    // Monster with only 3 HP
    let goblin = ctx.add_monster("Goblin", (1, 8, -1), 3, 14);
    let interp = Interpreter::new(&ctx.program, &ctx.check_result.env).unwrap();

    // Level 3 MU = 2 missiles. Roll 4, 2 on 1d4 => damage 5, 3 = 8 total.
    let state = run_function_with_rolls(
        &interp,
        ctx.state,
        vec![roll_1d4(4), roll_1d4(2)],
        "resolve_magic_missile",
        vec![
            Value::Entity(ctx.caster),
            Value::List(vec![Value::Entity(goblin), Value::Entity(goblin)]),
        ],
    );

    assert!(
        read_monster_hp(&state, &goblin) <= 0,
        "goblin should be dead"
    );
    assert!(
        has_condition(&state, &goblin, "Dead"),
        "goblin should have Dead condition"
    );
}

#[test]
fn fireball_damages_monsters_with_saves() {
    let mut ctx = SpellTestContext::magic_user("Merlin", 5, &[(1, 4), (2, 2), (3, 1)]);
    // Two orcs with 20 HP each
    let orc_a = ctx.add_monster("Orc A", (1, 8, 0), 20, 14);
    let orc_b = ctx.add_monster("Orc B", (1, 8, 0), 20, 14);
    let interp = Interpreter::new(&ctx.program, &ctx.check_result.env).unwrap();

    // Level 5 MU: 5d6 = 18 damage. Orc A fails save (roll 1), Orc B saves (roll 20).
    let damage_roll = scripted_roll(5, 6, 0, vec![3, 4, 2, 5, 4], vec![3, 4, 2, 5, 4], 18, 18);
    let state = run_function_with_rolls(
        &interp,
        ctx.state,
        vec![damage_roll, roll_save(1), roll_save(20)],
        "resolve_fireball_monsters",
        vec![
            Value::Entity(ctx.caster),
            Value::List(vec![Value::Entity(orc_a), Value::Entity(orc_b)]),
        ],
    );

    assert_eq!(
        read_monster_hp(&state, &orc_a),
        2,
        "orc A should take full 18 damage (20 - 18 = 2)"
    );
    assert_eq!(
        read_monster_hp(&state, &orc_b),
        11,
        "orc B should take half 9 damage (20 - 9 = 11)"
    );
}

#[test]
fn resolve_spell_monsters_dispatches_magic_missile() {
    let mut ctx = SpellTestContext::magic_user("Merlin", 1, &[(1, 1)]);
    let orc = ctx.add_monster("Orc", (1, 8, 0), 10, 14);
    let interp = Interpreter::new(&ctx.program, &ctx.check_result.env).unwrap();

    // Dispatch via resolve_spell_monsters
    let state = run_function_with_rolls(
        &interp,
        ctx.state,
        vec![roll_1d4(2)],
        "resolve_spell_monsters",
        vec![
            enum_variant("SpellId", "MagicMissile"),
            Value::Entity(ctx.caster),
            Value::List(vec![Value::Entity(orc)]),
        ],
    );

    assert_eq!(
        read_monster_hp(&state, &orc),
        7,
        "monster should take 3 damage via dispatch (10 - 3 = 7)"
    );
}
