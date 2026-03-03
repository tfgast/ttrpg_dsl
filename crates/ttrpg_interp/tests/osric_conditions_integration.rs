//! OSRIC conditions integration test.
//!
//! Verifies that osric/osric_conditions.ttrpg parses, lowers, and type-checks
//! through the full multi-file pipeline (core + ability + class + equipment +
//! combat + conditions). Exercises all 11 conditions with polymorphic entity
//! bearer type: Prone, Stunned, Staggered, Invisible, Paralyzed, Sleeping,
//! Fleeing, Surprised, RearAttacked (simple), Concealed(level), Cover(penalty)
//! (parameterised). Tests condition stacking, removal, and cross-entity-type
//! application (Character and Monster bearers).

use std::collections::{BTreeMap, VecDeque};

use rustc_hash::FxHashMap;
use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_ast::diagnostic::Severity;
use ttrpg_ast::Name;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::{EntityRef, StateProvider, WritableState};
use ttrpg_interp::value::{DiceExpr, RollResult, Value};
use ttrpg_interp::Interpreter;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_conditions() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    let core_source = include_str!("../../../osric/osric_core.ttrpg");
    let ability_source = include_str!("../../../osric/osric_ability.ttrpg");
    let class_source = include_str!("../../../osric/osric_class.ttrpg");
    let equipment_source = include_str!("../../../osric/osric_equipment.ttrpg");
    let combat_source = include_str!("../../../osric/osric_combat.ttrpg");
    let conditions_source = include_str!("../../../osric/osric_conditions.ttrpg");

    let sources = vec![
        (
            "osric/osric_core.ttrpg".to_string(),
            core_source.to_string(),
        ),
        (
            "osric/osric_ability.ttrpg".to_string(),
            ability_source.to_string(),
        ),
        (
            "osric/osric_class.ttrpg".to_string(),
            class_source.to_string(),
        ),
        (
            "osric/osric_equipment.ttrpg".to_string(),
            equipment_source.to_string(),
        ),
        (
            "osric/osric_combat.ttrpg".to_string(),
            combat_source.to_string(),
        ),
        (
            "osric/osric_conditions.ttrpg".to_string(),
            conditions_source.to_string(),
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

    (program.clone(), result)
}

fn get_conditions_decls(program: &ttrpg_ast::ast::Program) -> &[ttrpg_ast::Spanned<DeclKind>] {
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSRIC Conditions" {
                return &sys.decls;
            }
        }
    }
    panic!("no system block named 'OSRIC Conditions' found");
}

// ── Value helpers ──────────────────────────────────────────────

fn enum_variant(enum_name: &str, variant: &str) -> Value {
    Value::EnumVariant {
        enum_name: Name::from(enum_name),
        variant: Name::from(variant),
        fields: BTreeMap::new(),
    }
}

fn class_variant(variant: &str) -> Value {
    enum_variant("Class", variant)
}

fn ability(variant: &str) -> Value {
    enum_variant("Ability", variant)
}

fn feet(value: i64) -> Value {
    Value::Struct {
        name: Name::from("Feet"),
        fields: {
            let mut f = BTreeMap::new();
            f.insert(Name::from("value"), Value::Int(value));
            f
        },
    }
}

fn monster_attack(name: &str, count: u32, sides: u32, bonus: i64) -> Value {
    Value::Struct {
        name: Name::from("MonsterAttack"),
        fields: {
            let mut f = BTreeMap::new();
            f.insert(Name::from("name"), Value::Str(name.to_string()));
            f.insert(
                Name::from("damage"),
                Value::DiceExpr(DiceExpr::single(count, sides, None, bonus)),
            );
            f
        },
    }
}

// ── Effect handler ─────────────────────────────────────────────

struct ScriptedHandler {
    script: VecDeque<Response>,
    log: Vec<Effect>,
}

impl ScriptedHandler {
    fn with_responses(responses: Vec<Response>) -> Self {
        ScriptedHandler {
            script: responses.into(),
            log: Vec::new(),
        }
    }
}

impl EffectHandler for ScriptedHandler {
    fn handle(&mut self, effect: Effect) -> Response {
        self.log.push(effect);
        self.script.pop_front().unwrap_or(Response::Acknowledged)
    }
}

fn scripted_roll(
    count: u32,
    sides: u32,
    modifier: i64,
    dice_vals: Vec<i64>,
    kept_vals: Vec<i64>,
    total: i64,
    unmodified: i64,
) -> Response {
    Response::Rolled(RollResult {
        expr: DiceExpr::single(count, sides, None, modifier),
        dice: dice_vals,
        kept: kept_vals,
        modifier,
        total,
        unmodified,
    })
}

// ── Entity builders ────────────────────────────────────────────

#[allow(clippy::too_many_arguments)]
fn make_character(
    state: &mut GameState,
    name: &str,
    class: &str,
    level: i64,
    abilities: &[(&str, i64)],
    max_hp: i64,
    ac: i64,
    ancestry: &str,
) -> EntityRef {
    let mut ability_map = BTreeMap::new();
    for &(ab, score) in abilities {
        ability_map.insert(ability(ab), Value::Int(score));
    }

    let mut fields = FxHashMap::default();
    fields.insert(Name::from("name"), Value::Str(name.to_string()));
    fields.insert(Name::from("class"), class_variant(class));
    fields.insert(Name::from("ancestry"), enum_variant("Ancestry", ancestry));
    fields.insert(Name::from("level"), Value::Int(level));
    fields.insert(
        Name::from("alignment"),
        enum_variant("Alignment", "TrueNeutral"),
    );
    fields.insert(Name::from("abilities"), Value::Map(ability_map));
    fields.insert(Name::from("max_hp"), Value::Int(max_hp));
    fields.insert(Name::from("hp"), Value::Int(max_hp));
    fields.insert(Name::from("armor_ac"), Value::Int(ac));
    fields.insert(Name::from("shield_ac_bonus"), Value::Int(0));
    fields.insert(Name::from("xp"), Value::Int(0));
    fields.insert(Name::from("base_movement"), feet(120));
    fields.insert(Name::from("gold"), Value::Int(0));
    fields.insert(Name::from("saving_throws"), Value::Option(None));

    state.add_entity("Character", fields)
}

fn make_monster(
    state: &mut GameState,
    name: &str,
    hit_dice: i64,
    max_hp: i64,
    ac: i64,
    attacks: Vec<Value>,
) -> EntityRef {
    let mut fields = FxHashMap::default();
    fields.insert(Name::from("name"), Value::Str(name.to_string()));
    fields.insert(Name::from("hit_dice"), Value::Int(hit_dice));
    fields.insert(Name::from("max_hp"), Value::Int(max_hp));
    fields.insert(Name::from("hp"), Value::Int(max_hp));
    fields.insert(Name::from("armor_ac"), Value::Int(ac));
    fields.insert(Name::from("morale"), Value::Int(7));
    fields.insert(Name::from("xp_value"), Value::Int(0));
    fields.insert(Name::from("attacks"), Value::List(attacks));
    fields.insert(Name::from("size"), enum_variant("Size", "Medium"));
    fields.insert(Name::from("special"), Value::List(vec![]));

    state.add_entity("Monster", fields)
}

fn standard_abilities() -> Vec<(&'static str, i64)> {
    vec![
        ("STR", 12),
        ("DEX", 12),
        ("CON", 12),
        ("INT", 12),
        ("WIS", 12),
        ("CHA", 12),
    ]
}

fn high_dex_abilities() -> Vec<(&'static str, i64)> {
    vec![
        ("STR", 12),
        ("DEX", 17),
        ("CON", 12),
        ("INT", 12),
        ("WIS", 12),
        ("CHA", 12),
    ]
}

/// Build a Character with explicit shield AC bonus.
#[allow(clippy::too_many_arguments)]
fn make_character_with_shield(
    state: &mut GameState,
    name: &str,
    class: &str,
    level: i64,
    abilities: &[(&str, i64)],
    max_hp: i64,
    ac: i64,
    shield_ac_bonus: i64,
    ancestry: &str,
) -> EntityRef {
    let mut ability_map = BTreeMap::new();
    for &(ab, score) in abilities {
        ability_map.insert(ability(ab), Value::Int(score));
    }

    let mut fields = FxHashMap::default();
    fields.insert(Name::from("name"), Value::Str(name.to_string()));
    fields.insert(Name::from("class"), class_variant(class));
    fields.insert(Name::from("ancestry"), enum_variant("Ancestry", ancestry));
    fields.insert(Name::from("level"), Value::Int(level));
    fields.insert(
        Name::from("alignment"),
        enum_variant("Alignment", "TrueNeutral"),
    );
    fields.insert(Name::from("abilities"), Value::Map(ability_map));
    fields.insert(Name::from("max_hp"), Value::Int(max_hp));
    fields.insert(Name::from("hp"), Value::Int(max_hp));
    fields.insert(Name::from("armor_ac"), Value::Int(ac));
    fields.insert(Name::from("shield_ac_bonus"), Value::Int(shield_ac_bonus));
    fields.insert(Name::from("xp"), Value::Int(0));
    fields.insert(Name::from("base_movement"), feet(120));
    fields.insert(Name::from("gold"), Value::Int(0));
    fields.insert(Name::from("saving_throws"), Value::Option(None));

    state.add_entity("Character", fields)
}

fn get_int(fields: &BTreeMap<String, Value>, key: &str) -> i64 {
    match fields.get(key) {
        Some(Value::Int(n)) => *n,
        other => panic!("expected int for '{key}', got: {other:?}"),
    }
}

/// Call resolve_melee_attack and return the AttackResult fields.
/// Caller provides scripted responses (ModifyApplied acks + rolls).
fn resolve_melee(
    interp: &Interpreter,
    state: &GameState,
    responses: Vec<Response>,
    attacker: EntityRef,
    target: EntityRef,
    weapon: &str,
) -> (BTreeMap<String, Value>, Vec<Effect>) {
    let mut handler = ScriptedHandler::with_responses(responses);
    let val = interp
        .evaluate_mechanic(
            state,
            &mut handler,
            "resolve_melee_attack",
            vec![
                Value::Entity(attacker),
                Value::Entity(target),
                enum_variant("MeleeWeapon", weapon),
            ],
        )
        .unwrap();

    match val {
        Value::Struct { name, fields } => {
            assert_eq!(&*name, "AttackResult");
            let fields = fields
                .into_iter()
                .map(|(k, v)| (k.to_string(), v))
                .collect();
            (fields, handler.log)
        }
        other => panic!("expected AttackResult struct, got: {other:?}"),
    }
}

/// Call resolve_missile_attack and return the AttackResult fields.
fn resolve_missile(
    interp: &Interpreter,
    state: &GameState,
    responses: Vec<Response>,
    attacker: EntityRef,
    target: EntityRef,
    weapon: &str,
    distance: i64,
) -> (BTreeMap<String, Value>, Vec<Effect>) {
    let mut handler = ScriptedHandler::with_responses(responses);
    let val = interp
        .evaluate_mechanic(
            state,
            &mut handler,
            "resolve_missile_attack",
            vec![
                Value::Entity(attacker),
                Value::Entity(target),
                enum_variant("MissileWeapon", weapon),
                feet(distance),
            ],
        )
        .unwrap();

    match val {
        Value::Struct { name, fields } => {
            assert_eq!(&*name, "AttackResult");
            let fields = fields
                .into_iter()
                .map(|(k, v)| (k.to_string(), v))
                .collect();
            (fields, handler.log)
        }
        other => panic!("expected AttackResult struct, got: {other:?}"),
    }
}

/// Call resolve_monster_attack and return the AttackResult fields.
fn resolve_monster(
    interp: &Interpreter,
    state: &GameState,
    responses: Vec<Response>,
    attacker: EntityRef,
    target: EntityRef,
    attack: Value,
) -> (BTreeMap<String, Value>, Vec<Effect>) {
    let mut handler = ScriptedHandler::with_responses(responses);
    let val = interp
        .evaluate_mechanic(
            state,
            &mut handler,
            "resolve_monster_attack",
            vec![Value::Entity(attacker), Value::Entity(target), attack],
        )
        .unwrap();

    match val {
        Value::Struct { name, fields } => {
            assert_eq!(&*name, "AttackResult");
            let fields = fields
                .into_iter()
                .map(|(k, v)| (k.to_string(), v))
                .collect();
            (fields, handler.log)
        }
        other => panic!("expected AttackResult struct, got: {other:?}"),
    }
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
fn osric_conditions_has_all_eleven_conditions() {
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
        "Sleeping",
        "Fleeing",
        "Surprised",
        "RearAttacked",
        "Concealed",
        "Cover",
    ];

    for name in &expected {
        assert!(
            conditions.contains(name),
            "missing condition: {name}. Found: {conditions:?}"
        );
    }
    assert_eq!(
        conditions.len(),
        11,
        "expected 11 conditions, found {}: {:?}",
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
    ];

    for item in decls {
        if let DeclKind::Condition(c) = &item.node {
            if simple.contains(&&*c.name) {
                assert!(
                    c.params.is_empty(),
                    "condition {} should have no params but has {}",
                    c.name,
                    c.params.len()
                );
            }
        }
    }
}

#[test]
fn osric_conditions_concealed_has_level_param() {
    let (program, _) = compile_osric_conditions();
    let decls = get_conditions_decls(&program);
    for item in decls {
        if let DeclKind::Condition(c) = &item.node {
            if &*c.name == "Concealed" {
                assert_eq!(c.params.len(), 1, "Concealed should have 1 param");
                assert_eq!(&*c.params[0].name, "level");
                return;
            }
        }
    }
    panic!("Concealed condition not found");
}

#[test]
fn osric_conditions_cover_has_penalty_param() {
    let (program, _) = compile_osric_conditions();
    let decls = get_conditions_decls(&program);
    for item in decls {
        if let DeclKind::Condition(c) = &item.node {
            if &*c.name == "Cover" {
                assert_eq!(c.params.len(), 1, "Cover should have 1 param");
                assert_eq!(&*c.params[0].name, "penalty");
                return;
            }
        }
    }
    panic!("Cover condition not found");
}

// ── Target conditions: +attack_mod on target (#attack_resolution tag) ──

/// Baseline: no conditions, Fighter level 5 (BTHB=4), STR 12 (no mods),
/// SwordLong vs target AC 14. Roll 15 → 15+4 = 19 >= 14 → Hit.
/// total_mod should be 4 (BTHB only).
#[test]
fn baseline_melee_attack_no_conditions() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities(),
        30,
        15,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        14,
        "Human",
    );

    let atk_roll = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    let dmg_roll = scripted_roll(1, 8, 0, vec![6], vec![6], 6, 6);

    let (fields, _) = resolve_melee(
        &interp,
        &state,
        vec![atk_roll, dmg_roll],
        attacker,
        target,
        "SwordLong",
    );

    assert_eq!(
        fields.get("outcome").unwrap(),
        &enum_variant("AttackOutcome", "Hit")
    );
    assert_eq!(get_int(&fields, "total_mod"), 4); // BTHB=4 only
    assert_eq!(get_int(&fields, "damage"), 6);
}

/// Prone on target: +4 to attack_mod → total_mod increases by 4.
#[test]
fn prone_on_target_adds_4_to_attack_mod() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities(),
        30,
        15,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        14,
        "Human",
    );

    state.apply_condition(&target, "Prone", BTreeMap::new(), Value::None, None);

    // ModifyApplied (Phase 1 attack_resolution + effective_target_ac) → 2 Acks, then rolls
    let atk_roll = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    let dmg_roll = scripted_roll(1, 8, 0, vec![6], vec![6], 6, 6);

    let (fields, log) = resolve_melee(
        &interp,
        &state,
        vec![
            Response::Acknowledged,
            Response::Acknowledged,
            atk_roll,
            dmg_roll,
        ],
        attacker,
        target,
        "SwordLong",
    );

    assert_eq!(get_int(&fields, "total_mod"), 8); // BTHB=4 + attack_mod=4
    assert_eq!(
        fields.get("outcome").unwrap(),
        &enum_variant("AttackOutcome", "Hit")
    );

    // Verify ModifyApplied was emitted
    assert!(
        log.iter()
            .any(|e| matches!(e, Effect::ModifyApplied { .. })),
        "expected ModifyApplied effect"
    );
}

/// Stunned on target: +4 to attack_mod (same mechanic as Prone).
#[test]
fn stunned_on_target_adds_4_to_attack_mod() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities(),
        30,
        15,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        14,
        "Human",
    );

    state.apply_condition(&target, "Stunned", BTreeMap::new(), Value::None, None);

    let atk_roll = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    let dmg_roll = scripted_roll(1, 8, 0, vec![6], vec![6], 6, 6);

    let (fields, _) = resolve_melee(
        &interp,
        &state,
        vec![
            Response::Acknowledged,
            Response::Acknowledged,
            atk_roll,
            dmg_roll,
        ],
        attacker,
        target,
        "SwordLong",
    );

    assert_eq!(get_int(&fields, "total_mod"), 8); // BTHB=4 + attack_mod=4
}

/// Staggered on target: +2 to attack_mod.
#[test]
fn staggered_on_target_adds_2_to_attack_mod() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities(),
        30,
        15,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        14,
        "Human",
    );

    state.apply_condition(&target, "Staggered", BTreeMap::new(), Value::None, None);

    let atk_roll = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    let dmg_roll = scripted_roll(1, 8, 0, vec![6], vec![6], 6, 6);

    let (fields, _) = resolve_melee(
        &interp,
        &state,
        vec![Response::Acknowledged, atk_roll, dmg_roll],
        attacker,
        target,
        "SwordLong",
    );

    assert_eq!(get_int(&fields, "total_mod"), 6); // BTHB=4 + attack_mod=2
}

/// Invisible on target: -4 to attack_mod (harder to hit).
#[test]
fn invisible_on_target_subtracts_4_from_attack_mod() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities(),
        30,
        15,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        14,
        "Human",
    );

    state.apply_condition(&target, "Invisible", BTreeMap::new(), Value::None, None);

    // With attack_mod=-4, total_mod = 4+(-4) = 0
    // Roll 15 → 15+0 = 15 >= 14 → still Hit
    let atk_roll = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    let dmg_roll = scripted_roll(1, 8, 0, vec![6], vec![6], 6, 6);

    let (fields, _) = resolve_melee(
        &interp,
        &state,
        vec![Response::Acknowledged, atk_roll, dmg_roll],
        attacker,
        target,
        "SwordLong",
    );

    assert_eq!(get_int(&fields, "total_mod"), 0); // BTHB=4 + attack_mod=-4
}

/// Invisible causes a miss that would otherwise hit.
#[test]
fn invisible_on_target_causes_miss() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        10,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        14,
        "Human",
    );

    state.apply_condition(&target, "Invisible", BTreeMap::new(), Value::None, None);

    // BTHB=0, attack_mod=-4 → total_mod=-4
    // Roll 17 → 17+(-4) = 13 < 14 → Miss (without Invisible, 17+0=17 >= 14 → Hit)
    let atk_roll = scripted_roll(1, 20, 0, vec![17], vec![17], 17, 17);

    let (fields, _) = resolve_melee(
        &interp,
        &state,
        vec![Response::Acknowledged, atk_roll],
        attacker,
        target,
        "SwordLong",
    );

    assert_eq!(
        fields.get("outcome").unwrap(),
        &enum_variant("AttackOutcome", "Miss")
    );
    assert_eq!(get_int(&fields, "total_mod"), -4);
}

// ── Target conditions: melee-specific modifiers ────────────────

/// Paralyzed on target: auto_hit + max_damage on all attacks.
/// No d20 roll or damage roll needed — outcome is forced Hit, damage is max of weapon dice.
/// SwordLong: 1d8 → max = 8. STR 12 → no bonus. Total damage = 8.
#[test]
fn paralyzed_on_target_adds_20_melee() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        10,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        18,
        "Human",
    );

    state.apply_condition(&target, "Paralyzed", BTreeMap::new(), Value::None, None);

    // auto_hit + max_damage: no dice rolls, 2 ModifyApplied acks (attack_resolution + effective_target_ac)
    let (fields, _) = resolve_melee(
        &interp,
        &state,
        vec![Response::Acknowledged, Response::Acknowledged],
        attacker,
        target,
        "SwordLong",
    );

    assert_eq!(get_int(&fields, "total_mod"), 0); // BTHB=0, no attack_mod bonus
    assert_eq!(
        fields.get("outcome").unwrap(),
        &enum_variant("AttackOutcome", "Hit")
    );
    assert_eq!(get_int(&fields, "damage"), 8); // max(1d8) = 8
}

/// Sleeping on target: auto_hit + max_damage (same as Paralyzed).
/// SwordLong: 1d8 → max = 8. STR 12 → no bonus.
#[test]
fn sleeping_on_target_adds_20_melee() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        10,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        18,
        "Human",
    );

    state.apply_condition(&target, "Sleeping", BTreeMap::new(), Value::None, None);

    // auto_hit + max_damage: no dice rolls, 2 ModifyApplied acks
    let (fields, _) = resolve_melee(
        &interp,
        &state,
        vec![Response::Acknowledged, Response::Acknowledged],
        attacker,
        target,
        "SwordLong",
    );

    assert_eq!(get_int(&fields, "total_mod"), 0);
    assert_eq!(
        fields.get("outcome").unwrap(),
        &enum_variant("AttackOutcome", "Hit")
    );
    assert_eq!(get_int(&fields, "damage"), 8); // max(1d8) = 8
}

/// RearAttacked on target: +2 to attack_mod on resolve_melee_attack.
#[test]
fn rear_attacked_on_target_adds_2_melee() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities(),
        30,
        15,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        14,
        "Human",
    );

    state.apply_condition(&target, "RearAttacked", BTreeMap::new(), Value::None, None);

    let atk_roll = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    let dmg_roll = scripted_roll(1, 8, 0, vec![6], vec![6], 6, 6);

    let (fields, _) = resolve_melee(
        &interp,
        &state,
        vec![
            Response::Acknowledged,
            Response::Acknowledged,
            atk_roll,
            dmg_roll,
        ],
        attacker,
        target,
        "SwordLong",
    );

    assert_eq!(get_int(&fields, "total_mod"), 6); // BTHB=4 + attack_mod=2
}

// ── Paralyzed/Sleeping affect ALL attacks (auto_hit + max_damage) ──

/// Paralyzed DOES affect missile attacks (uses #attack_resolution tag).
/// Auto-hit with maximum damage. BowLong: 1d6 → max = 6.
#[test]
fn paralyzed_does_not_affect_missile_attack() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Archer",
        "Fighter",
        3,
        &standard_abilities(),
        20,
        14,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        14,
        "Human",
    );

    state.apply_condition(&target, "Paralyzed", BTreeMap::new(), Value::None, None);

    // auto_hit + max_damage: no dice rolls, 2 ModifyApplied acks
    let (fields, _) = resolve_missile(
        &interp,
        &state,
        vec![Response::Acknowledged, Response::Acknowledged],
        attacker,
        target,
        "BowLong",
        60,
    );

    // BTHB=2, dex_missile(12)=0, range_penalty=0
    assert_eq!(get_int(&fields, "total_mod"), 2);
    assert_eq!(
        fields.get("outcome").unwrap(),
        &enum_variant("AttackOutcome", "Hit")
    );
    assert_eq!(get_int(&fields, "damage"), 6); // max(1d6) = 6
}

// ── Attacker conditions: result override ───────────────────────

/// Surprised on attacker: forces result to Miss with 0 damage.
#[test]
fn surprised_on_attacker_forces_miss() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities(),
        30,
        15,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        10,
        "Human",
    );

    state.apply_condition(&attacker, "Surprised", BTreeMap::new(), Value::None, None);

    // The mechanic body will run (roll attack, possibly damage),
    // then Phase 2 override forces outcome=Miss, damage=0.
    let atk_roll = scripted_roll(1, 20, 0, vec![18], vec![18], 18, 18);
    let dmg_roll = scripted_roll(1, 8, 0, vec![6], vec![6], 6, 6);

    let (fields, _) = resolve_melee(
        &interp,
        &state,
        vec![atk_roll, dmg_roll],
        attacker,
        target,
        "SwordLong",
    );

    assert_eq!(
        fields.get("outcome").unwrap(),
        &enum_variant("AttackOutcome", "Miss"),
        "Surprised attacker should always miss"
    );
    assert_eq!(get_int(&fields, "damage"), 0);
}

/// Fleeing on attacker: forces result to Miss with 0 damage.
#[test]
fn fleeing_on_attacker_forces_miss() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities(),
        30,
        15,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        10,
        "Human",
    );

    state.apply_condition(&attacker, "Fleeing", BTreeMap::new(), Value::None, None);

    let atk_roll = scripted_roll(1, 20, 0, vec![18], vec![18], 18, 18);
    let dmg_roll = scripted_roll(1, 8, 0, vec![6], vec![6], 6, 6);

    let (fields, _) = resolve_melee(
        &interp,
        &state,
        vec![atk_roll, dmg_roll],
        attacker,
        target,
        "SwordLong",
    );

    assert_eq!(
        fields.get("outcome").unwrap(),
        &enum_variant("AttackOutcome", "Miss"),
        "Fleeing attacker should always miss"
    );
    assert_eq!(get_int(&fields, "damage"), 0);
}

// ── Fleeing dual effect ────────────────────────────────────────

/// Fleeing on target: +4 to attack_mod on resolve_melee_attack.
#[test]
fn fleeing_on_target_adds_4_to_melee() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities(),
        30,
        15,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        14,
        "Human",
    );

    state.apply_condition(&target, "Fleeing", BTreeMap::new(), Value::None, None);

    let atk_roll = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    let dmg_roll = scripted_roll(1, 8, 0, vec![6], vec![6], 6, 6);

    let (fields, _) = resolve_melee(
        &interp,
        &state,
        vec![Response::Acknowledged, atk_roll, dmg_roll],
        attacker,
        target,
        "SwordLong",
    );

    assert_eq!(get_int(&fields, "total_mod"), 8); // BTHB=4 + attack_mod=4
}

// ── Parameterised conditions ───────────────────────────────────

/// Concealed(level=1) subtracts 1 from attack_mod.
#[test]
fn concealed_level_1_subtracts_1() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities(),
        30,
        15,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        14,
        "Human",
    );

    let mut params = BTreeMap::new();
    params.insert(Name::from("level"), Value::Int(1));
    state.apply_condition(&target, "Concealed", params, Value::None, None);

    let atk_roll = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    let dmg_roll = scripted_roll(1, 8, 0, vec![6], vec![6], 6, 6);

    let (fields, _) = resolve_melee(
        &interp,
        &state,
        vec![Response::Acknowledged, atk_roll, dmg_roll],
        attacker,
        target,
        "SwordLong",
    );

    assert_eq!(get_int(&fields, "total_mod"), 3); // BTHB=4 + attack_mod=-1
}

/// Concealed(level=4) subtracts 4 from attack_mod (total concealment).
#[test]
fn concealed_level_4_subtracts_4() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities(),
        30,
        15,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        14,
        "Human",
    );

    let mut params = BTreeMap::new();
    params.insert(Name::from("level"), Value::Int(4));
    state.apply_condition(&target, "Concealed", params, Value::None, None);

    let atk_roll = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    let dmg_roll = scripted_roll(1, 8, 0, vec![6], vec![6], 6, 6);

    let (fields, _) = resolve_melee(
        &interp,
        &state,
        vec![Response::Acknowledged, atk_roll, dmg_roll],
        attacker,
        target,
        "SwordLong",
    );

    assert_eq!(get_int(&fields, "total_mod"), 0); // BTHB=4 + attack_mod=-4
}

/// Cover(penalty=2): 25% cover, -2 to attack_mod.
#[test]
fn cover_penalty_2_subtracts_2() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities(),
        30,
        15,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        14,
        "Human",
    );

    let mut params = BTreeMap::new();
    params.insert(Name::from("penalty"), Value::Int(2));
    state.apply_condition(&target, "Cover", params, Value::None, None);

    let atk_roll = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    let dmg_roll = scripted_roll(1, 8, 0, vec![6], vec![6], 6, 6);

    let (fields, _) = resolve_melee(
        &interp,
        &state,
        vec![Response::Acknowledged, atk_roll, dmg_roll],
        attacker,
        target,
        "SwordLong",
    );

    assert_eq!(get_int(&fields, "total_mod"), 2); // BTHB=4 + attack_mod=-2
}

/// Cover(penalty=10): 90% cover, -10 to attack_mod.
#[test]
fn cover_penalty_10_subtracts_10() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities(),
        30,
        15,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        14,
        "Human",
    );

    let mut params = BTreeMap::new();
    params.insert(Name::from("penalty"), Value::Int(10));
    state.apply_condition(&target, "Cover", params, Value::None, None);

    // BTHB=4, attack_mod=-10 → total_mod=-6
    // Roll 19 → 19+(-6) = 13 < 14 → Miss
    let atk_roll = scripted_roll(1, 20, 0, vec![19], vec![19], 19, 19);

    let (fields, _) = resolve_melee(
        &interp,
        &state,
        vec![Response::Acknowledged, atk_roll],
        attacker,
        target,
        "SwordLong",
    );

    assert_eq!(get_int(&fields, "total_mod"), -6); // BTHB=4 + attack_mod=-10
    assert_eq!(
        fields.get("outcome").unwrap(),
        &enum_variant("AttackOutcome", "Miss"),
        "90% cover should make this miss"
    );
}

// ── Cross-entity-type: conditions on tagged mechanics ──────────

/// Prone on a Character target applies via #attack_resolution tag
/// on resolve_missile_attack too.
#[test]
fn prone_on_target_applies_to_missile_attack() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Archer",
        "Fighter",
        3,
        &standard_abilities(),
        20,
        14,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        14,
        "Human",
    );

    state.apply_condition(&target, "Prone", BTreeMap::new(), Value::None, None);

    // BTHB=2, attack_mod=+4 (Prone) → total_mod=6
    let atk_roll = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    let dmg_roll = scripted_roll(1, 6, 0, vec![4], vec![4], 4, 4);

    let (fields, _) = resolve_missile(
        &interp,
        &state,
        vec![
            Response::Acknowledged,
            Response::Acknowledged,
            atk_roll,
            dmg_roll,
        ],
        attacker,
        target,
        "BowLong",
        60,
    );

    assert_eq!(get_int(&fields, "total_mod"), 6); // BTHB=2 + attack_mod=4
}

/// Prone on a Character target applies via #attack_resolution tag
/// on resolve_monster_attack.
#[test]
fn prone_on_target_applies_to_monster_attack() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let monster = make_monster(
        &mut state,
        "Ogre",
        4,
        26,
        15,
        vec![monster_attack("Club", 1, 10, 0)],
    );
    let target = make_character(
        &mut state,
        "Victim",
        "Fighter",
        1,
        &standard_abilities(),
        8,
        14,
        "Human",
    );

    state.apply_condition(&target, "Prone", BTreeMap::new(), Value::None, None);

    // monster_bthb(4)=5, attack_mod=+4 (Prone) → total_mod=9
    let atk_roll = scripted_roll(1, 20, 0, vec![12], vec![12], 12, 12);
    let dmg_roll = scripted_roll(1, 10, 0, vec![7], vec![7], 7, 7);

    let (fields, _) = resolve_monster(
        &interp,
        &state,
        vec![
            Response::Acknowledged,
            Response::Acknowledged,
            atk_roll,
            dmg_roll,
        ],
        monster,
        target,
        monster_attack("Club", 1, 10, 0),
    );

    assert_eq!(get_int(&fields, "total_mod"), 9); // monster_bthb=5 + attack_mod=4
}

/// RearAttacked now uses #attack_resolution tag, so it affects ALL attack types
/// including resolve_monster_attack. +2 to hit, negate DEX/shield AC.
#[test]
fn rear_attacked_does_not_affect_monster_attack() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let monster = make_monster(
        &mut state,
        "Ogre",
        4,
        26,
        15,
        vec![monster_attack("Club", 1, 10, 0)],
    );
    let target = make_character(
        &mut state,
        "Victim",
        "Fighter",
        1,
        &standard_abilities(),
        8,
        14,
        "Human",
    );

    state.apply_condition(&target, "RearAttacked", BTreeMap::new(), Value::None, None);

    // monster_bthb(4)=5, attack_mod=+2 → total_mod = 7
    let atk_roll = scripted_roll(1, 20, 0, vec![12], vec![12], 12, 12);
    let dmg_roll = scripted_roll(1, 10, 0, vec![7], vec![7], 7, 7);

    let (fields, _) = resolve_monster(
        &interp,
        &state,
        vec![
            Response::Acknowledged,
            Response::Acknowledged,
            atk_roll,
            dmg_roll,
        ],
        monster,
        target,
        monster_attack("Club", 1, 10, 0),
    );

    assert_eq!(get_int(&fields, "total_mod"), 7); // monster_bthb=5 + attack_mod=2
}

// ── Condition stacking ─────────────────────────────────────────

/// Multiple conditions on same target stack additively.
/// Prone (+4) + Staggered (+2) = +6 to attack_mod.
#[test]
fn prone_and_staggered_stack_on_target() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities(),
        30,
        15,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        14,
        "Human",
    );

    state.apply_condition(&target, "Prone", BTreeMap::new(), Value::None, None);
    state.apply_condition(&target, "Staggered", BTreeMap::new(), Value::None, None);

    let atk_roll = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    let dmg_roll = scripted_roll(1, 8, 0, vec![6], vec![6], 6, 6);

    // Three ModifyApplied effects: Prone(attack_res) + Staggered(attack_res) + Prone(effective_target_ac)
    let (fields, _) = resolve_melee(
        &interp,
        &state,
        vec![
            Response::Acknowledged,
            Response::Acknowledged,
            Response::Acknowledged,
            atk_roll,
            dmg_roll,
        ],
        attacker,
        target,
        "SwordLong",
    );

    assert_eq!(get_int(&fields, "total_mod"), 10); // BTHB=4 + Prone(4) + Staggered(2)
}

/// Prone (+4) + Invisible (-4) cancel out.
#[test]
fn prone_and_invisible_cancel_out() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities(),
        30,
        15,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        14,
        "Human",
    );

    state.apply_condition(&target, "Prone", BTreeMap::new(), Value::None, None);
    state.apply_condition(&target, "Invisible", BTreeMap::new(), Value::None, None);

    let atk_roll = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    let dmg_roll = scripted_roll(1, 8, 0, vec![6], vec![6], 6, 6);

    // Prone(attack_res) + Invisible(attack_res) + Prone(effective_target_ac)
    let (fields, _) = resolve_melee(
        &interp,
        &state,
        vec![
            Response::Acknowledged,
            Response::Acknowledged,
            Response::Acknowledged,
            atk_roll,
            dmg_roll,
        ],
        attacker,
        target,
        "SwordLong",
    );

    assert_eq!(get_int(&fields, "total_mod"), 4); // BTHB=4 + Prone(4) + Invisible(-4) = 4
}

/// Cover(7) + Concealed(2): both apply via #attack_resolution, stack to -9.
#[test]
fn cover_and_concealed_stack() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities(),
        30,
        15,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        14,
        "Human",
    );

    let mut cover_params = BTreeMap::new();
    cover_params.insert(Name::from("penalty"), Value::Int(7));
    state.apply_condition(&target, "Cover", cover_params, Value::None, None);

    let mut conceal_params = BTreeMap::new();
    conceal_params.insert(Name::from("level"), Value::Int(2));
    state.apply_condition(&target, "Concealed", conceal_params, Value::None, None);

    // BTHB=4, Cover(-7) + Concealed(-2) = attack_mod=-9 → total_mod=-5
    // Roll 19 → 19+(-5) = 14 >= 14 → Hit
    let atk_roll = scripted_roll(1, 20, 0, vec![19], vec![19], 19, 19);
    let dmg_roll = scripted_roll(1, 8, 0, vec![6], vec![6], 6, 6);

    let (fields, _) = resolve_melee(
        &interp,
        &state,
        vec![
            Response::Acknowledged,
            Response::Acknowledged,
            atk_roll,
            dmg_roll,
        ],
        attacker,
        target,
        "SwordLong",
    );

    assert_eq!(get_int(&fields, "total_mod"), -5); // BTHB=4 + Cover(-7) + Concealed(-2)
}

// ── Condition removal ──────────────────────────────────────────

/// After removing a condition, its modifier no longer applies.
#[test]
fn removing_condition_removes_modifier() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities(),
        30,
        15,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        14,
        "Human",
    );

    // Apply and verify
    state.apply_condition(&target, "Prone", BTreeMap::new(), Value::None, None);
    let conds = state.read_conditions(&target).unwrap();
    assert_eq!(conds.len(), 1);
    assert_eq!(&*conds[0].name, "Prone");

    // Remove
    state.remove_condition(&target, "Prone", None);
    let conds = state.read_conditions(&target).unwrap();
    assert!(conds.is_empty(), "Prone should be removed");

    // Attack without conditions — total_mod should be baseline (BTHB=4)
    let atk_roll = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    let dmg_roll = scripted_roll(1, 8, 0, vec![6], vec![6], 6, 6);

    let (fields, _) = resolve_melee(
        &interp,
        &state,
        vec![atk_roll, dmg_roll],
        attacker,
        target,
        "SwordLong",
    );

    assert_eq!(get_int(&fields, "total_mod"), 4); // BTHB=4, no condition modifier
}

/// Removing one of two stacked conditions leaves the other in effect.
#[test]
fn removing_one_stacked_condition_leaves_other() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities(),
        30,
        15,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        14,
        "Human",
    );

    state.apply_condition(&target, "Prone", BTreeMap::new(), Value::None, None);
    state.apply_condition(&target, "Staggered", BTreeMap::new(), Value::None, None);

    // Remove Prone, keep Staggered
    state.remove_condition(&target, "Prone", None);
    let conds = state.read_conditions(&target).unwrap();
    assert_eq!(conds.len(), 1);
    assert_eq!(&*conds[0].name, "Staggered");

    // Attack with only Staggered (+2)
    let atk_roll = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    let dmg_roll = scripted_roll(1, 8, 0, vec![6], vec![6], 6, 6);

    let (fields, _) = resolve_melee(
        &interp,
        &state,
        vec![Response::Acknowledged, atk_roll, dmg_roll],
        attacker,
        target,
        "SwordLong",
    );

    assert_eq!(get_int(&fields, "total_mod"), 6); // BTHB=4 + Staggered(2)
}

/// Remove parameterised condition by name+params.
#[test]
fn remove_parameterised_condition_by_params() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities(),
        30,
        15,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        14,
        "Human",
    );

    let mut params = BTreeMap::new();
    params.insert(Name::from("level"), Value::Int(3));
    state.apply_condition(&target, "Concealed", params.clone(), Value::None, None);

    // Remove with matching params
    state.remove_condition(&target, "Concealed", Some(&params));
    let conds = state.read_conditions(&target).unwrap();
    assert!(conds.is_empty());

    // Attack without conditions
    let atk_roll = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    let dmg_roll = scripted_roll(1, 8, 0, vec![6], vec![6], 6, 6);

    let (fields, _) = resolve_melee(
        &interp,
        &state,
        vec![atk_roll, dmg_roll],
        attacker,
        target,
        "SwordLong",
    );

    assert_eq!(get_int(&fields, "total_mod"), 4); // BTHB=4, no condition
}

// ── Polymorphic entity: conditions on Monster bearers ──────────

/// Surprised condition applied to a Monster (entity type) forces its attacks to miss.
#[test]
fn surprised_on_monster_forces_miss() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let monster = make_monster(
        &mut state,
        "Ogre",
        4,
        26,
        15,
        vec![monster_attack("Club", 1, 10, 0)],
    );
    let target = make_character(
        &mut state,
        "Victim",
        "Fighter",
        5,
        &standard_abilities(),
        30,
        17,
        "Human",
    );

    state.apply_condition(&monster, "Surprised", BTreeMap::new(), Value::None, None);

    // Monster is surprised: its attacks should be forced to Miss
    let atk_roll = scripted_roll(1, 20, 0, vec![18], vec![18], 18, 18);
    let dmg_roll = scripted_roll(1, 10, 0, vec![8], vec![8], 8, 8);

    let (fields, _) = resolve_monster(
        &interp,
        &state,
        vec![atk_roll, dmg_roll],
        monster,
        target,
        monster_attack("Club", 1, 10, 0),
    );

    assert_eq!(
        fields.get("outcome").unwrap(),
        &enum_variant("AttackOutcome", "Miss"),
        "Surprised monster should always miss"
    );
    assert_eq!(get_int(&fields, "damage"), 0);
}

/// Concealed condition applied to a Character target works via
/// resolve_monster_attack (#attack_resolution tag).
#[test]
fn concealed_on_target_applies_to_monster_attack() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let monster = make_monster(
        &mut state,
        "Goblin",
        1,
        4,
        13,
        vec![monster_attack("Shortsword", 1, 6, 0)],
    );
    let target = make_character(
        &mut state,
        "Ranger",
        "Ranger",
        5,
        &standard_abilities(),
        30,
        15,
        "Human",
    );

    let mut params = BTreeMap::new();
    params.insert(Name::from("level"), Value::Int(3));
    state.apply_condition(&target, "Concealed", params, Value::None, None);

    // monster_bthb(1)=1, attack_mod=-3 (Concealed level 3) → total_mod=-2
    let atk_roll = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);

    let (fields, _) = resolve_monster(
        &interp,
        &state,
        vec![Response::Acknowledged, atk_roll],
        monster,
        target,
        monster_attack("Shortsword", 1, 6, 0),
    );

    assert_eq!(get_int(&fields, "total_mod"), -2); // monster_bthb=1 + Concealed(-3)
}

// ── All cover levels ───────────────────────────────────────────

/// Cover at all standard OSRIC levels: 25%=-2, 50%=-4, 75%=-7, 90%=-10.
#[test]
fn cover_all_standard_levels() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();

    let cases = [(2, 2), (4, 0), (7, -3), (10, -6)]; // (penalty, expected total_mod)

    for (penalty, expected_total_mod) in cases {
        let mut state = GameState::new();

        let attacker = make_character(
            &mut state,
            "Fighter",
            "Fighter",
            5,
            &standard_abilities(),
            30,
            15,
            "Human",
        );
        let target = make_character(
            &mut state,
            "Target",
            "Fighter",
            1,
            &standard_abilities(),
            10,
            14,
            "Human",
        );

        let mut params = BTreeMap::new();
        params.insert(Name::from("penalty"), Value::Int(penalty));
        state.apply_condition(&target, "Cover", params, Value::None, None);

        let atk_roll = scripted_roll(1, 20, 0, vec![19], vec![19], 19, 19);
        let dmg_roll = scripted_roll(1, 8, 0, vec![6], vec![6], 6, 6);

        let (fields, _) = resolve_melee(
            &interp,
            &state,
            vec![Response::Acknowledged, atk_roll, dmg_roll],
            attacker,
            target,
            "SwordLong",
        );

        assert_eq!(
            get_int(&fields, "total_mod"),
            expected_total_mod,
            "Cover(penalty={penalty}): expected total_mod={expected_total_mod} (BTHB=4 + penalty=-{penalty})"
        );
    }
}

/// Concealed at all OSRIC levels: 1/4=-1, 1/2=-2, 3/4=-3, total=-4.
#[test]
fn concealed_all_levels() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();

    let cases = [(1, 3), (2, 2), (3, 1), (4, 0)]; // (level, expected total_mod)

    for (level, expected_total_mod) in cases {
        let mut state = GameState::new();

        let attacker = make_character(
            &mut state,
            "Fighter",
            "Fighter",
            5,
            &standard_abilities(),
            30,
            15,
            "Human",
        );
        let target = make_character(
            &mut state,
            "Target",
            "Fighter",
            1,
            &standard_abilities(),
            10,
            14,
            "Human",
        );

        let mut params = BTreeMap::new();
        params.insert(Name::from("level"), Value::Int(level));
        state.apply_condition(&target, "Concealed", params, Value::None, None);

        let atk_roll = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
        let dmg_roll = scripted_roll(1, 8, 0, vec![6], vec![6], 6, 6);

        let (fields, _) = resolve_melee(
            &interp,
            &state,
            vec![Response::Acknowledged, atk_roll, dmg_roll],
            attacker,
            target,
            "SwordLong",
        );

        assert_eq!(
            get_int(&fields, "total_mod"),
            expected_total_mod,
            "Concealed(level={level}): expected total_mod={expected_total_mod} (BTHB=4 + level=-{level})"
        );
    }
}

// ── Surprised on attacker: applies to missile attack too ───────

/// Surprised on attacker suppresses attacks via #attack_resolution,
/// so it also affects resolve_missile_attack.
#[test]
fn surprised_on_attacker_forces_miss_on_missile() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Archer",
        "Fighter",
        3,
        &standard_abilities(),
        20,
        14,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        14,
        "Human",
    );

    state.apply_condition(&attacker, "Surprised", BTreeMap::new(), Value::None, None);

    let atk_roll = scripted_roll(1, 20, 0, vec![18], vec![18], 18, 18);
    let dmg_roll = scripted_roll(1, 6, 0, vec![5], vec![5], 5, 5);

    let (fields, _) = resolve_missile(
        &interp,
        &state,
        vec![atk_roll, dmg_roll],
        attacker,
        target,
        "BowLong",
        60,
    );

    assert_eq!(
        fields.get("outcome").unwrap(),
        &enum_variant("AttackOutcome", "Miss"),
        "Surprised archer should always miss"
    );
    assert_eq!(get_int(&fields, "damage"), 0);
}

// ── Condition counts ───────────────────────────────────────────

/// Applying multiple conditions shows correct count, removing specific ones works.
#[test]
fn condition_count_after_apply_and_remove() {
    let (_, _) = compile_osric_conditions();
    let mut state = GameState::new();
    let mut char_fields = FxHashMap::default();
    char_fields.insert(Name::from("name"), Value::Str("Test".to_string()));
    char_fields.insert(Name::from("class"), class_variant("Fighter"));
    char_fields.insert(Name::from("ancestry"), enum_variant("Ancestry", "Human"));
    char_fields.insert(Name::from("level"), Value::Int(1));
    char_fields.insert(
        Name::from("alignment"),
        enum_variant("Alignment", "TrueNeutral"),
    );
    char_fields.insert(Name::from("abilities"), Value::Map(BTreeMap::new()));
    char_fields.insert(Name::from("max_hp"), Value::Int(10));
    char_fields.insert(Name::from("hp"), Value::Int(10));
    char_fields.insert(Name::from("armor_ac"), Value::Int(10));
    char_fields.insert(Name::from("shield_ac_bonus"), Value::Int(0));
    char_fields.insert(Name::from("xp"), Value::Int(0));
    char_fields.insert(Name::from("base_movement"), feet(120));
    char_fields.insert(Name::from("gold"), Value::Int(0));
    char_fields.insert(Name::from("saving_throws"), Value::Option(None));
    let entity = state.add_entity("Character", char_fields);

    // Apply three conditions
    state.apply_condition(&entity, "Prone", BTreeMap::new(), Value::None, None);
    state.apply_condition(&entity, "Stunned", BTreeMap::new(), Value::None, None);
    state.apply_condition(&entity, "Staggered", BTreeMap::new(), Value::None, None);
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

// ── New tests: DEX AC negation ──────────────────────────────────

/// Prone negates DEX AC bonus. Target with DEX 17 has dex_ac_adj=+3.
/// armor_ac=14, effective_target_ac normally = 14+3+0 = 17.
/// With Prone: effective_target_ac = 14 (dex/shield stripped), total_mod = BTHB=4 + attack_mod=4 = 8.
#[test]
fn prone_negates_dex_ac_bonus() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities(),
        30,
        15,
        "Human",
    );
    // DEX 17 → dex_ac_adj = +3; armor_ac=14 (effective AC = 14+3 = 17)
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &high_dex_abilities(),
        10,
        14,
        "Human",
    );

    state.apply_condition(&target, "Prone", BTreeMap::new(), Value::None, None);

    let atk_roll = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    let dmg_roll = scripted_roll(1, 8, 0, vec![6], vec![6], 6, 6);

    let (fields, _) = resolve_melee(
        &interp,
        &state,
        vec![
            Response::Acknowledged,
            Response::Acknowledged,
            atk_roll,
            dmg_roll,
        ],
        attacker,
        target,
        "SwordLong",
    );

    // BTHB=4 + attack_mod=4 = 8 (DEX negation now on AC side)
    assert_eq!(get_int(&fields, "total_mod"), 8);
}

/// Stunned negates DEX AC bonus. DEX 17 → dex_ac_adj=+3.
/// total_mod = BTHB=4 + attack_mod=4 = 8 (DEX negation on AC side).
#[test]
fn stunned_negates_dex_ac_bonus() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities(),
        30,
        15,
        "Human",
    );
    // armor_ac=14 (effective AC = 14+3 = 17)
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &high_dex_abilities(),
        10,
        14,
        "Human",
    );

    state.apply_condition(&target, "Stunned", BTreeMap::new(), Value::None, None);

    let atk_roll = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    let dmg_roll = scripted_roll(1, 8, 0, vec![6], vec![6], 6, 6);

    let (fields, _) = resolve_melee(
        &interp,
        &state,
        vec![
            Response::Acknowledged,
            Response::Acknowledged,
            atk_roll,
            dmg_roll,
        ],
        attacker,
        target,
        "SwordLong",
    );

    assert_eq!(get_int(&fields, "total_mod"), 8);
}

/// RearAttacked negates DEX AC bonus on missile attacks too.
/// DEX 17 target → dex_ac_adj=+3. DEX negation now on AC side.
#[test]
fn rear_attacked_negates_dex_ac_on_missile() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Archer",
        "Fighter",
        3,
        &standard_abilities(),
        20,
        14,
        "Human",
    );
    // armor_ac=14 (effective AC = 14+3 = 17)
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &high_dex_abilities(),
        10,
        14,
        "Human",
    );

    state.apply_condition(&target, "RearAttacked", BTreeMap::new(), Value::None, None);

    let atk_roll = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    let dmg_roll = scripted_roll(1, 6, 0, vec![4], vec![4], 4, 4);

    let (fields, _) = resolve_missile(
        &interp,
        &state,
        vec![
            Response::Acknowledged,
            Response::Acknowledged,
            atk_roll,
            dmg_roll,
        ],
        attacker,
        target,
        "BowLong",
        60,
    );

    // BTHB=2 + attack_mod=2 = 4 (DEX negation on AC side)
    assert_eq!(get_int(&fields, "total_mod"), 4);
}

// ── New tests: shield AC negation ───────────────────────────────

/// Prone negates shield AC bonus. Target with shield_ac_bonus=1.
/// armor_ac=14, shield=1 → effective AC = 14+0+1 = 15.
/// With Prone: effective AC = 14, total_mod = BTHB=4 + attack_mod=4 = 8.
#[test]
fn prone_negates_shield_ac_bonus() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities(),
        30,
        15,
        "Human",
    );
    // armor_ac=14, shield=1 → effective AC = 14+0+1 = 15
    let target = make_character_with_shield(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        14,
        1,
        "Human",
    );

    state.apply_condition(&target, "Prone", BTreeMap::new(), Value::None, None);

    let atk_roll = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    let dmg_roll = scripted_roll(1, 8, 0, vec![6], vec![6], 6, 6);

    let (fields, _) = resolve_melee(
        &interp,
        &state,
        vec![
            Response::Acknowledged,
            Response::Acknowledged,
            atk_roll,
            dmg_roll,
        ],
        attacker,
        target,
        "SwordLong",
    );

    // BTHB=4 + attack_mod=4 = 8 (shield negation on AC side)
    assert_eq!(get_int(&fields, "total_mod"), 8);
}

/// RearAttacked negates both DEX and shield bonuses combined.
/// Target: DEX 17 (dex_ac_adj=+3), shield_ac_bonus=1.
/// armor_ac=14, effective AC normally = 14+3+1 = 18. With RearAttacked: 14.
#[test]
fn rear_attacked_negates_dex_and_shield_combined() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities(),
        30,
        15,
        "Human",
    );
    // armor_ac=14, shield=1 → effective AC = 14+3+1 = 18
    let target = make_character_with_shield(
        &mut state,
        "Target",
        "Fighter",
        1,
        &high_dex_abilities(),
        10,
        14,
        1,
        "Human",
    );

    state.apply_condition(&target, "RearAttacked", BTreeMap::new(), Value::None, None);

    let atk_roll = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    let dmg_roll = scripted_roll(1, 8, 0, vec![6], vec![6], 6, 6);

    let (fields, _) = resolve_melee(
        &interp,
        &state,
        vec![
            Response::Acknowledged,
            Response::Acknowledged,
            atk_roll,
            dmg_roll,
        ],
        attacker,
        target,
        "SwordLong",
    );

    // BTHB=4 + attack_mod=2 = 6 (DEX+shield negation on AC side)
    assert_eq!(get_int(&fields, "total_mod"), 6);
}

// ── New tests: stunned suppresses bearer attacks ────────────────

/// Stunned bearer cannot attack — forces Miss with 0 damage.
#[test]
fn stunned_on_attacker_forces_miss() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities(),
        30,
        15,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        10,
        "Human",
    );

    state.apply_condition(&attacker, "Stunned", BTreeMap::new(), Value::None, None);

    // Mechanic body runs normally, then Phase 2 forces Miss + damage=0.
    // No ModifyApplied before body for attacker-side Phase 2 overrides.
    let atk_roll = scripted_roll(1, 20, 0, vec![18], vec![18], 18, 18);
    let dmg_roll = scripted_roll(1, 8, 0, vec![6], vec![6], 6, 6);

    let (fields, _) = resolve_melee(
        &interp,
        &state,
        vec![atk_roll, dmg_roll],
        attacker,
        target,
        "SwordLong",
    );

    assert_eq!(
        fields.get("outcome").unwrap(),
        &enum_variant("AttackOutcome", "Miss")
    );
    assert_eq!(get_int(&fields, "damage"), 0);
}

// ── New tests: paralyzed/sleeping suppress bearer attacks ───────

/// Paralyzed bearer cannot attack — forces Miss with 0 damage.
#[test]
fn paralyzed_on_attacker_forces_miss() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities(),
        30,
        15,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        10,
        "Human",
    );

    state.apply_condition(&attacker, "Paralyzed", BTreeMap::new(), Value::None, None);

    // auto_hit is NOT triggered (attacker is paralyzed, not target)
    // Mechanic body runs normally, then Phase 2 override forces Miss
    let atk_roll = scripted_roll(1, 20, 0, vec![18], vec![18], 18, 18);
    let dmg_roll = scripted_roll(1, 8, 0, vec![6], vec![6], 6, 6);

    let (fields, _) = resolve_melee(
        &interp,
        &state,
        vec![atk_roll, dmg_roll],
        attacker,
        target,
        "SwordLong",
    );

    assert_eq!(
        fields.get("outcome").unwrap(),
        &enum_variant("AttackOutcome", "Miss")
    );
    assert_eq!(get_int(&fields, "damage"), 0);
}

/// Sleeping bearer cannot attack — forces Miss with 0 damage.
#[test]
fn sleeping_on_attacker_forces_miss() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities(),
        30,
        15,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        10,
        "Human",
    );

    state.apply_condition(&attacker, "Sleeping", BTreeMap::new(), Value::None, None);

    let atk_roll = scripted_roll(1, 20, 0, vec![18], vec![18], 18, 18);
    let dmg_roll = scripted_roll(1, 8, 0, vec![6], vec![6], 6, 6);

    let (fields, _) = resolve_melee(
        &interp,
        &state,
        vec![atk_roll, dmg_roll],
        attacker,
        target,
        "SwordLong",
    );

    assert_eq!(
        fields.get("outcome").unwrap(),
        &enum_variant("AttackOutcome", "Miss")
    );
    assert_eq!(get_int(&fields, "damage"), 0);
}

// ── New tests: paralyzed auto-hit + max damage variations ───────

/// Paralyzed on target: auto_hit + max_damage with BattleAxe (1d8 vs S/M).
/// Max damage = 8.
#[test]
fn paralyzed_auto_hit_max_damage_battleaxe() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities(),
        30,
        15,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        18,
        "Human",
    );

    state.apply_condition(&target, "Paralyzed", BTreeMap::new(), Value::None, None);

    // No dice rolls needed (auto_hit + max_damage), 2 ModifyApplied acks
    let (fields, _) = resolve_melee(
        &interp,
        &state,
        vec![Response::Acknowledged, Response::Acknowledged],
        attacker,
        target,
        "BattleAxe",
    );

    assert_eq!(
        fields.get("outcome").unwrap(),
        &enum_variant("AttackOutcome", "Hit")
    );
    assert_eq!(get_int(&fields, "damage"), 8); // max(1d8) = 8
}

/// Paralyzed on target: auto_hit on monster attack with max damage.
/// MonsterAttack with 2d6 → max = 12.
#[test]
fn paralyzed_auto_hit_max_damage_monster_attack() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let monster = make_monster(
        &mut state,
        "Ogre",
        4,
        26,
        15,
        vec![monster_attack("Greatclub", 2, 6, 0)],
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities(),
        10,
        18,
        "Human",
    );

    state.apply_condition(&target, "Paralyzed", BTreeMap::new(), Value::None, None);

    // No dice rolls needed (auto_hit + max_damage), 2 ModifyApplied acks
    let (fields, _) = resolve_monster(
        &interp,
        &state,
        vec![Response::Acknowledged, Response::Acknowledged],
        monster,
        target,
        monster_attack("Greatclub", 2, 6, 0),
    );

    assert_eq!(
        fields.get("outcome").unwrap(),
        &enum_variant("AttackOutcome", "Hit")
    );
    assert_eq!(get_int(&fields, "damage"), 12); // max(2d6) = 12
}

/// Paralyzed also negates DEX and shield AC on the auto-hit.
/// DEX 17 target (dex_ac_adj=+3) with shield (1). DEX/shield negation on AC side.
#[test]
fn paralyzed_negates_dex_and_shield_on_auto_hit() {
    let (program, result) = compile_osric_conditions();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities(),
        30,
        15,
        "Human",
    );
    // armor_ac=14, shield=1 → effective AC = 14+3+1 = 18
    let target = make_character_with_shield(
        &mut state,
        "Target",
        "Fighter",
        1,
        &high_dex_abilities(),
        10,
        14,
        1,
        "Human",
    );

    state.apply_condition(&target, "Paralyzed", BTreeMap::new(), Value::None, None);

    let (fields, _) = resolve_melee(
        &interp,
        &state,
        vec![Response::Acknowledged, Response::Acknowledged],
        attacker,
        target,
        "SwordLong",
    );

    // BTHB=4 (DEX/shield negation now on AC side)
    assert_eq!(get_int(&fields, "total_mod"), 4);
    assert_eq!(
        fields.get("outcome").unwrap(),
        &enum_variant("AttackOutcome", "Hit")
    );
    assert_eq!(get_int(&fields, "damage"), 8); // max(1d8) = 8
}
