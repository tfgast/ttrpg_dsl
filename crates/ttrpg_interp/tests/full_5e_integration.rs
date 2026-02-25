//! Full D&D 5e integration tests.
//!
//! Runs the real 5e example (`spec/v0/04_full_example.ttrpg`, 321 lines) through
//! the entire pipeline (parse → lower → check → interpret), exercising every layer
//! together with realistic game scenarios.

use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};

use ttrpg_ast::DiceFilter;
use ttrpg_ast::FileId;
use ttrpg_ast::diagnostic::Severity;
use ttrpg_interp::adapter::StateAdapter;
use ttrpg_interp::effect::{ActionKind, Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::{GameState, GridPosition};
use ttrpg_interp::state::{EntityRef, StateProvider};
use ttrpg_interp::value::{DiceExpr, RollResult, Value, duration_variant};
use ttrpg_interp::Interpreter;

// ── Setup ──────────────────────────────────────────────────────

fn setup() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    let source = include_str!("../../../spec/v0/04_full_example.ttrpg");
    let (program, parse_errors) = ttrpg_parser::parse(source, FileId::SYNTH);
    assert!(
        parse_errors.is_empty(),
        "parse errors: {:?}",
        parse_errors.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    let mut lower_diags = Vec::new();
    let program = ttrpg_parser::lower_moves(program, &mut lower_diags);
    assert!(
        lower_diags.is_empty(),
        "lowering errors: {:?}",
        lower_diags.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    let result = ttrpg_checker::check(&program);
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
    (program, result)
}

// ── ScriptedHandler ────────────────────────────────────────────

struct ScriptedHandler {
    script: VecDeque<Response>,
    log: Vec<Effect>,
}

impl ScriptedHandler {
    fn new() -> Self {
        ScriptedHandler {
            script: VecDeque::new(),
            log: Vec::new(),
        }
    }

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

// ── Entity helper functions ────────────────────────────────────

fn enum_variant(enum_name: &str, variant: &str) -> Value {
    Value::EnumVariant {
        enum_name: ttrpg_ast::Name::from(enum_name),
        variant: ttrpg_ast::Name::from(variant),
        fields: BTreeMap::new(),
    }
}

fn abilities_map(str_: i64, dex: i64, con: i64, int: i64, wis: i64, cha: i64) -> Value {
    let mut map = BTreeMap::new();
    map.insert(enum_variant("Ability", "STR"), Value::Int(str_));
    map.insert(enum_variant("Ability", "DEX"), Value::Int(dex));
    map.insert(enum_variant("Ability", "CON"), Value::Int(con));
    map.insert(enum_variant("Ability", "INT"), Value::Int(int));
    map.insert(enum_variant("Ability", "WIS"), Value::Int(wis));
    map.insert(enum_variant("Ability", "CHA"), Value::Int(cha));
    Value::Map(map)
}

fn weapon_properties(props: &[&str]) -> Value {
    let mut set = BTreeSet::new();
    for p in props {
        set.insert(enum_variant("WeaponProperty", p));
    }
    Value::Set(set)
}

fn damage_type_set(types: &[&str]) -> Value {
    let mut set = BTreeSet::new();
    for t in types {
        set.insert(enum_variant("DamageType", t));
    }
    Value::Set(set)
}

fn damage_spec(count: u32, sides: u32, damage_type: &str) -> Value {
    Value::Struct {
        name: "DamageSpec".into(),
        fields: {
            let mut f = BTreeMap::new();
            f.insert(
                "dice".into(),
                Value::DiceExpr(DiceExpr {
                    count,
                    sides,
                    filter: None,
                    modifier: 0,
                }),
            );
            f.insert("type".into(), enum_variant("DamageType", damage_type));
            f
        },
    }
}

fn add_weapon(
    state: &mut GameState,
    name: &str,
    dmg: Value,
    ability: &str,
    properties: Value,
    range: i64,
    long_range: Option<i64>,
) -> EntityRef {
    let mut fields = HashMap::new();
    fields.insert("name".into(), Value::Str(name.to_string()));
    fields.insert("damage".into(), dmg);
    fields.insert("ability".into(), enum_variant("Ability", ability));
    fields.insert("properties".into(), properties);
    fields.insert("range".into(), Value::Int(range));
    fields.insert(
        "long_range".into(),
        match long_range {
            Some(r) => Value::Option(Some(Box::new(Value::Int(r)))),
            None => Value::Option(None),
        },
    );
    state.add_entity(name, fields)
}

#[allow(clippy::too_many_arguments)]
fn add_character(
    state: &mut GameState,
    name: &str,
    level: i64,
    abilities: Value,
    proficient_saves: Value,
    ac: i64,
    hp: i64,
    max_hp: i64,
    speed: i64,
    resistances: Value,
    immunities: Value,
    vulnerabilities: Value,
    conditions: Value,
    position: Value,
    equipped_weapon: EntityRef,
) -> EntityRef {
    let mut fields = HashMap::new();
    fields.insert("name".into(), Value::Str(name.to_string()));
    fields.insert("level".into(), Value::Int(level));
    fields.insert("abilities".into(), abilities);
    fields.insert("proficient_saves".into(), proficient_saves);
    fields.insert("AC".into(), Value::Int(ac));
    fields.insert("HP".into(), Value::Int(hp));
    fields.insert("max_HP".into(), Value::Int(max_hp));
    fields.insert("speed".into(), Value::Int(speed));
    fields.insert("resistances".into(), resistances);
    fields.insert("immunities".into(), immunities);
    fields.insert("vulnerabilities".into(), vulnerabilities);
    fields.insert("conditions".into(), conditions);
    fields.insert("position".into(), position);
    fields.insert("equipped_weapon".into(), Value::Entity(equipped_weapon));
    state.add_entity(name, fields)
}

fn standard_turn_budget() -> BTreeMap<ttrpg_ast::Name, Value> {
    let mut b = BTreeMap::new();
    b.insert("actions".into(), Value::Int(1));
    b.insert("bonus_actions".into(), Value::Int(1));
    b.insert("reactions".into(), Value::Int(1));
    b.insert("movement".into(), Value::Int(30));
    b.insert("free_interactions".into(), Value::Int(1));
    b
}

#[allow(clippy::too_many_arguments)]
fn scripted_roll(
    count: u32,
    sides: u32,
    filter: Option<DiceFilter>,
    modifier: i64,
    dice_vals: Vec<i64>,
    kept_vals: Vec<i64>,
    total: i64,
    unmodified: i64,
) -> Response {
    Response::Rolled(RollResult {
        expr: DiceExpr {
            count,
            sides,
            filter,
            modifier,
        },
        dice: dice_vals,
        kept: kept_vals,
        modifier,
        total,
        unmodified,
    })
}

// ── Standard test entities ─────────────────────────────────────

/// Build standard Fighter (STR 16, DEX 14) and Goblin (STR 8, DEX 14) entities
/// with a longsword and a shortsword respectively. Returns (state, fighter, goblin).
fn standard_combatants() -> (GameState, EntityRef, EntityRef) {
    let mut state = GameState::new();

    let longsword = add_weapon(
        &mut state,
        "Longsword",
        damage_spec(1, 8, "slashing"),
        "STR",
        weapon_properties(&[]),
        5,
        None,
    );

    let shortsword = add_weapon(
        &mut state,
        "Shortsword",
        damage_spec(1, 6, "piercing"),
        "DEX",
        weapon_properties(&["finesse", "light"]),
        5,
        None,
    );

    let fighter_pos = GridPosition(0, 0).to_value();
    let fighter = add_character(
        &mut state,
        "Fighter",
        5,                                       // level 5 → prof bonus 3
        abilities_map(16, 14, 14, 10, 12, 8),    // STR 16, DEX 14
        damage_type_set(&[]),                     // proficient_saves (using empty set)
        18,                                       // AC
        45,                                       // HP
        45,                                       // max_HP
        30,                                       // speed
        damage_type_set(&[]),                     // resistances
        damage_type_set(&[]),                     // immunities
        damage_type_set(&[]),                     // vulnerabilities
        Value::Set(BTreeSet::new()),              // conditions
        fighter_pos,
        longsword,
    );

    let goblin_pos = GridPosition(1, 0).to_value();
    let goblin = add_character(
        &mut state,
        "Goblin",
        1,                                        // level 1 → prof bonus 2
        abilities_map(8, 14, 10, 10, 8, 8),       // STR 8, DEX 14
        damage_type_set(&[]),
        15,                                        // AC
        7,                                         // HP
        7,                                         // max_HP
        30,                                        // speed
        damage_type_set(&[]),
        damage_type_set(&[]),
        damage_type_set(&[]),
        Value::Set(BTreeSet::new()),
        goblin_pos,
        shortsword,
    );

    state.set_turn_budget(&fighter, standard_turn_budget());
    state.set_turn_budget(&goblin, standard_turn_budget());

    (state, fighter, goblin)
}

// ════════════════════════════════════════════════════════════════
// Group 1: Pipeline Validation
// ════════════════════════════════════════════════════════════════

#[test]
fn pipeline_parses_and_builds_interpreter() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();

    // Smoke-test: verify key declarations are accessible by calling each API
    let state = GameState::new();
    let mut handler = ScriptedHandler::new();

    // Derive: modifier exists and computes correctly
    let val = interp
        .evaluate_derive(&state, &mut handler, "modifier", vec![Value::Int(10)])
        .unwrap();
    assert_eq!(val, Value::Int(0));

    // Undefined names produce errors (proves index was populated correctly)
    assert!(interp
        .evaluate_derive(&state, &mut handler, "nonexistent", vec![])
        .is_err());
    assert!(interp
        .evaluate_mechanic(&state, &mut handler, "nonexistent", vec![])
        .is_err());
    assert!(interp
        .execute_action(&state, &mut handler, "Nonexistent", EntityRef(1), vec![])
        .is_err());
    assert!(interp
        .execute_reaction(&state, &mut handler, "Nonexistent", EntityRef(1), Value::None)
        .is_err());
}

// ════════════════════════════════════════════════════════════════
// Group 2: Derive Functions
// ════════════════════════════════════════════════════════════════

#[test]
fn modifier_scores() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = ScriptedHandler::new();

    // modifier(10) = floor((10-10)/2) = 0
    let val = interp
        .evaluate_derive(&state, &mut handler, "modifier", vec![Value::Int(10)])
        .unwrap();
    assert_eq!(val, Value::Int(0));

    // modifier(16) = floor((16-10)/2) = 3
    let val = interp
        .evaluate_derive(&state, &mut handler, "modifier", vec![Value::Int(16)])
        .unwrap();
    assert_eq!(val, Value::Int(3));

    // modifier(8) = floor((8-10)/2) = floor(-1.0) = -1
    let val = interp
        .evaluate_derive(&state, &mut handler, "modifier", vec![Value::Int(8)])
        .unwrap();
    assert_eq!(val, Value::Int(-1));

    // modifier(15) = floor((15-10)/2) = floor(2.5) = 2
    let val = interp
        .evaluate_derive(&state, &mut handler, "modifier", vec![Value::Int(15)])
        .unwrap();
    assert_eq!(val, Value::Int(2));
}

#[test]
fn proficiency_bonus_levels() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = ScriptedHandler::new();

    // proficiency_bonus(1) = floor((1-1)/4)+2 = 2
    let val = interp
        .evaluate_derive(&state, &mut handler, "proficiency_bonus", vec![Value::Int(1)])
        .unwrap();
    assert_eq!(val, Value::Int(2));

    // proficiency_bonus(5) = floor((5-1)/4)+2 = floor(1)+2 = 3
    let val = interp
        .evaluate_derive(&state, &mut handler, "proficiency_bonus", vec![Value::Int(5)])
        .unwrap();
    assert_eq!(val, Value::Int(3));

    // proficiency_bonus(9) = floor((9-1)/4)+2 = floor(2)+2 = 4
    let val = interp
        .evaluate_derive(&state, &mut handler, "proficiency_bonus", vec![Value::Int(9)])
        .unwrap();
    assert_eq!(val, Value::Int(4));
}

#[test]
fn initial_budget() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let (state, fighter, _goblin) = standard_combatants();
    let mut handler = ScriptedHandler::new();

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "initial_budget",
            vec![Value::Entity(fighter)],
        )
        .unwrap();

    // Expected: TurnBudget { actions: 1, bonus_actions: 1, reactions: 1, movement: 30, free_interactions: 1 }
    match val {
        Value::Struct { name, fields } => {
            assert_eq!(name, "TurnBudget");
            assert_eq!(fields.get("actions"), Some(&Value::Int(1)));
            assert_eq!(fields.get("bonus_actions"), Some(&Value::Int(1)));
            assert_eq!(fields.get("reactions"), Some(&Value::Int(1)));
            assert_eq!(fields.get("movement"), Some(&Value::Int(30)));
            assert_eq!(fields.get("free_interactions"), Some(&Value::Int(1)));
        }
        other => panic!("expected TurnBudget struct, got {:?}", other),
    }
}

#[test]
fn apply_resistances_immune() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    // Create a target with fire immunity
    let sword = add_weapon(
        &mut state,
        "Sword",
        damage_spec(1, 8, "slashing"),
        "STR",
        weapon_properties(&[]),
        5,
        None,
    );
    let target = add_character(
        &mut state,
        "FireImmune",
        1,
        abilities_map(10, 10, 10, 10, 10, 10),
        damage_type_set(&[]),
        10,
        20,
        20,
        30,
        damage_type_set(&[]),
        damage_type_set(&["fire"]), // immunities: fire
        damage_type_set(&[]),
        Value::Set(BTreeSet::new()),
        GridPosition(0, 0).to_value(),
        sword,
    );

    let mut handler = ScriptedHandler::new();
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "apply_resistances",
            vec![
                Value::Entity(target),
                Value::Int(20),
                enum_variant("DamageType", "fire"),
            ],
        )
        .unwrap();
    assert_eq!(val, Value::Int(0));
}

#[test]
fn apply_resistances_resistant() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let sword = add_weapon(
        &mut state,
        "Sword",
        damage_spec(1, 8, "slashing"),
        "STR",
        weapon_properties(&[]),
        5,
        None,
    );
    let target = add_character(
        &mut state,
        "FireResistant",
        1,
        abilities_map(10, 10, 10, 10, 10, 10),
        damage_type_set(&[]),
        10,
        20,
        20,
        30,
        damage_type_set(&["fire"]), // resistances: fire
        damage_type_set(&[]),
        damage_type_set(&[]),
        Value::Set(BTreeSet::new()),
        GridPosition(0, 0).to_value(),
        sword,
    );

    let mut handler = ScriptedHandler::new();
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "apply_resistances",
            vec![
                Value::Entity(target),
                Value::Int(20),
                enum_variant("DamageType", "fire"),
            ],
        )
        .unwrap();
    // floor(20/2) = 10
    assert_eq!(val, Value::Int(10));
}

#[test]
fn apply_resistances_vulnerable() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let sword = add_weapon(
        &mut state,
        "Sword",
        damage_spec(1, 8, "slashing"),
        "STR",
        weapon_properties(&[]),
        5,
        None,
    );
    let target = add_character(
        &mut state,
        "FireVulnerable",
        1,
        abilities_map(10, 10, 10, 10, 10, 10),
        damage_type_set(&[]),
        10,
        20,
        20,
        30,
        damage_type_set(&[]),
        damage_type_set(&[]),
        damage_type_set(&["fire"]), // vulnerabilities: fire
        Value::Set(BTreeSet::new()),
        GridPosition(0, 0).to_value(),
        sword,
    );

    let mut handler = ScriptedHandler::new();
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "apply_resistances",
            vec![
                Value::Entity(target),
                Value::Int(20),
                enum_variant("DamageType", "fire"),
            ],
        )
        .unwrap();
    // 20 * 2 = 40
    assert_eq!(val, Value::Int(40));
}

#[test]
fn apply_resistances_normal() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();

    let sword = add_weapon(
        &mut state,
        "Sword",
        damage_spec(1, 8, "slashing"),
        "STR",
        weapon_properties(&[]),
        5,
        None,
    );
    let target = add_character(
        &mut state,
        "Normal",
        1,
        abilities_map(10, 10, 10, 10, 10, 10),
        damage_type_set(&[]),
        10,
        20,
        20,
        30,
        damage_type_set(&[]),
        damage_type_set(&[]),
        damage_type_set(&[]),
        Value::Set(BTreeSet::new()),
        GridPosition(0, 0).to_value(),
        sword,
    );

    let mut handler = ScriptedHandler::new();
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "apply_resistances",
            vec![
                Value::Entity(target),
                Value::Int(20),
                enum_variant("DamageType", "fire"),
            ],
        )
        .unwrap();
    // No fire in any set → pass-through
    assert_eq!(val, Value::Int(20));
}

// ════════════════════════════════════════════════════════════════
// Group 3: Mechanics
// ════════════════════════════════════════════════════════════════

#[test]
fn choose_attack_ability_non_finesse() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let (state, fighter, _goblin) = standard_combatants();
    let mut handler = ScriptedHandler::new();

    // Fighter's longsword (no finesse) → should return weapon's ability (STR)
    // Weapon is EntityRef(1) (first entity added)
    let longsword = EntityRef(1);
    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "choose_attack_ability",
            vec![Value::Entity(fighter), Value::Entity(longsword)],
        )
        .unwrap();
    assert_eq!(val, enum_variant("Ability", "STR"));
}

#[test]
fn choose_attack_ability_finesse_dex_higher() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let (state, _fighter, goblin) = standard_combatants();
    let mut handler = ScriptedHandler::new();

    // Goblin (STR 8/mod -1, DEX 14/mod +2) with shortsword (finesse) → DEX higher → DEX
    let shortsword = EntityRef(2);
    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "choose_attack_ability",
            vec![Value::Entity(goblin), Value::Entity(shortsword)],
        )
        .unwrap();
    assert_eq!(val, enum_variant("Ability", "DEX"));
}

#[test]
fn choose_attack_ability_finesse_str_higher() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let (state, fighter, _goblin) = standard_combatants();
    let mut handler = ScriptedHandler::new();

    // Fighter (STR 16/mod +3, DEX 14/mod +2) with shortsword (finesse) → STR >= DEX → weapon.ability (DEX)
    let shortsword = EntityRef(2);
    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "choose_attack_ability",
            vec![Value::Entity(fighter), Value::Entity(shortsword)],
        )
        .unwrap();
    // STR mod (3) > DEX mod (2) → else branch → weapon.ability (DEX for shortsword)
    assert_eq!(val, enum_variant("Ability", "DEX"));
}

#[test]
fn d20_expr_normal_mode() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = ScriptedHandler::new();

    // d20_expr(score=16, proficiency=2, bonus=0, mode=normal)
    // modifier(16) = 3, total modifier = 3 + 2 + 0 = 5
    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "d20_expr",
            vec![
                Value::Int(16),
                Value::Int(2),
                Value::Int(0),
                enum_variant("RollMode", "normal"),
            ],
        )
        .unwrap();

    match val {
        Value::DiceExpr(expr) => {
            assert_eq!(expr.count, 1);
            assert_eq!(expr.sides, 20);
            assert_eq!(expr.filter, None);
            assert_eq!(expr.modifier, 5); // 3 + 2 + 0
        }
        other => panic!("expected DiceExpr, got {:?}", other),
    }
}

#[test]
fn d20_expr_advantage_mode() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = ScriptedHandler::new();

    // d20_expr(score=16, proficiency=2, bonus=0, mode=advantage)
    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "d20_expr",
            vec![
                Value::Int(16),
                Value::Int(2),
                Value::Int(0),
                enum_variant("RollMode", "advantage"),
            ],
        )
        .unwrap();

    match val {
        Value::DiceExpr(expr) => {
            assert_eq!(expr.count, 2);
            assert_eq!(expr.sides, 20);
            assert_eq!(expr.filter, Some(DiceFilter::KeepHighest(1)));
            assert_eq!(expr.modifier, 5);
        }
        other => panic!("expected DiceExpr, got {:?}", other),
    }
}

#[test]
fn attack_roll_emits_roll_dice() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let (state, fighter, goblin) = standard_combatants();

    // Fighter (STR 16/mod+3, level 5/prof+3) attacks Goblin with longsword
    // d20_expr(16, 3, 0, normal) → 1d20+6
    let longsword = EntityRef(1);
    let roll_response = scripted_roll(1, 20, None, 6, vec![14], vec![14], 20, 14);
    let mut handler = ScriptedHandler::with_responses(vec![roll_response]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "attack_roll",
            vec![
                Value::Entity(fighter),
                Value::Entity(goblin),
                Value::Entity(longsword),
                enum_variant("RollMode", "normal"),
            ],
        )
        .unwrap();

    // Should have emitted RollDice
    assert!(handler.log.iter().any(|e| matches!(e, Effect::RollDice { .. })));

    // Should return a RollResult
    match val {
        Value::RollResult(rr) => {
            assert_eq!(rr.total, 20);
        }
        other => panic!("expected RollResult, got {:?}", other),
    }
}

#[test]
fn resolve_melee_attack_hit() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let (state, fighter, goblin) = standard_combatants();
    let longsword = EntityRef(1);

    // Fighter attacks Goblin. Attack roll: total=20, unmodified=14 → hits AC 15
    // Damage roll: 1d8+3 = total 7
    let atk_roll = scripted_roll(1, 20, None, 6, vec![14], vec![14], 20, 14);
    let dmg_roll = scripted_roll(1, 8, None, 3, vec![4], vec![4], 7, 4);
    let mut handler = ScriptedHandler::with_responses(vec![atk_roll, dmg_roll]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "resolve_melee_attack",
            vec![
                Value::Entity(fighter),
                Value::Entity(goblin),
                Value::Entity(longsword),
                enum_variant("RollMode", "normal"),
            ],
        )
        .unwrap();

    // Should return ResolvedDamage.hit(7) — no resistances
    match val {
        Value::EnumVariant {
            enum_name,
            variant,
            fields,
        } => {
            assert_eq!(enum_name, "ResolvedDamage");
            assert_eq!(variant, "hit");
            assert_eq!(fields.get("amount"), Some(&Value::Int(7)));
        }
        other => panic!("expected ResolvedDamage.hit, got {:?}", other),
    }
}

#[test]
fn resolve_melee_attack_nat_20_crit() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let (state, fighter, goblin) = standard_combatants();
    let longsword = EntityRef(1);

    // Attack roll: unmodified=20 → crit
    // Crit damage: multiply_dice(1d8, 2) = 2d8+3
    let atk_roll = scripted_roll(1, 20, None, 6, vec![20], vec![20], 26, 20);
    let dmg_roll = scripted_roll(2, 8, None, 3, vec![5, 6], vec![5, 6], 14, 11);
    let mut handler = ScriptedHandler::with_responses(vec![atk_roll, dmg_roll]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "resolve_melee_attack",
            vec![
                Value::Entity(fighter),
                Value::Entity(goblin),
                Value::Entity(longsword),
                enum_variant("RollMode", "normal"),
            ],
        )
        .unwrap();

    match val {
        Value::EnumVariant {
            enum_name,
            variant,
            fields,
        } => {
            assert_eq!(enum_name, "ResolvedDamage");
            assert_eq!(variant, "hit");
            assert_eq!(fields.get("amount"), Some(&Value::Int(14)));
        }
        other => panic!("expected ResolvedDamage.hit (crit), got {:?}", other),
    }
}

#[test]
fn resolve_melee_attack_nat_1_miss() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let (state, fighter, goblin) = standard_combatants();
    let longsword = EntityRef(1);

    // Attack roll: unmodified=1 → auto-miss regardless of total
    let atk_roll = scripted_roll(1, 20, None, 6, vec![1], vec![1], 7, 1);
    let mut handler = ScriptedHandler::with_responses(vec![atk_roll]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "resolve_melee_attack",
            vec![
                Value::Entity(fighter),
                Value::Entity(goblin),
                Value::Entity(longsword),
                enum_variant("RollMode", "normal"),
            ],
        )
        .unwrap();

    match val {
        Value::EnumVariant {
            enum_name, variant, ..
        } => {
            assert_eq!(enum_name, "ResolvedDamage");
            assert_eq!(variant, "miss");
        }
        other => panic!("expected ResolvedDamage.miss, got {:?}", other),
    }
}

#[test]
fn resolve_melee_attack_below_ac_miss() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let (state, fighter, goblin) = standard_combatants();
    let longsword = EntityRef(1);

    // Attack roll: total=8, unmodified=2 → below Goblin's AC 15 → miss
    let atk_roll = scripted_roll(1, 20, None, 6, vec![2], vec![2], 8, 2);
    let mut handler = ScriptedHandler::with_responses(vec![atk_roll]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "resolve_melee_attack",
            vec![
                Value::Entity(fighter),
                Value::Entity(goblin),
                Value::Entity(longsword),
                enum_variant("RollMode", "normal"),
            ],
        )
        .unwrap();

    match val {
        Value::EnumVariant {
            enum_name, variant, ..
        } => {
            assert_eq!(enum_name, "ResolvedDamage");
            assert_eq!(variant, "miss");
        }
        other => panic!("expected ResolvedDamage.miss, got {:?}", other),
    }

    // No damage roll should have been emitted (only 1 RollDice for the attack)
    let roll_count = handler
        .log
        .iter()
        .filter(|e| matches!(e, Effect::RollDice { .. }))
        .count();
    assert_eq!(roll_count, 1);
}

// ════════════════════════════════════════════════════════════════
// Group 4: Actions
// ════════════════════════════════════════════════════════════════

#[test]
fn attack_action_hit() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let (state, fighter, goblin) = standard_combatants();
    let longsword = EntityRef(1);

    // Attack roll: total=20, unmodified=14 → hits AC 15
    // Damage roll: 1d8+3 = total 7
    let atk_roll = scripted_roll(1, 20, None, 6, vec![14], vec![14], 20, 14);
    let dmg_roll = scripted_roll(1, 8, None, 3, vec![4], vec![4], 7, 4);
    // Responses consumed in effect order: ActionStarted(Ack), RequiresCheck(Ack),
    // DeductCost(Ack), RollDice(atk), RollDice(dmg), MutateField(Ack), ActionCompleted(Ack)
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged,
        Response::Acknowledged,
        Response::Acknowledged,
        atk_roll,
        dmg_roll,
    ]);

    let val = interp
        .execute_action(
            &state,
            &mut handler,
            "Attack",
            fighter,
            vec![Value::Entity(goblin), Value::Entity(longsword)],
        )
        .unwrap();
    assert_eq!(val, Value::None);

    // Verify effect sequence
    assert!(matches!(
        &handler.log[0],
        Effect::ActionStarted { name, kind: ActionKind::Action, .. } if name == "Attack"
    ));
    assert!(matches!(
        &handler.log[1],
        Effect::RequiresCheck { action, passed: true, .. } if action == "Attack"
    ));
    assert!(matches!(
        &handler.log[2],
        Effect::DeductCost { token, budget_field, .. }
        if token == "action" && budget_field == "actions"
    ));
    // RollDice effects for attack and damage
    let roll_indices: Vec<_> = handler
        .log
        .iter()
        .enumerate()
        .filter(|(_, e)| matches!(e, Effect::RollDice { .. }))
        .map(|(i, _)| i)
        .collect();
    assert_eq!(roll_indices.len(), 2);

    // MutateField for HP damage
    assert!(handler.log.iter().any(|e| matches!(
        e,
        Effect::MutateField { entity, path, .. }
        if entity == &goblin && !path.is_empty()
    )));

    // ActionCompleted at the end
    assert!(matches!(
        handler.log.last().unwrap(),
        Effect::ActionCompleted { name, .. } if name == "Attack"
    ));
}

#[test]
fn attack_action_out_of_range() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();

    // Place target far away (distance > weapon.range=5)
    let mut state = GameState::new();
    let longsword = add_weapon(
        &mut state,
        "Longsword",
        damage_spec(1, 8, "slashing"),
        "STR",
        weapon_properties(&[]),
        5,
        None,
    );
    let shortsword = add_weapon(
        &mut state,
        "Shortsword",
        damage_spec(1, 6, "piercing"),
        "DEX",
        weapon_properties(&["finesse", "light"]),
        5,
        None,
    );
    let fighter_pos = GridPosition(0, 0).to_value();
    let fighter = add_character(
        &mut state,
        "Fighter",
        5,
        abilities_map(16, 14, 14, 10, 12, 8),
        damage_type_set(&[]),
        18,
        45,
        45,
        30,
        damage_type_set(&[]),
        damage_type_set(&[]),
        damage_type_set(&[]),
        Value::Set(BTreeSet::new()),
        fighter_pos,
        longsword,
    );
    let goblin_pos = GridPosition(10, 0).to_value(); // distance=10 > range=5
    let goblin = add_character(
        &mut state,
        "Goblin",
        1,
        abilities_map(8, 14, 10, 10, 8, 8),
        damage_type_set(&[]),
        15,
        7,
        7,
        30,
        damage_type_set(&[]),
        damage_type_set(&[]),
        damage_type_set(&[]),
        Value::Set(BTreeSet::new()),
        goblin_pos,
        shortsword,
    );
    state.set_turn_budget(&fighter, standard_turn_budget());

    let mut handler = ScriptedHandler::new();
    let val = interp
        .execute_action(
            &state,
            &mut handler,
            "Attack",
            fighter,
            vec![Value::Entity(goblin), Value::Entity(longsword)],
        )
        .unwrap();
    assert_eq!(val, Value::None);

    // RequiresCheck should have passed=false
    assert!(handler.log.iter().any(|e| matches!(
        e,
        Effect::RequiresCheck { passed: false, .. }
    )));
    // No DeductCost
    assert!(!handler.log.iter().any(|e| matches!(e, Effect::DeductCost { .. })));
    // No RollDice
    assert!(!handler.log.iter().any(|e| matches!(e, Effect::RollDice { .. })));
    // ActionCompleted should still be present
    assert!(matches!(
        handler.log.last().unwrap(),
        Effect::ActionCompleted { .. }
    ));
}

#[test]
fn dash_action() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let (state, fighter, _goblin) = standard_combatants();
    let mut handler = ScriptedHandler::new();

    let val = interp
        .execute_action(&state, &mut handler, "Dash", fighter, vec![])
        .unwrap();
    assert_eq!(val, Value::None);

    // Verify: DeductCost(action), MutateTurnField(movement, PlusEq, 30)
    assert!(handler.log.iter().any(|e| matches!(
        e,
        Effect::DeductCost { token, .. } if token == "action"
    )));
    assert!(handler.log.iter().any(|e| matches!(
        e,
        Effect::MutateTurnField { field, op, value, .. }
        if field == "movement" && matches!(op, ttrpg_ast::ast::AssignOp::PlusEq) && *value == Value::Int(30)
    )));
    assert!(matches!(
        handler.log.last().unwrap(),
        Effect::ActionCompleted { name, .. } if name == "Dash"
    ));
}

#[test]
fn dodge_action() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let (state, fighter, _goblin) = standard_combatants();
    let mut handler = ScriptedHandler::new();

    let val = interp
        .execute_action(&state, &mut handler, "Dodge", fighter, vec![])
        .unwrap();
    assert_eq!(val, Value::None);

    assert!(handler.log.iter().any(|e| matches!(
        e,
        Effect::DeductCost { token, .. } if token == "action"
    )));
    assert!(handler.log.iter().any(|e| matches!(
        e,
        Effect::ApplyCondition { condition, duration, .. }
        if condition == "Dodging" && matches!(duration, Value::EnumVariant { ref enum_name, ref variant, .. } if enum_name == "Duration" && variant == "start_of_next_turn")
    )));
    assert!(matches!(
        handler.log.last().unwrap(),
        Effect::ActionCompleted { name, .. } if name == "Dodge"
    ));
}

#[test]
fn disengage_action() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let (state, fighter, _goblin) = standard_combatants();
    let mut handler = ScriptedHandler::new();

    let val = interp
        .execute_action(&state, &mut handler, "Disengage", fighter, vec![])
        .unwrap();
    assert_eq!(val, Value::None);

    assert!(handler.log.iter().any(|e| matches!(
        e,
        Effect::DeductCost { token, .. } if token == "action"
    )));
    assert!(handler.log.iter().any(|e| matches!(
        e,
        Effect::ApplyCondition { condition, duration, .. }
        if condition == "Disengaging" && matches!(duration, Value::EnumVariant { ref enum_name, ref variant, .. } if enum_name == "Duration" && variant == "end_of_turn")
    )));
    assert!(matches!(
        handler.log.last().unwrap(),
        Effect::ActionCompleted { name, .. } if name == "Disengage"
    ));
}

// ════════════════════════════════════════════════════════════════
// Group 5: Events & Reactions
// ════════════════════════════════════════════════════════════════

#[test]
fn fire_entity_leaves_reach_triggers_opportunity_attack() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let (state, fighter, goblin) = standard_combatants();

    // Fire entity_leaves_reach with reactor=fighter, entity=goblin
    let payload = Value::Struct {
        name: "__event_entity_leaves_reach".into(),
        fields: {
            let mut f = BTreeMap::new();
            f.insert("reactor".into(), Value::Entity(fighter));
            f.insert("entity".into(), Value::Entity(goblin));
            f.insert("from_position".into(), GridPosition(1, 0).to_value());
            f.insert("to_position".into(), GridPosition(2, 0).to_value());
            f
        },
    };

    let event_result = interp
        .what_triggers(&state, "entity_leaves_reach", payload, &[fighter])
        .unwrap();

    assert_eq!(event_result.triggerable.len(), 1);
    assert_eq!(event_result.triggerable[0].name, "OpportunityAttack");
    assert_eq!(event_result.triggerable[0].reactor, fighter);
    assert!(event_result.suppressed.is_empty());
}

#[test]
fn execute_opportunity_attack_reaction() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let (state, fighter, goblin) = standard_combatants();

    let payload = Value::Struct {
        name: "__event_entity_leaves_reach".into(),
        fields: {
            let mut f = BTreeMap::new();
            f.insert("reactor".into(), Value::Entity(fighter));
            f.insert("entity".into(), Value::Entity(goblin));
            f.insert("from_position".into(), GridPosition(1, 0).to_value());
            f.insert("to_position".into(), GridPosition(2, 0).to_value());
            f
        },
    };

    // Script attack roll (hit) and damage roll
    // Responses consumed in effect order: ActionStarted(Ack), DeductCost(Ack),
    // RollDice(atk), RollDice(dmg), MutateField(Ack), ActionCompleted(Ack)
    let atk_roll = scripted_roll(1, 20, None, 6, vec![14], vec![14], 20, 14);
    let dmg_roll = scripted_roll(1, 8, None, 3, vec![4], vec![4], 7, 4);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged,
        Response::Acknowledged,
        atk_roll,
        dmg_roll,
    ]);

    let val = interp
        .execute_reaction(&state, &mut handler, "OpportunityAttack", fighter, payload)
        .unwrap();
    assert_eq!(val, Value::None);

    // Verify ActionStarted with Reaction kind
    assert!(matches!(
        &handler.log[0],
        Effect::ActionStarted { kind: ActionKind::Reaction { event, .. }, .. }
        if event == "entity_leaves_reach"
    ));
    // Verify DeductCost(reaction)
    assert!(handler.log.iter().any(|e| matches!(
        e,
        Effect::DeductCost { token, budget_field, .. }
        if token == "reaction" && budget_field == "reactions"
    )));
    // ActionCompleted at the end
    assert!(matches!(
        handler.log.last().unwrap(),
        Effect::ActionCompleted { name, .. } if name == "OpportunityAttack"
    ));
}

#[test]
fn fire_entity_leaves_reach_no_match() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let (state, _fighter, goblin) = standard_combatants();

    // Fire entity_leaves_reach with reactor=goblin but candidate is also goblin
    // The trigger is: trigger: entity_leaves_reach(reactor: reactor)
    // So the candidate's reactor binding must match the reactor in the payload
    // When candidate = goblin and payload reactor = goblin, it would match.
    // For "no match", use a non-existent candidate.
    let payload = Value::Struct {
        name: "__event_entity_leaves_reach".into(),
        fields: {
            let mut f = BTreeMap::new();
            f.insert("reactor".into(), Value::Entity(EntityRef(99))); // doesn't match any candidate
            f.insert("entity".into(), Value::Entity(goblin));
            f.insert("from_position".into(), GridPosition(1, 0).to_value());
            f.insert("to_position".into(), GridPosition(2, 0).to_value());
            f
        },
    };

    let event_result = interp
        .what_triggers(&state, "entity_leaves_reach", payload, &[goblin])
        .unwrap();

    assert!(event_result.triggerable.is_empty());
    assert!(event_result.suppressed.is_empty());
}

// ════════════════════════════════════════════════════════════════
// Group 6: Condition Modifiers
// ════════════════════════════════════════════════════════════════

#[test]
fn prone_on_attacker_disadvantage() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let (mut state, fighter, goblin) = standard_combatants();
    let longsword = EntityRef(1);

    // Give fighter the Prone condition
    state.apply_condition(
        &fighter,
        "Prone",
        BTreeMap::new(),
        duration_variant("indefinite"),
    );

    // Call attack_roll — should have disadvantage (2d20kl1)
    // Responses consumed: ModifyApplied(Ack), RollDice(roll)
    let roll_response = scripted_roll(
        2,
        20,
        Some(DiceFilter::KeepLowest(1)),
        6,
        vec![14, 8],
        vec![8],
        14,
        8,
    );
    let mut handler =
        ScriptedHandler::with_responses(vec![Response::Acknowledged, roll_response]);

    let _val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "attack_roll",
            vec![
                Value::Entity(fighter),
                Value::Entity(goblin),
                Value::Entity(longsword),
                enum_variant("RollMode", "normal"),
            ],
        )
        .unwrap();

    // Verify RollDice was emitted with disadvantage (2d20kl1)
    let roll_effect = handler
        .log
        .iter()
        .find(|e| matches!(e, Effect::RollDice { .. }))
        .expect("expected RollDice effect");
    match roll_effect {
        Effect::RollDice { expr } => {
            assert_eq!(expr.count, 2);
            assert_eq!(expr.sides, 20);
            assert_eq!(expr.filter, Some(DiceFilter::KeepLowest(1)));
        }
        _ => unreachable!(),
    }

    // Verify ModifyApplied was emitted
    assert!(handler
        .log
        .iter()
        .any(|e| matches!(e, Effect::ModifyApplied { .. })));
}

#[test]
fn prone_on_target_melee_advantage() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let (mut state, fighter, goblin) = standard_combatants();
    let longsword = EntityRef(1);

    // Give goblin (target) the Prone condition
    state.apply_condition(
        &goblin,
        "Prone",
        BTreeMap::new(),
        duration_variant("indefinite"),
    );

    // Fighter is at (0,0), Goblin at (1,0) → distance=1 <= 5 → advantage
    // Responses consumed: ModifyApplied(Ack), RollDice(roll)
    let roll_response = scripted_roll(
        2,
        20,
        Some(DiceFilter::KeepHighest(1)),
        6,
        vec![14, 18],
        vec![18],
        24,
        18,
    );
    let mut handler =
        ScriptedHandler::with_responses(vec![Response::Acknowledged, roll_response]);

    let _val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "attack_roll",
            vec![
                Value::Entity(fighter),
                Value::Entity(goblin),
                Value::Entity(longsword),
                enum_variant("RollMode", "normal"),
            ],
        )
        .unwrap();

    let roll_effect = handler
        .log
        .iter()
        .find(|e| matches!(e, Effect::RollDice { .. }))
        .expect("expected RollDice effect");
    match roll_effect {
        Effect::RollDice { expr } => {
            assert_eq!(expr.count, 2);
            assert_eq!(expr.sides, 20);
            assert_eq!(expr.filter, Some(DiceFilter::KeepHighest(1)));
        }
        _ => unreachable!(),
    }
}

#[test]
fn prone_on_target_ranged_disadvantage() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();

    // Create entities with distance > 5
    let mut state = GameState::new();
    let longsword = add_weapon(
        &mut state,
        "Longbow",
        damage_spec(1, 8, "piercing"),
        "DEX",
        weapon_properties(&[]),
        150,
        Some(600),
    );
    let shortsword = add_weapon(
        &mut state,
        "Shortsword",
        damage_spec(1, 6, "piercing"),
        "DEX",
        weapon_properties(&["finesse", "light"]),
        5,
        None,
    );
    let fighter_pos = GridPosition(0, 0).to_value();
    let fighter = add_character(
        &mut state,
        "Fighter",
        5,
        abilities_map(16, 14, 14, 10, 12, 8),
        damage_type_set(&[]),
        18,
        45,
        45,
        30,
        damage_type_set(&[]),
        damage_type_set(&[]),
        damage_type_set(&[]),
        Value::Set(BTreeSet::new()),
        fighter_pos,
        longsword,
    );
    let goblin_pos = GridPosition(10, 0).to_value(); // distance=10 > 5
    let goblin = add_character(
        &mut state,
        "Goblin",
        1,
        abilities_map(8, 14, 10, 10, 8, 8),
        damage_type_set(&[]),
        15,
        7,
        7,
        30,
        damage_type_set(&[]),
        damage_type_set(&[]),
        damage_type_set(&[]),
        Value::Set(BTreeSet::new()),
        goblin_pos,
        shortsword,
    );

    // Give goblin Prone condition
    state.apply_condition(
        &goblin,
        "Prone",
        BTreeMap::new(),
        duration_variant("indefinite"),
    );

    // Responses consumed: ModifyApplied(Ack), RollDice(roll)
    let roll_response = scripted_roll(
        2,
        20,
        Some(DiceFilter::KeepLowest(1)),
        5, // DEX 14 mod +2, prof +3 = +5
        vec![14, 8],
        vec![8],
        13,
        8,
    );
    let mut handler =
        ScriptedHandler::with_responses(vec![Response::Acknowledged, roll_response]);

    let _val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "attack_roll",
            vec![
                Value::Entity(fighter),
                Value::Entity(goblin),
                Value::Entity(longsword),
                enum_variant("RollMode", "normal"),
            ],
        )
        .unwrap();

    let roll_effect = handler
        .log
        .iter()
        .find(|e| matches!(e, Effect::RollDice { .. }))
        .expect("expected RollDice effect");
    match roll_effect {
        Effect::RollDice { expr } => {
            assert_eq!(expr.count, 2);
            assert_eq!(expr.sides, 20);
            assert_eq!(expr.filter, Some(DiceFilter::KeepLowest(1))); // disadvantage
        }
        _ => unreachable!(),
    }
}

#[test]
fn prone_modifies_initial_budget() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let (mut state, fighter, _goblin) = standard_combatants();

    // Give fighter Prone condition
    state.apply_condition(
        &fighter,
        "Prone",
        BTreeMap::new(),
        duration_variant("indefinite"),
    );

    let mut handler = ScriptedHandler::new();
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "initial_budget",
            vec![Value::Entity(fighter)],
        )
        .unwrap();

    match val {
        Value::Struct { name, fields } => {
            assert_eq!(name, "TurnBudget");
            // movement reduced by floor(30/2) = 15 → 30 - 15 = 15
            assert_eq!(fields.get("movement"), Some(&Value::Int(15)));
            // Other fields unchanged
            assert_eq!(fields.get("actions"), Some(&Value::Int(1)));
        }
        other => panic!("expected TurnBudget struct, got {:?}", other),
    }

    // Verify ModifyApplied was emitted
    assert!(handler
        .log
        .iter()
        .any(|e| matches!(e, Effect::ModifyApplied { .. })));
}

// ════════════════════════════════════════════════════════════════
// Group 7: Condition Suppression
// ════════════════════════════════════════════════════════════════

#[test]
fn disengaging_suppresses_entity_leaves_reach() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let (mut state, fighter, goblin) = standard_combatants();

    // Give goblin (the leaving entity) the Disengaging condition
    state.apply_condition(
        &goblin,
        "Disengaging",
        BTreeMap::new(),
        duration_variant("end_of_turn"),
    );

    let payload = Value::Struct {
        name: "__event_entity_leaves_reach".into(),
        fields: {
            let mut f = BTreeMap::new();
            f.insert("reactor".into(), Value::Entity(fighter));
            f.insert("entity".into(), Value::Entity(goblin));
            f.insert("from_position".into(), GridPosition(1, 0).to_value());
            f.insert("to_position".into(), GridPosition(2, 0).to_value());
            f
        },
    };

    let event_result = interp
        .what_triggers(&state, "entity_leaves_reach", payload, &[fighter])
        .unwrap();

    // Reaction should appear in suppressed, not triggerable
    assert!(event_result.triggerable.is_empty());
    assert_eq!(event_result.suppressed.len(), 1);
    assert_eq!(event_result.suppressed[0].name, "OpportunityAttack");
}

#[test]
fn no_disengaging_allows_entity_leaves_reach() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let (state, fighter, goblin) = standard_combatants();

    // No Disengaging condition — reaction should be triggerable
    let payload = Value::Struct {
        name: "__event_entity_leaves_reach".into(),
        fields: {
            let mut f = BTreeMap::new();
            f.insert("reactor".into(), Value::Entity(fighter));
            f.insert("entity".into(), Value::Entity(goblin));
            f.insert("from_position".into(), GridPosition(1, 0).to_value());
            f.insert("to_position".into(), GridPosition(2, 0).to_value());
            f
        },
    };

    let event_result = interp
        .what_triggers(&state, "entity_leaves_reach", payload, &[fighter])
        .unwrap();

    assert_eq!(event_result.triggerable.len(), 1);
    assert_eq!(event_result.triggerable[0].name, "OpportunityAttack");
    assert!(event_result.suppressed.is_empty());
}

// ════════════════════════════════════════════════════════════════
// Group 8: StateAdapter Integration
// ════════════════════════════════════════════════════════════════

#[test]
fn adapter_attack_applies_damage() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let (state, fighter, goblin) = standard_combatants();
    let longsword = EntityRef(1);

    // Wrap GameState in StateAdapter
    let adapter = StateAdapter::new(state);

    // Script rolls: attack roll hits, damage roll = 7
    // Adapter intercepts MutateField, so handler sees:
    // ActionStarted(Ack), RequiresCheck(Ack), DeductCost(Ack), RollDice(atk), RollDice(dmg), ActionCompleted(Ack)
    let atk_roll = scripted_roll(1, 20, None, 6, vec![14], vec![14], 20, 14);
    let dmg_roll = scripted_roll(1, 8, None, 3, vec![4], vec![4], 7, 4);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged,
        Response::Acknowledged,
        Response::Acknowledged,
        atk_roll,
        dmg_roll,
    ]);

    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "Attack",
                fighter,
                vec![Value::Entity(goblin), Value::Entity(longsword)],
            )
            .unwrap();
    });

    // Verify DeductCost WAS passed through (decision effect)
    assert!(handler
        .log
        .iter()
        .any(|e| matches!(e, Effect::DeductCost { .. })));

    // Verify MutateField was NOT passed through (intercepted by adapter)
    assert!(!handler
        .log
        .iter()
        .any(|e| matches!(e, Effect::MutateField { .. })));

    // Verify target's HP was decremented in the GameState
    let final_state = adapter.into_inner();
    let hp = final_state.read_field(&goblin, "HP").unwrap();
    // Original HP was 7, damage was 7, clamped to bounds(0..7) → 0
    assert_eq!(hp, Value::Int(0));
}
