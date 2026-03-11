//! Shared helpers for OSRIC integration tests.
//!
//! Extracts duplicated value constructors, extractors, handlers, and entity
//! builders that appear across the 10 `osric_*_integration.rs` test files.
#![allow(dead_code)]

use std::collections::{BTreeMap, VecDeque};

use rustc_hash::FxHashMap;
use ttrpg_ast::Name;
use ttrpg_ast::diagnostic::Severity;
use ttrpg_interp::Interpreter;
use ttrpg_interp::adapter::StateAdapter;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::ConditionArgs;
use ttrpg_interp::state::{EntityRef, StateProvider, WritableState};
use ttrpg_interp::value::{DiceExpr, RollResult, Value};

// ── Compilation ────────────────────────────────────────────────

/// Compile multiple OSRIC source files through the full pipeline.
pub fn compile_osric_sources(
    sources: Vec<(String, String)>,
) -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
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

// ── Value constructors ─────────────────────────────────────────

pub fn enum_variant(enum_name: &str, variant: &str) -> Value {
    Value::EnumVariant {
        enum_name: Name::from(enum_name),
        variant: Name::from(variant),
        fields: BTreeMap::new(),
    }
}

pub fn enum_variant_with(enum_name: &str, variant: &str, fields: BTreeMap<Name, Value>) -> Value {
    Value::EnumVariant {
        enum_name: Name::from(enum_name),
        variant: Name::from(variant),
        fields,
    }
}

pub fn ability(variant: &str) -> Value {
    enum_variant("Ability", variant)
}

pub fn ancestry(variant: &str) -> Value {
    enum_variant("Ancestry", variant)
}

pub fn class_variant(variant: &str) -> Value {
    enum_variant("Class", variant)
}

pub fn feet(value: i64) -> Value {
    Value::Struct {
        name: Name::from("Feet"),
        fields: {
            let mut f = BTreeMap::new();
            f.insert(Name::from("value"), Value::Int(value));
            f
        },
    }
}

pub fn tier(variant: &str) -> Value {
    enum_variant("EncumbranceTier", variant)
}

pub fn action_type(variant: &str) -> Value {
    enum_variant("DeclaredActionType", variant)
}

pub fn melee_variant(variant: &str) -> Value {
    enum_variant("MeleeWeapon", variant)
}

pub fn missile_variant(variant: &str) -> Value {
    enum_variant("MissileWeapon", variant)
}

pub fn armour_variant(variant: &str) -> Value {
    enum_variant("ArmourType", variant)
}

pub fn shield_variant(variant: &str) -> Value {
    enum_variant("ShieldType", variant)
}

/// Construct an `option<Armor>` value with the given ArmourType variant.
pub fn worn_armor(armour_type: &str) -> Value {
    worn_armor_magic(armour_type, 0)
}

/// Construct an `option<Armor>` value with the given ArmourType variant and magic bonus.
pub fn worn_armor_magic(armour_type: &str, magic_bonus: i64) -> Value {
    Value::Option(Some(Box::new(Value::Struct {
        name: Name::from("Armor"),
        fields: {
            let mut f = BTreeMap::new();
            f.insert(
                Name::from("armour_type"),
                enum_variant("ArmourType", armour_type),
            );
            f.insert(Name::from("magic_bonus"), Value::Int(magic_bonus));
            f
        },
    })))
}

/// Construct an `option<Shield>` value with the given ShieldType variant.
pub fn worn_shield(shield_type: &str) -> Value {
    worn_shield_magic(shield_type, 0)
}

/// Construct an `option<Shield>` value with the given ShieldType variant and magic bonus.
pub fn worn_shield_magic(shield_type: &str, magic_bonus: i64) -> Value {
    Value::Option(Some(Box::new(Value::Struct {
        name: Name::from("Shield"),
        fields: {
            let mut f = BTreeMap::new();
            f.insert(
                Name::from("shield_type"),
                enum_variant("ShieldType", shield_type),
            );
            f.insert(Name::from("magic_bonus"), Value::Int(magic_bonus));
            f
        },
    })))
}

/// Construct an `option<WieldedItem>` for a melee weapon.
pub fn wielded_melee_item(weapon: &str) -> Value {
    wielded_melee_item_magic(weapon, 0)
}

/// Construct an `option<WieldedItem>` for a melee weapon with magic bonus.
pub fn wielded_melee_item_magic(weapon: &str, magic_bonus: i64) -> Value {
    wielded_melee_item_full(weapon, magic_bonus, "Normal")
}

/// Construct an `option<WieldedItem>` for a melee weapon with magic bonus and material.
pub fn wielded_melee_item_full(weapon: &str, magic_bonus: i64, material: &str) -> Value {
    Value::Option(Some(Box::new(Value::EnumVariant {
        enum_name: Name::from("WieldedItem"),
        variant: Name::from("Melee"),
        fields: {
            let mut f = BTreeMap::new();
            f.insert(Name::from("weapon"), enum_variant("MeleeWeapon", weapon));
            f.insert(Name::from("magic_bonus"), Value::Int(magic_bonus));
            f.insert(
                Name::from("material"),
                enum_variant("WeaponMaterial", material),
            );
            f
        },
    })))
}

/// Construct an `option<WieldedItem>` for a missile weapon.
pub fn wielded_missile_item(weapon: &str) -> Value {
    wielded_missile_item_magic(weapon, 0)
}

/// Construct an `option<WieldedItem>` for a missile weapon with magic bonus.
pub fn wielded_missile_item_magic(weapon: &str, magic_bonus: i64) -> Value {
    wielded_missile_item_full(weapon, magic_bonus, "Normal")
}

/// Construct an `option<WieldedItem>` for a missile weapon with magic bonus and material.
pub fn wielded_missile_item_full(weapon: &str, magic_bonus: i64, material: &str) -> Value {
    Value::Option(Some(Box::new(Value::EnumVariant {
        enum_name: Name::from("WieldedItem"),
        variant: Name::from("Missile"),
        fields: {
            let mut f = BTreeMap::new();
            f.insert(Name::from("weapon"), enum_variant("MissileWeapon", weapon));
            f.insert(Name::from("magic_bonus"), Value::Int(magic_bonus));
            f.insert(
                Name::from("material"),
                enum_variant("WeaponMaterial", material),
            );
            f
        },
    })))
}

/// Map an AC value to the appropriate `option<Armor>`.
/// Standard armor ACs: 10(none), 12(Leather), 13(StuddedLeather),
/// 14(ScaleLamellar), 15(ChainMail), 16(Banded), 17(PlateMail).
pub fn armor_for_ac(ac: i64) -> Value {
    match ac {
        10 => Value::Option(None),
        12 => worn_armor("Leather"),
        13 => worn_armor("StuddedLeather"),
        14 => worn_armor("ScaleLamellar"),
        15 => worn_armor("ChainMail"),
        16 => worn_armor("Banded"),
        17 => worn_armor("PlateMail"),
        _ => panic!("No standard armor for AC {ac}; use worn_armor() directly"),
    }
}

/// Map an armour movement cap to an appropriate armor type.
pub fn armor_for_movement_cap(cap: i64) -> Value {
    match cap {
        0 => Value::Option(None),
        60 => worn_armor("PlateMail"),
        90 => worn_armor("ChainMail"),
        120 => worn_armor("Leather"),
        _ => panic!("No standard armor for movement cap {cap}ft"),
    }
}

/// Read a field from inside an included group on an entity.
pub fn read_group_field(
    state: &GameState,
    entity: &EntityRef,
    group: &str,
    field: &str,
) -> Option<Value> {
    if let Some(Value::Struct { fields, .. }) = state.read_field(entity, group) {
        fields.get(field).cloned()
    } else {
        None
    }
}

/// Build a HitPoints include-group struct value.
pub fn hit_points_group(max_hp: i64) -> Value {
    Value::Struct {
        name: Name::from("HitPoints"),
        fields: {
            let mut f = BTreeMap::new();
            f.insert(Name::from("max_hp"), Value::Int(max_hp));
            f.insert(Name::from("hp"), Value::Int(max_hp));
            f
        },
    }
}

/// Build an EquipmentSlots include-group struct value.
pub fn equipment_slots_group(worn_armor: Value, worn_shield: Value) -> Value {
    equipment_slots_group_full(
        Value::Option(None),
        Value::Option(None),
        worn_armor,
        worn_shield,
    )
}

/// Build an EquipmentSlots include-group struct value with weapon slots.
pub fn equipment_slots_group_full(
    wielded_main: Value,
    wielded_off: Value,
    worn_armor: Value,
    worn_shield: Value,
) -> Value {
    Value::Struct {
        name: Name::from("EquipmentSlots"),
        fields: {
            let mut f = BTreeMap::new();
            f.insert(Name::from("wielded_main"), wielded_main);
            f.insert(Name::from("wielded_off"), wielded_off);
            f.insert(Name::from("worn_armor"), worn_armor);
            f.insert(Name::from("worn_shield"), worn_shield);
            f.insert(Name::from("current_weight"), Value::Int(0));
            f
        },
    }
}

/// Build an Inventory optional-group value with items in loose_items.
pub fn inventory_group(loose_items: Vec<Value>) -> Value {
    Value::Struct {
        name: Name::from("Inventory"),
        fields: {
            let mut f = BTreeMap::new();
            f.insert(
                Name::from("coins"),
                Value::Struct {
                    name: Name::from("CoinPurse"),
                    fields: {
                        let mut cp = BTreeMap::new();
                        cp.insert(Name::from("cp"), Value::Int(0));
                        cp.insert(Name::from("sp"), Value::Int(0));
                        cp.insert(Name::from("ep"), Value::Int(0));
                        cp.insert(Name::from("gp"), Value::Int(0));
                        cp.insert(Name::from("pp"), Value::Int(0));
                        cp
                    },
                },
            );
            f.insert(Name::from("containers"), Value::List(vec![]));
            f.insert(Name::from("loose_items"), Value::List(loose_items));
            f.insert(Name::from("coin_xp_ledger"), Value::Int(0));
            f
        },
    }
}

/// Build an Item struct value (for inventory).
pub fn item_value(name: &str, weight: i64, gp_value: i64) -> Value {
    Value::Struct {
        name: Name::from("Item"),
        fields: {
            let mut f = BTreeMap::new();
            f.insert(Name::from("name"), Value::Str(name.to_string()));
            f.insert(Name::from("weight"), Value::Int(weight));
            f.insert(Name::from("cost_cp"), Value::Int(gp_value * 100));
            f.insert(Name::from("quantity"), Value::Int(1));
            f.insert(Name::from("gp_value"), Value::Int(gp_value));
            f.insert(Name::from("xp_awarded"), Value::Bool(false));
            f
        },
    }
}

/// Build a Character with Inventory group and optional equipment.
#[allow(clippy::too_many_arguments)]
pub fn make_character_with_inventory(
    state: &mut GameState,
    name: &str,
    class: &str,
    level: i64,
    abilities: &[(&str, i64)],
    max_hp: i64,
    ac: i64,
    ancestry: &str,
    loose_items: Vec<Value>,
) -> EntityRef {
    let mut ability_map = BTreeMap::new();
    for &(ab, score) in abilities {
        ability_map.insert(ability(ab), Value::Int(score));
    }

    let mut fields = FxHashMap::default();
    fields.insert(Name::from("name"), Value::Str(name.to_string()));
    fields.insert(
        Name::from("classes"),
        Value::List(vec![class_level_struct(class, level, 0)]),
    );
    fields.insert(Name::from("classing_mode"), classing_mode("Single"));
    fields.insert(Name::from("ancestry"), enum_variant("Ancestry", ancestry));
    fields.insert(
        Name::from("alignment"),
        enum_variant("Alignment", "TrueNeutral"),
    );
    fields.insert(Name::from("abilities"), Value::Map(ability_map));
    fields.insert(Name::from("HitPoints"), hit_points_group(max_hp));
    fields.insert(Name::from("base_movement"), feet(120));
    fields.insert(Name::from("saving_throws"), Value::Option(None));
    fields.insert(
        Name::from("EquipmentSlots"),
        equipment_slots_group(armor_for_ac(ac), Value::Option(None)),
    );
    fields.insert(Name::from("Inventory"), inventory_group(loose_items));

    state.add_entity("Character", fields)
}

pub fn class_level_struct(class: &str, level: i64, xp: i64) -> Value {
    Value::Struct {
        name: Name::from("ClassLevel"),
        fields: {
            let mut f = BTreeMap::new();
            f.insert(Name::from("class"), class_variant(class));
            f.insert(Name::from("level"), Value::Int(level));
            f.insert(Name::from("xp"), Value::Int(xp));
            f
        },
    }
}

pub fn classing_mode(variant: &str) -> Value {
    enum_variant("ClassingMode", variant)
}

/// Build a multi-classed Character entity with multiple ClassLevel entries.
pub fn make_multiclass_character(
    state: &mut GameState,
    name: &str,
    classes: &[(&str, i64)],
    ancestry_name: &str,
) -> EntityRef {
    let mut ability_map = BTreeMap::new();
    for &(ab, score) in &standard_abilities_14() {
        ability_map.insert(ability(ab), Value::Int(score));
    }

    let class_levels: Vec<Value> = classes
        .iter()
        .map(|(c, l)| class_level_struct(c, *l, 0))
        .collect();

    let mode = if classes.len() > 1 { "Multi" } else { "Single" };

    let mut fields = FxHashMap::default();
    fields.insert(Name::from("name"), Value::Str(name.to_string()));
    fields.insert(Name::from("classes"), Value::List(class_levels));
    fields.insert(Name::from("classing_mode"), classing_mode(mode));
    fields.insert(
        Name::from("ancestry"),
        enum_variant("Ancestry", ancestry_name),
    );
    fields.insert(
        Name::from("alignment"),
        enum_variant("Alignment", "TrueNeutral"),
    );
    fields.insert(Name::from("abilities"), Value::Map(ability_map));
    fields.insert(Name::from("HitPoints"), hit_points_group(20));
    fields.insert(Name::from("base_movement"), feet(120));

    fields.insert(Name::from("saving_throws"), Value::Option(None));
    fields.insert(
        Name::from("EquipmentSlots"),
        equipment_slots_group(Value::Option(None), Value::Option(None)),
    );

    state.add_entity("Character", fields)
}

/// Build a dual-classed Character entity with old class and new class entries.
/// Abilities are provided explicitly (dual-class tests need specific scores).
pub fn make_dualclass_character(
    state: &mut GameState,
    name: &str,
    old_class: &str,
    old_level: i64,
    new_class: &str,
    new_level: i64,
    abilities: &[(&str, i64)],
) -> EntityRef {
    let mut ability_map = BTreeMap::new();
    for &(ab, score) in abilities {
        ability_map.insert(ability(ab), Value::Int(score));
    }

    let class_levels = vec![
        class_level_struct(old_class, old_level, 0),
        class_level_struct(new_class, new_level, 0),
    ];

    let mut fields = FxHashMap::default();
    fields.insert(Name::from("name"), Value::Str(name.to_string()));
    fields.insert(Name::from("classes"), Value::List(class_levels));
    fields.insert(Name::from("classing_mode"), classing_mode("Dual"));
    fields.insert(Name::from("ancestry"), enum_variant("Ancestry", "Human"));
    fields.insert(
        Name::from("alignment"),
        enum_variant("Alignment", "TrueNeutral"),
    );
    fields.insert(Name::from("abilities"), Value::Map(ability_map));
    fields.insert(Name::from("HitPoints"), hit_points_group(20));
    fields.insert(Name::from("base_movement"), feet(120));

    fields.insert(Name::from("saving_throws"), Value::Option(None));
    fields.insert(
        Name::from("EquipmentSlots"),
        equipment_slots_group(Value::Option(None), Value::Option(None)),
    );

    state.add_entity("Character", fields)
}

/// Standard abilities all at 14 (for multi-class tests).
pub fn standard_abilities_14() -> Vec<(&'static str, i64)> {
    vec![
        ("STR", 14),
        ("DEX", 14),
        ("CON", 14),
        ("INT", 14),
        ("WIS", 14),
        ("CHA", 14),
    ]
}

pub fn monster_attack(name: &str, count: u32, sides: u32, bonus: i64) -> Value {
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

pub fn ability_map(scores: &[(&str, i64)]) -> Value {
    let mut map = BTreeMap::new();
    for &(ab, score) in scores {
        map.insert(ability(ab), Value::Int(score));
    }
    Value::Map(map)
}

/// Turn budget for OSRIC combat: just `action` token.
pub fn combat_turn_budget() -> BTreeMap<Name, Value> {
    let mut b = BTreeMap::new();
    b.insert("action".into(), Value::Int(1));
    b
}

// ── Extractors ─────────────────────────────────────────────────

pub fn expect_int(val: Value, ctx: &str) -> i64 {
    match val {
        Value::Int(n) => n,
        other => panic!("{ctx}: expected Int, got {other:?}"),
    }
}

pub fn expect_bool(val: Value, ctx: &str) -> bool {
    match val {
        Value::Bool(b) => b,
        other => panic!("{ctx}: expected Bool, got {other:?}"),
    }
}

pub fn expect_feet(val: Value, ctx: &str) -> i64 {
    match val {
        Value::Struct { name, fields } => {
            assert_eq!(&*name, "Feet", "{ctx}: expected Feet struct");
            match fields.get::<Name>(&"value".into()) {
                Some(Value::Int(n)) => *n,
                other => panic!("{ctx}: expected Feet.value Int, got {other:?}"),
            }
        }
        other => panic!("{ctx}: expected Feet struct, got {other:?}"),
    }
}

pub fn field<'a>(fields: &'a BTreeMap<Name, Value>, key: &str) -> Option<&'a Value> {
    fields.get::<Name>(&key.into())
}

pub fn get_int(fields: &BTreeMap<String, Value>, key: &str) -> i64 {
    match fields.get(key) {
        Some(Value::Int(n)) => *n,
        other => panic!("expected int for '{key}', got: {other:?}"),
    }
}

pub fn get_bool(fields: &BTreeMap<String, Value>, key: &str) -> bool {
    match fields.get(key) {
        Some(Value::Bool(b)) => *b,
        other => panic!("expected bool for '{key}', got: {other:?}"),
    }
}

// ── Handlers ───────────────────────────────────────────────────

pub struct NullHandler;
impl EffectHandler for NullHandler {
    fn handle(&mut self, _effect: Effect) -> Response {
        Response::Acknowledged
    }
}

pub struct ScriptedHandler {
    pub script: VecDeque<Response>,
    pub log: Vec<Effect>,
}

impl ScriptedHandler {
    pub fn with_responses(responses: Vec<Response>) -> Self {
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

pub fn scripted_roll(
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

// ── Roll helpers ────────────────────────────────────────────────

/// Handler that returns scripted Rolled responses for RollDice effects
/// and Acknowledged for everything else.
pub struct RollHandler {
    pub rolls: VecDeque<Response>,
}

impl RollHandler {
    pub fn new(rolls: Vec<Response>) -> Self {
        RollHandler {
            rolls: rolls.into(),
        }
    }
}

impl EffectHandler for RollHandler {
    fn handle(&mut self, effect: Effect) -> Response {
        match effect {
            Effect::RollDice { .. } => self
                .rolls
                .pop_front()
                .expect("RollHandler: ran out of scripted rolls"),
            _ => Response::Acknowledged,
        }
    }
}

pub fn run_function_with_rolls(
    interp: &Interpreter,
    state: GameState,
    rolls: Vec<Response>,
    func: &str,
    args: Vec<Value>,
) -> GameState {
    let mut handler = RollHandler::new(rolls);
    let adapter = StateAdapter::new(state);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .evaluate_function(state, eff_handler, func, args)
            .unwrap();
    });
    adapter.into_inner()
}

pub fn run_function(
    interp: &Interpreter,
    state: GameState,
    handler: &mut ScriptedHandler,
    func: &str,
    args: Vec<Value>,
) -> GameState {
    let adapter = StateAdapter::new(state);
    adapter.run(handler, |state, eff_handler| {
        interp
            .evaluate_function(state, eff_handler, func, args)
            .unwrap();
    });
    adapter.into_inner()
}

pub fn run_action(
    interp: &Interpreter,
    state: GameState,
    handler: &mut ScriptedHandler,
    action: &str,
    actor: EntityRef,
    args: Vec<Value>,
) -> GameState {
    let adapter = StateAdapter::new(state);
    adapter.run(handler, |state, eff_handler| {
        interp
            .execute_action(state, eff_handler, action, actor, args)
            .unwrap();
    });
    adapter.into_inner()
}

pub fn roll_save(val: i64) -> Response {
    scripted_roll(1, 20, 0, vec![val], vec![val], val, val)
}

pub fn read_hp(state: &GameState, entity: &EntityRef) -> i64 {
    let val = read_group_field(state, entity, "HitPoints", "hp")
        .expect("entity should have HitPoints.hp");
    match val {
        Value::Int(n) => n,
        other => panic!("expected int for hp, got {other:?}"),
    }
}

// ── Entity builders ────────────────────────────────────────────

pub fn standard_abilities() -> Vec<(&'static str, i64)> {
    vec![
        ("STR", 10),
        ("DEX", 10),
        ("CON", 10),
        ("INT", 10),
        ("WIS", 10),
        ("CHA", 10),
    ]
}

/// Standard abilities with all 12s (no modifiers) — used by combat/conditions/initiative.
pub fn standard_abilities_12() -> Vec<(&'static str, i64)> {
    vec![
        ("STR", 12),
        ("DEX", 12),
        ("CON", 12),
        ("INT", 12),
        ("WIS", 12),
        ("CHA", 12),
    ]
}

/// Build a Character for combat/conditions/initiative tests (full params).
#[allow(clippy::too_many_arguments)]
pub fn make_character(
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
    fields.insert(
        Name::from("classes"),
        Value::List(vec![class_level_struct(class, level, 0)]),
    );
    fields.insert(Name::from("classing_mode"), classing_mode("Single"));
    fields.insert(Name::from("ancestry"), enum_variant("Ancestry", ancestry));
    fields.insert(
        Name::from("alignment"),
        enum_variant("Alignment", "TrueNeutral"),
    );
    fields.insert(Name::from("abilities"), Value::Map(ability_map));
    fields.insert(Name::from("HitPoints"), hit_points_group(max_hp));
    fields.insert(Name::from("base_movement"), feet(120));

    fields.insert(Name::from("saving_throws"), Value::Option(None));
    fields.insert(
        Name::from("EquipmentSlots"),
        equipment_slots_group(armor_for_ac(ac), Value::Option(None)),
    );

    state.add_entity("Character", fields)
}

/// Build a Character with a weapon equipped and optional magic bonus.
#[allow(clippy::too_many_arguments)]
pub fn make_armed_character(
    state: &mut GameState,
    name: &str,
    class: &str,
    level: i64,
    abilities: &[(&str, i64)],
    max_hp: i64,
    worn_armor_val: Value,
    worn_shield_val: Value,
    wielded_main: Value,
    ancestry: &str,
) -> EntityRef {
    let mut ability_map = BTreeMap::new();
    for &(ab, score) in abilities {
        ability_map.insert(ability(ab), Value::Int(score));
    }

    let mut fields = FxHashMap::default();
    fields.insert(Name::from("name"), Value::Str(name.to_string()));
    fields.insert(
        Name::from("classes"),
        Value::List(vec![class_level_struct(class, level, 0)]),
    );
    fields.insert(Name::from("classing_mode"), classing_mode("Single"));
    fields.insert(Name::from("ancestry"), enum_variant("Ancestry", ancestry));
    fields.insert(
        Name::from("alignment"),
        enum_variant("Alignment", "TrueNeutral"),
    );
    fields.insert(Name::from("abilities"), Value::Map(ability_map));
    fields.insert(Name::from("HitPoints"), hit_points_group(max_hp));
    fields.insert(Name::from("base_movement"), feet(120));

    fields.insert(Name::from("saving_throws"), Value::Option(None));
    fields.insert(
        Name::from("EquipmentSlots"),
        equipment_slots_group_full(
            wielded_main,
            Value::Option(None),
            worn_armor_val,
            worn_shield_val,
        ),
    );

    state.add_entity("Character", fields)
}

/// Build a Character with TurnUndead optional group and configurable alignment.
/// Used for Turn Undead integration tests.
pub fn make_turner(
    state: &mut GameState,
    name: &str,
    class: &str,
    level: i64,
    alignment: &str,
) -> EntityRef {
    let mut ability_map = BTreeMap::new();
    for &(ab, score) in &standard_abilities_12() {
        ability_map.insert(ability(ab), Value::Int(score));
    }

    let mut fields = FxHashMap::default();
    fields.insert(Name::from("name"), Value::Str(name.to_string()));
    fields.insert(
        Name::from("classes"),
        Value::List(vec![class_level_struct(class, level, 0)]),
    );
    fields.insert(Name::from("classing_mode"), classing_mode("Single"));
    fields.insert(Name::from("ancestry"), enum_variant("Ancestry", "Human"));
    fields.insert(
        Name::from("alignment"),
        enum_variant("Alignment", alignment),
    );
    fields.insert(Name::from("abilities"), Value::Map(ability_map));
    fields.insert(Name::from("HitPoints"), hit_points_group(30));
    fields.insert(Name::from("base_movement"), feet(120));

    fields.insert(Name::from("saving_throws"), Value::Option(None));
    fields.insert(
        Name::from("EquipmentSlots"),
        equipment_slots_group(armor_for_ac(15), Value::Option(None)),
    );
    fields.insert(
        Name::from("TurnUndead"),
        Value::Struct {
            name: Name::from("TurnUndead"),
            fields: BTreeMap::new(),
        },
    );

    state.add_entity("Character", fields)
}

/// Build a Character with a shield equipped (SmallShield, +1 AC).
#[allow(clippy::too_many_arguments)]
pub fn make_character_with_shield(
    state: &mut GameState,
    name: &str,
    class: &str,
    level: i64,
    abilities: &[(&str, i64)],
    max_hp: i64,
    ac: i64,
    _shield_ac_bonus: i64,
    ancestry: &str,
) -> EntityRef {
    let mut ability_map = BTreeMap::new();
    for &(ab, score) in abilities {
        ability_map.insert(ability(ab), Value::Int(score));
    }

    let mut fields = FxHashMap::default();
    fields.insert(Name::from("name"), Value::Str(name.to_string()));
    fields.insert(
        Name::from("classes"),
        Value::List(vec![class_level_struct(class, level, 0)]),
    );
    fields.insert(Name::from("classing_mode"), classing_mode("Single"));
    fields.insert(Name::from("ancestry"), enum_variant("Ancestry", ancestry));
    fields.insert(
        Name::from("alignment"),
        enum_variant("Alignment", "TrueNeutral"),
    );
    fields.insert(Name::from("abilities"), Value::Map(ability_map));
    fields.insert(Name::from("HitPoints"), hit_points_group(max_hp));
    fields.insert(Name::from("base_movement"), feet(120));

    fields.insert(Name::from("saving_throws"), Value::Option(None));
    fields.insert(
        Name::from("EquipmentSlots"),
        equipment_slots_group(armor_for_ac(ac), worn_shield("SmallShield")),
    );

    state.add_entity("Character", fields)
}

/// Build a Character with the Spellcasting optional group (for initiative tests).
#[allow(clippy::too_many_arguments)]
pub fn make_caster(
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
    fields.insert(
        Name::from("classes"),
        Value::List(vec![class_level_struct(class, level, 0)]),
    );
    fields.insert(Name::from("classing_mode"), classing_mode("Single"));
    fields.insert(Name::from("ancestry"), enum_variant("Ancestry", ancestry));
    fields.insert(
        Name::from("alignment"),
        enum_variant("Alignment", "TrueNeutral"),
    );
    fields.insert(Name::from("abilities"), Value::Map(ability_map));
    fields.insert(Name::from("HitPoints"), hit_points_group(max_hp));
    fields.insert(Name::from("base_movement"), feet(120));

    fields.insert(Name::from("saving_throws"), Value::Option(None));
    fields.insert(
        Name::from("EquipmentSlots"),
        equipment_slots_group(armor_for_ac(ac), Value::Option(None)),
    );
    fields.insert(
        Name::from("Spellcasting"),
        Value::Struct {
            name: Name::from("Spellcasting"),
            fields: {
                let mut f = BTreeMap::new();
                f.insert(Name::from("concentrating_on"), Value::Option(None));
                f.insert(Name::from("spell_slots"), Value::Map(BTreeMap::new()));
                f.insert(Name::from("slots_used"), Value::Map(BTreeMap::new()));
                f.insert(Name::from("memorised_spells"), Value::List(vec![]));
                f
            },
        },
    );

    state.add_entity("Character", fields)
}

/// Build a Character with the Spellcasting optional group pre-populated with slot data.
/// `slots` is a list of (spell_level, max_slots) pairs.
#[allow(clippy::too_many_arguments)]
pub fn make_caster_with_slots(
    state: &mut GameState,
    name: &str,
    class: &str,
    level: i64,
    abilities: &[(&str, i64)],
    max_hp: i64,
    ac: i64,
    ancestry: &str,
    slots: &[(i64, i64)],
) -> EntityRef {
    let mut ability_map = BTreeMap::new();
    for &(ab, score) in abilities {
        ability_map.insert(ability(ab), Value::Int(score));
    }

    let mut fields = FxHashMap::default();
    fields.insert(Name::from("name"), Value::Str(name.to_string()));
    fields.insert(
        Name::from("classes"),
        Value::List(vec![class_level_struct(class, level, 0)]),
    );
    fields.insert(Name::from("classing_mode"), classing_mode("Single"));
    fields.insert(Name::from("ancestry"), enum_variant("Ancestry", ancestry));
    fields.insert(
        Name::from("alignment"),
        enum_variant("Alignment", "TrueNeutral"),
    );
    fields.insert(Name::from("abilities"), Value::Map(ability_map));
    fields.insert(Name::from("HitPoints"), hit_points_group(max_hp));
    fields.insert(Name::from("base_movement"), feet(120));

    fields.insert(Name::from("saving_throws"), Value::Option(None));
    fields.insert(
        Name::from("EquipmentSlots"),
        equipment_slots_group(armor_for_ac(ac), Value::Option(None)),
    );

    // Build list-based spell slots: index 0 = spell level 1, etc.
    let max_level = slots.iter().map(|&(lvl, _)| lvl).max().unwrap_or(0) as usize;
    let mut spell_slots_list = vec![Value::Int(0); max_level];
    let slots_used_list = vec![Value::Int(0); max_level];
    for &(spell_level, max) in slots {
        spell_slots_list[(spell_level - 1) as usize] = Value::Int(max);
    }

    fields.insert(
        Name::from("Spellcasting"),
        Value::Struct {
            name: Name::from("Spellcasting"),
            fields: {
                let mut f = BTreeMap::new();
                f.insert(Name::from("concentrating_on"), Value::Option(None));
                f.insert(Name::from("spell_slots"), Value::List(spell_slots_list));
                f.insert(Name::from("slots_used"), Value::List(slots_used_list));
                f.insert(Name::from("memorised_spells"), Value::List(vec![]));
                f
            },
        },
    );

    state.add_entity("Character", fields)
}

/// Build a Monster entity.
pub fn make_monster(
    state: &mut GameState,
    name: &str,
    hit_dice: (u32, u32, i64),
    max_hp: i64,
    ac: i64,
    attacks: Vec<Value>,
) -> EntityRef {
    let mut fields = FxHashMap::default();
    fields.insert(Name::from("name"), Value::Str(name.to_string()));
    fields.insert(
        Name::from("hit_dice"),
        Value::DiceExpr(DiceExpr::single(hit_dice.0, hit_dice.1, None, hit_dice.2)),
    );
    fields.insert(Name::from("max_hp"), Value::Int(max_hp));
    fields.insert(Name::from("hp"), Value::Int(max_hp));
    fields.insert(Name::from("ac"), Value::Int(ac));
    fields.insert(Name::from("morale"), Value::Int(7));
    fields.insert(Name::from("morale_checks_made"), Value::Int(0));
    fields.insert(Name::from("xp_value"), Value::Int(0));
    fields.insert(Name::from("intelligence"), Value::Int(1));
    fields.insert(Name::from("attacks"), Value::List(attacks));
    fields.insert(Name::from("size"), enum_variant("Size", "Medium"));
    fields.insert(Name::from("special"), Value::List(vec![]));

    state.add_entity("Monster", fields)
}

/// Build a Character for encumbrance tests (different signature: weight + armour cap).
/// Maps armour_cap to an appropriate worn armor type (0=none, 60=PlateMail, 90=ChainMail, 120=Leather).
pub fn make_encumbrance_character(
    state: &mut GameState,
    name: &str,
    abilities: &[(&str, i64)],
    ancestry_name: &str,
    current_weight: i64,
    armour_cap: i64,
) -> EntityRef {
    let mut ability_map = BTreeMap::new();
    for &(ab, score) in abilities {
        ability_map.insert(ability(ab), Value::Int(score));
    }

    let mut fields = FxHashMap::default();
    fields.insert(Name::from("name"), Value::Str(name.to_string()));
    fields.insert(
        Name::from("classes"),
        Value::List(vec![class_level_struct("Fighter", 1, 0)]),
    );
    fields.insert(Name::from("classing_mode"), classing_mode("Single"));
    fields.insert(
        Name::from("ancestry"),
        enum_variant("Ancestry", ancestry_name),
    );
    fields.insert(
        Name::from("alignment"),
        enum_variant("Alignment", "TrueNeutral"),
    );
    fields.insert(Name::from("abilities"), Value::Map(ability_map));
    fields.insert(Name::from("max_hp"), Value::Int(10));
    fields.insert(Name::from("hp"), Value::Int(10));
    fields.insert(Name::from("base_movement"), feet(120));
    fields.insert(Name::from("current_weight"), Value::Int(current_weight));

    fields.insert(Name::from("saving_throws"), Value::Option(None));
    fields.insert(Name::from("wielded_main"), Value::Option(None));
    fields.insert(Name::from("wielded_off"), Value::Option(None));
    fields.insert(Name::from("worn_armor"), armor_for_movement_cap(armour_cap));
    fields.insert(Name::from("worn_shield"), Value::Option(None));

    state.add_entity("Character", fields)
}

/// Build a Character for ability tests (minimal signature).
pub fn make_ability_character(
    state: &mut GameState,
    name: &str,
    abilities: &[(&str, i64)],
) -> EntityRef {
    let mut ability_map = BTreeMap::new();
    for &(ab, score) in abilities {
        ability_map.insert(ability(ab), Value::Int(score));
    }

    let mut fields = FxHashMap::default();
    fields.insert(Name::from("name"), Value::Str(name.to_string()));
    fields.insert(
        Name::from("classes"),
        Value::List(vec![class_level_struct("Fighter", 1, 0)]),
    );
    fields.insert(Name::from("classing_mode"), classing_mode("Single"));
    fields.insert(Name::from("ancestry"), enum_variant("Ancestry", "Human"));
    fields.insert(
        Name::from("alignment"),
        enum_variant("Alignment", "TrueNeutral"),
    );
    fields.insert(Name::from("abilities"), Value::Map(ability_map));
    fields.insert(Name::from("max_hp"), Value::Int(10));
    fields.insert(Name::from("hp"), Value::Int(10));
    fields.insert(Name::from("base_movement"), feet(120));
    fields.insert(Name::from("current_weight"), Value::Int(0));

    fields.insert(Name::from("saving_throws"), Value::Option(None));
    fields.insert(Name::from("wielded_main"), Value::Option(None));
    fields.insert(Name::from("wielded_off"), Value::Option(None));
    fields.insert(Name::from("worn_armor"), Value::Option(None));
    fields.insert(Name::from("worn_shield"), Value::Option(None));

    state.add_entity("Character", fields)
}

/// Write a top-level field on an entity by name.
pub fn set_field(state: &mut GameState, entity: &EntityRef, field: &str, value: Value) {
    use ttrpg_interp::effect::FieldPathSegment;
    state.write_field(entity, &[FieldPathSegment::Field(field.into())], value);
}

/// Write a field inside a group on an entity (e.g. HitPoints.hp).
pub fn set_group_field(
    state: &mut GameState,
    entity: &EntityRef,
    group: &str,
    field: &str,
    value: Value,
) {
    use ttrpg_interp::effect::FieldPathSegment;
    state.write_field(
        entity,
        &[
            FieldPathSegment::Field(group.into()),
            FieldPathSegment::Field(field.into()),
        ],
        value,
    );
}

/// Build a WeaponSpecialization optional group struct value.
/// `spec_kind` is "SpecMelee" or "SpecMissile".
/// `weapon_enum` is "MeleeWeapon" or "MissileWeapon".
/// `weapon_variant` is the weapon name e.g. "SwordLong".
/// `spec_level` is "Single" or "Double".
pub fn weapon_spec_group(
    spec_kind: &str,
    weapon_enum: &str,
    weapon_variant: &str,
    spec_level: &str,
) -> Value {
    let mut weapon_fields = BTreeMap::new();
    weapon_fields.insert(
        Name::from("weapon"),
        enum_variant(weapon_enum, weapon_variant),
    );
    let spec_weapon = enum_variant_with("SpecWeapon", spec_kind, weapon_fields);

    Value::Struct {
        name: Name::from("WeaponSpecialization"),
        fields: {
            let mut f = BTreeMap::new();
            f.insert(Name::from("spec_weapon"), spec_weapon);
            f.insert(
                Name::from("spec_level"),
                enum_variant("SpecLevel", spec_level),
            );
            f
        },
    }
}

/// Grant weapon specialisation to a character entity.
pub fn grant_weapon_spec(
    state: &mut GameState,
    entity: &EntityRef,
    spec_kind: &str,
    weapon_enum: &str,
    weapon_variant: &str,
    spec_level: &str,
) {
    set_field(
        state,
        entity,
        "WeaponSpecialization",
        weapon_spec_group(spec_kind, weapon_enum, weapon_variant, spec_level),
    );
}

pub fn apply_encumbrance(state: &mut GameState, entity: &EntityRef, tier_variant: &str) {
    let mut params = BTreeMap::new();
    params.insert(Name::from("tier"), tier(tier_variant));
    state.apply_condition(
        entity,
        "EncumbranceState",
        ConditionArgs {
            params,
            duration: Value::Option(None),
            ..Default::default()
        },
    );
}

// ── OSRIC source loading ───────────────────────────────────────

/// Load all OSRIC source files from `osric/ttrpg.toml` (the "full" bundle).
///
/// Reads the manifest at runtime and loads each entry from disk.
pub fn all_osric_sources() -> Vec<(String, String)> {
    load_bundle_sources("osric", "full")
}

/// Workspace root, derived from `CARGO_MANIFEST_DIR` at compile time.
fn workspace_root() -> std::path::PathBuf {
    // CARGO_MANIFEST_DIR for ttrpg_interp is crates/ttrpg_interp
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent() // crates/
        .unwrap()
        .parent() // workspace root
        .unwrap()
        .to_path_buf()
}

/// Load all source files for a given package bundle from its `ttrpg.toml`.
///
/// `pkg_dir` is relative to the workspace root (e.g. `"osric"` or `"ose"`).
pub fn load_bundle_sources(pkg_dir: &str, bundle: &str) -> Vec<(String, String)> {
    let root = workspace_root();
    let pkg_path = root.join(pkg_dir);
    let manifest_path = pkg_path.join("ttrpg.toml");
    let content = std::fs::read_to_string(&manifest_path)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", manifest_path.display()));
    let manifest: toml::Value = content
        .parse()
        .unwrap_or_else(|e| panic!("cannot parse {}: {e}", manifest_path.display()));

    let bundle_entries = manifest["bundles"][bundle]["entries"]
        .as_array()
        .unwrap_or_else(|| panic!("bundle '{bundle}' not found in {}", manifest_path.display()));
    let entries = manifest["entries"]
        .as_table()
        .unwrap_or_else(|| panic!("no [entries] in {}", manifest_path.display()));

    bundle_entries
        .iter()
        .map(|name| {
            let name = name.as_str().unwrap();
            let path = entries[name]["path"].as_str().unwrap();
            let full_path = pkg_path.join(path);
            let display_path = format!("{pkg_dir}/{path}");
            let source = std::fs::read_to_string(&full_path)
                .unwrap_or_else(|e| panic!("cannot read {display_path}: {e}"));
            (display_path, source)
        })
        .collect()
}

// ── SpellTestContext builder ───────────────────────────────────

/// Pre-compiled OSRIC context with a caster entity ready for spell tests.
///
/// Owns `Program` and `CheckResult` so that `interp()` can borrow from them.
/// Reduces the typical 5-8 line setup to 2-3 lines.
///
/// # Example
/// ```ignore
/// let ctx = SpellTestContext::cleric("Alaric", 3, &[(1, 2), (2, 1)]);
/// let interp = ctx.interp();
/// let state = run_function_with_rolls(&interp, ctx.state, rolls, "resolve_cure_light_wounds", args);
/// ```
pub struct SpellTestContext {
    pub program: ttrpg_ast::ast::Program,
    pub check_result: ttrpg_checker::CheckResult,
    pub state: GameState,
    pub caster: EntityRef,
}

impl SpellTestContext {
    /// Build a caster with full customisation.
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        name: &str,
        class: &str,
        level: i64,
        abilities: &[(&str, i64)],
        max_hp: i64,
        ac: i64,
        ancestry: &str,
        slots: &[(i64, i64)],
    ) -> Self {
        let (program, check_result) = compile_osric_sources(all_osric_sources());
        let mut state = GameState::new();
        let caster = make_caster_with_slots(
            &mut state, name, class, level, abilities, max_hp, ac, ancestry, slots,
        );
        Self {
            program,
            check_result,
            state,
            caster,
        }
    }

    /// Shorthand for a Cleric caster with standard abilities (all 12), 20 HP, AC 10, Human.
    pub fn cleric(name: &str, level: i64, slots: &[(i64, i64)]) -> Self {
        Self::new(
            name,
            "Cleric",
            level,
            &standard_abilities_12(),
            20,
            10,
            "Human",
            slots,
        )
    }

    /// Shorthand for a MagicUser caster with standard abilities (all 12), 10 HP, AC 10, Human.
    pub fn magic_user(name: &str, level: i64, slots: &[(i64, i64)]) -> Self {
        Self::new(
            name,
            "MagicUser",
            level,
            &standard_abilities_12(),
            10,
            10,
            "Human",
            slots,
        )
    }

    /// Create an `Interpreter` that borrows from this context.
    pub fn interp(&self) -> Interpreter<'_> {
        Interpreter::new(&self.program, &self.check_result.env).unwrap()
    }

    /// Add a character target to the state and return its entity ref.
    pub fn add_target(
        &mut self,
        name: &str,
        class: &str,
        level: i64,
        max_hp: i64,
        ac: i64,
    ) -> EntityRef {
        make_character(
            &mut self.state,
            name,
            class,
            level,
            &standard_abilities_12(),
            max_hp,
            ac,
            "Human",
        )
    }

    /// Add a monster target to the state and return its entity ref.
    pub fn add_monster(
        &mut self,
        name: &str,
        hit_dice: (u32, u32, i64),
        max_hp: i64,
        ac: i64,
    ) -> EntityRef {
        make_monster(&mut self.state, name, hit_dice, max_hp, ac, vec![])
    }
}

// ── Scenario runners (exercise DSL code paths for coverage) ────

/// Exercise ability table lookups (STR, DEX, CON, INT, WIS, CHA modifiers + ancestry defs).
pub fn run_all_ability(interp: &Interpreter, state: &GameState) {
    let mut handler = NullHandler;

    // STR tables at representative scores
    for score in [3, 10, 16, 18] {
        let _ = interp.evaluate_derive(state, &mut handler, "str_to_hit", vec![Value::Int(score)]);
        let _ = interp.evaluate_derive(state, &mut handler, "str_damage", vec![Value::Int(score)]);
        let _ = interp.evaluate_derive(
            state,
            &mut handler,
            "str_encumbrance",
            vec![Value::Int(score)],
        );
        let _ = interp.evaluate_derive(
            state,
            &mut handler,
            "str_minor_test",
            vec![Value::Int(score)],
        );
        let _ = interp.evaluate_derive(
            state,
            &mut handler,
            "str_major_test",
            vec![Value::Int(score)],
        );
    }

    // Exceptional STR tables
    for pct in [1, 50, 76, 100] {
        let _ =
            interp.evaluate_derive(state, &mut handler, "exc_str_to_hit", vec![Value::Int(pct)]);
        let _ =
            interp.evaluate_derive(state, &mut handler, "exc_str_damage", vec![Value::Int(pct)]);
        let _ = interp.evaluate_derive(
            state,
            &mut handler,
            "exc_str_encumbrance",
            vec![Value::Int(pct)],
        );
    }

    // DEX tables
    for score in [3, 10, 16, 18] {
        let _ =
            interp.evaluate_derive(state, &mut handler, "dex_surprise", vec![Value::Int(score)]);
        let _ = interp.evaluate_derive(state, &mut handler, "dex_missile", vec![Value::Int(score)]);
        let _ = interp.evaluate_derive(state, &mut handler, "dex_ac_adj", vec![Value::Int(score)]);
    }

    // CON tables
    for score in [3, 10, 15, 18] {
        let _ = interp.evaluate_derive(state, &mut handler, "con_hp_adj", vec![Value::Int(score)]);
        let _ = interp.evaluate_derive(
            state,
            &mut handler,
            "con_system_shock",
            vec![Value::Int(score)],
        );
        let _ = interp.evaluate_derive(
            state,
            &mut handler,
            "con_resurrection",
            vec![Value::Int(score)],
        );
    }

    // CHA table
    for score in [3, 10, 16, 18] {
        let _ = interp.evaluate_derive(
            state,
            &mut handler,
            "cha_reaction_adj",
            vec![Value::Int(score)],
        );
    }

    // Ancestry defs
    for anc in [
        "Dwarf", "Elf", "Gnome", "HalfElf", "HalfOrc", "Halfling", "Human",
    ] {
        let _ = interp.evaluate_derive(state, &mut handler, "ancestry_def", vec![ancestry(anc)]);
    }
}

/// Exercise character derives (dex_ac_adj, apply_ancestry_mods, class requirements, etc.).
pub fn run_all_character(interp: &Interpreter, state: &GameState) {
    let mut handler = NullHandler;

    // dex_ac_adj
    for score in [3, 10, 16, 18] {
        let _ = interp.evaluate_derive(state, &mut handler, "dex_ac_adj", vec![Value::Int(score)]);
    }

    // apply_ancestry_mods
    let scores = ability_map(&[
        ("STR", 14),
        ("DEX", 12),
        ("CON", 13),
        ("INT", 10),
        ("WIS", 11),
        ("CHA", 9),
    ]);
    for anc in ["Human", "Dwarf", "Elf", "HalfOrc", "Halfling"] {
        let _ = interp.evaluate_derive(
            state,
            &mut handler,
            "apply_ancestry_mods",
            vec![scores.clone(), ancestry(anc)],
        );
    }

    // validate_ancestry_scores
    let _ = interp.evaluate_derive(
        state,
        &mut handler,
        "validate_ancestry_scores",
        vec![scores.clone(), ancestry("Human")],
    );
    let _ = interp.evaluate_derive(
        state,
        &mut handler,
        "validate_ancestry_scores",
        vec![scores.clone(), ancestry("Dwarf")],
    );

    // meets_class_requirements
    let good_scores = ability_map(&[
        ("STR", 16),
        ("DEX", 16),
        ("CON", 16),
        ("INT", 16),
        ("WIS", 16),
        ("CHA", 17),
    ]);
    for class in [
        "Fighter",
        "Paladin",
        "Ranger",
        "Cleric",
        "Druid",
        "Thief",
        "Assassin",
        "MagicUser",
        "Illusionist",
        "Monk",
    ] {
        let _ = interp.evaluate_derive(
            state,
            &mut handler,
            "meets_class_requirements",
            vec![class_variant(class), good_scores.clone()],
        );
    }

    // prime_req_xp_bonus
    for class in [
        "Fighter",
        "Paladin",
        "Ranger",
        "Cleric",
        "Druid",
        "Thief",
        "MagicUser",
        "Assassin",
        "Illusionist",
        "Monk",
    ] {
        let _ = interp.evaluate_derive(
            state,
            &mut handler,
            "prime_req_xp_bonus",
            vec![class_variant(class), good_scores.clone()],
        );
    }

    // base_movement
    for anc in [
        "Dwarf", "Elf", "Gnome", "HalfElf", "HalfOrc", "Halfling", "Human",
    ] {
        let _ = interp.evaluate_derive(state, &mut handler, "base_movement", vec![ancestry(anc)]);
    }

    // check_ability_in_range
    let range = Value::Struct {
        name: Name::from("AbilityRange"),
        fields: {
            let mut f = BTreeMap::new();
            f.insert(Name::from("min"), Value::Int(8));
            f.insert(Name::from("max"), Value::Int(18));
            f
        },
    };
    let _ = interp.evaluate_derive(
        state,
        &mut handler,
        "check_ability_in_range",
        vec![Value::Int(12), range],
    );
}

/// Exercise class_def and xp_for_level tables for all 10 classes.
pub fn run_all_class(interp: &Interpreter, state: &GameState) {
    let mut handler = NullHandler;

    for class in [
        "Fighter",
        "Paladin",
        "Ranger",
        "Cleric",
        "Druid",
        "Thief",
        "Assassin",
        "MagicUser",
        "Illusionist",
        "Monk",
    ] {
        let _ =
            interp.evaluate_derive(state, &mut handler, "class_def", vec![class_variant(class)]);
        // XP for levels 1, 5, 10
        for level in [1, 5, 10] {
            let _ = interp.evaluate_derive(
                state,
                &mut handler,
                "xp_for_level",
                vec![class_variant(class), Value::Int(level)],
            );
        }
        // check_level_up
        let _ = interp.evaluate_derive(
            state,
            &mut handler,
            "check_level_up",
            vec![class_variant(class), Value::Int(1), Value::Int(2000)],
        );
    }
}

/// Exercise saving throw tables for all classes at representative levels.
pub fn run_all_saves(interp: &Interpreter, state: &GameState) {
    let mut handler = NullHandler;

    for class in [
        "Fighter",
        "Paladin",
        "Ranger",
        "Cleric",
        "Druid",
        "Thief",
        "Assassin",
        "MagicUser",
        "Illusionist",
        "Monk",
    ] {
        for level in [1, 5, 10, 15] {
            let _ = interp.evaluate_derive(
                state,
                &mut handler,
                "saving_throws_for",
                vec![class_variant(class), Value::Int(level)],
            );
        }
    }
}

/// Exercise equipment derives (melee/missile/armour/shield defs, equipment packages).
pub fn run_all_equipment(interp: &Interpreter, state: &GameState) {
    let mut handler = NullHandler;

    // Melee weapon defs
    for weapon in [
        "BattleAxe",
        "Dagger",
        "SwordLong",
        "SwordTwoHanded",
        "Halberd",
        "FlailHeavy",
        "Lance",
        "Club",
        "FistOrKick",
        "SwordBastard",
        "SwordBroad",
    ] {
        let _ = interp.evaluate_derive(
            state,
            &mut handler,
            "melee_weapon_def",
            vec![melee_variant(weapon)],
        );
    }

    // Missile weapon defs
    for weapon in [
        "BowLong",
        "CrossbowHeavy",
        "DaggerThrown",
        "Sling",
        "DartThrown",
        "SlingStone",
        "ClubThrown",
        "JavelinThrown",
    ] {
        let _ = interp.evaluate_derive(
            state,
            &mut handler,
            "missile_weapon_def",
            vec![missile_variant(weapon)],
        );
    }

    // Armour defs
    for armour in [
        "PlateMail",
        "ChainMail",
        "Leather",
        "ElfinMail",
        "Banded",
        "Splint",
    ] {
        let _ = interp.evaluate_derive(
            state,
            &mut handler,
            "armour_def",
            vec![armour_variant(armour)],
        );
    }

    // Shield defs
    for shield in ["SmallShield", "MediumShield", "LargeShield"] {
        let _ = interp.evaluate_derive(
            state,
            &mut handler,
            "shield_def",
            vec![shield_variant(shield)],
        );
    }

    // Equipment packages
    for class in [
        "Fighter",
        "Paladin",
        "Ranger",
        "Cleric",
        "Druid",
        "Thief",
        "Assassin",
        "MagicUser",
        "Illusionist",
        "Monk",
    ] {
        let _ = interp.evaluate_derive(
            state,
            &mut handler,
            "equipment_package",
            vec![class_variant(class)],
        );
        let _ = interp.evaluate_derive(
            state,
            &mut handler,
            "default_starting_armour",
            vec![class_variant(class)],
        );
    }
}

/// Exercise encumbrance derives and conditions.
pub fn run_all_encumbrance(interp: &Interpreter) {
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // encumbrance_tier
    for weight in [0, 1, 40, 41, 80, 81, 120, 121] {
        let _ = interp.evaluate_derive(
            &state,
            &mut handler,
            "encumbrance_tier",
            vec![Value::Int(weight)],
        );
    }

    // encumbrance_movement_numerator
    for t in ["Unencumbered", "Light", "Moderate", "Heavy", "Overloaded"] {
        let _ = interp.evaluate_derive(
            &state,
            &mut handler,
            "encumbrance_movement_numerator",
            vec![tier(t)],
        );
    }

    // effective_str_encumbrance
    let char_ref =
        make_encumbrance_character(&mut state, "Enc-Test", &standard_abilities(), "Human", 0, 0);
    let _ = interp.evaluate_derive(
        &state,
        &mut handler,
        "effective_str_encumbrance",
        vec![Value::Entity(char_ref)],
    );

    // character_encumbrance
    let _ = interp.evaluate_derive(
        &state,
        &mut handler,
        "character_encumbrance",
        vec![Value::Entity(char_ref)],
    );

    // character_movement
    let _ = interp.evaluate_derive(
        &state,
        &mut handler,
        "character_movement",
        vec![Value::Entity(char_ref)],
    );

    // character_movement with encumbrance condition
    for t in ["Unencumbered", "Light", "Moderate", "Heavy", "Overloaded"] {
        let ent = make_encumbrance_character(
            &mut state,
            &format!("Enc-{t}"),
            &standard_abilities(),
            "Human",
            0,
            0,
        );
        apply_encumbrance(&mut state, &ent, t);
        let _ = interp.evaluate_derive(
            &state,
            &mut handler,
            "character_movement",
            vec![Value::Entity(ent)],
        );
    }

    // character_surprise_adj
    let ent2 = make_encumbrance_character(
        &mut state,
        "Surprise-Test",
        &[
            ("STR", 10),
            ("DEX", 16),
            ("CON", 10),
            ("INT", 10),
            ("WIS", 10),
            ("CHA", 10),
        ],
        "Human",
        0,
        0,
    );
    apply_encumbrance(&mut state, &ent2, "Unencumbered");
    let _ = interp.evaluate_derive(
        &state,
        &mut handler,
        "character_surprise_adj",
        vec![Value::Entity(ent2)],
    );

    // update_encumbrance (function)
    let ent3 = make_encumbrance_character(
        &mut state,
        "UpdateEnc",
        &standard_abilities(),
        "Human",
        0,
        0,
    );
    let adapter = StateAdapter::new(state);
    adapter.run(&mut handler, |s, h| {
        let _ = interp.evaluate_function(s, h, "update_encumbrance", vec![Value::Entity(ent3)]);
    });
}

/// Exercise condition defines and their modify clauses.
pub fn run_all_conditions(interp: &Interpreter) {
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Attacker",
        "Fighter",
        5,
        &standard_abilities_12(),
        30,
        15,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        5,
        &standard_abilities_12(),
        30,
        15,
        "Human",
    );
    let _goblin = make_monster(&mut state, "Goblin", (1, 8, 0), 5, 14, vec![]);

    // Apply simple conditions
    for cond in [
        "Prone",
        "Stunned",
        "Staggered",
        "Invisible",
        "Paralyzed",
        "Sleeping",
        "Surprised",
        "RearAttacked",
    ] {
        state.apply_condition(
            &target,
            cond,
            ConditionArgs {
                duration: Value::Option(None),
                ..Default::default()
            },
        );
    }

    // Apply parameterised conditions
    {
        let mut params = BTreeMap::new();
        params.insert(Name::from("level"), Value::Int(2));
        state.apply_condition(
            &target,
            "Concealed",
            ConditionArgs {
                params,
                duration: Value::Option(None),
                ..Default::default()
            },
        );
    }
    {
        let mut params = BTreeMap::new();
        params.insert(Name::from("penalty"), Value::Int(-4));
        state.apply_condition(
            &target,
            "Cover",
            ConditionArgs {
                params,
                duration: Value::Option(None),
                ..Default::default()
            },
        );
    }
    {
        let mut params = BTreeMap::new();
        params.insert(Name::from("parry_bonus"), Value::Int(2));
        state.apply_condition(
            &target,
            "Parrying",
            ConditionArgs {
                params,
                duration: Value::Option(None),
                ..Default::default()
            },
        );
    }

    // Exercise resolve_melee_attack with conditions active
    let roll_hit = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    let roll_dmg = scripted_roll(1, 8, 0, vec![5], vec![5], 5, 5);
    let mut handler = ScriptedHandler::with_responses(vec![
        Response::Acknowledged,
        Response::Acknowledged,
        Response::Acknowledged,
        Response::Acknowledged,
        Response::Acknowledged,
        Response::Acknowledged,
        roll_hit,
        roll_dmg,
    ]);
    let _ = interp.evaluate_mechanic(
        &state,
        &mut handler,
        "resolve_melee_attack",
        vec![
            Value::Entity(attacker),
            Value::Entity(target),
            melee_variant("SwordLong"),
        ],
    );

    // Remove conditions and try again
    state.remove_condition(&target, "Prone", None);
    state.remove_condition(&target, "Invisible", None);
}

/// Exercise combat mechanics (BTHB, attack_roll, damage_roll, resolve_* mechanics).
pub fn run_all_combat(interp: &Interpreter) {
    let mut state = GameState::new();

    let attacker = make_character(
        &mut state,
        "Fighter",
        "Fighter",
        5,
        &standard_abilities_12(),
        30,
        15,
        "Human",
    );
    let target = make_character(
        &mut state,
        "Target",
        "Fighter",
        1,
        &standard_abilities_12(),
        10,
        12,
        "Human",
    );
    let goblin = make_monster(
        &mut state,
        "Goblin",
        (1, 8, 0),
        5,
        14,
        vec![monster_attack("Bite", 1, 6, 0)],
    );

    let mut handler = NullHandler;

    // BTHB tables
    for group in [
        "FighterGroup",
        "ClericGroup",
        "ThiefGroup",
        "MagicUserGroup",
    ] {
        for level in [1, 5, 10, 15, 20] {
            let _ = interp.evaluate_derive(
                &state,
                &mut handler,
                "bthb",
                vec![enum_variant("CombatGroup", group), Value::Int(level)],
            );
        }
    }

    // fighter_attacks
    for level in [1, 7, 13] {
        let _ = interp.evaluate_derive(
            &state,
            &mut handler,
            "fighter_attacks",
            vec![Value::Int(level)],
        );
    }

    // missile_range_penalty
    for dist in [1, 2, 3] {
        let _ = interp.evaluate_derive(
            &state,
            &mut handler,
            "missile_range_penalty",
            vec![Value::Int(dist)],
        );
    }

    // attack_roll_aac
    let _ = interp.evaluate_derive(
        &state,
        &mut handler,
        "attack_roll_aac",
        vec![Value::Int(15), Value::Int(15)],
    );

    // resolve_melee_attack
    let roll_hit = scripted_roll(1, 20, 0, vec![18], vec![18], 18, 18);
    let roll_dmg = scripted_roll(1, 8, 0, vec![6], vec![6], 6, 6);
    let mut handler2 = ScriptedHandler::with_responses(vec![roll_hit, roll_dmg]);
    let _ = interp.evaluate_mechanic(
        &state,
        &mut handler2,
        "resolve_melee_attack",
        vec![
            Value::Entity(attacker),
            Value::Entity(target),
            melee_variant("SwordLong"),
        ],
    );

    // resolve_missile_attack
    let roll_hit = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    let roll_dmg = scripted_roll(1, 6, 0, vec![4], vec![4], 4, 4);
    let mut handler3 = ScriptedHandler::with_responses(vec![roll_hit, roll_dmg]);
    let _ = interp.evaluate_mechanic(
        &state,
        &mut handler3,
        "resolve_missile_attack",
        vec![
            Value::Entity(attacker),
            Value::Entity(target),
            missile_variant("BowLong"),
            Value::Int(1),
        ],
    );

    // resolve_monster_attack
    let roll_hit = scripted_roll(1, 20, 0, vec![15], vec![15], 15, 15);
    let roll_dmg = scripted_roll(1, 6, 0, vec![3], vec![3], 3, 3);
    let mut handler4 = ScriptedHandler::with_responses(vec![roll_hit, roll_dmg]);
    let _ = interp.evaluate_mechanic(
        &state,
        &mut handler4,
        "resolve_monster_attack",
        vec![
            Value::Entity(goblin),
            Value::Entity(target),
            monster_attack("Bite", 1, 6, 0),
        ],
    );

    // damage_roll
    let roll = scripted_roll(1, 8, 0, vec![5], vec![5], 5, 5);
    let mut handler5 = ScriptedHandler::with_responses(vec![roll]);
    let _ = interp.evaluate_mechanic(
        &state,
        &mut handler5,
        "damage_roll",
        vec![
            Value::Entity(attacker),
            melee_variant("SwordLong"),
            enum_variant("Size", "Medium"),
        ],
    );

    // MeleeAttack action (via execute_action)
    let roll_hit = scripted_roll(1, 20, 0, vec![19], vec![19], 19, 19);
    let roll_dmg = scripted_roll(1, 8, 0, vec![4], vec![4], 4, 4);
    let mut handler6 = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, // ModifyApplied
        roll_hit,
        roll_dmg,
        Response::Acknowledged, // Damaged event
        Response::Acknowledged, // MutateField
    ]);
    let adapter = StateAdapter::new(state);
    adapter.run(&mut handler6, |s, h| {
        let _ = interp.execute_action(
            s,
            h,
            "MeleeAttack",
            attacker,
            vec![Value::Entity(target), melee_variant("SwordLong")],
        );
    });
}

/// Exercise initiative derives and mechanics.
pub fn run_all_initiative(interp: &Interpreter) {
    let mut state = GameState::new();
    let mut handler = NullHandler;

    // surprise_duration
    for segments in [1, 2, 3] {
        let _ = interp.evaluate_derive(
            &state,
            &mut handler,
            "surprise_duration",
            vec![Value::Int(segments)],
        );
    }

    // free_surprise_segments
    for segments in [0, 1, 3] {
        let _ = interp.evaluate_derive(
            &state,
            &mut handler,
            "free_surprise_segments",
            vec![Value::Int(segments), Value::Int(0)],
        );
    }

    // wrap_segment
    for seg in [0, 5, 10, 15] {
        let _ = interp.evaluate_derive(&state, &mut handler, "wrap_segment", vec![Value::Int(seg)]);
    }

    // action_segment for each action type
    for at in [
        "Melee", "Missile", "Movement", "SetSpear", "Spell", "Turning", "Other",
    ] {
        let _ = interp.evaluate_derive(
            &state,
            &mut handler,
            "action_segment",
            vec![action_type(at), Value::Int(3), Value::Int(5), Value::Int(0)],
        );
    }

    // missile_init_segment
    let _ = interp.evaluate_derive(
        &state,
        &mut handler,
        "missile_init_segment",
        vec![Value::Int(3), Value::Int(0)],
    );

    // assign_segment
    let _ = interp.evaluate_derive(
        &state,
        &mut handler,
        "assign_segment",
        vec![Value::Int(5), Value::Int(3)],
    );

    // fighter_attack_segments
    for level in [1, 7, 13] {
        let _ = interp.evaluate_derive(
            &state,
            &mut handler,
            "fighter_attack_segments",
            vec![Value::Int(level), Value::Int(5), Value::Int(3)],
        );
    }

    // spell_effect_segment / is_casting_at_segment / spell_completed_at_segment
    let _ = interp.evaluate_derive(
        &state,
        &mut handler,
        "spell_effect_segment",
        vec![Value::Int(3), Value::Int(3)],
    );
    let _ = interp.evaluate_derive(
        &state,
        &mut handler,
        "is_casting_at_segment",
        vec![Value::Int(3), Value::Int(3), Value::Int(5)],
    );
    let _ = interp.evaluate_derive(
        &state,
        &mut handler,
        "spell_completed_at_segment",
        vec![Value::Int(3), Value::Int(3), Value::Int(5)],
    );

    // acts_first_by_speed
    let _ = interp.evaluate_derive(
        &state,
        &mut handler,
        "acts_first_by_speed",
        vec![Value::Int(3), Value::Int(7)],
    );

    // melee_order
    let _ = interp.evaluate_derive(
        &state,
        &mut handler,
        "melee_order",
        vec![Value::Int(3), Value::Int(7), Value::Int(5), Value::Int(5)],
    );

    // movement_per_segment / movement_through_segment
    let _ = interp.evaluate_derive(
        &state,
        &mut handler,
        "movement_per_segment",
        vec![feet(120)],
    );
    let _ = interp.evaluate_derive(
        &state,
        &mut handler,
        "movement_through_segment",
        vec![feet(120), Value::Int(3), Value::Int(5)],
    );

    // roll_surprise (mechanic — needs scripted handler)
    let roll = scripted_roll(1, 6, 0, vec![2], vec![2], 2, 2);
    let mut handler2 = ScriptedHandler::with_responses(vec![roll]);
    let _ = interp.evaluate_mechanic(&state, &mut handler2, "roll_surprise", vec![Value::Int(2)]);

    // roll_initiative
    let roll = scripted_roll(1, 6, 0, vec![4], vec![4], 4, 4);
    let mut handler3 = ScriptedHandler::with_responses(vec![roll]);
    let _ = interp.evaluate_mechanic(&state, &mut handler3, "roll_initiative", vec![]);

    // CastingSpell condition + SpellInterruption hook + BeginCasting action
    let caster = make_caster(
        &mut state,
        "Mage",
        "MagicUser",
        5,
        &standard_abilities_12(),
        10,
        10,
        "Human",
    );
    let _ = make_character(
        &mut state,
        "Target2",
        "Fighter",
        1,
        &standard_abilities_12(),
        10,
        10,
        "Human",
    );

    // BeginCasting action
    let mut handler4 = ScriptedHandler::with_responses(vec![
        Response::Acknowledged, // ModifyApplied
        Response::Acknowledged, // apply_condition
    ]);
    let adapter = StateAdapter::new(state);
    adapter.run(&mut handler4, |s, h| {
        let _ = interp.execute_action(
            s,
            h,
            "BeginCasting",
            caster,
            vec![Value::Int(3), Value::Int(3)],
        );
    });
}
