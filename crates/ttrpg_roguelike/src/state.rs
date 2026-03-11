use rand::Rng;
use rand::rngs::StdRng;
use std::collections::BTreeMap;

use ttrpg_ast::DiceFilter;
use ttrpg_ast::Name;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::{GameState, GridPosition};
use ttrpg_interp::state::{EntityRef, StateProvider};
use ttrpg_interp::value::{DiceExpr, RollResult, Value};

// ── RoguelikeHandler ────────────────────────────────────────────

/// Effect handler for the roguelike host.
///
/// Handles dice rolling via RNG. Mutation effects are intercepted
/// by StateAdapter before reaching this handler, so we only see
/// non-mutation effects here (RollDice, ActionStarted, etc.).
pub struct RoguelikeHandler {
    pub rng: StdRng,
    pub log: Vec<String>,
}

impl RoguelikeHandler {
    pub fn new(rng: StdRng) -> Self {
        RoguelikeHandler {
            rng,
            log: Vec::new(),
        }
    }
}

impl EffectHandler for RoguelikeHandler {
    fn handle(&mut self, effect: Effect) -> Response {
        match effect {
            Effect::RollDice { expr } => {
                let result = roll_dice(&mut self.rng, &expr);
                Response::Rolled(result)
            }
            _ => Response::Acknowledged,
        }
    }
}

// ── Dice rolling ────────────────────────────────────────────────

fn roll_dice(rng: &mut StdRng, expr: &DiceExpr) -> RollResult {
    let mut all_dice = Vec::new();
    let mut all_kept = Vec::new();

    for group in &expr.groups {
        let sides = (group.sides as i64).max(1);
        let mut dice: Vec<i64> = (0..group.count)
            .map(|_| rng.random_range(1..=sides))
            .collect();
        let kept = apply_dice_filter(&mut dice, &group.filter);
        all_dice.extend(&dice);
        all_kept.extend(&kept);
    }

    let unmodified: i64 = all_kept.iter().sum();
    let total = unmodified + expr.modifier;

    RollResult {
        expr: expr.clone(),
        dice: all_dice,
        kept: all_kept,
        modifier: expr.modifier,
        total,
        unmodified,
    }
}

fn apply_dice_filter(dice: &mut [i64], filter: &Option<DiceFilter>) -> Vec<i64> {
    match filter {
        None => dice.to_owned(),
        Some(f) => {
            let mut sorted = dice.to_owned();
            sorted.sort_unstable();
            match f {
                DiceFilter::KeepHighest(n) => sorted.into_iter().rev().take(*n as usize).collect(),
                DiceFilter::KeepLowest(n) => sorted.into_iter().take(*n as usize).collect(),
                DiceFilter::DropHighest(n) => {
                    let keep = sorted.len().saturating_sub(*n as usize);
                    sorted.into_iter().take(keep).collect()
                }
                DiceFilter::DropLowest(n) => {
                    let skip = (*n as usize).min(sorted.len());
                    sorted.into_iter().skip(skip).collect()
                }
            }
        }
    }
}

// ── Entity helpers ──────────────────────────────────────────────

/// Create a Creature entity in the game state.
pub fn spawn_creature(
    state: &mut GameState,
    name: &str,
    kind: &str,
    pos: (i64, i64),
    hp: i64,
    ac: i64,
    attack_bonus: i64,
    damage: DiceExpr,
) -> EntityRef {
    use rustc_hash::FxHashMap;

    let mut fields = FxHashMap::default();
    fields.insert(Name::from("name"), Value::Str(name.into()));
    fields.insert(
        Name::from("kind"),
        Value::EnumVariant {
            enum_name: Name::from("CreatureKind"),
            variant: Name::from(kind),
            fields: BTreeMap::new(),
        },
    );
    fields.insert(
        Name::from("position"),
        state.register_position(GridPosition(pos.0, pos.1)),
    );
    fields.insert(Name::from("HP"), Value::Int(hp));
    fields.insert(Name::from("max_HP"), Value::Int(hp));
    fields.insert(Name::from("AC"), Value::Int(ac));
    fields.insert(Name::from("attack_bonus"), Value::Int(attack_bonus));
    fields.insert(Name::from("damage"), Value::DiceExpr(damage));
    fields.insert(Name::from("speed"), Value::Int(30));

    state.add_entity("Creature", fields)
}

/// Update a creature's position in the game state.
pub fn set_position(state: &mut GameState, entity: &EntityRef, x: i64, y: i64) {
    use ttrpg_interp::effect::FieldPathSegment;
    use ttrpg_interp::state::WritableState;

    let pos_val = state.register_position(GridPosition(x, y));
    state.write_field(
        entity,
        &[FieldPathSegment::Field(Name::from("position"))],
        pos_val,
    );
}

/// Read a creature's current position as (x, y).
pub fn read_position(state: &dyn StateProvider, entity: &EntityRef) -> Option<(i64, i64)> {
    match state.read_field(entity, "position")? {
        Value::Position(pv) => state.resolve_position(pv.0),
        _ => None,
    }
}

/// Read a creature's current HP.
pub fn read_hp(state: &dyn StateProvider, entity: &EntityRef) -> i64 {
    match state.read_field(entity, "HP") {
        Some(Value::Int(hp)) => hp,
        _ => 0,
    }
}

/// Read a creature's name.
pub fn read_name(state: &dyn StateProvider, entity: &EntityRef) -> String {
    match state.read_field(entity, "name") {
        Some(Value::Str(s)) => s,
        _ => format!("Entity({})", entity.0),
    }
}
