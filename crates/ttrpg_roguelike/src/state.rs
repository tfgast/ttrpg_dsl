use rand::Rng;
use rand::rngs::StdRng;

use ttrpg_ast::DiceFilter;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
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
}

impl RoguelikeHandler {
    pub fn new(rng: StdRng) -> Self {
        RoguelikeHandler { rng }
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
