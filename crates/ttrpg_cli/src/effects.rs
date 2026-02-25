use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap, VecDeque};

use rand::Rng;
use rand::rngs::StdRng;
use ttrpg_ast::DiceFilter;
use ttrpg_ast::ast::AssignOp;
use ttrpg_interp::adapter;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::{EntityRef, StateProvider, WritableState};
use ttrpg_interp::value::{DiceExpr, RollResult, Value};

use crate::format::{format_dice_expr, format_path, format_value};

// ── MinimalHandler ──────────────────────────────────────────────

/// A minimal effect handler for the CLI.
///
/// Acknowledges all informational/mutation/gate effects.
/// Returns `RuntimeError`-inducing responses for `RollDice` and `ResolvePrompt`
/// since the CLI has no RNG or user interaction in Phase 1.
pub struct MinimalHandler;

impl EffectHandler for MinimalHandler {
    fn handle(&mut self, effect: Effect) -> Response {
        match &effect {
            Effect::RollDice { .. } | Effect::ResolvePrompt { .. } => {
                // Phase 1: no RNG or interaction support.
                // Return Vetoed — the interpreter will produce a RuntimeError
                // for RollDice (which requires a Rolled response).
                // For ResolvePrompt, Vetoed similarly signals inability.
                Response::Vetoed
            }
            _ => Response::Acknowledged,
        }
    }
}

// ── RefCellState ────────────────────────────────────────────────

/// A `StateProvider` that delegates to `&RefCell<GameState>` with
/// short-lived borrows.
///
/// Needed because the interpreter takes `&dyn StateProvider` while
/// the `CliHandler` writes to the same `GameState`. The interpreter
/// never reads state during a handler call, so borrows never overlap
/// at runtime.
pub struct RefCellState<'a>(pub &'a RefCell<GameState>);

impl StateProvider for RefCellState<'_> {
    fn read_field(&self, entity: &EntityRef, field: &str) -> Option<Value> {
        self.0.borrow().read_field(entity, field)
    }

    fn read_conditions(
        &self,
        entity: &EntityRef,
    ) -> Option<Vec<ttrpg_interp::state::ActiveCondition>> {
        self.0.borrow().read_conditions(entity)
    }

    fn read_turn_budget(&self, entity: &EntityRef) -> Option<BTreeMap<String, Value>> {
        self.0.borrow().read_turn_budget(entity)
    }

    fn read_enabled_options(&self) -> Vec<String> {
        self.0.borrow().read_enabled_options()
    }

    fn position_eq(&self, a: &Value, b: &Value) -> bool {
        self.0.borrow().position_eq(a, b)
    }

    fn distance(&self, a: &Value, b: &Value) -> Option<i64> {
        self.0.borrow().distance(a, b)
    }

    fn entity_type_name(&self, entity: &EntityRef) -> Option<String> {
        let gs = self.0.borrow();
        gs.entity_type_name(entity).map(|s| s.to_string())
    }
}

// ── CliHandler ──────────────────────────────────────────────────

/// Full `EffectHandler` for the CLI with dice rolling, mutation
/// application, and effect logging.
///
/// Every mutation is logged with before/after values for transparency.
pub struct CliHandler<'a> {
    game_state: &'a RefCell<GameState>,
    reverse_handles: &'a HashMap<EntityRef, String>,
    rng: &'a mut StdRng,
    roll_queue: &'a mut VecDeque<i64>,
    pub log: Vec<String>,
}

impl<'a> CliHandler<'a> {
    pub fn new(
        game_state: &'a RefCell<GameState>,
        reverse_handles: &'a HashMap<EntityRef, String>,
        rng: &'a mut StdRng,
        roll_queue: &'a mut VecDeque<i64>,
    ) -> Self {
        CliHandler {
            game_state,
            reverse_handles,
            rng,
            roll_queue,
            log: Vec::new(),
        }
    }

    /// Human-readable name for an entity ref.
    fn entity_name(&self, entity: &EntityRef) -> String {
        self.reverse_handles
            .get(entity)
            .cloned()
            .unwrap_or_else(|| format!("Entity({})", entity.0))
    }
}

impl EffectHandler for CliHandler<'_> {
    fn handle(&mut self, effect: Effect) -> Response {
        match effect {
            Effect::RollDice { expr } => {
                if !self.roll_queue.is_empty() {
                    match roll_dice_from_queue(self.roll_queue, self.rng, &expr) {
                        Ok(result) => {
                            self.log.push(format!(
                                "[RollDice] {} -> {} (queued)",
                                format_dice_expr(&expr),
                                result.total,
                            ));
                            Response::Rolled(result)
                        }
                        Err(msg) => {
                            self.log.push(format!("[RollDice] error: {}", msg));
                            Response::Vetoed
                        }
                    }
                } else {
                    let result = roll_dice(self.rng, &expr);
                    self.log.push(format!(
                        "[RollDice] {} -> {}",
                        format_dice_expr(&expr),
                        result.total,
                    ));
                    Response::Rolled(result)
                }
            }

            Effect::ResolvePrompt { suggest, name, .. } => {
                if let Some(val) = suggest {
                    self.log
                        .push(format!("[ResolvePrompt] {} -> auto: {}", name, format_value(&val)));
                    Response::PromptResult(val)
                } else {
                    self.log
                        .push(format!("[ResolvePrompt] {} -> vetoed (no suggestion)", name));
                    Response::Vetoed
                }
            }

            Effect::MutateField {
                entity,
                path,
                op,
                value,
                bounds,
            } => {
                let name = self.entity_name(&entity);
                let field_str = format_path(&path);
                let old = adapter::read_at_path(&*self.game_state.borrow(), &entity, &path)
                    .unwrap_or_else(|| match op {
                        AssignOp::PlusEq | AssignOp::MinusEq => Value::Int(0),
                        AssignOp::Eq => Value::None,
                    });
                let new_val = match adapter::compute_field_value(
                    &*self.game_state.borrow(),
                    &entity,
                    &path,
                    op,
                    &value,
                    &bounds,
                ) {
                    Ok(v) => v,
                    Err(e) => {
                        self.log.push(format!(
                            "[MutateField] {}.{}: error: {}",
                            name, field_str, e.message,
                        ));
                        return Response::Vetoed;
                    }
                };
                // Write to state
                self.game_state
                    .borrow_mut()
                    .write_field(&entity, &path, new_val.clone());

                let clamped = bounds.is_some() && {
                    // Check if clamping actually changed the value
                    let unclamped = match op {
                        AssignOp::Eq => value.clone(),
                        AssignOp::PlusEq | AssignOp::MinusEq => {
                            match adapter::apply_op(op, &old, &value) {
                                Ok(v) => v,
                                Err(_) => return Response::Vetoed,
                            }
                        }
                    };
                    unclamped != new_val
                };
                let suffix = if clamped { " (clamped)" } else { "" };
                self.log.push(format!(
                    "[MutateField] {}.{}: {} -> {}{}",
                    name,
                    field_str,
                    format_value(&old),
                    format_value(&new_val),
                    suffix,
                ));
                Response::Acknowledged
            }

            Effect::ApplyCondition {
                target,
                condition,
                params,
                duration,
            } => {
                let name = self.entity_name(&target);
                self.game_state
                    .borrow_mut()
                    .apply_condition(&target, &condition, params.clone(), duration.clone());
                if params.is_empty() {
                    self.log.push(format!(
                        "[ApplyCondition] {} gains {} ({:?})",
                        name, condition, duration,
                    ));
                } else {
                    self.log.push(format!(
                        "[ApplyCondition] {} gains {}({:?}) ({:?})",
                        name, condition, params, duration,
                    ));
                }
                Response::Acknowledged
            }

            Effect::RemoveCondition { target, condition, params } => {
                let name = self.entity_name(&target);
                self.game_state
                    .borrow_mut()
                    .remove_condition(&target, &condition, params.as_ref());
                if let Some(ref p) = params {
                    self.log.push(format!(
                        "[RemoveCondition] {} loses {}({:?})",
                        name, condition, p,
                    ));
                } else {
                    self.log.push(format!(
                        "[RemoveCondition] {} loses {}",
                        name, condition,
                    ));
                }
                Response::Acknowledged
            }

            Effect::MutateTurnField {
                actor,
                field,
                op,
                value,
            } => {
                let name = self.entity_name(&actor);
                let old = self
                    .game_state
                    .borrow()
                    .read_turn_budget(&actor)
                    .and_then(|b| b.get(&field).cloned())
                    .unwrap_or(Value::Int(0));
                let new_val = match adapter::compute_turn_field_value(
                    &*self.game_state.borrow(),
                    &actor,
                    &field,
                    op,
                    &value,
                ) {
                    Ok(v) => v,
                    Err(e) => {
                        self.log.push(format!(
                            "[MutateTurnField] {}.{}: error: {}",
                            name, field, e.message,
                        ));
                        return Response::Vetoed;
                    }
                };
                self.game_state
                    .borrow_mut()
                    .write_turn_field(&actor, &field, new_val.clone());
                self.log.push(format!(
                    "[MutateTurnField] {}.{}: {} -> {}",
                    name,
                    field,
                    format_value(&old),
                    format_value(&new_val),
                ));
                Response::Acknowledged
            }

            Effect::DeductCost {
                actor,
                budget_field,
                token,
            } => {
                let name = self.entity_name(&actor);
                adapter::deduct_budget_field(&mut *self.game_state.borrow_mut(), &actor, &budget_field);
                self.log
                    .push(format!("[DeductCost] {}: {}", name, token));
                Response::Acknowledged
            }

            Effect::ActionStarted {
                name: action_name,
                actor,
                ..
            } => {
                let ename = self.entity_name(&actor);
                self.log
                    .push(format!("[ActionStarted] {} by {}", action_name, ename));
                Response::Acknowledged
            }

            Effect::RequiresCheck {
                action,
                passed,
                reason,
            } => {
                let status = if passed { "passed" } else { "failed" };
                let reason_str = reason
                    .map(|r| format!(" ({})", r))
                    .unwrap_or_default();
                self.log.push(format!(
                    "[RequiresCheck] {}: {}{}",
                    action, status, reason_str,
                ));
                Response::Acknowledged
            }

            Effect::ActionCompleted {
                name: action_name,
                actor,
            } => {
                let ename = self.entity_name(&actor);
                self.log
                    .push(format!("[ActionCompleted] {} by {}", action_name, ename));
                Response::Acknowledged
            }

            Effect::GrantGroup {
                entity,
                group_name,
                fields,
            } => {
                let name = self.entity_name(&entity);
                self.game_state.borrow_mut().write_field(
                    &entity,
                    &[ttrpg_interp::effect::FieldPathSegment::Field(
                        group_name.clone(),
                    )],
                    fields.clone(),
                );
                self.log.push(format!(
                    "[GrantGroup] {}.{}: {}",
                    name,
                    group_name,
                    format_value(&fields),
                ));
                Response::Acknowledged
            }

            Effect::RevokeGroup {
                entity,
                group_name,
            } => {
                let name = self.entity_name(&entity);
                self.game_state
                    .borrow_mut()
                    .remove_field(&entity, &group_name);
                self.log
                    .push(format!("[RevokeGroup] {}.{}", name, group_name));
                Response::Acknowledged
            }

            Effect::ModifyApplied {
                source,
                target_fn,
                changes,
                ..
            } => {
                let source_str = match &source {
                    ttrpg_interp::effect::ModifySource::Condition(c) => {
                        format!("condition:{}", c)
                    }
                    ttrpg_interp::effect::ModifySource::Option(o) => format!("option:{}", o),
                };
                let changes_str: Vec<String> = changes
                    .iter()
                    .map(|c| {
                        format!(
                            "{}: {} -> {}",
                            c.name,
                            format_value(&c.old),
                            format_value(&c.new)
                        )
                    })
                    .collect();
                self.log.push(format!(
                    "[ModifyApplied] {} on {}: {}",
                    source_str,
                    target_fn,
                    changes_str.join(", "),
                ));
                Response::Acknowledged
            }
        }
    }
}

// ── Dice rolling helpers ────────────────────────────────────────

/// Roll a dice expression using the given RNG.
pub fn roll_dice(rng: &mut StdRng, expr: &DiceExpr) -> RollResult {
    let sides = (expr.sides as i64).max(1);
    let mut dice: Vec<i64> = (0..expr.count)
        .map(|_| rng.random_range(1..=sides))
        .collect();

    let kept = apply_dice_filter(&mut dice, &expr.filter);
    let unmodified: i64 = kept.iter().sum();
    let total = unmodified + expr.modifier;

    RollResult {
        expr: expr.clone(),
        dice,
        kept,
        modifier: expr.modifier,
        total,
        unmodified,
    }
}

/// Roll a dice expression using queued values, falling back to RNG when
/// the queue is exhausted mid-roll.
pub fn roll_dice_from_queue(
    queue: &mut VecDeque<i64>,
    rng: &mut StdRng,
    expr: &DiceExpr,
) -> Result<RollResult, String> {
    let mut dice: Vec<i64> = Vec::with_capacity(expr.count as usize);
    for _ in 0..expr.count {
        if let Some(val) = queue.pop_front() {
            if val < 1 || val > expr.sides as i64 {
                return Err(format!(
                    "queued value {} out of range for d{} (expected 1..={})",
                    val, expr.sides, expr.sides
                ));
            }
            dice.push(val);
        } else {
            let sides = (expr.sides as i64).max(1);
            dice.push(rng.random_range(1..=sides));
        }
    }

    let kept = apply_dice_filter(&mut dice, &expr.filter);
    let unmodified: i64 = kept.iter().sum();
    let total = unmodified + expr.modifier;

    Ok(RollResult {
        expr: expr.clone(),
        dice,
        kept,
        modifier: expr.modifier,
        total,
        unmodified,
    })
}

/// Apply a dice filter (keep/drop highest/lowest) and return the kept dice.
fn apply_dice_filter(dice: &mut [i64], filter: &Option<DiceFilter>) -> Vec<i64> {
    match filter {
        None => dice.to_owned(),
        Some(f) => {
            let mut sorted = dice.to_owned();
            sorted.sort();
            match f {
                DiceFilter::KeepHighest(n) => {
                    let n = *n as usize;
                    sorted.into_iter().rev().take(n).collect()
                }
                DiceFilter::KeepLowest(n) => {
                    let n = *n as usize;
                    sorted.into_iter().take(n).collect()
                }
                DiceFilter::DropHighest(n) => {
                    let n = *n as usize;
                    let len = sorted.len();
                    if n >= len {
                        vec![]
                    } else {
                        sorted.into_iter().take(len - n).collect()
                    }
                }
                DiceFilter::DropLowest(n) => {
                    let n = *n as usize;
                    sorted.into_iter().skip(n).collect()
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::SeedableRng;
    use ttrpg_interp::effect::FieldPathSegment;

    #[test]
    fn acknowledges_action_started() {
        let mut handler = MinimalHandler;
        let effect = Effect::ActionCompleted {
            name: "Test".into(),
            actor: ttrpg_interp::state::EntityRef(1),
        };
        assert!(matches!(handler.handle(effect), Response::Acknowledged));
    }

    #[test]
    fn vetoes_roll_dice() {
        let mut handler = MinimalHandler;
        let effect = Effect::RollDice {
            expr: DiceExpr {
                count: 1,
                sides: 20,
                filter: None,
                modifier: 0,
            },
        };
        assert!(matches!(handler.handle(effect), Response::Vetoed));
    }

    #[test]
    fn roll_dice_basic() {
        let mut rng = StdRng::seed_from_u64(42);
        let expr = DiceExpr {
            count: 2,
            sides: 6,
            filter: None,
            modifier: 3,
        };
        let result = roll_dice(&mut rng, &expr);
        assert_eq!(result.dice.len(), 2);
        assert!(result.dice.iter().all(|&d| (1..=6).contains(&d)));
        assert_eq!(result.kept.len(), 2);
        assert_eq!(result.total, result.unmodified + 3);
    }

    #[test]
    fn roll_dice_with_filter() {
        let mut rng = StdRng::seed_from_u64(42);
        let expr = DiceExpr {
            count: 4,
            sides: 6,
            filter: Some(DiceFilter::KeepHighest(3)),
            modifier: 0,
        };
        let result = roll_dice(&mut rng, &expr);
        assert_eq!(result.dice.len(), 4);
        assert_eq!(result.kept.len(), 3);
        // Kept should be the 3 highest
        let mut all_sorted = result.dice.clone();
        all_sorted.sort();
        let expected_kept: Vec<i64> = all_sorted.into_iter().rev().take(3).collect();
        let mut kept_sorted = result.kept.clone();
        kept_sorted.sort();
        kept_sorted.reverse();
        assert_eq!(kept_sorted, expected_kept);
    }

    #[test]
    fn roll_dice_drop_lowest() {
        let mut rng = StdRng::seed_from_u64(123);
        let expr = DiceExpr {
            count: 4,
            sides: 6,
            filter: Some(DiceFilter::DropLowest(1)),
            modifier: 0,
        };
        let result = roll_dice(&mut rng, &expr);
        assert_eq!(result.dice.len(), 4);
        assert_eq!(result.kept.len(), 3);
    }

    #[test]
    fn cli_handler_rolls_dice() {
        let game_state = RefCell::new(GameState::new());
        let reverse_handles = HashMap::new();
        let mut rng = StdRng::seed_from_u64(42);
        let mut queue = VecDeque::new();
        let mut handler = CliHandler::new(&game_state, &reverse_handles, &mut rng, &mut queue);

        let effect = Effect::RollDice {
            expr: DiceExpr {
                count: 1,
                sides: 20,
                filter: None,
                modifier: 5,
            },
        };
        let response = handler.handle(effect);
        assert!(matches!(response, Response::Rolled(_)));
        assert_eq!(handler.log.len(), 1);
        assert!(handler.log[0].starts_with("[RollDice]"));
    }

    #[test]
    fn cli_handler_mutate_field() {
        let mut gs = GameState::new();
        let entity = gs.add_entity("Fighter", {
            let mut f = HashMap::new();
            f.insert("HP".into(), Value::Int(30));
            f
        });
        let game_state = RefCell::new(gs);
        let mut reverse = HashMap::new();
        reverse.insert(entity, "fighter".to_string());
        let mut rng = StdRng::seed_from_u64(42);
        let mut queue = VecDeque::new();
        let mut handler = CliHandler::new(&game_state, &reverse, &mut rng, &mut queue);

        let effect = Effect::MutateField {
            entity,
            path: vec![FieldPathSegment::Field("HP".into())],
            op: AssignOp::MinusEq,
            value: Value::Int(10),
            bounds: None,
        };
        let response = handler.handle(effect);
        assert!(matches!(response, Response::Acknowledged));
        assert_eq!(handler.log.len(), 1);
        assert!(handler.log[0].contains("fighter.HP"));
        assert!(handler.log[0].contains("30 -> 20"));

        // Verify state was updated
        assert_eq!(
            game_state.borrow().read_field(&entity, "HP"),
            Some(Value::Int(20)),
        );
    }

    #[test]
    fn cli_handler_mutate_field_clamped() {
        let mut gs = GameState::new();
        let entity = gs.add_entity("Fighter", {
            let mut f = HashMap::new();
            f.insert("HP".into(), Value::Int(5));
            f
        });
        let game_state = RefCell::new(gs);
        let mut reverse = HashMap::new();
        reverse.insert(entity, "fighter".to_string());
        let mut rng = StdRng::seed_from_u64(42);
        let mut queue = VecDeque::new();
        let mut handler = CliHandler::new(&game_state, &reverse, &mut rng, &mut queue);

        let effect = Effect::MutateField {
            entity,
            path: vec![FieldPathSegment::Field("HP".into())],
            op: AssignOp::MinusEq,
            value: Value::Int(20),
            bounds: Some((Value::Int(0), Value::Int(100))),
        };
        handler.handle(effect);
        assert!(handler.log[0].contains("(clamped)"));
        assert_eq!(
            game_state.borrow().read_field(&entity, "HP"),
            Some(Value::Int(0)),
        );
    }

    #[test]
    fn cli_handler_deduct_cost() {
        let mut gs = GameState::new();
        let entity = gs.add_entity("Fighter", HashMap::new());
        let mut budget = BTreeMap::new();
        budget.insert("actions".into(), Value::Int(1));
        gs.set_turn_budget(&entity, budget);
        let game_state = RefCell::new(gs);
        let mut reverse = HashMap::new();
        reverse.insert(entity, "fighter".to_string());
        let mut rng = StdRng::seed_from_u64(42);
        let mut queue = VecDeque::new();
        let mut handler = CliHandler::new(&game_state, &reverse, &mut rng, &mut queue);

        let effect = Effect::DeductCost {
            actor: entity,
            token: "action".into(),
            budget_field: "actions".into(),
        };
        handler.handle(effect);
        assert!(handler.log[0].contains("[DeductCost]"));
        assert!(handler.log[0].contains("action"));

        assert_eq!(
            game_state
                .borrow()
                .read_turn_budget(&entity)
                .and_then(|b| b.get("actions").cloned()),
            Some(Value::Int(0)),
        );
    }

    #[test]
    fn cli_handler_resolve_prompt_with_suggest() {
        let game_state = RefCell::new(GameState::new());
        let reverse_handles = HashMap::new();
        let mut rng = StdRng::seed_from_u64(42);
        let mut queue = VecDeque::new();
        let mut handler = CliHandler::new(&game_state, &reverse_handles, &mut rng, &mut queue);

        let effect = Effect::ResolvePrompt {
            name: "choose_target".into(),
            params: vec![],
            hint: None,
            suggest: Some(Value::Int(1)),
        };
        let response = handler.handle(effect);
        assert!(matches!(response, Response::PromptResult(Value::Int(1))));
    }

    #[test]
    fn cli_handler_resolve_prompt_without_suggest() {
        let game_state = RefCell::new(GameState::new());
        let reverse_handles = HashMap::new();
        let mut rng = StdRng::seed_from_u64(42);
        let mut queue = VecDeque::new();
        let mut handler = CliHandler::new(&game_state, &reverse_handles, &mut rng, &mut queue);

        let effect = Effect::ResolvePrompt {
            name: "choose_target".into(),
            params: vec![],
            hint: None,
            suggest: None,
        };
        let response = handler.handle(effect);
        assert!(matches!(response, Response::Vetoed));
    }

    #[test]
    fn refcell_state_reads() {
        let mut gs = GameState::new();
        let entity = gs.add_entity("Fighter", {
            let mut f = HashMap::new();
            f.insert("HP".into(), Value::Int(30));
            f
        });
        let cell = RefCell::new(gs);
        let state = RefCellState(&cell);

        assert_eq!(state.read_field(&entity, "HP"), Some(Value::Int(30)));
        assert_eq!(state.read_field(&entity, "AC"), None);
    }

    // ── Roll queue tests ─────────────────────────────────────────

    #[test]
    fn roll_dice_from_queue_basic() {
        let mut queue = VecDeque::from(vec![3, 5]);
        let mut rng = StdRng::seed_from_u64(42);
        let expr = DiceExpr {
            count: 2,
            sides: 6,
            filter: None,
            modifier: 1,
        };
        let result = roll_dice_from_queue(&mut queue, &mut rng, &expr).unwrap();
        assert_eq!(result.dice, vec![3, 5]);
        assert_eq!(result.total, 3 + 5 + 1);
        assert!(queue.is_empty());
    }

    #[test]
    fn roll_dice_from_queue_fallback() {
        // Queue has only 1 value but we need 2 dice
        let mut queue = VecDeque::from(vec![4]);
        let mut rng = StdRng::seed_from_u64(42);
        let expr = DiceExpr {
            count: 2,
            sides: 6,
            filter: None,
            modifier: 0,
        };
        let result = roll_dice_from_queue(&mut queue, &mut rng, &expr).unwrap();
        assert_eq!(result.dice[0], 4); // from queue
        assert!(result.dice[1] >= 1 && result.dice[1] <= 6); // from rng
        assert!(queue.is_empty());
    }

    #[test]
    fn roll_dice_from_queue_out_of_range() {
        let mut queue = VecDeque::from(vec![7]); // out of range for d6
        let mut rng = StdRng::seed_from_u64(42);
        let expr = DiceExpr {
            count: 1,
            sides: 6,
            filter: None,
            modifier: 0,
        };
        let result = roll_dice_from_queue(&mut queue, &mut rng, &expr);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("out of range"));
    }

    #[test]
    fn cli_handler_rolls_from_queue() {
        let game_state = RefCell::new(GameState::new());
        let reverse_handles = HashMap::new();
        let mut rng = StdRng::seed_from_u64(42);
        let mut queue = VecDeque::from(vec![15]);
        let mut handler = CliHandler::new(&game_state, &reverse_handles, &mut rng, &mut queue);

        let effect = Effect::RollDice {
            expr: DiceExpr {
                count: 1,
                sides: 20,
                filter: None,
                modifier: 5,
            },
        };
        let response = handler.handle(effect);
        match response {
            Response::Rolled(r) => {
                assert_eq!(r.dice, vec![15]);
                assert_eq!(r.total, 20);
            }
            _ => panic!("expected Rolled"),
        }
        assert!(handler.log[0].contains("(queued)"));
    }

    #[test]
    fn cli_handler_grant_group() {
        let mut gs = GameState::new();
        let entity = gs.add_entity("Character", HashMap::new());
        let game_state = RefCell::new(gs);
        let mut reverse = HashMap::new();
        reverse.insert(entity, "wizard".to_string());
        let mut rng = StdRng::seed_from_u64(42);
        let mut queue = VecDeque::new();
        let mut handler = CliHandler::new(&game_state, &reverse, &mut rng, &mut queue);

        let struct_val = Value::Struct {
            name: "Spellcasting".into(),
            fields: {
                let mut f = std::collections::BTreeMap::new();
                f.insert("spell_slots".into(), Value::Int(3));
                f
            },
        };
        let effect = Effect::GrantGroup {
            entity,
            group_name: "Spellcasting".into(),
            fields: struct_val.clone(),
        };
        let response = handler.handle(effect);
        assert!(matches!(response, Response::Acknowledged));
        assert_eq!(handler.log.len(), 1);
        assert!(handler.log[0].contains("[GrantGroup]"));
        assert!(handler.log[0].contains("wizard.Spellcasting"));

        // Verify state was updated
        assert_eq!(
            game_state.borrow().read_field(&entity, "Spellcasting"),
            Some(struct_val),
        );
    }

    #[test]
    fn cli_handler_revoke_group() {
        let mut gs = GameState::new();
        let entity = gs.add_entity("Character", {
            let mut f = HashMap::new();
            f.insert("HP".into(), Value::Int(30));
            f
        });
        // Simulate a granted group by writing a field directly
        gs.write_field(
            &entity,
            &[FieldPathSegment::Field("Spellcasting".into())],
            Value::Struct {
                name: "Spellcasting".into(),
                fields: std::collections::BTreeMap::new(),
            },
        );
        let game_state = RefCell::new(gs);
        let mut reverse = HashMap::new();
        reverse.insert(entity, "wizard".to_string());
        let mut rng = StdRng::seed_from_u64(42);
        let mut queue = VecDeque::new();
        let mut handler = CliHandler::new(&game_state, &reverse, &mut rng, &mut queue);

        let effect = Effect::RevokeGroup {
            entity,
            group_name: "Spellcasting".into(),
        };
        let response = handler.handle(effect);
        assert!(matches!(response, Response::Acknowledged));
        assert_eq!(handler.log.len(), 1);
        assert!(handler.log[0].contains("[RevokeGroup]"));
        assert!(handler.log[0].contains("wizard.Spellcasting"));

        // Verify field was removed
        assert_eq!(
            game_state.borrow().read_field(&entity, "Spellcasting"),
            None,
        );
        // Other fields untouched
        assert_eq!(
            game_state.borrow().read_field(&entity, "HP"),
            Some(Value::Int(30)),
        );
    }

    // ── Regression: tdsl-4uk — MutateField audit on missing field with bounds ──

    #[test]
    fn cli_handler_mutate_missing_field_plus_eq_log_shows_zero_baseline() {
        // When a field doesn't exist, compute_field_value uses Int(0) as baseline
        // for +=. The audit log should show "0 -> 5", not "none -> 5".
        let mut gs = GameState::new();
        let entity = gs.add_entity("Fighter", HashMap::new());
        let game_state = RefCell::new(gs);
        let mut reverse = HashMap::new();
        reverse.insert(entity, "fighter".to_string());
        let mut rng = StdRng::seed_from_u64(42);
        let mut queue = VecDeque::new();
        let mut handler = CliHandler::new(&game_state, &reverse, &mut rng, &mut queue);

        let effect = Effect::MutateField {
            entity,
            path: vec![FieldPathSegment::Field("HP".into())],
            op: AssignOp::PlusEq,
            value: Value::Int(5),
            bounds: Some((Value::Int(0), Value::Int(100))),
        };
        let response = handler.handle(effect);
        assert!(matches!(response, Response::Acknowledged));
        assert_eq!(handler.log.len(), 1);

        // Log should show 0 as baseline (matching compute_field_value), not "none"
        assert!(
            handler.log[0].contains("0 -> 5"),
            "expected log to show '0 -> 5' (the compute baseline), got: {}",
            handler.log[0],
        );
        assert!(
            !handler.log[0].contains("none"),
            "log should not show 'none' as old value; got: {}",
            handler.log[0],
        );
    }

    #[test]
    fn cli_handler_mutate_missing_field_minus_eq_log_shows_zero_baseline() {
        // -= on missing field: compute baseline is 0, so 0 - 10 = -10, clamped to 0.
        // Log should show "0 -> 0 (clamped)", not "none -> 0 (clamped)".
        let mut gs = GameState::new();
        let entity = gs.add_entity("Fighter", HashMap::new());
        let game_state = RefCell::new(gs);
        let mut reverse = HashMap::new();
        reverse.insert(entity, "fighter".to_string());
        let mut rng = StdRng::seed_from_u64(42);
        let mut queue = VecDeque::new();
        let mut handler = CliHandler::new(&game_state, &reverse, &mut rng, &mut queue);

        let effect = Effect::MutateField {
            entity,
            path: vec![FieldPathSegment::Field("HP".into())],
            op: AssignOp::MinusEq,
            value: Value::Int(10),
            bounds: Some((Value::Int(0), Value::Int(100))),
        };
        let response = handler.handle(effect);
        assert!(matches!(response, Response::Acknowledged));
        assert_eq!(handler.log.len(), 1);

        assert!(
            handler.log[0].contains("0 -> 0"),
            "expected log to show '0 -> 0' (the compute baseline), got: {}",
            handler.log[0],
        );
        assert!(
            handler.log[0].contains("(clamped)"),
            "expected (clamped) in log; got: {}",
            handler.log[0],
        );
        assert!(
            !handler.log[0].contains("none"),
            "log should not show 'none' as old value; got: {}",
            handler.log[0],
        );
    }
}
