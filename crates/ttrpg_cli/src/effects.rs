use std::cell::RefCell;
use std::collections::{HashMap, VecDeque};
use std::io;

use nu_ansi_term::Color;
use rand::Rng;
use rand::rngs::StdRng;
use ttrpg_ast::DiceFilter;
use ttrpg_ast::ast::AssignOp;
use ttrpg_checker::ty::Ty;
use ttrpg_interp::adapter;
use ttrpg_interp::effect::{ActionOutcome, Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::{
    ConditionArgs, EntityRef, StateProvider, SuspensionRecord, WritableState,
};
use ttrpg_interp::value::{DiceExpr, RollResult, Value};

use crate::format::{UnitSuffixes, format_dice_expr, format_path, format_value};

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

// ── CliHandler ──────────────────────────────────────────────────

/// Full `EffectHandler` for the CLI with dice rolling, mutation
/// application, and effect logging.
///
/// Every mutation is logged with before/after values for transparency.
pub struct CliHandler<'a> {
    game_state: &'a RefCell<GameState>,
    /// When set, reads go through this provider instead of `game_state`.
    /// Used in step-based execution where the real state lives in the
    /// Execution's StateAdapter, not in the Runner's RefCell.
    state_override: Option<&'a dyn StateProvider>,
    reverse_handles: &'a HashMap<EntityRef, String>,
    rng: &'a mut StdRng,
    roll_queue: &'a mut VecDeque<i64>,
    prompt_queue: &'a mut VecDeque<Value>,
    unit_suffixes: &'a UnitSuffixes,
    pub log: Vec<String>,
    pub effects: Vec<Effect>,
    quiet: bool,
    interactive: bool,
}

impl<'a> CliHandler<'a> {
    pub fn new(
        game_state: &'a RefCell<GameState>,
        reverse_handles: &'a HashMap<EntityRef, String>,
        rng: &'a mut StdRng,
        roll_queue: &'a mut VecDeque<i64>,
        prompt_queue: &'a mut VecDeque<Value>,
        unit_suffixes: &'a UnitSuffixes,
    ) -> Self {
        CliHandler {
            game_state,
            state_override: None,
            reverse_handles,
            rng,
            roll_queue,
            prompt_queue,
            unit_suffixes,
            log: Vec::new(),
            effects: Vec::new(),
            quiet: false,
            interactive: false,
        }
    }

    /// Use an external StateProvider for reads instead of the RefCell.
    ///
    /// In step-based execution the real game state lives in the Execution's
    /// StateAdapter while the Runner's RefCell is empty. Setting this
    /// override makes CliHandler read before-values from the correct source.
    pub fn with_state(mut self, sp: &'a dyn StateProvider) -> Self {
        self.state_override = Some(sp);
        self
    }

    pub fn quiet(mut self, quiet: bool) -> Self {
        self.quiet = quiet;
        self
    }

    pub fn interactive(mut self, interactive: bool) -> Self {
        self.interactive = interactive;
        self
    }

    /// Run a closure against the best available read-only state.
    ///
    /// Uses `state_override` when set (step-based mode), otherwise
    /// falls back to a short-lived borrow of `game_state` (callback mode).
    fn with_state_ref<R>(&self, f: impl FnOnce(&dyn StateProvider) -> R) -> R {
        if let Some(sp) = self.state_override {
            f(sp)
        } else {
            let gs = self.game_state.borrow();
            f(&*gs)
        }
    }

    /// Push a log line (suppressed in quiet mode).
    fn log(&mut self, line: String) {
        if !self.quiet {
            self.log.push(line);
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
        self.effects.push(effect.clone());
        match effect {
            Effect::RollDice { expr } => {
                if !self.roll_queue.is_empty() {
                    match roll_dice_from_queue(self.roll_queue, self.rng, &expr) {
                        Ok(result) => {
                            self.log(format!(
                                "[RollDice] {} -> {} (queued)",
                                format_dice_expr(&expr),
                                result.total,
                            ));
                            Response::Rolled(result)
                        }
                        Err(msg) => {
                            self.log(format!("[RollDice] error: {msg}"));
                            Response::Vetoed
                        }
                    }
                } else {
                    let result = roll_dice(self.rng, &expr);
                    self.log(format!(
                        "[RollDice] {} -> {}",
                        format_dice_expr(&expr),
                        result.total,
                    ));
                    Response::Rolled(result)
                }
            }

            Effect::ResolvePrompt {
                suggest,
                name,
                has_default,
                return_type,
                hint,
                ..
            } => {
                if let Some(val) = self.prompt_queue.pop_front() {
                    self.log(format!(
                        "[ResolvePrompt] {} -> {} (queued)",
                        name,
                        format_value(&val, self.unit_suffixes)
                    ));
                    return Response::PromptResult(val);
                }

                if self.interactive {
                    match prompt_stdin(&name, hint.as_deref(), &return_type, suggest.as_ref()) {
                        PromptOutcome::Value(val) => {
                            self.log(format!(
                                "[ResolvePrompt] {} -> {}",
                                name,
                                format_value(&val, self.unit_suffixes)
                            ));
                            return Response::PromptResult(val);
                        }
                        PromptOutcome::UseDefault => {
                            self.log
                                .push(format!("[ResolvePrompt] {name} -> use default"));
                            return Response::UseDefault;
                        }
                        PromptOutcome::Vetoed => {
                            self.log.push(format!("[ResolvePrompt] {name} -> vetoed"));
                            return Response::Vetoed;
                        }
                    }
                }

                // Non-interactive fallback
                if has_default {
                    self.log
                        .push(format!("[ResolvePrompt] {name} -> use default"));
                    Response::UseDefault
                } else if let Some(val) = suggest {
                    self.log(format!(
                        "[ResolvePrompt] {} -> auto: {}",
                        name,
                        format_value(&val, self.unit_suffixes)
                    ));
                    Response::PromptResult(val)
                } else {
                    self.log
                        .push(format!("[ResolvePrompt] {name} -> use default"));
                    Response::UseDefault
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
                let field_str = format_path(&path, self.unit_suffixes);
                let old = self
                    .with_state_ref(|sp| adapter::read_at_path(sp, &entity, &path))
                    .unwrap_or(match op {
                        AssignOp::PlusEq | AssignOp::MinusEq => Value::Int(0),
                        AssignOp::Eq => Value::Void,
                    });
                let result = match self.with_state_ref(|sp| {
                    adapter::compute_field_value(sp, &entity, &path, op, &value, &bounds)
                }) {
                    Ok(r) => r,
                    Err(e) => {
                        self.log(format!(
                            "[MutateField] {}.{}: error: {}",
                            name, field_str, e.message,
                        ));
                        return Response::Vetoed;
                    }
                };
                // Write to state
                self.game_state
                    .borrow_mut()
                    .write_field(&entity, &path, result.value.clone());

                let suffix = if result.clamped { " (clamped)" } else { "" };
                self.log(format!(
                    "[MutateField] {}.{}: {} -> {}{}",
                    name,
                    field_str,
                    format_value(&old, self.unit_suffixes),
                    format_value(&result.value, self.unit_suffixes),
                    suffix,
                ));
                Response::Acknowledged
            }

            Effect::ApplyCondition {
                target,
                condition,
                params,
                duration,
                invocation,
                source,
                tags,
                state_fields,
                ..
            } => {
                let name = self.entity_name(&target);
                self.game_state.borrow_mut().apply_condition(
                    &target,
                    &condition,
                    ConditionArgs {
                        params: params.clone(),
                        duration: duration.clone(),
                        invocation,
                        source,
                        tags,
                        state_fields: state_fields.clone(),
                    },
                );
                if params.is_empty() {
                    self.log(format!(
                        "[ApplyCondition] {name} gains {condition} ({duration:?})",
                    ));
                } else {
                    self.log(format!(
                        "[ApplyCondition] {name} gains {condition}({params:?}) ({duration:?})",
                    ));
                }
                Response::Acknowledged
            }

            Effect::RemoveCondition {
                target,
                condition,
                params,
                id,
            } => {
                let name = self.entity_name(&target);
                if let Some(cid) = id {
                    self.game_state
                        .borrow_mut()
                        .remove_condition_by_id(&target, cid);
                    self.log(format!(
                        "[RemoveCondition] {name} loses {condition} (id={cid})",
                    ));
                } else {
                    self.game_state.borrow_mut().remove_condition(
                        &target,
                        &condition,
                        params.as_ref(),
                    );
                    if let Some(ref p) = params {
                        self.log
                            .push(format!("[RemoveCondition] {name} loses {condition}({p:?})",));
                    } else {
                        self.log
                            .push(format!("[RemoveCondition] {name} loses {condition}",));
                    }
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
                    .with_state_ref(|sp| sp.read_turn_budget(&actor))
                    .and_then(|b| b.get(&field).cloned())
                    .unwrap_or(Value::Int(0));
                let new_val = match self.with_state_ref(|sp| {
                    adapter::compute_turn_field_value(sp, &actor, &field, op, &value)
                }) {
                    Ok(v) => v,
                    Err(e) => {
                        self.log(format!(
                            "[MutateTurnField] {}.{}: error: {}",
                            name, field, e.message,
                        ));
                        return Response::Vetoed;
                    }
                };
                self.game_state
                    .borrow_mut()
                    .write_turn_field(&actor, &field, new_val.clone());
                self.log(format!(
                    "[MutateTurnField] {}.{}: {} -> {}",
                    name,
                    field,
                    format_value(&old, self.unit_suffixes),
                    format_value(&new_val, self.unit_suffixes),
                ));
                Response::Acknowledged
            }

            Effect::DeductCost {
                actor,
                budget_field,
                token,
            } => {
                let name = self.entity_name(&actor);
                adapter::deduct_budget_field(
                    &mut *self.game_state.borrow_mut(),
                    &actor,
                    &budget_field,
                );
                self.log(format!("[DeductCost] {name}: {token}"));
                Response::Acknowledged
            }

            Effect::ActionStarted {
                name: action_name,
                actor,
                ..
            } => {
                let ename = self.entity_name(&actor);
                self.log(format!("[ActionStarted] {action_name} by {ename}"));
                Response::Acknowledged
            }

            Effect::RequiresCheck {
                action,
                passed,
                reason,
            } => {
                let status = if passed { "passed" } else { "failed" };
                let reason_str = reason.map(|r| format!(" ({r})")).unwrap_or_default();
                self.log(format!("[RequiresCheck] {action}: {status}{reason_str}",));
                Response::Acknowledged
            }

            Effect::ActionCompleted {
                name: action_name,
                actor,
                outcome,
                ..
            } => {
                let ename = self.entity_name(&actor);
                let outcome_str = match outcome {
                    ActionOutcome::Succeeded => "succeeded",
                    ActionOutcome::Vetoed => "vetoed",
                    ActionOutcome::Failed => "failed",
                };
                self.log(format!(
                    "[ActionCompleted] {action_name} by {ename} ({outcome_str})"
                ));
                Response::Acknowledged
            }

            Effect::RevokeInvocation { invocation } => {
                self.game_state
                    .borrow_mut()
                    .remove_conditions_by_invocation(invocation);
                self.log(format!("[RevokeInvocation] invocation {}", invocation.0));
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
                self.log(format!(
                    "[GrantGroup] {}.{}: {}",
                    name,
                    group_name,
                    format_value(&fields, self.unit_suffixes),
                ));
                Response::Acknowledged
            }

            Effect::RevokeGroup { entity, group_name } => {
                let name = self.entity_name(&entity);
                self.game_state
                    .borrow_mut()
                    .remove_field(&entity, &group_name);
                self.log(format!("[RevokeGroup] {name}.{group_name}"));
                Response::Acknowledged
            }

            Effect::ProvisionBudget { actor, budget } => {
                let name = self.entity_name(&actor);
                self.game_state
                    .borrow_mut()
                    .set_turn_budget(&actor, budget.clone());
                let fields_str: Vec<String> = budget
                    .iter()
                    .map(|(k, v)| format!("{}: {}", k, format_value(v, self.unit_suffixes)))
                    .collect();
                self.log(format!(
                    "[ProvisionBudget] {name}: {{ {} }}",
                    fields_str.join(", "),
                ));
                Response::Acknowledged
            }

            Effect::ClearBudget { actor } => {
                let name = self.entity_name(&actor);
                self.game_state.borrow_mut().clear_turn_budget(&actor);
                self.log(format!("[ClearBudget] {name}"));
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
                        format!("condition:{c}")
                    }
                    ttrpg_interp::effect::ModifySource::Option(o) => format!("option:{o}"),
                };
                let changes_str: Vec<String> = changes
                    .iter()
                    .map(|c| {
                        format!(
                            "{}: {} -> {}",
                            c.name,
                            format_value(&c.old, self.unit_suffixes),
                            format_value(&c.new, self.unit_suffixes)
                        )
                    })
                    .collect();
                self.log(format!(
                    "[ModifyApplied] {} on {}: {}",
                    source_str,
                    target_fn,
                    changes_str.join(", "),
                ));
                Response::Acknowledged
            }
            Effect::AdvanceTime { amount } => {
                self.log(format!("[AdvanceTime] +{amount}"));
                Response::Acknowledged
            }

            Effect::ConditionApplyGate {
                target, condition, ..
            } => {
                let name = self.entity_name(&target);
                self.log(format!("[ConditionApplyGate] {condition} on {name}"));
                Response::Acknowledged
            }

            Effect::ConditionRemovalGate {
                target,
                condition,
                id,
            } => {
                let name = self.entity_name(&target);
                self.log(format!("[ConditionRemovalGate] {condition}#{id} on {name}"));
                Response::Acknowledged
            }

            Effect::SpawnEntity {
                entity_type,
                fields,
            } => {
                // When passed through, create the entity in game state
                let entity = self
                    .game_state
                    .borrow_mut()
                    .add_entity(&entity_type, fields);
                self.log(format!("[SpawnEntity] {entity_type} ({})", entity.0));
                Response::EntitySpawned(entity)
            }

            Effect::RemoveEntity { entity } => {
                let name = self.entity_name(&entity);
                self.game_state.borrow_mut().remove_entity(&entity);
                self.log(format!("[RemoveEntity] {name}"));
                Response::Acknowledged
            }

            Effect::AddSuspension {
                entity,
                source_id,
                presence,
                freeze_turns,
                freeze_durations,
            } => {
                let name = self.entity_name(&entity);
                let time = self.with_state_ref(|sp| sp.read_game_time());
                self.game_state.borrow_mut().add_suspension(
                    &entity,
                    SuspensionRecord {
                        source_id,
                        presence,
                        freeze_turns,
                        freeze_durations,
                        suspended_at: time,
                    },
                );
                self.log(format!(
                    "[AddSuspension] {name} source={source_id} presence={presence:?} \
                     freeze_turns={freeze_turns} freeze_durations={freeze_durations}"
                ));
                Response::Acknowledged
            }

            Effect::RemoveSuspensionSource { entity, source_id } => {
                let name = self.entity_name(&entity);
                self.game_state
                    .borrow_mut()
                    .remove_suspension_source(&entity, source_id);
                self.log(format!(
                    "[RemoveSuspensionSource] {name} source={source_id}"
                ));
                Response::Acknowledged
            }

            Effect::TransferConditions {
                from,
                to,
                tag,
                exclude_instance,
            } => {
                let from_name = self.entity_name(&from);
                let to_name = self.entity_name(&to);
                adapter::apply_transfer_conditions(
                    &mut *self.game_state.borrow_mut(),
                    &from,
                    &to,
                    &tag,
                    exclude_instance,
                    &rustc_hash::FxHashMap::default(), // Bearer type check skipped in CLI
                );
                self.log(format!(
                    "[TransferConditions] {from_name} -> {to_name} tag={tag}"
                ));
                Response::Acknowledged
            }

            Effect::SetConditionState {
                target,
                condition_id,
                fields,
            } => {
                self.log(format!(
                    "[SetConditionState] condition_id={condition_id} fields={fields:?}"
                ));
                self.game_state
                    .borrow_mut()
                    .set_condition_state(&target, condition_id, fields);
                Response::Acknowledged
            }
        }
    }
}

// ── Interactive prompt helpers ──────────────────────────────────

enum PromptOutcome {
    Value(Value),
    UseDefault,
    Vetoed,
}

/// Prompt the user via stdin for a value. Temporarily disables raw mode
/// so the user gets normal line editing, then re-enables it.
fn prompt_stdin(
    name: &str,
    hint: Option<&str>,
    return_type: &Ty,
    suggest: Option<&Value>,
) -> PromptOutcome {
    let _ = crossterm::terminal::disable_raw_mode();

    let result = prompt_stdin_inner(name, hint, return_type, suggest);

    let _ = crossterm::terminal::enable_raw_mode();
    result
}

fn prompt_stdin_inner(
    name: &str,
    hint: Option<&str>,
    return_type: &Ty,
    suggest: Option<&Value>,
) -> PromptOutcome {
    let stdin = io::stdin();
    let mut reader = stdin.lock();
    let mut writer = io::stderr();
    prompt_loop(&mut reader, &mut writer, name, hint, return_type, suggest)
}

fn prompt_loop(
    reader: &mut dyn io::BufRead,
    writer: &mut dyn io::Write,
    name: &str,
    hint: Option<&str>,
    return_type: &Ty,
    suggest: Option<&Value>,
) -> PromptOutcome {
    let amber = Color::Yellow;
    let dim = Color::DarkGray;

    // Print prompt header
    write!(writer, "{}", amber.bold().paint(format!("[prompt] {name}"))).ok();
    if let Some(h) = hint {
        write!(writer, " — {}", amber.paint(h)).ok();
    }
    write!(
        writer,
        " {}",
        dim.paint(format!("({})", type_hint(return_type)))
    )
    .ok();
    if let Some(val) = suggest {
        write!(
            writer,
            " {}",
            dim.paint(format!("[default: {}]", format_suggest(val)))
        )
        .ok();
    }
    writeln!(writer).ok();

    loop {
        write!(writer, "{}", amber.paint("  > ")).ok();
        writer.flush().ok();

        let mut line = String::new();
        match reader.read_line(&mut line) {
            Ok(0) => return PromptOutcome::Vetoed, // EOF / Ctrl-D
            Err(_) => return PromptOutcome::Vetoed,
            Ok(_) => {}
        }

        let trimmed = line.trim();

        // Empty input: use suggest if available, else UseDefault
        if trimmed.is_empty() {
            if let Some(val) = suggest {
                return PromptOutcome::Value(val.clone());
            }
            return PromptOutcome::UseDefault;
        }

        // Parse according to return type
        match parse_prompt_input(trimmed, return_type) {
            Ok(val) => return PromptOutcome::Value(val),
            Err(msg) => {
                writeln!(
                    writer,
                    "  {} expected {}, got {:?}: {}",
                    Color::Red.bold().paint("error:"),
                    type_hint(return_type),
                    trimmed,
                    msg,
                )
                .ok();
                // Loop to re-prompt
            }
        }
    }
}

/// Parse user input string into a Value according to the expected type.
pub(crate) fn parse_prompt_input(input: &str, ty: &Ty) -> Result<Value, String> {
    match ty {
        Ty::Int | Ty::Resource => input
            .parse::<i64>()
            .map(Value::Int)
            .map_err(|_| "not a valid integer".to_string()),
        Ty::Float => input
            .parse::<f64>()
            .map(Value::Float)
            .map_err(|_| "not a valid number".to_string()),
        Ty::Bool => match input {
            "true" | "yes" | "y" | "1" => Ok(Value::Bool(true)),
            "false" | "no" | "n" | "0" => Ok(Value::Bool(false)),
            _ => Err("expected true/false".to_string()),
        },
        Ty::String => Ok(Value::Str(input.to_string())),
        _ => {
            // For entity handles and other complex types, try parsing as
            // a DSL expression via the parser and extract literals.
            let (parsed, diags) = ttrpg_parser::parse_expr(input);
            if !diags.is_empty() {
                return Err(diags[0].message.clone());
            }
            match parsed {
                Some(expr) => eval_simple_expr(&expr),
                None => Err("could not parse input".to_string()),
            }
        }
    }
}

/// Evaluate a simple parsed expression into a Value without an interpreter.
/// Handles literals (int, string, bool) that the parser produces.
fn eval_simple_expr(expr: &ttrpg_ast::Spanned<ttrpg_ast::ast::ExprKind>) -> Result<Value, String> {
    use ttrpg_ast::ast::ExprKind;
    match &expr.node {
        ExprKind::IntLit(n) => Ok(Value::Int(*n)),
        ExprKind::StringLit(s) => Ok(Value::Str(s.clone())),
        ExprKind::BoolLit(b) => Ok(Value::Bool(*b)),
        _ => Err("input too complex — enter a simple value".to_string()),
    }
}

/// Human-readable type hint for prompt display.
pub(crate) fn type_hint(ty: &Ty) -> &'static str {
    match ty {
        Ty::Int | Ty::Resource => "int",
        Ty::Float => "float",
        Ty::Bool => "bool",
        Ty::String => "string",
        Ty::Entity(_) | Ty::AnyEntity => "entity",
        _ => "value",
    }
}

/// Format a suggest value for display in the prompt header.
pub(crate) fn format_suggest(val: &Value) -> String {
    match val {
        Value::Int(n) => n.to_string(),
        Value::Float(n) => n.to_string(),
        Value::Bool(b) => b.to_string(),
        Value::Str(s) => format!("{s:?}"),
        _ => format!("{val:?}"),
    }
}

// ── Dice rolling helpers ────────────────────────────────────────

/// Roll a dice expression using the given RNG.
pub fn roll_dice(rng: &mut StdRng, expr: &DiceExpr) -> RollResult {
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

/// Roll a dice expression using queued values, falling back to RNG when
/// the queue is exhausted mid-roll.
pub fn roll_dice_from_queue(
    queue: &mut VecDeque<i64>,
    rng: &mut StdRng,
    expr: &DiceExpr,
) -> Result<RollResult, String> {
    let mut all_dice = Vec::new();
    let mut all_kept = Vec::new();

    for group in &expr.groups {
        let sides = (group.sides as i64).max(1);
        let mut dice: Vec<i64> = Vec::with_capacity(group.count as usize);
        for _ in 0..group.count {
            if let Some(val) = queue.pop_front() {
                if val < 1 || val > sides {
                    return Err(format!(
                        "queued value {} out of range for d{} (expected 1..={})",
                        val, group.sides, sides
                    ));
                }
                dice.push(val);
            } else {
                dice.push(rng.random_range(1..=sides));
            }
        }
        let kept = apply_dice_filter(&mut dice, &group.filter);
        all_dice.extend(&dice);
        all_kept.extend(&kept);
    }

    let unmodified: i64 = all_kept.iter().sum();
    let total = unmodified + expr.modifier;

    Ok(RollResult {
        expr: expr.clone(),
        dice: all_dice,
        kept: all_kept,
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
            sorted.sort_unstable();
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
    use std::collections::BTreeMap;

    use super::*;
    use rand::SeedableRng;
    use rustc_hash::FxHashMap;
    use ttrpg_interp::effect::FieldPathSegment;
    use ttrpg_interp::reference_state::RefCellState;
    use ttrpg_interp::state::StateProvider;

    #[test]
    fn acknowledges_action_started() {
        let mut handler = MinimalHandler;
        let effect = Effect::ActionCompleted {
            name: "Test".into(),
            actor: ttrpg_interp::state::EntityRef(1),
            outcome: ttrpg_interp::effect::ActionOutcome::Succeeded,
            invocation: None,
        };
        assert!(matches!(handler.handle(effect), Response::Acknowledged));
    }

    #[test]
    fn vetoes_roll_dice() {
        let mut handler = MinimalHandler;
        let effect = Effect::RollDice {
            expr: DiceExpr::single(1, 20, None, 0),
        };
        assert!(matches!(handler.handle(effect), Response::Vetoed));
    }

    #[test]
    fn roll_dice_basic() {
        let mut rng = StdRng::seed_from_u64(42);
        let expr = DiceExpr::single(2, 6, None, 3);
        let result = roll_dice(&mut rng, &expr);
        assert_eq!(result.dice.len(), 2);
        assert!(result.dice.iter().all(|&d| (1..=6).contains(&d)));
        assert_eq!(result.kept.len(), 2);
        assert_eq!(result.total, result.unmodified + 3);
    }

    #[test]
    fn roll_dice_with_filter() {
        let mut rng = StdRng::seed_from_u64(42);
        let expr = DiceExpr::single(4, 6, Some(DiceFilter::KeepHighest(3)), 0);
        let result = roll_dice(&mut rng, &expr);
        assert_eq!(result.dice.len(), 4);
        assert_eq!(result.kept.len(), 3);
        // Kept should be the 3 highest
        let mut all_sorted = result.dice.clone();
        all_sorted.sort_unstable();
        let expected_kept: Vec<i64> = all_sorted.into_iter().rev().take(3).collect();
        let mut kept_sorted = result.kept.clone();
        kept_sorted.sort_unstable();
        kept_sorted.reverse();
        assert_eq!(kept_sorted, expected_kept);
    }

    #[test]
    fn roll_dice_drop_lowest() {
        let mut rng = StdRng::seed_from_u64(123);
        let expr = DiceExpr::single(4, 6, Some(DiceFilter::DropLowest(1)), 0);
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
        let mut prompt_queue = VecDeque::new();
        let no_units = UnitSuffixes::new();
        let mut handler = CliHandler::new(
            &game_state,
            &reverse_handles,
            &mut rng,
            &mut queue,
            &mut prompt_queue,
            &no_units,
        );

        let effect = Effect::RollDice {
            expr: DiceExpr::single(1, 20, None, 5),
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
            let mut f = FxHashMap::default();
            f.insert("HP".into(), Value::Int(30));
            f
        });
        let game_state = RefCell::new(gs);
        let mut reverse = HashMap::new();
        reverse.insert(entity, "fighter".to_string());
        let mut rng = StdRng::seed_from_u64(42);
        let mut queue = VecDeque::new();
        let mut prompt_queue = VecDeque::new();
        let no_units = UnitSuffixes::new();
        let mut handler = CliHandler::new(
            &game_state,
            &reverse,
            &mut rng,
            &mut queue,
            &mut prompt_queue,
            &no_units,
        );

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
            let mut f = FxHashMap::default();
            f.insert("HP".into(), Value::Int(5));
            f
        });
        let game_state = RefCell::new(gs);
        let mut reverse = HashMap::new();
        reverse.insert(entity, "fighter".to_string());
        let mut rng = StdRng::seed_from_u64(42);
        let mut queue = VecDeque::new();
        let mut prompt_queue = VecDeque::new();
        let no_units = UnitSuffixes::new();
        let mut handler = CliHandler::new(
            &game_state,
            &reverse,
            &mut rng,
            &mut queue,
            &mut prompt_queue,
            &no_units,
        );

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
        let entity = gs.add_entity("Fighter", FxHashMap::default());
        let mut budget = BTreeMap::new();
        budget.insert("actions".into(), Value::Int(1));
        gs.set_turn_budget(&entity, budget);
        let game_state = RefCell::new(gs);
        let mut reverse = HashMap::new();
        reverse.insert(entity, "fighter".to_string());
        let mut rng = StdRng::seed_from_u64(42);
        let mut queue = VecDeque::new();
        let mut prompt_queue = VecDeque::new();
        let no_units = UnitSuffixes::new();
        let mut handler = CliHandler::new(
            &game_state,
            &reverse,
            &mut rng,
            &mut queue,
            &mut prompt_queue,
            &no_units,
        );

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
        let mut prompt_queue = VecDeque::new();
        let no_units = UnitSuffixes::new();
        let mut handler = CliHandler::new(
            &game_state,
            &reverse_handles,
            &mut rng,
            &mut queue,
            &mut prompt_queue,
            &no_units,
        );

        let effect = Effect::ResolvePrompt {
            name: "choose_target".into(),
            params: vec![],
            return_type: ttrpg_checker::ty::Ty::Int,
            hint: None,
            suggest: Some(Value::Int(1)),
            has_default: false,
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
        let mut prompt_queue = VecDeque::new();
        let no_units = UnitSuffixes::new();
        let mut handler = CliHandler::new(
            &game_state,
            &reverse_handles,
            &mut rng,
            &mut queue,
            &mut prompt_queue,
            &no_units,
        );

        let effect = Effect::ResolvePrompt {
            name: "choose_target".into(),
            params: vec![],
            return_type: ttrpg_checker::ty::Ty::Int,
            hint: None,
            suggest: None,
            has_default: false,
        };
        let response = handler.handle(effect);
        assert!(matches!(response, Response::UseDefault));
    }

    #[test]
    fn refcell_state_reads() {
        let mut gs = GameState::new();
        let entity = gs.add_entity("Fighter", {
            let mut f = FxHashMap::default();
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
        let expr = DiceExpr::single(2, 6, None, 1);
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
        let expr = DiceExpr::single(2, 6, None, 0);
        let result = roll_dice_from_queue(&mut queue, &mut rng, &expr).unwrap();
        assert_eq!(result.dice[0], 4); // from queue
        assert!(result.dice[1] >= 1 && result.dice[1] <= 6); // from rng
        assert!(queue.is_empty());
    }

    #[test]
    fn roll_dice_from_queue_out_of_range() {
        let mut queue = VecDeque::from(vec![7]); // out of range for d6
        let mut rng = StdRng::seed_from_u64(42);
        let expr = DiceExpr::single(1, 6, None, 0);
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
        let mut prompt_queue = VecDeque::new();
        let no_units = UnitSuffixes::new();
        let mut handler = CliHandler::new(
            &game_state,
            &reverse_handles,
            &mut rng,
            &mut queue,
            &mut prompt_queue,
            &no_units,
        );

        let effect = Effect::RollDice {
            expr: DiceExpr::single(1, 20, None, 5),
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
        let entity = gs.add_entity("Character", FxHashMap::default());
        let game_state = RefCell::new(gs);
        let mut reverse = HashMap::new();
        reverse.insert(entity, "wizard".to_string());
        let mut rng = StdRng::seed_from_u64(42);
        let mut queue = VecDeque::new();
        let mut prompt_queue = VecDeque::new();
        let no_units = UnitSuffixes::new();
        let mut handler = CliHandler::new(
            &game_state,
            &reverse,
            &mut rng,
            &mut queue,
            &mut prompt_queue,
            &no_units,
        );

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
            let mut f = FxHashMap::default();
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
        let mut prompt_queue = VecDeque::new();
        let no_units = UnitSuffixes::new();
        let mut handler = CliHandler::new(
            &game_state,
            &reverse,
            &mut rng,
            &mut queue,
            &mut prompt_queue,
            &no_units,
        );

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
        let entity = gs.add_entity("Fighter", FxHashMap::default());
        let game_state = RefCell::new(gs);
        let mut reverse = HashMap::new();
        reverse.insert(entity, "fighter".to_string());
        let mut rng = StdRng::seed_from_u64(42);
        let mut queue = VecDeque::new();
        let mut prompt_queue = VecDeque::new();
        let no_units = UnitSuffixes::new();
        let mut handler = CliHandler::new(
            &game_state,
            &reverse,
            &mut rng,
            &mut queue,
            &mut prompt_queue,
            &no_units,
        );

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
        let entity = gs.add_entity("Fighter", FxHashMap::default());
        let game_state = RefCell::new(gs);
        let mut reverse = HashMap::new();
        reverse.insert(entity, "fighter".to_string());
        let mut rng = StdRng::seed_from_u64(42);
        let mut queue = VecDeque::new();
        let mut prompt_queue = VecDeque::new();
        let no_units = UnitSuffixes::new();
        let mut handler = CliHandler::new(
            &game_state,
            &reverse,
            &mut rng,
            &mut queue,
            &mut prompt_queue,
            &no_units,
        );

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

    // ── Interactive prompt helper tests ──────────────────────────

    #[test]
    fn parse_prompt_input_int() {
        assert_eq!(parse_prompt_input("42", &Ty::Int), Ok(Value::Int(42)));
        assert_eq!(parse_prompt_input("-7", &Ty::Int), Ok(Value::Int(-7)));
        assert!(parse_prompt_input("abc", &Ty::Int).is_err());
        assert!(parse_prompt_input("3.14", &Ty::Int).is_err());
    }

    #[test]
    fn parse_prompt_input_resource() {
        assert_eq!(parse_prompt_input("10", &Ty::Resource), Ok(Value::Int(10)));
        assert!(parse_prompt_input("nope", &Ty::Resource).is_err());
    }

    #[test]
    fn parse_prompt_input_float() {
        assert_eq!(parse_prompt_input("2.5", &Ty::Float), Ok(Value::Float(2.5)));
        assert_eq!(parse_prompt_input("42", &Ty::Float), Ok(Value::Float(42.0)));
        assert!(parse_prompt_input("abc", &Ty::Float).is_err());
    }

    #[test]
    fn parse_prompt_input_bool() {
        assert_eq!(parse_prompt_input("true", &Ty::Bool), Ok(Value::Bool(true)));
        assert_eq!(parse_prompt_input("yes", &Ty::Bool), Ok(Value::Bool(true)));
        assert_eq!(parse_prompt_input("y", &Ty::Bool), Ok(Value::Bool(true)));
        assert_eq!(parse_prompt_input("1", &Ty::Bool), Ok(Value::Bool(true)));
        assert_eq!(
            parse_prompt_input("false", &Ty::Bool),
            Ok(Value::Bool(false))
        );
        assert_eq!(parse_prompt_input("no", &Ty::Bool), Ok(Value::Bool(false)));
        assert_eq!(parse_prompt_input("n", &Ty::Bool), Ok(Value::Bool(false)));
        assert_eq!(parse_prompt_input("0", &Ty::Bool), Ok(Value::Bool(false)));
        assert!(parse_prompt_input("maybe", &Ty::Bool).is_err());
    }

    #[test]
    fn parse_prompt_input_string() {
        assert_eq!(
            parse_prompt_input("hello world", &Ty::String),
            Ok(Value::Str("hello world".to_string()))
        );
        assert_eq!(
            parse_prompt_input("", &Ty::String),
            Ok(Value::Str(String::new()))
        );
    }

    #[test]
    fn parse_prompt_input_fallback_literal() {
        // Unknown type falls back to parser — int literal works
        let entity_ty = Ty::Entity("Monster".into());
        assert_eq!(parse_prompt_input("42", &entity_ty), Ok(Value::Int(42)));
        // String literal via parser
        assert_eq!(
            parse_prompt_input("\"hello\"", &entity_ty),
            Ok(Value::Str("hello".to_string()))
        );
        // Complex expression is rejected
        assert!(parse_prompt_input("1 + 2", &entity_ty).is_err());
    }

    #[test]
    fn type_hint_returns_expected_labels() {
        assert_eq!(type_hint(&Ty::Int), "int");
        assert_eq!(type_hint(&Ty::Resource), "int");
        assert_eq!(type_hint(&Ty::Float), "float");
        assert_eq!(type_hint(&Ty::Bool), "bool");
        assert_eq!(type_hint(&Ty::String), "string");
        assert_eq!(type_hint(&Ty::Entity("Foo".into())), "entity");
        assert_eq!(type_hint(&Ty::AnyEntity), "entity");
        assert_eq!(type_hint(&Ty::DiceExpr), "value");
    }

    #[test]
    fn format_suggest_values() {
        assert_eq!(format_suggest(&Value::Int(42)), "42");
        assert_eq!(format_suggest(&Value::Float(3.5)), "3.5");
        assert_eq!(format_suggest(&Value::Bool(true)), "true");
        assert_eq!(format_suggest(&Value::Str("hi".into())), "\"hi\"");
    }

    #[test]
    fn interactive_handler_prefers_queue_over_stdin() {
        // Even with interactive=true, queued values take priority
        let game_state = RefCell::new(GameState::new());
        let reverse_handles = HashMap::new();
        let mut rng = StdRng::seed_from_u64(42);
        let mut queue = VecDeque::new();
        let mut prompt_queue = VecDeque::from(vec![Value::Int(99)]);
        let no_units = UnitSuffixes::new();
        let mut handler = CliHandler::new(
            &game_state,
            &reverse_handles,
            &mut rng,
            &mut queue,
            &mut prompt_queue,
            &no_units,
        )
        .interactive(true);

        let effect = Effect::ResolvePrompt {
            name: "pick".into(),
            params: vec![],
            return_type: Ty::Int,
            hint: None,
            suggest: Some(Value::Int(1)),
            has_default: false,
        };
        let response = handler.handle(effect);
        assert!(
            matches!(response, Response::PromptResult(Value::Int(99))),
            "queued value should take priority, got: {response:?}"
        );
        assert!(handler.log[0].contains("(queued)"));
    }

    #[test]
    fn non_interactive_handler_uses_suggest() {
        // When not interactive and no queue, suggest is used
        let game_state = RefCell::new(GameState::new());
        let reverse_handles = HashMap::new();
        let mut rng = StdRng::seed_from_u64(42);
        let mut queue = VecDeque::new();
        let mut prompt_queue = VecDeque::new();
        let no_units = UnitSuffixes::new();
        let mut handler = CliHandler::new(
            &game_state,
            &reverse_handles,
            &mut rng,
            &mut queue,
            &mut prompt_queue,
            &no_units,
        )
        .interactive(false);

        let effect = Effect::ResolvePrompt {
            name: "pick".into(),
            params: vec![],
            return_type: Ty::Int,
            hint: None,
            suggest: Some(Value::Int(7)),
            has_default: false,
        };
        let response = handler.handle(effect);
        assert!(matches!(response, Response::PromptResult(Value::Int(7))));
        assert!(handler.log[0].contains("auto:"));
    }

    #[test]
    fn non_interactive_handler_uses_default_over_suggest() {
        // When not interactive, has_default=true takes priority over suggest
        let game_state = RefCell::new(GameState::new());
        let reverse_handles = HashMap::new();
        let mut rng = StdRng::seed_from_u64(42);
        let mut queue = VecDeque::new();
        let mut prompt_queue = VecDeque::new();
        let no_units = UnitSuffixes::new();
        let mut handler = CliHandler::new(
            &game_state,
            &reverse_handles,
            &mut rng,
            &mut queue,
            &mut prompt_queue,
            &no_units,
        )
        .interactive(false);

        let effect = Effect::ResolvePrompt {
            name: "pick".into(),
            params: vec![],
            return_type: Ty::Int,
            hint: None,
            suggest: Some(Value::Int(7)),
            has_default: true,
        };
        let response = handler.handle(effect);
        assert!(matches!(response, Response::UseDefault));
        assert!(handler.log[0].contains("use default"));
    }

    // ── prompt_loop tests ───────────────────────────────────────

    use std::io::Cursor;

    fn run_prompt_loop(
        input: &str,
        return_type: &Ty,
        suggest: Option<&Value>,
    ) -> (PromptOutcome, String) {
        let mut reader = Cursor::new(input.as_bytes().to_vec());
        let mut writer = Vec::new();
        let result = prompt_loop(
            &mut reader,
            &mut writer,
            "test_prompt",
            Some("Pick a value"),
            return_type,
            suggest,
        );
        let output = String::from_utf8(writer).unwrap();
        (result, output)
    }

    #[test]
    fn prompt_loop_valid_int_input() {
        let (result, output) = run_prompt_loop("42\n", &Ty::Int, None);
        assert!(matches!(result, PromptOutcome::Value(Value::Int(42))));
        assert!(output.contains("[prompt] test_prompt"));
        assert!(output.contains("Pick a value"));
        assert!(output.contains("(int)"));
    }

    #[test]
    fn prompt_loop_valid_bool_input() {
        let (result, _) = run_prompt_loop("yes\n", &Ty::Bool, None);
        assert!(matches!(result, PromptOutcome::Value(Value::Bool(true))));
    }

    #[test]
    fn prompt_loop_valid_string_input() {
        let (result, _) = run_prompt_loop("hello world\n", &Ty::String, None);
        assert!(matches!(result, PromptOutcome::Value(Value::Str(s)) if s == "hello world"));
    }

    #[test]
    fn prompt_loop_empty_input_with_suggest() {
        let suggest = Value::Int(7);
        let (result, _) = run_prompt_loop("\n", &Ty::Int, Some(&suggest));
        assert!(matches!(result, PromptOutcome::Value(Value::Int(7))));
    }

    #[test]
    fn prompt_loop_empty_input_without_suggest() {
        let (result, _) = run_prompt_loop("\n", &Ty::Int, None);
        assert!(matches!(result, PromptOutcome::UseDefault));
    }

    #[test]
    fn prompt_loop_eof_returns_vetoed() {
        let (result, _) = run_prompt_loop("", &Ty::Int, None);
        assert!(matches!(result, PromptOutcome::Vetoed));
    }

    #[test]
    fn prompt_loop_retry_then_succeed() {
        // First line is invalid, second is valid
        let (result, output) = run_prompt_loop("abc\n42\n", &Ty::Int, None);
        assert!(matches!(result, PromptOutcome::Value(Value::Int(42))));
        assert!(output.contains("error:"));
    }

    #[test]
    fn prompt_loop_retry_then_eof() {
        // Invalid input followed by EOF
        let (result, output) = run_prompt_loop("abc\n", &Ty::Int, None);
        assert!(matches!(result, PromptOutcome::Vetoed));
        assert!(output.contains("error:"));
    }

    #[test]
    fn prompt_loop_shows_suggest_in_header() {
        let suggest = Value::Int(5);
        let (_, output) = run_prompt_loop("10\n", &Ty::Int, Some(&suggest));
        assert!(output.contains("[default: 5]"));
    }

    #[test]
    fn prompt_loop_float_input() {
        let (result, _) = run_prompt_loop("2.5\n", &Ty::Float, None);
        assert!(
            matches!(result, PromptOutcome::Value(Value::Float(f)) if (f - 2.5).abs() < f64::EPSILON)
        );
    }
}
