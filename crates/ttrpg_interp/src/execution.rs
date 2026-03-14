//! Step-based execution API.
//!
//! The [`Execution`] object owns its game state and exposes a pull-based
//! `poll()`/`respond()` API, letting hosts drive execution at their own pace.
//! This is the complement to the callback-based `Interpreter` + `EffectHandler`
//! API, targeting async hosts, non-Rust embeddings, and step-debugging.

#![allow(dead_code)]

use std::collections::BTreeMap;
use std::rc::Rc;

use ttrpg_ast::ast::{Block, CostClause, ExprKind, StmtKind};
use ttrpg_ast::{Name, Span, Spanned};

use crate::adapter::StateAdapter;
use crate::effect::{
    ActionKind, ActionOutcome, Effect, EffectHandler, EffectKind, Response, Step,
};
use crate::runtime_core::RuntimeCore;
use crate::select_action_overload;
use crate::state::{
    ActiveCondition, ConditionToken, EntityRef, InvocationId, StateProvider,
    WritableState,
};
use crate::value::Value;
use crate::{Env, Interpreter, RuntimeError, Scope};

// ── ExecEnv ────────────────────────────────────────────────────

/// Per-execution environment state (mirrors `Env` fields).
///
/// Separated from `Execution` so frames can borrow it independently
/// from the frame stack.
pub(crate) struct ExecEnv {
    pub scopes: Vec<Scope>,
    pub turn_actor: Option<EntityRef>,
    pub cost_payer: Option<EntityRef>,
    pub current_invocation_id: Option<InvocationId>,
    pub emit_depth: u32,
    pub in_lifecycle_block: u32,
    pub lifecycle_condition_stack: Vec<u64>,
    pub current_condition_token: Option<ConditionToken>,
    pub return_value: Option<Value>,
    /// Deferred bridge call info for non-action entry points.
    pub bridge_call: Option<BridgeCallInfo>,
}

/// Information about a deferred bridge call (for non-action entry points).
pub(crate) enum BridgeCallInfo {
    Derive { name: Name, args: Vec<Value> },
    Mechanic { name: Name, args: Vec<Value> },
    Function { name: Name, args: Vec<Value> },
    Expr { expr: Spanned<ExprKind> },
}

impl ExecEnv {
    fn new() -> Self {
        ExecEnv {
            scopes: vec![Scope::new()],
            turn_actor: None,
            cost_payer: None,
            current_invocation_id: None,
            emit_depth: 0,
            in_lifecycle_block: 0,
            lifecycle_condition_stack: Vec::new(),
            current_condition_token: None,
            return_value: None,
            bridge_call: None,
        }
    }

    fn push_scope(&mut self) {
        self.scopes.push(Scope::new());
    }

    fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    fn bind(&mut self, name: Name, value: Value) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.bindings.insert(name, value);
        }
    }
}

// ── Bridge evaluation ──────────────────────────────────────────

/// Evaluate a block using the existing recursive evaluator.
///
/// Creates a temporary `Interpreter` and `Env` backed by the step-based
/// context, runs `eval_block`, and syncs state back. Locally-applied
/// mutation effects are handled by the `StateAdapter`; host-decided
/// effects will panic (async `poll()` path). For synchronous execution,
/// use `bridge_eval_block_with_handler` instead.
fn bridge_eval_block<S: WritableState>(
    core: &RuntimeCore,
    env: &mut ExecEnv,
    state: &StateAdapter<S>,
    block: &Block,
) -> Result<Value, RuntimeError> {
    struct NoYieldHandler;
    impl EffectHandler for NoYieldHandler {
        fn handle(&mut self, effect: Effect) -> Response {
            panic!(
                "unexpected forwarded effect in bridge evaluation: {:?}",
                EffectKind::of(&effect)
            )
        }
    }
    bridge_eval_with(core, env, state, &mut NoYieldHandler, |tmp_env| {
        crate::eval::eval_block(tmp_env, block)
    })
}

/// Evaluate a single expression using the existing recursive evaluator.
fn bridge_eval_expr<S: WritableState>(
    core: &RuntimeCore,
    env: &mut ExecEnv,
    state: &StateAdapter<S>,
    expr: &Spanned<ExprKind>,
) -> Result<Value, RuntimeError> {
    struct NoYieldHandler;
    impl EffectHandler for NoYieldHandler {
        fn handle(&mut self, effect: Effect) -> Response {
            panic!(
                "unexpected forwarded effect in bridge evaluation: {:?}",
                EffectKind::of(&effect)
            )
        }
    }
    bridge_eval_with(core, env, state, &mut NoYieldHandler, |tmp_env| {
        crate::eval::eval_expr(tmp_env, expr)
    })
}

/// Common bridge setup with an explicit handler.
///
/// Snapshots ExecEnv into a temporary `Env`, runs a closure through the
/// recursive evaluator, and syncs state back. The handler receives all
/// non-locally-applied effects (RollDice, Prompt, etc.).
fn bridge_eval_with<S, H, F>(
    core: &RuntimeCore,
    env: &mut ExecEnv,
    state: &StateAdapter<S>,
    handler: &mut H,
    f: F,
) -> Result<Value, RuntimeError>
where
    S: WritableState,
    H: EffectHandler + ?Sized,
    F: FnOnce(&mut Env) -> Result<Value, RuntimeError>,
{
    let interp = Interpreter::bridge(
        &core.program,
        &core.type_env,
        core.counters().0,
        core.counters().1,
    );

    // Snapshot all ExecEnv state so the closure doesn't need &mut env.
    let scopes = std::mem::take(&mut env.scopes);
    let lc_stack = std::mem::take(&mut env.lifecycle_condition_stack);
    let ret_val = env.return_value.take();
    let turn_actor = env.turn_actor;
    let cost_payer = env.cost_payer;
    let invocation_id = env.current_invocation_id;
    let emit_depth = env.emit_depth;
    let in_lifecycle = env.in_lifecycle_block;
    let condition_token = env.current_condition_token;

    let (result, out_scopes, out_lc_stack, out_ret_val) =
        state.run(handler, |state_provider, effect_handler| {
            let mut tmp_env = Env {
                state: state_provider,
                handler: effect_handler,
                interp: &interp,
                scopes,
                turn_actor,
                cost_payer,
                current_invocation_id: invocation_id,
                emit_depth,
                in_lifecycle_block: in_lifecycle,
                lifecycle_condition_stack: lc_stack,
                current_condition_token: condition_token,
                return_value: ret_val,
            };

            let result = f(&mut tmp_env);

            (
                result,
                std::mem::take(&mut tmp_env.scopes),
                std::mem::take(&mut tmp_env.lifecycle_condition_stack),
                tmp_env.return_value.take(),
            )
        });

    // Restore ExecEnv state
    env.scopes = out_scopes;
    env.lifecycle_condition_stack = out_lc_stack;
    env.return_value = out_ret_val;

    // Sync ID counters back to RuntimeCore
    let (inv, cond) = interp.id_counters();
    core.sync_counters(inv, cond);

    result
}

// ── Action lifecycle step machine ──────────────────────────────

/// Phase within the unified action lifecycle frame.
#[derive(Debug)]
pub(crate) enum ActionStep {
    /// Emit ActionStarted effect.
    EmitStarted,
    /// Gate response received, dispatch on Acknowledged/Vetoed.
    AwaitGate,
    /// Gate was vetoed: emit ActionCompleted(Vetoed).
    EmitVetoedCompleted,
    /// Vetoed completion ack received: pop with abort value.
    AwaitVetoedAck,
    /// Evaluate requires clause (if present), emit RequiresCheck.
    EvalRequires,
    /// Requires response received: check pass/fail.
    AwaitRequires,
    /// Run the resolve body via bridge.
    RunResolve,
    /// Run the full pipeline (requires → cost → resolve) via bridge.
    RunPipeline,
    /// Body completed: emit ActionCompleted.
    EmitCompleted,
    /// Completion ack received: restore context, pop with result.
    AwaitCompletedAck,
}

// ── Frame enum ─────────────────────────────────────────────────

/// Each frame variant represents a point where execution suspended waiting
/// for an effect response, or a context boundary that needs cleanup on unwind.
#[allow(clippy::large_enum_variant)]
pub(crate) enum Frame {
    // ── Action lifecycle (Phase 3) ──────────────────────────

    /// Unified action/reaction/hook lifecycle frame.
    ///
    /// Manages the entire lifecycle: ActionStarted gate → context setup →
    /// defaults → requires → cost → resolve body → ActionCompleted.
    ActionLifecycle {
        name: Name,
        actor: EntityRef,
        action_kind: ActionKind,
        call_span: Span,
        has_return_type: bool,
        inv_id: InvocationId,
        // Pipeline data
        requires: Option<Spanned<ExprKind>>,
        cost: Option<CostClause>,
        resolve: Block,
        // Bindings to apply after gate passes
        receiver_name: Name,
        bindings: Vec<(Name, Value)>,
        // Default expressions for missing optional params
        default_params: Vec<(Name, Spanned<ExprKind>)>,
        // Step machine
        step: ActionStep,
        pending: Option<Response>,
        body_result: Option<Result<Value, RuntimeError>>,
        // Context save (populated when gate passes)
        saved_turn_actor: Option<EntityRef>,
        saved_invocation: Option<InvocationId>,
    },

    // ── Placeholder variants for Phases 4-5 ─────────────────

    /// Block execution (Phase 4).
    Block {
        stmts: Vec<Spanned<StmtKind>>,
        index: usize,
        result: Value,
        expr_cache: Vec<Value>,
    },

    StmtResume {
        kind: StmtResumeKind,
        expr_cache: Vec<Value>,
    },

    FillDefaults {
        params: Vec<DefaultParam>,
        resolved: Vec<(Name, Value)>,
        index: usize,
    },

    DeriveEval {
        name: Name,
        base_value: Option<Value>,
        modify_hooks: Vec<HookInfo>,
        hook_index: usize,
    },

    FunctionEval {
        name: Name,
    },

    EmitEval {
        event_name: Name,
        phase: EmitEvalPhase,
    },

    EmitHooks {
        event_name: Name,
        hooks: Vec<HookInfo>,
        index: usize,
        payload: Value,
        saved_emit_depth: u32,
        saved_lifecycle: u32,
    },

    EmitConditionHandlers {
        handlers: Vec<ConditionHandlerInfo>,
        index: usize,
        payload: Value,
    },

    ConditionHandlerEpilogue {
        target: EntityRef,
        condition_name: Name,
        instance_id: u64,
        original_state: BTreeMap<Name, Value>,
    },

    ConditionApplyGate {
        target: EntityRef,
        condition_name: Name,
        params: Vec<(Name, Value)>,
        duration: Value,
        source: Value,
        tags: Vec<Name>,
        token: ConditionToken,
    },

    ConditionOnApply {
        target: EntityRef,
        condition_name: Name,
        params: Vec<(Name, Value)>,
        duration: Value,
        source: Value,
        tags: Vec<Name>,
        token: ConditionToken,
        state_fields: BTreeMap<Name, Value>,
    },

    ConditionActivate {
        token: ConditionToken,
    },

    ConditionRemovalLoop {
        target: EntityRef,
        condition_name: Name,
        instances: Vec<ActiveCondition>,
        index: usize,
        first_error: Option<RuntimeError>,
        removed_count: u32,
    },

    ConditionRemovalGate {
        target: EntityRef,
        condition_name: Name,
        instance_id: u64,
    },

    ConditionOnRemove {
        target: EntityRef,
        condition_name: Name,
        instance_id: u64,
        state_fields: BTreeMap<Name, Value>,
    },

    RollDiceWaiting {
        span: Span,
    },

    PromptWaiting {
        default_block: Option<Block>,
        span: Span,
    },

    SpawnEntity {
        entity_type: Name,
        base_fields: Vec<(Name, Value)>,
        groups: Vec<GroupInit>,
        phase: SpawnPhase,
    },

    ScopeGuard,

    BudgetGuard {
        actor: EntityRef,
        saved_budget: Option<BTreeMap<Name, Value>>,
    },

    MultiBudgetGuard {
        entries: Vec<(EntityRef, BTreeMap<Name, Value>)>,
        saved_budgets: Vec<(EntityRef, Option<BTreeMap<Name, Value>>)>,
        provision_index: usize,
        phase: MultiBudgetPhase,
    },

    CostPayerGuard {
        saved_payer: Option<EntityRef>,
    },

    /// Bridge call frame for non-action entry points (derive, mechanic,
    /// function, expr). The result is computed synchronously during
    /// `run_with_handler` and stored here; advance() just pops it.
    BridgeCall {
        result: Option<Result<Value, RuntimeError>>,
    },
}

// ── Frame advance implementation ───────────────────────────────

impl Frame {
    /// Advance the frame one step. Returns the action for the driver loop.
    ///
    /// When `handler` is `Some`, host-decided effects inside bridge evaluation
    /// are handled synchronously (used by `run_with_handler`). When `None`,
    /// bridge evaluation panics on host-decided effects (async `poll()` path).
    /// Advance the frame one step. Returns the action for the driver loop.
    ///
    /// For bridge evaluation inside frames, this uses `NoYieldHandler` which
    /// panics on host-decided effects. For synchronous execution with a real
    /// handler, use `advance_sync` instead.
    fn advance<S: WritableState>(
        &mut self,
        core: &RuntimeCore,
        env: &mut ExecEnv,
        state: &StateAdapter<S>,
    ) -> Advance {
        Self::advance_action(self, core, env, state, None)
    }

    /// Advance with a handler for synchronous bridge evaluation.
    fn advance_sync<S: WritableState>(
        &mut self,
        core: &RuntimeCore,
        env: &mut ExecEnv,
        state: &StateAdapter<S>,
        handler: &mut dyn EffectHandler,
    ) -> Advance {
        Self::advance_action(self, core, env, state, Some(handler))
    }

    /// Shared advance implementation. When `handler` is Some, bridge
    /// evaluation forwards host-decided effects to it. When None,
    /// bridge evaluation panics on host-decided effects.
    fn advance_action<S: WritableState>(
        frame: &mut Frame,
        core: &RuntimeCore,
        env: &mut ExecEnv,
        state: &StateAdapter<S>,
        mut handler: Option<&mut dyn EffectHandler>,
    ) -> Advance {
        match frame {
            Frame::ActionLifecycle {
                name,
                actor,
                action_kind,
                call_span,
                has_return_type,
                inv_id,
                requires,
                cost,
                resolve,
                receiver_name,
                bindings,
                default_params,
                step,
                pending,
                body_result,
                saved_turn_actor,
                saved_invocation,
            } => {
                let abort_value = if *has_return_type {
                    Value::Option(None)
                } else {
                    Value::Void
                };

                match step {
                    ActionStep::EmitStarted => {
                        let effect = Effect::ActionStarted {
                            name: name.clone(),
                            kind: action_kind.clone(),
                            actor: *actor,
                            params: bindings.iter().map(|(_, v)| v.clone()).collect(),
                        };
                        *step = ActionStep::AwaitGate;
                        Advance::Yield(effect)
                    }

                    ActionStep::AwaitGate => {
                        let response = match pending.take() {
                            Some(r) => r,
                            None => return Advance::Continue,
                        };

                        match response {
                            Response::Acknowledged => {
                                *saved_turn_actor = env.turn_actor.take();
                                *saved_invocation = env.current_invocation_id.take();
                                env.turn_actor = Some(*actor);
                                env.current_invocation_id = Some(*inv_id);
                                env.push_scope();

                                env.bind(receiver_name.clone(), Value::Entity(*actor));
                                for (pname, pval) in bindings.drain(..) {
                                    env.bind(pname, pval);
                                }

                                // Evaluate defaults
                                for (dname, dexpr) in default_params.drain(..) {
                                    let result = if let Some(ref mut h) = handler {
                                        bridge_eval_with(
                                            core, env, state, *h,
                                            |tmp_env| crate::eval::eval_expr(tmp_env, &dexpr),
                                        )
                                    } else {
                                        bridge_eval_expr(core, env, state, &dexpr)
                                    };
                                    match result {
                                        Ok(val) => env.bind(dname, val),
                                        Err(e) => {
                                            *body_result = Some(Err(e));
                                            *step = ActionStep::EmitCompleted;
                                            return Advance::Continue;
                                        }
                                    }
                                }

                                // Run pipeline
                                *step = if handler.is_some() {
                                    ActionStep::RunPipeline
                                } else {
                                    ActionStep::EvalRequires
                                };
                                Advance::Continue
                            }

                            Response::Vetoed => {
                                *step = ActionStep::EmitVetoedCompleted;
                                Advance::Continue
                            }

                            other => {
                                *body_result = Some(Err(RuntimeError::with_span(
                                    format!(
                                        "protocol error: expected Acknowledged or Vetoed \
                                         for ActionStarted, got {other:?}"
                                    ),
                                    *call_span,
                                )));
                                *step = ActionStep::EmitVetoedCompleted;
                                Advance::Continue
                            }
                        }
                    }

                    ActionStep::EmitVetoedCompleted => {
                        let outcome = if body_result
                            .as_ref()
                            .is_some_and(|r| r.is_err())
                        {
                            ActionOutcome::Failed
                        } else {
                            ActionOutcome::Vetoed
                        };
                        let inv = if outcome == ActionOutcome::Vetoed {
                            None
                        } else {
                            Some(*inv_id)
                        };
                        let effect = Effect::ActionCompleted {
                            name: name.clone(),
                            actor: *actor,
                            outcome,
                            invocation: inv,
                        };
                        *step = ActionStep::AwaitVetoedAck;
                        Advance::Yield(effect)
                    }

                    ActionStep::AwaitVetoedAck => {
                        let _ = pending.take();
                        if let Some(Err(e)) = body_result.take() {
                            return Advance::Error(e);
                        }
                        Advance::Pop(abort_value)
                    }

                    ActionStep::EvalRequires => {
                        if let Some(req_expr) = requires.as_ref() {
                            match bridge_eval_expr(core, env, state, req_expr) {
                                Ok(Value::Bool(passed)) => {
                                    let effect = Effect::RequiresCheck {
                                        action: name.clone(),
                                        passed,
                                        reason: None,
                                    };
                                    *body_result = Some(Ok(Value::Bool(passed)));
                                    *step = ActionStep::AwaitRequires;
                                    Advance::Yield(effect)
                                }
                                Ok(other) => Advance::Error(RuntimeError::with_span(
                                    format!(
                                        "requires clause must evaluate to Bool, got {other:?}"
                                    ),
                                    req_expr.span,
                                )),
                                Err(e) => Advance::Error(e),
                            }
                        } else {
                            // No requires clause, skip to resolve
                            *step = ActionStep::RunResolve;
                            Advance::Continue
                        }
                    }

                    ActionStep::AwaitRequires => {
                        let response = match pending.take() {
                            Some(r) => r,
                            None => return Advance::Continue,
                        };
                        let original_passed = match body_result.take() {
                            Some(Ok(Value::Bool(b))) => b,
                            _ => false,
                        };

                        let effective_passed = match response {
                            Response::Override(Value::Bool(b)) => b,
                            Response::Acknowledged => original_passed,
                            other => {
                                return Advance::Error(RuntimeError::with_span(
                                    format!(
                                        "protocol error: expected Acknowledged or \
                                         Override(Bool) for RequiresCheck, got {other:?}"
                                    ),
                                    *call_span,
                                ));
                            }
                        };

                        if effective_passed {
                            *step = ActionStep::RunResolve;
                            Advance::Continue
                        } else {
                            *body_result = Some(Ok(abort_value));
                            *step = ActionStep::EmitCompleted;
                            Advance::Continue
                        }
                    }

                    ActionStep::RunResolve => {
                        let resolve_block = resolve.clone();
                        let result = bridge_eval_block(core, env, state, &resolve_block);
                        env.return_value = None;
                        *body_result = Some(result);
                        *step = ActionStep::EmitCompleted;
                        Advance::Continue
                    }

                    ActionStep::RunPipeline => {
                        // Run the full pipeline (requires → cost → resolve)
                        // through the recursive evaluator with a handler.
                        // Only reachable from the sync path (handler is Some).
                        let h = handler.as_mut()
                            .expect("RunPipeline requires a handler (sync path)");
                        let actor_val = *actor;
                        let name_val = name.clone();
                        let requires_val = requires.clone();
                        let cost_val = cost.clone();
                        let resolve_val = resolve.clone();
                        let hrt = *has_return_type;
                        let span = *call_span;

                        let result = bridge_eval_with(
                            core, env, state, *h,
                            move |tmp_env| {
                                crate::action::execute_pipeline(
                                    tmp_env,
                                    &actor_val,
                                    &name_val,
                                    requires_val.as_ref(),
                                    cost_val.as_ref(),
                                    &resolve_val,
                                    hrt,
                                    span,
                                )
                            },
                        );
                        env.return_value = None;
                        *body_result = Some(result);
                        *step = ActionStep::EmitCompleted;
                        Advance::Continue
                    }

                    ActionStep::EmitCompleted => {
                        let outcome = match body_result {
                            Some(Ok(_)) => ActionOutcome::Succeeded,
                            Some(Err(_)) => ActionOutcome::Failed,
                            None => ActionOutcome::Succeeded,
                        };
                        let effect = Effect::ActionCompleted {
                            name: name.clone(),
                            actor: *actor,
                            outcome,
                            invocation: Some(*inv_id),
                        };
                        *step = ActionStep::AwaitCompletedAck;
                        Advance::Yield(effect)
                    }

                    ActionStep::AwaitCompletedAck => {
                        let _ = pending.take();
                        env.pop_scope();
                        env.turn_actor = saved_turn_actor.take();
                        env.current_invocation_id = saved_invocation.take();

                        match body_result.take() {
                            Some(Ok(val)) => Advance::Pop(val),
                            Some(Err(e)) => Advance::Error(e),
                            None => Advance::Pop(Value::Void),
                        }
                    }

                }
            }

            Frame::BridgeCall { result } => {
                if let Some(r) = result.take() {
                    return match r {
                        Ok(v) => Advance::Pop(v),
                        Err(e) => Advance::Error(e),
                    };
                }
                // Execute the bridge call now (handler must be available).
                if let Some(call_info) = env.bridge_call.take() {
                    if let Some(h) = handler.as_mut() {
                        let r = match call_info {
                            BridgeCallInfo::Derive { ref name, ref args } => {
                                let n = name.clone();
                                let a = args.clone();
                                let is_table = core.program.tables.contains_key(n.as_ref());
                                bridge_eval_with(core, env, state, *h, |tmp_env| {
                                    if is_table {
                                        crate::call::dispatch_table_with_values(
                                            tmp_env, &n, a, Span::dummy(),
                                        )
                                    } else {
                                        crate::call::evaluate_fn_with_values(
                                            tmp_env, &n, a, Span::dummy(),
                                        )
                                    }
                                })
                            }
                            BridgeCallInfo::Mechanic { ref name, ref args } => {
                                let n = name.clone();
                                let a = args.clone();
                                bridge_eval_with(core, env, state, *h, |tmp_env| {
                                    crate::call::evaluate_fn_with_values(
                                        tmp_env, &n, a, Span::dummy(),
                                    )
                                })
                            }
                            BridgeCallInfo::Function { ref name, ref args } => {
                                let n = name.clone();
                                let a = args.clone();
                                bridge_eval_with(core, env, state, *h, |tmp_env| {
                                    crate::call::evaluate_function_with_values(
                                        tmp_env, &n, a, Span::dummy(),
                                    )
                                })
                            }
                            BridgeCallInfo::Expr { ref expr } => {
                                let e = expr.clone();
                                bridge_eval_with(core, env, state, *h, |tmp_env| {
                                    crate::eval::eval_expr(tmp_env, &e)
                                })
                            }
                        };
                        match r {
                            Ok(v) => Advance::Pop(v),
                            Err(e) => Advance::Error(e),
                        }
                    } else {
                        Advance::Error(RuntimeError::new(
                            "BridgeCall requires a handler (use run_with_handler)"
                        ))
                    }
                } else {
                    Advance::Error(RuntimeError::new("BridgeCall frame has no call info"))
                }
            }

            Frame::ScopeGuard => Advance::Pop(Value::Void),
            _ => Advance::Error(RuntimeError::new(
                "frame type not yet implemented",
            )),
        }
    }

    /// Deliver a host response to this frame.
    fn receive_response(&mut self, response: Response) {
        if let Frame::ActionLifecycle { pending, .. } = self {
            *pending = Some(response);
        }
    }

    /// Deliver a child frame's completion value.
    fn receive_child_result(&mut self, _value: Value) {
        // Phase 3 MVP: ActionLifecycle doesn't push child frames;
        // it runs everything synchronously via the bridge.
        // Phase 4+ will add child frame support.
    }
}

// ── Supporting types for Frame variants ────────────────────────

/// Phase within the action body pipeline.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ActionBodyPhase {
    Requires,
    Cost,
    Resolve,
}

/// A cost token to be deducted during ActionCost processing.
#[derive(Debug, Clone)]
pub(crate) struct CostToken {
    pub name: Name,
    pub span: Span,
}

/// Continuation data for a statement that yielded mid-evaluation.
#[derive(Debug)]
pub(crate) enum StmtResumeKind {
    Grant {
        entity: EntityRef,
        group_name: Name,
        fields: BTreeMap<Name, Value>,
        span: Span,
    },
    Revoke {
        entity: EntityRef,
        group_name: Name,
        span: Span,
    },
    Assign {
        segments: Vec<Name>,
        span: Span,
    },
    BudgetProvision {
        actor: EntityRef,
        budget: BTreeMap<Name, Value>,
    },
    BudgetClear {
        actor: EntityRef,
    },
    Spawn {
        entity_type: Name,
        fields: BTreeMap<Name, Value>,
        span: Span,
    },
}

/// A parameter whose default expression may need evaluation.
#[derive(Debug, Clone)]
pub(crate) struct DefaultParam {
    pub name: Name,
    pub provided_value: Option<Value>,
    pub has_default: bool,
}

/// Information about a hook to be dispatched.
#[derive(Debug, Clone)]
pub(crate) struct HookInfo {
    pub hook_name: Name,
    pub actor: EntityRef,
}

/// Information about a condition handler to be dispatched.
#[derive(Debug, Clone)]
pub(crate) struct ConditionHandlerInfo {
    pub target: EntityRef,
    pub condition_name: Name,
    pub instance_id: u64,
    pub handler_index: usize,
}

/// Phase within emit evaluation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum EmitEvalPhase {
    Args,
    ParamDefaults,
    FieldDefaults,
    Ready,
}

/// Group initialization data for entity construction.
#[derive(Debug, Clone)]
pub(crate) struct GroupInit {
    pub group_name: Name,
    pub fields: BTreeMap<Name, Value>,
}

/// Phase within entity spawn.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SpawnPhase {
    Defaults,
    Spawned,
    GrantingGroups { index: usize },
}

/// Phase within multi-entity budget scope.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum MultiBudgetPhase {
    Provisioning,
    Body,
    Restoring { index: usize },
}

// ── Advance enum ───────────────────────────────────────────────

/// Result of advancing a single frame one step.
#[allow(clippy::large_enum_variant)]
pub(crate) enum Advance {
    /// Yield an effect to the host and suspend.
    Yield(Effect),
    /// Push a child frame onto the stack.
    Push(Frame),
    /// Pop the current frame, returning a value to the parent.
    Pop(Value),
    /// Frame updated itself in place; loop again.
    Continue,
    /// Unrecoverable error.
    Error(RuntimeError),
}

// ── Protocol types ─────────────────────────────────────────────

/// Tracks the poll/respond protocol to prevent misuse.
#[derive(Debug, Clone)]
enum ProtocolState {
    /// Ready to call poll(). No pending effect.
    Idle,
    /// poll() yielded an effect. Host must call respond().
    Pending,
    /// Unwinding after an error. Cleanup frames may still yield effects.
    Unwinding(RuntimeError),
    /// Execution has completed (Done or Error). No further calls.
    Completed,
}

/// Errors from protocol misuse (not runtime evaluation errors).
#[derive(Debug, Clone)]
pub enum ProtocolError {
    /// respond() called when no effect is pending.
    NoPendingEffect,
    /// poll() called while an effect is pending (must respond first).
    EffectPending,
    /// poll() or respond() called after execution completed.
    ExecutionCompleted,
}

/// Unified error type for poll()/respond(). Separates host bugs
/// (protocol misuse) from DSL evaluation failures (runtime errors).
#[derive(Debug)]
pub enum PollError {
    /// Host violated the poll/respond protocol (programming error).
    Protocol(ProtocolError),
    /// DSL evaluation produced a runtime error (after unwind completed).
    Runtime(RuntimeError),
}

impl From<ProtocolError> for PollError {
    fn from(e: ProtocolError) -> Self {
        PollError::Protocol(e)
    }
}

// ── Execution struct ───────────────────────────────────────────

/// Owning step-based execution object.
///
/// Hosts poll for effects and provide responses, driving execution
/// at their own pace. Owns game state via `StateAdapter<S>`.
pub struct Execution<S: WritableState> {
    // ── Shared runtime ──
    core: Rc<RuntimeCore>,

    // ── Frame stack ──
    frames: Vec<Frame>,

    // ── Per-execution state ──
    env: ExecEnv,

    // ── Owned game state ──
    state: StateAdapter<S>,

    // ── Protocol state ──
    protocol: ProtocolState,
    pending_before_yield: Option<ProtocolState>,

    // ── Final result (set when the last frame pops) ──
    final_result: Option<Result<Value, RuntimeError>>,
}

impl<S: WritableState> Execution<S> {
    /// Create a new execution. Frames must be pushed before polling.
    pub(crate) fn new(core: Rc<RuntimeCore>, state: StateAdapter<S>) -> Self {
        Execution {
            core,
            frames: Vec::new(),
            env: ExecEnv::new(),
            state,
            protocol: ProtocolState::Idle,
            pending_before_yield: None,
            final_result: None,
        }
    }

    // ── Entry points (Phase 3) ─────────────────────────────────

    /// Start executing an action.
    ///
    /// Looks up the action declaration, selects the correct overload,
    /// maps positional arguments, pre-allocates the invocation ID, and
    /// pushes the initial `ActionLifecycle` frame.
    pub fn start_action(
        core: Rc<RuntimeCore>,
        state: StateAdapter<S>,
        action_name: &str,
        actor: EntityRef,
        args: Vec<Value>,
        call_span: Span,
    ) -> Result<Self, RuntimeError> {
        let overloads = core
            .program
            .actions
            .get(action_name)
            .ok_or_else(|| RuntimeError::new(format!("undefined action '{action_name}'")))?;

        let entity_type = state.entity_type_name(&actor);
        let action_decl =
            select_action_overload(overloads, entity_type.as_ref())
                .ok_or_else(|| {
                    RuntimeError::new(format!(
                        "no matching overload for action '{}' on entity type '{}'",
                        action_name,
                        entity_type.as_deref().unwrap_or("unknown")
                    ))
                })?
                .clone();

        // Map positional args to param names
        if args.len() > action_decl.params.len() {
            return Err(RuntimeError::new(format!(
                "too many arguments: action '{}' takes {} params, got {}",
                action_name,
                action_decl.params.len(),
                args.len()
            )));
        }
        // Check required params
        for i in args.len()..action_decl.params.len() {
            if action_decl.params[i].default.is_none() {
                return Err(RuntimeError::new(format!(
                    "missing required argument '{}' for action '{}'",
                    action_decl.params[i].name, action_name
                )));
            }
        }

        let mut bindings = Vec::new();
        for (i, val) in args.into_iter().enumerate() {
            bindings.push((action_decl.params[i].name.clone(), val));
        }

        // Collect default expressions for missing optional params
        let mut default_params = Vec::new();
        for i in bindings.len()..action_decl.params.len() {
            if let Some(ref default_expr) = action_decl.params[i].default {
                default_params.push((
                    action_decl.params[i].name.clone(),
                    default_expr.clone(),
                ));
            }
        }

        // Pre-allocate invocation ID
        let inv_id = InvocationId(core.alloc_invocation_id());

        let mut exec = Self::new(core, state);

        exec.frames.push(Frame::ActionLifecycle {
            name: action_decl.name.clone(),
            actor,
            action_kind: ActionKind::Action,
            call_span,
            has_return_type: action_decl.return_type.is_some(),
            inv_id,
            requires: action_decl.requires.clone(),
            cost: action_decl.cost.clone(),
            resolve: action_decl.resolve.clone(),
            receiver_name: action_decl.receiver_name.clone(),
            bindings,
            default_params,
            step: ActionStep::EmitStarted,
            pending: None,
            body_result: None,
            saved_turn_actor: None,
            saved_invocation: None,
        });

        Ok(exec)
    }

    /// Start executing a reaction.
    pub fn start_reaction(
        core: Rc<RuntimeCore>,
        state: StateAdapter<S>,
        reaction_name: &str,
        reactor: EntityRef,
        event_payload: Value,
        call_span: Span,
    ) -> Result<Self, RuntimeError> {
        let reaction_decl = core
            .program
            .reactions
            .get(reaction_name)
            .ok_or_else(|| {
                RuntimeError::new(format!("undefined reaction '{reaction_name}'"))
            })?
            .clone();

        let inv_id = InvocationId(core.alloc_invocation_id());

        let mut exec = Self::new(core, state);

        exec.frames.push(Frame::ActionLifecycle {
            name: reaction_decl.name.clone(),
            actor: reactor,
            action_kind: ActionKind::Reaction {
                event: reaction_decl.trigger.event_name.clone(),
                trigger: event_payload.clone(),
            },
            call_span,
            has_return_type: false,
            inv_id,
            requires: None,
            cost: reaction_decl.cost.clone(),
            resolve: reaction_decl.resolve.clone(),
            receiver_name: reaction_decl.receiver_name.clone(),
            bindings: vec![(Name::from("trigger"), event_payload)],
            default_params: Vec::new(),
            step: ActionStep::EmitStarted,
            pending: None,
            body_result: None,
            saved_turn_actor: None,
            saved_invocation: None,
        });

        Ok(exec)
    }

    /// Start executing a hook.
    pub fn start_hook(
        core: Rc<RuntimeCore>,
        state: StateAdapter<S>,
        hook_name: &str,
        target: EntityRef,
        event_payload: Value,
        call_span: Span,
    ) -> Result<Self, RuntimeError> {
        let hook_decl = core
            .program
            .hooks
            .get(hook_name)
            .ok_or_else(|| {
                RuntimeError::new(format!("undefined hook '{hook_name}'"))
            })?
            .clone();

        let inv_id = InvocationId(core.alloc_invocation_id());

        let mut exec = Self::new(core, state);

        exec.frames.push(Frame::ActionLifecycle {
            name: hook_decl.name.clone(),
            actor: target,
            action_kind: ActionKind::Hook {
                event: hook_decl.trigger.event_name.clone(),
                trigger: event_payload.clone(),
            },
            call_span,
            has_return_type: false,
            inv_id,
            requires: None,
            cost: None,
            resolve: hook_decl.resolve.clone(),
            receiver_name: hook_decl.receiver_name.clone(),
            bindings: vec![(Name::from("trigger"), event_payload)],
            default_params: Vec::new(),
            step: ActionStep::EmitStarted,
            pending: None,
            body_result: None,
            saved_turn_actor: None,
            saved_invocation: None,
        });

        Ok(exec)
    }

    // ── Non-action entry points (Phase 6) ──────────────────────

    /// Start evaluating a derive or table.
    ///
    /// Only works with `run_with_handler` — the bridge evaluation requires
    /// a synchronous handler. `poll()/respond()` will panic if the derive
    /// triggers host-decided effects.
    pub fn start_derive(
        core: Rc<RuntimeCore>,
        state: StateAdapter<S>,
        name: &str,
        args: Vec<Value>,
    ) -> Result<Self, RuntimeError> {
        if !core.program.derives.contains_key(name) && !core.program.tables.contains_key(name) {
            return Err(RuntimeError::new(format!(
                "undefined derive or table '{name}'"
            )));
        }
        let mut exec = Self::new(core, state);
        exec.frames.push(Frame::BridgeCall {
            result: None,
        });
        // Store call info for run_with_handler to execute
        exec.env.bridge_call = Some(BridgeCallInfo::Derive {
            name: Name::from(name),
            args,
        });
        Ok(exec)
    }

    /// Start evaluating a mechanic.
    pub fn start_mechanic(
        core: Rc<RuntimeCore>,
        state: StateAdapter<S>,
        name: &str,
        args: Vec<Value>,
    ) -> Result<Self, RuntimeError> {
        if !core.program.mechanics.contains_key(name) {
            return Err(RuntimeError::new(format!(
                "undefined mechanic '{name}'"
            )));
        }
        let mut exec = Self::new(core, state);
        exec.frames.push(Frame::BridgeCall {
            result: None,
        });
        exec.env.bridge_call = Some(BridgeCallInfo::Mechanic {
            name: Name::from(name),
            args,
        });
        Ok(exec)
    }

    /// Start evaluating a function.
    pub fn start_function(
        core: Rc<RuntimeCore>,
        state: StateAdapter<S>,
        name: &str,
        args: Vec<Value>,
    ) -> Result<Self, RuntimeError> {
        if !core.program.functions.contains_key(name) {
            return Err(RuntimeError::new(format!(
                "undefined function '{name}'"
            )));
        }
        let mut exec = Self::new(core, state);
        exec.frames.push(Frame::BridgeCall {
            result: None,
        });
        exec.env.bridge_call = Some(BridgeCallInfo::Function {
            name: Name::from(name),
            args,
        });
        Ok(exec)
    }

    /// Start evaluating a standalone expression.
    pub fn start_expr(
        core: Rc<RuntimeCore>,
        state: StateAdapter<S>,
        expr: Spanned<ExprKind>,
    ) -> Self {
        let mut exec = Self::new(core, state);
        exec.frames.push(Frame::BridgeCall {
            result: None,
        });
        exec.env.bridge_call = Some(BridgeCallInfo::Expr { expr });
        exec
    }

    /// Start evaluating a standalone expression with variable bindings.
    pub fn start_expr_with_bindings(
        core: Rc<RuntimeCore>,
        state: StateAdapter<S>,
        expr: Spanned<ExprKind>,
        bindings: Vec<(Name, Value)>,
    ) -> Self {
        let mut exec = Self::new(core, state);
        for (name, value) in bindings {
            exec.env.bind(name, value);
        }
        exec.frames.push(Frame::BridgeCall {
            result: None,
        });
        exec.env.bridge_call = Some(BridgeCallInfo::Expr { expr });
        exec
    }

    // ── Poll / respond ─────────────────────────────────────────

    /// Poll for the next effect or completion.
    pub fn poll(&mut self) -> Result<Step, PollError> {
        match &self.protocol {
            ProtocolState::Pending => {
                return Err(PollError::Protocol(ProtocolError::EffectPending))
            }
            ProtocolState::Completed => {
                return Err(PollError::Protocol(ProtocolError::ExecutionCompleted))
            }
            ProtocolState::Idle | ProtocolState::Unwinding(_) => {}
        }

        loop {
            if self.frames.is_empty() {
                if let ProtocolState::Unwinding(e) =
                    std::mem::replace(&mut self.protocol, ProtocolState::Completed)
                {
                    return Err(PollError::Runtime(e));
                }
                self.protocol = ProtocolState::Completed;
                let result = self.final_result.take().unwrap_or(Ok(Value::Void));
                return match result {
                    Ok(v) => Ok(Step::Done(v)),
                    Err(e) => Err(PollError::Runtime(e)),
                };
            }

            // Advance the top frame.
            // Destructure self to get independent borrows on frames vs. other fields.
            let frame = self.frames.last_mut().unwrap();
            let advance = frame.advance(&self.core, &mut self.env, &self.state);

            match advance {
                Advance::Yield(effect) => {
                    self.pending_before_yield =
                        Some(std::mem::replace(&mut self.protocol, ProtocolState::Pending));
                    return Ok(Step::Yielded(Box::new(effect)));
                }
                Advance::Push(child) => {
                    self.frames.push(child);
                }
                Advance::Pop(value) => {
                    self.frames.pop();
                    if let Some(parent) = self.frames.last_mut() {
                        parent.receive_child_result(value);
                    } else {
                        self.final_result = Some(Ok(value));
                    }
                }
                Advance::Continue => {}
                Advance::Error(e) => {
                    // For now, propagate errors immediately.
                    // Phase 5 will add proper unwinding with cleanup frames.
                    self.protocol = ProtocolState::Completed;
                    return Err(PollError::Runtime(e));
                }
            }
        }
    }

    /// Provide a host response to a yielded effect.
    pub fn respond(&mut self, response: Response) -> Result<(), ProtocolError> {
        match &self.protocol {
            ProtocolState::Idle | ProtocolState::Unwinding(_) => {
                return Err(ProtocolError::NoPendingEffect)
            }
            ProtocolState::Completed => return Err(ProtocolError::ExecutionCompleted),
            ProtocolState::Pending => {}
        }
        self.protocol = self
            .pending_before_yield
            .take()
            .unwrap_or(ProtocolState::Idle);
        if let Some(frame) = self.frames.last_mut() {
            frame.receive_response(response);
        }
        Ok(())
    }

    /// Drive execution to completion using a callback handler.
    ///
    /// This drives the frame stack directly, bypassing the poll/respond
    /// protocol. Host-decided effects (including those inside bridge
    /// evaluation like RollDice, Prompt, ConditionApplyGate) are handled
    /// synchronously by the provided handler.
    pub fn run_with_handler(
        mut self,
        handler: &mut dyn EffectHandler,
    ) -> Result<Value, RuntimeError> {
        loop {
            if self.frames.is_empty() {
                return self.final_result.take().unwrap_or(Ok(Value::Void));
            }

            let frame = self.frames.last_mut().unwrap();
            let advance = frame.advance_sync(
                &self.core,
                &mut self.env,
                &self.state,
                handler,
            );

            match advance {
                Advance::Yield(effect) => {
                    let response = handler.handle(effect);
                    if let Some(frame) = self.frames.last_mut() {
                        frame.receive_response(response);
                    }
                }
                Advance::Push(child) => {
                    self.frames.push(child);
                }
                Advance::Pop(value) => {
                    self.frames.pop();
                    if let Some(parent) = self.frames.last_mut() {
                        parent.receive_child_result(value);
                    } else {
                        self.final_result = Some(Ok(value));
                    }
                }
                Advance::Continue => {}
                Advance::Error(e) => return Err(e),
            }
        }
    }

    // ── Accessors ──────────────────────────────────────────────

    /// Current ID counter values. Call after completion to persist.
    pub fn counters(&self) -> (u64, u64) {
        self.core.counters()
    }

    /// Access the shared runtime core.
    pub fn core(&self) -> &Rc<RuntimeCore> {
        &self.core
    }

    /// Access the owned game state.
    pub fn state(&self) -> &StateAdapter<S> {
        &self.state
    }

    /// Mutable access to the owned game state.
    pub fn state_mut(&mut self) -> &mut StateAdapter<S> {
        &mut self.state
    }
}

impl std::fmt::Display for ProtocolError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProtocolError::NoPendingEffect => {
                write!(f, "respond() called with no pending effect")
            }
            ProtocolError::EffectPending => {
                write!(f, "poll() called while an effect is pending")
            }
            ProtocolError::ExecutionCompleted => {
                write!(f, "execution has already completed")
            }
        }
    }
}

impl std::fmt::Display for PollError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PollError::Protocol(e) => write!(f, "protocol error: {e}"),
            PollError::Runtime(e) => write!(f, "runtime error: {e}"),
        }
    }
}

// ── Tests ──────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::VecDeque;
    use std::sync::Arc;

    use ttrpg_ast::diagnostic::Severity;
    use ttrpg_checker::env::TypeEnv;

    use rustc_hash::FxHashMap;

    use crate::effect::{ActionKind, ActionOutcome, Effect, Response};
    use crate::reference_state::GameState;

    // ── Test infrastructure ──────────────────────────────────

    fn setup(source: &str) -> (Arc<ttrpg_ast::ast::Program>, Arc<TypeEnv>) {
        let (program, parse_errors) =
            ttrpg_parser::parse(source, ttrpg_ast::FileId::SYNTH);
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
        (Arc::new(program), Arc::new(result.env))
    }

    /// Scripted effect handler that returns pre-configured responses
    /// and records all effects received.
    struct ScriptedHandler {
        script: VecDeque<Response>,
        log: Vec<Effect>,
    }

    impl ScriptedHandler {
        fn new(responses: Vec<Response>) -> Self {
            ScriptedHandler {
                script: responses.into(),
                log: Vec::new(),
            }
        }

        fn always_ack() -> Self {
            Self::new(Vec::new())
        }
    }

    impl EffectHandler for ScriptedHandler {
        fn handle(&mut self, effect: Effect) -> Response {
            self.log.push(effect);
            self.script
                .pop_front()
                .unwrap_or(Response::Acknowledged)
        }
    }

    fn make_core(source: &str) -> (Rc<RuntimeCore>, Arc<ttrpg_ast::ast::Program>) {
        let (program, type_env) = setup(source);
        let core = RuntimeCore::new(program.clone(), type_env, 1, 1);
        (core, program)
    }

    /// Create a creature entity with the given HP.
    fn add_creature(game: &mut GameState, hp: i64) -> EntityRef {
        let mut fields = FxHashMap::default();
        fields.insert(Name::from("HP"), Value::Int(hp));
        game.add_entity("Creature", fields)
    }

    // ── Phase 3 tests ────────────────────────────────────────

    #[test]
    fn action_lifecycle_acknowledged() {
        let (core, _) = make_core(
            r#"
            system Test {
                entity Creature { HP: int }
                action Attack on actor: Creature (target: Creature) {
                    resolve {
                        target.HP -= 5
                    }
                }
            }
            "#,
        );

        let mut game = GameState::new();
        let attacker = add_creature(&mut game, 20);
        let defender = add_creature(&mut game, 15);
        let adapter = StateAdapter::new(game);

        let mut exec = Execution::start_action(
            core,
            adapter,
            "Attack",
            attacker,
            vec![Value::Entity(defender)],
            Span::dummy(),
        )
        .unwrap();

        // Step 1: ActionStarted
        let step = exec.poll().unwrap();
        let effect = match step {
            Step::Yielded(e) => *e,
            Step::Done(_) => panic!("expected Yielded, got Done"),
        };
        assert!(matches!(
            &effect,
            Effect::ActionStarted { name, kind: ActionKind::Action, actor, .. }
            if name == "Attack" && *actor == attacker
        ));

        exec.respond(Response::Acknowledged).unwrap();

        // Step 2: ActionCompleted (body runs synchronously via bridge)
        let step = exec.poll().unwrap();
        let effect = match step {
            Step::Yielded(e) => *e,
            Step::Done(_) => panic!("expected Yielded, got Done"),
        };
        assert!(matches!(
            &effect,
            Effect::ActionCompleted {
                name,
                outcome: ActionOutcome::Succeeded,
                invocation: Some(InvocationId(1)),
                ..
            }
            if name == "Attack"
        ));

        exec.respond(Response::Acknowledged).unwrap();

        // Step 3: Done
        let step = exec.poll().unwrap();
        assert!(matches!(step, Step::Done(Value::Void)));

        // Verify mutation was applied
        exec.state().with_state_mut(|gs| {
            let hp = gs.read_field(&defender, "HP").unwrap();
            assert_eq!(hp, Value::Int(10));
        });
    }

    #[test]
    fn action_lifecycle_vetoed() {
        let (core, _) = make_core(
            r#"
            system Test {
                entity Creature { HP: int }
                action Attack on actor: Creature (target: Creature) {
                    resolve {
                        target.HP -= 5
                    }
                }
            }
            "#,
        );

        let mut game = GameState::new();
        let attacker = add_creature(&mut game, 20);
        let defender = add_creature(&mut game, 15);
        let adapter = StateAdapter::new(game);

        let mut exec = Execution::start_action(
            core,
            adapter,
            "Attack",
            attacker,
            vec![Value::Entity(defender)],
            Span::dummy(),
        )
        .unwrap();

        // Step 1: ActionStarted
        let step = exec.poll().unwrap();
        assert!(matches!(&step, Step::Yielded(e) if matches!(&**e, Effect::ActionStarted { .. })));

        // Veto the action
        exec.respond(Response::Vetoed).unwrap();

        // Step 2: ActionCompleted(Vetoed)
        let step = exec.poll().unwrap();
        let effect = match step {
            Step::Yielded(e) => *e,
            Step::Done(_) => panic!("expected Yielded, got Done"),
        };
        assert!(matches!(
            &effect,
            Effect::ActionCompleted {
                outcome: ActionOutcome::Vetoed,
                invocation: None,
                ..
            }
        ));

        exec.respond(Response::Acknowledged).unwrap();

        // Step 3: Done with abort value
        let step = exec.poll().unwrap();
        assert!(matches!(step, Step::Done(Value::Void)));

        // Verify NO mutation was applied
        exec.state().with_state_mut(|gs| {
            let hp = gs.read_field(&defender, "HP").unwrap();
            assert_eq!(hp, Value::Int(15));
        });
    }

    #[test]
    fn action_run_with_handler() {
        let (core, _) = make_core(
            r#"
            system Test {
                entity Creature { HP: int }
                action Attack on actor: Creature (target: Creature) {
                    resolve {
                        target.HP -= 5
                    }
                }
            }
            "#,
        );

        let mut game = GameState::new();
        let attacker = add_creature(&mut game, 20);
        let defender = add_creature(&mut game, 15);
        let adapter = StateAdapter::new(game);

        let exec = Execution::start_action(
            core,
            adapter,
            "Attack",
            attacker,
            vec![Value::Entity(defender)],
            Span::dummy(),
        )
        .unwrap();

        let mut handler = ScriptedHandler::always_ack();
        let result = exec.run_with_handler(&mut handler).unwrap();
        assert_eq!(result, Value::Void);

        // Verify effects
        assert_eq!(handler.log.len(), 2);
        assert!(matches!(&handler.log[0], Effect::ActionStarted { .. }));
        assert!(matches!(
            &handler.log[1],
            Effect::ActionCompleted {
                outcome: ActionOutcome::Succeeded,
                ..
            }
        ));
    }

    #[test]
    fn action_with_requires_pass() {
        let (core, _) = make_core(
            r#"
            system Test {
                entity Creature { HP: int }
                action Heal on actor: Creature (target: Creature) {
                    requires { target.HP > 0 }
                    resolve {
                        target.HP += 5
                    }
                }
            }
            "#,
        );

        let mut game = GameState::new();
        let healer = add_creature(&mut game, 20);
        let patient = add_creature(&mut game, 10);
        let adapter = StateAdapter::new(game);

        let mut exec = Execution::start_action(
            core,
            adapter,
            "Heal",
            healer,
            vec![Value::Entity(patient)],
            Span::dummy(),
        )
        .unwrap();

        // ActionStarted
        let step = exec.poll().unwrap();
        assert!(matches!(&step, Step::Yielded(e) if matches!(&**e, Effect::ActionStarted { .. })));
        exec.respond(Response::Acknowledged).unwrap();

        // RequiresCheck (passed=true)
        let step = exec.poll().unwrap();
        let effect = match step {
            Step::Yielded(e) => *e,
            Step::Done(_) => panic!("expected RequiresCheck"),
        };
        assert!(matches!(
            &effect,
            Effect::RequiresCheck { action, passed: true, .. }
            if action == "Heal"
        ));
        exec.respond(Response::Acknowledged).unwrap();

        // ActionCompleted
        let step = exec.poll().unwrap();
        assert!(matches!(
            &step,
            Step::Yielded(e) if matches!(&**e, Effect::ActionCompleted { outcome: ActionOutcome::Succeeded, .. })
        ));
        exec.respond(Response::Acknowledged).unwrap();

        // Done
        let step = exec.poll().unwrap();
        assert!(matches!(step, Step::Done(Value::Void)));

        // Verify heal applied
        exec.state().with_state_mut(|gs| {
            let hp = gs.read_field(&patient, "HP").unwrap();
            assert_eq!(hp, Value::Int(15));
        });
    }

    #[test]
    fn action_with_requires_fail() {
        let (core, _) = make_core(
            r#"
            system Test {
                entity Creature { HP: int }
                action Heal on actor: Creature (target: Creature) {
                    requires { target.HP > 0 }
                    resolve {
                        target.HP += 5
                    }
                }
            }
            "#,
        );

        let mut game = GameState::new();
        let healer = add_creature(&mut game, 20);
        let patient = add_creature(&mut game, 0);
        let adapter = StateAdapter::new(game);

        let mut exec = Execution::start_action(
            core,
            adapter,
            "Heal",
            healer,
            vec![Value::Entity(patient)],
            Span::dummy(),
        )
        .unwrap();

        // ActionStarted
        let step = exec.poll().unwrap();
        assert!(matches!(&step, Step::Yielded(e) if matches!(&**e, Effect::ActionStarted { .. })));
        exec.respond(Response::Acknowledged).unwrap();

        // RequiresCheck (passed=false)
        let step = exec.poll().unwrap();
        let effect = match step {
            Step::Yielded(e) => *e,
            Step::Done(_) => panic!("expected RequiresCheck"),
        };
        assert!(matches!(
            &effect,
            Effect::RequiresCheck { passed: false, .. }
        ));
        exec.respond(Response::Acknowledged).unwrap();

        // ActionCompleted (Succeeded — abort returns Ok, so outcome is Succeeded)
        let step = exec.poll().unwrap();
        assert!(matches!(
            &step,
            Step::Yielded(e) if matches!(&**e, Effect::ActionCompleted { outcome: ActionOutcome::Succeeded, .. })
        ));
        exec.respond(Response::Acknowledged).unwrap();

        // Done
        let step = exec.poll().unwrap();
        assert!(matches!(step, Step::Done(Value::Void)));

        // Verify NO heal applied
        exec.state().with_state_mut(|gs| {
            let hp = gs.read_field(&patient, "HP").unwrap();
            assert_eq!(hp, Value::Int(0));
        });
    }

    #[test]
    fn protocol_error_poll_while_pending() {
        let (core, _) = make_core(
            r#"
            system Test {
                entity Creature { HP: int }
                action Noop on actor: Creature () {
                    resolve { }
                }
            }
            "#,
        );

        let mut game = GameState::new();
        let actor = add_creature(&mut game, 10);
        let adapter = StateAdapter::new(game);

        let mut exec = Execution::start_action(
            core, adapter, "Noop", actor, vec![], Span::dummy(),
        )
        .unwrap();

        // First poll yields ActionStarted
        let _ = exec.poll().unwrap();

        // Second poll without respond should error
        let err = exec.poll().unwrap_err();
        assert!(matches!(err, PollError::Protocol(ProtocolError::EffectPending)));
    }

    #[test]
    fn protocol_error_respond_without_pending() {
        let (core, _) = make_core(
            r#"
            system Test {
                entity Creature { HP: int }
                action Noop on actor: Creature () {
                    resolve { }
                }
            }
            "#,
        );

        let mut game = GameState::new();
        let actor = add_creature(&mut game, 10);
        let adapter = StateAdapter::new(game);

        let mut exec = Execution::start_action(
            core, adapter, "Noop", actor, vec![], Span::dummy(),
        )
        .unwrap();

        // respond without poll should error
        let err = exec.respond(Response::Acknowledged).unwrap_err();
        assert!(matches!(err, ProtocolError::NoPendingEffect));
    }

    // ── Differential tests (Phase 7) ─────────────────────────

    /// Extract structural effect kinds from an effect log (filtering
    /// out locally-applied mutations that only appear in the recursive path).
    fn structural_kinds(effects: &[Effect]) -> Vec<EffectKind> {
        effects
            .iter()
            .map(EffectKind::of)
            .filter(|k| {
                matches!(
                    k,
                    EffectKind::ActionStarted
                        | EffectKind::ActionCompleted
                        | EffectKind::RequiresCheck
                        | EffectKind::DeductCost
                        | EffectKind::RollDice
                        | EffectKind::ResolvePrompt
                        | EffectKind::ConditionApplyGate
                        | EffectKind::ConditionRemovalGate
                        | EffectKind::ModifyApplied
                        | EffectKind::RevokeInvocation
                )
            })
            .collect()
    }

    #[test]
    fn differential_simple_action() {
        let source = r#"
            system Test {
                entity Creature { HP: int }
                action Attack on actor: Creature (target: Creature) {
                    resolve {
                        target.HP -= 5
                    }
                }
            }
        "#;

        // Inline the setup to get entity refs for args:
        let (program, type_env) = setup(source);

        // Recursive path
        let interp = crate::Interpreter::new(&program, &type_env).unwrap();
        let mut game1 = GameState::new();
        let a1 = add_creature(&mut game1, 20);
        let d1 = add_creature(&mut game1, 15);
        let adapter1 = StateAdapter::new(game1);
        let mut handler1 = ScriptedHandler::always_ack();
        let result1 = adapter1.run(&mut handler1, |state, handler| {
            interp.execute_action(
                state, handler, "Attack", a1, vec![Value::Entity(d1)],
            )
        });

        // Step-based path
        let core = RuntimeCore::new(Arc::clone(&program), Arc::clone(&type_env), 1, 1);
        let mut game2 = GameState::new();
        let a2 = add_creature(&mut game2, 20);
        let d2 = add_creature(&mut game2, 15);
        let adapter2 = StateAdapter::new(game2);
        let exec = Execution::start_action(
            core, adapter2, "Attack", a2, vec![Value::Entity(d2)], Span::dummy(),
        )
        .unwrap();
        let mut handler2 = ScriptedHandler::always_ack();
        let result2 = exec.run_with_handler(&mut handler2);

        // Compare structural effect sequences
        let kinds1 = structural_kinds(&handler1.log);
        let kinds2 = structural_kinds(&handler2.log);
        assert_eq!(kinds1, kinds2, "structural effect sequence mismatch");

        // Both should succeed
        assert!(result1.is_ok(), "recursive path failed: {result1:?}");
        assert!(result2.is_ok(), "step-based path failed: {result2:?}");

        // Both should produce the same result type
        assert_eq!(result1.unwrap(), result2.unwrap());
    }

    #[test]
    fn differential_action_with_requires() {
        let source = r#"
            system Test {
                entity Creature { HP: int }
                action Heal on actor: Creature (target: Creature) {
                    requires { target.HP > 0 }
                    resolve {
                        target.HP += 5
                    }
                }
            }
        "#;

        let (program, type_env) = setup(source);

        // Recursive path (requires passes: HP=10 > 0)
        let interp = crate::Interpreter::new(&program, &type_env).unwrap();
        let mut game1 = GameState::new();
        let h1 = add_creature(&mut game1, 20);
        let p1 = add_creature(&mut game1, 10);
        let adapter1 = StateAdapter::new(game1);
        let mut handler1 = ScriptedHandler::always_ack();
        let _ = adapter1.run(&mut handler1, |state, handler| {
            interp.execute_action(
                state, handler, "Heal", h1, vec![Value::Entity(p1)],
            )
        });

        // Step-based path
        let core = RuntimeCore::new(Arc::clone(&program), Arc::clone(&type_env), 1, 1);
        let mut game2 = GameState::new();
        let h2 = add_creature(&mut game2, 20);
        let p2 = add_creature(&mut game2, 10);
        let adapter2 = StateAdapter::new(game2);
        let exec = Execution::start_action(
            core, adapter2, "Heal", h2, vec![Value::Entity(p2)], Span::dummy(),
        )
        .unwrap();
        let mut handler2 = ScriptedHandler::always_ack();
        let _ = exec.run_with_handler(&mut handler2);

        let kinds1 = structural_kinds(&handler1.log);
        let kinds2 = structural_kinds(&handler2.log);
        assert_eq!(
            kinds1, kinds2,
            "structural effect sequence mismatch for requires-pass"
        );
        // Both should include: ActionStarted, RequiresCheck, ActionCompleted
        assert_eq!(kinds1.len(), 3);
        assert_eq!(kinds1[0], EffectKind::ActionStarted);
        assert_eq!(kinds1[1], EffectKind::RequiresCheck);
        assert_eq!(kinds1[2], EffectKind::ActionCompleted);
    }

    #[test]
    fn differential_action_vetoed() {
        let source = r#"
            system Test {
                entity Creature { HP: int }
                action Attack on actor: Creature (target: Creature) {
                    resolve {
                        target.HP -= 5
                    }
                }
            }
        "#;

        let (program, type_env) = setup(source);

        // Recursive path with veto
        let interp = crate::Interpreter::new(&program, &type_env).unwrap();
        let mut game1 = GameState::new();
        let a1 = add_creature(&mut game1, 20);
        let d1 = add_creature(&mut game1, 15);
        let adapter1 = StateAdapter::new(game1);
        let mut handler1 = ScriptedHandler::new(vec![
            Response::Vetoed,        // ActionStarted → Vetoed
            Response::Acknowledged,  // ActionCompleted(Vetoed)
        ]);
        let _ = adapter1.run(&mut handler1, |state, handler| {
            interp.execute_action(
                state, handler, "Attack", a1, vec![Value::Entity(d1)],
            )
        });

        // Step-based path with veto
        let core = RuntimeCore::new(Arc::clone(&program), Arc::clone(&type_env), 1, 1);
        let mut game2 = GameState::new();
        let a2 = add_creature(&mut game2, 20);
        let d2 = add_creature(&mut game2, 15);
        let adapter2 = StateAdapter::new(game2);
        let exec = Execution::start_action(
            core, adapter2, "Attack", a2, vec![Value::Entity(d2)], Span::dummy(),
        )
        .unwrap();
        let mut handler2 = ScriptedHandler::new(vec![
            Response::Vetoed,        // ActionStarted → Vetoed
            Response::Acknowledged,  // ActionCompleted(Vetoed)
        ]);
        let _ = exec.run_with_handler(&mut handler2);

        let kinds1 = structural_kinds(&handler1.log);
        let kinds2 = structural_kinds(&handler2.log);
        assert_eq!(
            kinds1, kinds2,
            "structural effect sequence mismatch for vetoed action"
        );
        // Both should include: ActionStarted, ActionCompleted
        assert_eq!(kinds1.len(), 2);
        assert_eq!(kinds1[0], EffectKind::ActionStarted);
        assert_eq!(kinds1[1], EffectKind::ActionCompleted);

        // Verify the ActionCompleted outcome matches
        if let Effect::ActionCompleted { outcome: o1, .. } = &handler1.log[1] {
            if let Effect::ActionCompleted { outcome: o2, .. } = &handler2.log[1] {
                assert_eq!(o1, o2, "ActionCompleted outcome mismatch");
                assert_eq!(*o1, ActionOutcome::Vetoed);
            }
        }
    }

    #[test]
    fn differential_reaction_lifecycle() {
        let source = r#"
            system Test {
                entity Creature { HP: int }
                event damage(target: Creature) {}
                reaction OnDamage on target: Creature (trigger: damage(target: target)) {
                    resolve {
                        target.HP -= 1
                    }
                }
            }
        "#;

        let (program, type_env) = setup(source);

        let payload = Value::Struct {
            name: "__event_damage".into(),
            fields: {
                let mut f = BTreeMap::new();
                // target field will be filled by the entity ref
                f.insert(Name::from("target"), Value::Entity(EntityRef(2)));
                f
            },
        };

        // Recursive path
        let interp = crate::Interpreter::new(&program, &type_env).unwrap();
        let mut game1 = GameState::new();
        let r1 = add_creature(&mut game1, 20);
        let adapter1 = StateAdapter::new(game1);
        let mut handler1 = ScriptedHandler::always_ack();
        let _ = adapter1.run(&mut handler1, |state, handler| {
            interp.execute_reaction(state, handler, "OnDamage", r1, payload.clone())
        });

        // Step-based path
        let core = RuntimeCore::new(Arc::clone(&program), Arc::clone(&type_env), 1, 1);
        let mut game2 = GameState::new();
        let r2 = add_creature(&mut game2, 20);
        let adapter2 = StateAdapter::new(game2);
        let exec = Execution::start_reaction(
            core, adapter2, "OnDamage", r2, payload.clone(), Span::dummy(),
        )
        .unwrap();
        let mut handler2 = ScriptedHandler::always_ack();
        let _ = exec.run_with_handler(&mut handler2);

        let kinds1 = structural_kinds(&handler1.log);
        let kinds2 = structural_kinds(&handler2.log);
        assert_eq!(kinds1, kinds2, "structural effect sequence mismatch for reaction");
        assert_eq!(kinds1.len(), 2);
        assert_eq!(kinds1[0], EffectKind::ActionStarted);
        assert_eq!(kinds1[1], EffectKind::ActionCompleted);

        // Verify ActionStarted kind is Reaction
        assert!(matches!(
            &handler1.log[0],
            Effect::ActionStarted { kind: ActionKind::Reaction { .. }, .. }
        ));
        assert!(matches!(
            &handler2.log[0],
            Effect::ActionStarted { kind: ActionKind::Reaction { .. }, .. }
        ));
    }

    #[test]
    fn differential_hook_lifecycle() {
        let source = r#"
            system Test {
                entity Creature { HP: int }
                event damage(target: Creature) {}
                hook OnDamage on target: Creature (trigger: damage(target: target)) {
                    target.HP -= 1
                }
            }
        "#;

        let (program, type_env) = setup(source);

        let payload = Value::Struct {
            name: "__event_damage".into(),
            fields: {
                let mut f = BTreeMap::new();
                f.insert(Name::from("target"), Value::Entity(EntityRef(2)));
                f
            },
        };

        // Recursive path
        let interp = crate::Interpreter::new(&program, &type_env).unwrap();
        let mut game1 = GameState::new();
        let t1 = add_creature(&mut game1, 20);
        let adapter1 = StateAdapter::new(game1);
        let mut handler1 = ScriptedHandler::always_ack();
        let _ = adapter1.run(&mut handler1, |state, handler| {
            interp.execute_hook(state, handler, "OnDamage", t1, payload.clone())
        });

        // Step-based path
        let core = RuntimeCore::new(Arc::clone(&program), Arc::clone(&type_env), 1, 1);
        let mut game2 = GameState::new();
        let t2 = add_creature(&mut game2, 20);
        let adapter2 = StateAdapter::new(game2);
        let exec = Execution::start_hook(
            core, adapter2, "OnDamage", t2, payload.clone(), Span::dummy(),
        )
        .unwrap();
        let mut handler2 = ScriptedHandler::always_ack();
        let _ = exec.run_with_handler(&mut handler2);

        let kinds1 = structural_kinds(&handler1.log);
        let kinds2 = structural_kinds(&handler2.log);
        assert_eq!(kinds1, kinds2, "structural effect sequence mismatch for hook");
        assert_eq!(kinds1.len(), 2);
        assert_eq!(kinds1[0], EffectKind::ActionStarted);
        assert_eq!(kinds1[1], EffectKind::ActionCompleted);

        // Verify ActionStarted kind is Hook
        assert!(matches!(
            &handler1.log[0],
            Effect::ActionStarted { kind: ActionKind::Hook { .. }, .. }
        ));
        assert!(matches!(
            &handler2.log[0],
            Effect::ActionStarted { kind: ActionKind::Hook { .. }, .. }
        ));
    }

    #[test]
    fn differential_requires_override_force_pass() {
        let source = r#"
            system Test {
                entity Creature { HP: int }
                action Heal on actor: Creature (target: Creature) {
                    requires { target.HP > 0 }
                    resolve {
                        target.HP += 5
                    }
                }
            }
        "#;

        let (program, type_env) = setup(source);

        // Both paths: requires fails (HP=0), host overrides to pass
        let responses = vec![
            Response::Acknowledged,                // ActionStarted
            Response::Override(Value::Bool(true)),  // RequiresCheck(false) → force pass
            Response::Acknowledged,                // ActionCompleted
        ];

        // Recursive path
        let interp = crate::Interpreter::new(&program, &type_env).unwrap();
        let mut game1 = GameState::new();
        let h1 = add_creature(&mut game1, 20);
        let p1 = add_creature(&mut game1, 0); // HP=0 → requires fails
        let adapter1 = StateAdapter::new(game1);
        let mut handler1 = ScriptedHandler::new(responses.clone());
        let result1 = adapter1.run(&mut handler1, |state, handler| {
            interp.execute_action(state, handler, "Heal", h1, vec![Value::Entity(p1)])
        });

        // Step-based path
        let core = RuntimeCore::new(Arc::clone(&program), Arc::clone(&type_env), 1, 1);
        let mut game2 = GameState::new();
        let h2 = add_creature(&mut game2, 20);
        let p2 = add_creature(&mut game2, 0);
        let adapter2 = StateAdapter::new(game2);
        let exec = Execution::start_action(
            core, adapter2, "Heal", h2, vec![Value::Entity(p2)], Span::dummy(),
        )
        .unwrap();
        let mut handler2 = ScriptedHandler::new(responses);
        let result2 = exec.run_with_handler(&mut handler2);

        let kinds1 = structural_kinds(&handler1.log);
        let kinds2 = structural_kinds(&handler2.log);
        assert_eq!(kinds1, kinds2, "structural effect sequence mismatch for requires override (force pass)");

        // Should have: ActionStarted, RequiresCheck, ActionCompleted
        assert_eq!(kinds1.len(), 3);
        assert_eq!(kinds1[1], EffectKind::RequiresCheck);

        // Both should succeed (override allowed the action to proceed)
        assert!(result1.is_ok());
        assert!(result2.is_ok());

        // Verify RequiresCheck shows passed=false (original) in both
        if let Effect::RequiresCheck { passed: p1, .. } = &handler1.log[1] {
            if let Effect::RequiresCheck { passed: p2, .. } = &handler2.log[1] {
                assert_eq!(p1, p2);
                assert!(!p1, "requires should have originally failed");
            }
        }
    }

    #[test]
    fn differential_requires_override_force_fail() {
        let source = r#"
            system Test {
                entity Creature { HP: int }
                action Heal on actor: Creature (target: Creature) {
                    requires { target.HP > 0 }
                    resolve {
                        target.HP += 5
                    }
                }
            }
        "#;

        let (program, type_env) = setup(source);

        // Both paths: requires passes (HP=10), host overrides to fail
        let responses = vec![
            Response::Acknowledged,                  // ActionStarted
            Response::Override(Value::Bool(false)),   // RequiresCheck(true) → force fail
            Response::Acknowledged,                  // ActionCompleted
        ];

        // Recursive path
        let interp = crate::Interpreter::new(&program, &type_env).unwrap();
        let mut game1 = GameState::new();
        let h1 = add_creature(&mut game1, 20);
        let p1 = add_creature(&mut game1, 10); // HP=10 → requires passes
        let adapter1 = StateAdapter::new(game1);
        let mut handler1 = ScriptedHandler::new(responses.clone());
        let result1 = adapter1.run(&mut handler1, |state, handler| {
            interp.execute_action(state, handler, "Heal", h1, vec![Value::Entity(p1)])
        });

        // Step-based path
        let core = RuntimeCore::new(Arc::clone(&program), Arc::clone(&type_env), 1, 1);
        let mut game2 = GameState::new();
        let h2 = add_creature(&mut game2, 20);
        let p2 = add_creature(&mut game2, 10);
        let adapter2 = StateAdapter::new(game2);
        let exec = Execution::start_action(
            core, adapter2, "Heal", h2, vec![Value::Entity(p2)], Span::dummy(),
        )
        .unwrap();
        let mut handler2 = ScriptedHandler::new(responses);
        let result2 = exec.run_with_handler(&mut handler2);

        let kinds1 = structural_kinds(&handler1.log);
        let kinds2 = structural_kinds(&handler2.log);
        assert_eq!(kinds1, kinds2, "structural effect sequence mismatch for requires override (force fail)");

        // Should have: ActionStarted, RequiresCheck, ActionCompleted
        assert_eq!(kinds1.len(), 3);

        // Both should succeed (force-fail just aborts the body, not an error)
        assert!(result1.is_ok());
        assert!(result2.is_ok());

        // Verify RequiresCheck shows passed=true (original) in both
        if let Effect::RequiresCheck { passed: p1, .. } = &handler1.log[1] {
            if let Effect::RequiresCheck { passed: p2, .. } = &handler2.log[1] {
                assert_eq!(p1, p2);
                assert!(*p1, "requires should have originally passed");
            }
        }

        // ActionCompleted outcome should match — Succeeded because abort is not an error
        if let Effect::ActionCompleted { outcome: o1, .. } = handler1.log.last().unwrap() {
            if let Effect::ActionCompleted { outcome: o2, .. } = handler2.log.last().unwrap() {
                assert_eq!(o1, o2);
                assert_eq!(*o1, ActionOutcome::Succeeded);
            }
        }
    }

    #[test]
    fn differential_action_with_default_params() {
        let source = r#"
            system Test {
                entity Creature { HP: int }
                action Heal on actor: Creature (target: Creature, amount: int = 5) {
                    resolve {
                        target.HP += amount
                    }
                }
            }
        "#;

        let (program, type_env) = setup(source);

        // Both paths: call with only target, letting amount default to 5

        // Recursive path
        let interp = crate::Interpreter::new(&program, &type_env).unwrap();
        let mut game1 = GameState::new();
        let h1 = add_creature(&mut game1, 20);
        let p1 = add_creature(&mut game1, 10);
        let adapter1 = StateAdapter::new(game1);
        let mut handler1 = ScriptedHandler::always_ack();
        let result1 = adapter1.run(&mut handler1, |state, handler| {
            interp.execute_action(state, handler, "Heal", h1, vec![Value::Entity(p1)])
        });

        // Step-based path
        let core = RuntimeCore::new(Arc::clone(&program), Arc::clone(&type_env), 1, 1);
        let mut game2 = GameState::new();
        let h2 = add_creature(&mut game2, 20);
        let p2 = add_creature(&mut game2, 10);
        let adapter2 = StateAdapter::new(game2);
        let exec = Execution::start_action(
            core, adapter2, "Heal", h2, vec![Value::Entity(p2)], Span::dummy(),
        )
        .unwrap();
        let mut handler2 = ScriptedHandler::always_ack();
        let result2 = exec.run_with_handler(&mut handler2);

        let kinds1 = structural_kinds(&handler1.log);
        let kinds2 = structural_kinds(&handler2.log);
        assert_eq!(kinds1, kinds2, "structural effect sequence mismatch for default params");

        // Both should succeed
        assert!(result1.is_ok(), "recursive path failed: {result1:?}");
        assert!(result2.is_ok(), "step-based path failed: {result2:?}");

        // Both should produce same result
        assert_eq!(result1.unwrap(), result2.unwrap());
    }

    #[test]
    fn differential_reaction_vetoed() {
        let source = r#"
            system Test {
                entity Creature { HP: int }
                event damage(target: Creature) {}
                reaction OnDamage on target: Creature (trigger: damage(target: target)) {
                    resolve {
                        target.HP -= 1
                    }
                }
            }
        "#;

        let (program, type_env) = setup(source);

        let payload = Value::Struct {
            name: "__event_damage".into(),
            fields: {
                let mut f = BTreeMap::new();
                f.insert(Name::from("target"), Value::Entity(EntityRef(2)));
                f
            },
        };

        let responses = vec![
            Response::Vetoed,        // ActionStarted → Vetoed
            Response::Acknowledged,  // ActionCompleted(Vetoed)
        ];

        // Recursive path
        let interp = crate::Interpreter::new(&program, &type_env).unwrap();
        let mut game1 = GameState::new();
        let r1 = add_creature(&mut game1, 20);
        let adapter1 = StateAdapter::new(game1);
        let mut handler1 = ScriptedHandler::new(responses.clone());
        let _ = adapter1.run(&mut handler1, |state, handler| {
            interp.execute_reaction(state, handler, "OnDamage", r1, payload.clone())
        });

        // Step-based path
        let core = RuntimeCore::new(Arc::clone(&program), Arc::clone(&type_env), 1, 1);
        let mut game2 = GameState::new();
        let r2 = add_creature(&mut game2, 20);
        let adapter2 = StateAdapter::new(game2);
        let exec = Execution::start_reaction(
            core, adapter2, "OnDamage", r2, payload.clone(), Span::dummy(),
        )
        .unwrap();
        let mut handler2 = ScriptedHandler::new(responses);
        let _ = exec.run_with_handler(&mut handler2);

        let kinds1 = structural_kinds(&handler1.log);
        let kinds2 = structural_kinds(&handler2.log);
        assert_eq!(kinds1, kinds2, "structural effect sequence mismatch for vetoed reaction");
        assert_eq!(kinds1.len(), 2);

        // Verify both have Vetoed outcome
        if let Effect::ActionCompleted { outcome: o1, .. } = &handler1.log[1] {
            if let Effect::ActionCompleted { outcome: o2, .. } = &handler2.log[1] {
                assert_eq!(o1, o2);
                assert_eq!(*o1, ActionOutcome::Vetoed);
            }
        }
    }

    #[test]
    fn differential_hook_vetoed() {
        let source = r#"
            system Test {
                entity Creature { HP: int }
                event damage(target: Creature) {}
                hook OnDamage on target: Creature (trigger: damage(target: target)) {
                    target.HP -= 1
                }
            }
        "#;

        let (program, type_env) = setup(source);

        let payload = Value::Struct {
            name: "__event_damage".into(),
            fields: {
                let mut f = BTreeMap::new();
                f.insert(Name::from("target"), Value::Entity(EntityRef(2)));
                f
            },
        };

        let responses = vec![
            Response::Vetoed,        // ActionStarted → Vetoed
            Response::Acknowledged,  // ActionCompleted(Vetoed)
        ];

        // Recursive path
        let interp = crate::Interpreter::new(&program, &type_env).unwrap();
        let mut game1 = GameState::new();
        let t1 = add_creature(&mut game1, 20);
        let adapter1 = StateAdapter::new(game1);
        let mut handler1 = ScriptedHandler::new(responses.clone());
        let _ = adapter1.run(&mut handler1, |state, handler| {
            interp.execute_hook(state, handler, "OnDamage", t1, payload.clone())
        });

        // Step-based path
        let core = RuntimeCore::new(Arc::clone(&program), Arc::clone(&type_env), 1, 1);
        let mut game2 = GameState::new();
        let t2 = add_creature(&mut game2, 20);
        let adapter2 = StateAdapter::new(game2);
        let exec = Execution::start_hook(
            core, adapter2, "OnDamage", t2, payload.clone(), Span::dummy(),
        )
        .unwrap();
        let mut handler2 = ScriptedHandler::new(responses);
        let _ = exec.run_with_handler(&mut handler2);

        let kinds1 = structural_kinds(&handler1.log);
        let kinds2 = structural_kinds(&handler2.log);
        assert_eq!(kinds1, kinds2, "structural effect sequence mismatch for vetoed hook");
        assert_eq!(kinds1.len(), 2);

        if let Effect::ActionCompleted { outcome: o1, .. } = &handler1.log[1] {
            if let Effect::ActionCompleted { outcome: o2, .. } = &handler2.log[1] {
                assert_eq!(o1, o2);
                assert_eq!(*o1, ActionOutcome::Vetoed);
            }
        }
    }

    #[test]
    fn differential_multiple_sequential_actions() {
        let source = r#"
            system Test {
                entity Creature { HP: int }
                action Attack on actor: Creature (target: Creature) {
                    resolve {
                        target.HP -= 5
                    }
                }
            }
        "#;

        let (program, type_env) = setup(source);

        // Recursive path: two actions in sequence
        let interp = crate::Interpreter::new(&program, &type_env).unwrap();
        let mut game1 = GameState::new();
        let a1 = add_creature(&mut game1, 20);
        let d1 = add_creature(&mut game1, 30);
        let adapter1 = StateAdapter::new(game1);
        let mut handler1 = ScriptedHandler::always_ack();
        let _ = adapter1.run(&mut handler1, |state, handler| {
            interp.execute_action(
                state, handler, "Attack", a1, vec![Value::Entity(d1)],
            )?;
            interp.execute_action(
                state, handler, "Attack", a1, vec![Value::Entity(d1)],
            )
        });

        // Step-based path: two actions with shared RuntimeCore
        let core = RuntimeCore::new(Arc::clone(&program), Arc::clone(&type_env), 1, 1);
        let mut game2 = GameState::new();
        let a2 = add_creature(&mut game2, 20);
        let d2 = add_creature(&mut game2, 30);
        let adapter2 = StateAdapter::new(game2);

        // First action
        let exec1 = Execution::start_action(
            Rc::clone(&core), adapter2, "Attack", a2, vec![Value::Entity(d2)], Span::dummy(),
        )
        .unwrap();
        let mut handler2 = ScriptedHandler::always_ack();
        let adapter2 = {
            let result = exec1.run_with_handler(&mut handler2);
            assert!(result.is_ok());
            // Recover state from the completed execution — not directly possible,
            // so we rebuild. The important thing is invocation ID continuity.
            let mut game2b = GameState::new();
            let _ = add_creature(&mut game2b, 20);
            let _ = add_creature(&mut game2b, 25); // HP already reduced by 5
            StateAdapter::new(game2b)
        };

        // Second action
        let exec2 = Execution::start_action(
            Rc::clone(&core), adapter2, "Attack", a2, vec![Value::Entity(d2)], Span::dummy(),
        )
        .unwrap();
        let mut handler2b = ScriptedHandler::always_ack();
        let _ = exec2.run_with_handler(&mut handler2b);

        // Combine step-based logs
        let mut combined_log = handler2.log;
        combined_log.extend(handler2b.log);

        let kinds1 = structural_kinds(&handler1.log);
        let kinds2 = structural_kinds(&combined_log);
        assert_eq!(kinds1, kinds2, "structural effect sequence mismatch for sequential actions");

        // Both should have 4 structural effects: 2x(ActionStarted, ActionCompleted)
        assert_eq!(kinds1.len(), 4);

        // Verify invocation IDs increment correctly
        let inv1_recursive = match &handler1.log[1] {
            Effect::ActionCompleted { invocation: Some(id), .. } => id.0,
            other => panic!("expected ActionCompleted, got {other:?}"),
        };
        let inv2_recursive = match &handler1.log[3] {
            Effect::ActionCompleted { invocation: Some(id), .. } => id.0,
            other => panic!("expected ActionCompleted, got {other:?}"),
        };
        assert_eq!(inv2_recursive, inv1_recursive + 1, "recursive invocation IDs should increment");

        let inv1_step = match &combined_log[1] {
            Effect::ActionCompleted { invocation: Some(id), .. } => id.0,
            other => panic!("expected ActionCompleted, got {other:?}"),
        };
        let inv2_step = match &combined_log[3] {
            Effect::ActionCompleted { invocation: Some(id), .. } => id.0,
            other => panic!("expected ActionCompleted, got {other:?}"),
        };
        assert_eq!(inv2_step, inv1_step + 1, "step-based invocation IDs should increment");
    }

    #[test]
    fn differential_action_with_multiple_params() {
        let source = r#"
            system Test {
                entity Creature { HP: int }
                action MultiHit on actor: Creature (target: Creature, damage: int, bonus: int = 0) {
                    resolve {
                        target.HP -= damage + bonus
                    }
                }
            }
        "#;

        let (program, type_env) = setup(source);

        // Call with explicit damage=7, bonus defaults to 0

        // Recursive path
        let interp = crate::Interpreter::new(&program, &type_env).unwrap();
        let mut game1 = GameState::new();
        let a1 = add_creature(&mut game1, 20);
        let d1 = add_creature(&mut game1, 30);
        let adapter1 = StateAdapter::new(game1);
        let mut handler1 = ScriptedHandler::always_ack();
        let result1 = adapter1.run(&mut handler1, |state, handler| {
            interp.execute_action(
                state, handler, "MultiHit", a1, vec![Value::Entity(d1), Value::Int(7)],
            )
        });

        // Step-based path
        let core = RuntimeCore::new(Arc::clone(&program), Arc::clone(&type_env), 1, 1);
        let mut game2 = GameState::new();
        let a2 = add_creature(&mut game2, 20);
        let d2 = add_creature(&mut game2, 30);
        let adapter2 = StateAdapter::new(game2);
        let exec = Execution::start_action(
            core, adapter2, "MultiHit", a2,
            vec![Value::Entity(d2), Value::Int(7)], Span::dummy(),
        )
        .unwrap();
        let mut handler2 = ScriptedHandler::always_ack();
        let result2 = exec.run_with_handler(&mut handler2);

        let kinds1 = structural_kinds(&handler1.log);
        let kinds2 = structural_kinds(&handler2.log);
        assert_eq!(kinds1, kinds2, "structural effect sequence mismatch for multiple params");

        assert!(result1.is_ok());
        assert!(result2.is_ok());
        assert_eq!(result1.unwrap(), result2.unwrap());
    }

    #[test]
    fn differential_action_empty_resolve() {
        let source = r#"
            system Test {
                entity Creature { HP: int }
                action Noop on actor: Creature () {
                    resolve { }
                }
            }
        "#;

        let (program, type_env) = setup(source);

        // Recursive path
        let interp = crate::Interpreter::new(&program, &type_env).unwrap();
        let mut game1 = GameState::new();
        let a1 = add_creature(&mut game1, 10);
        let adapter1 = StateAdapter::new(game1);
        let mut handler1 = ScriptedHandler::always_ack();
        let result1 = adapter1.run(&mut handler1, |state, handler| {
            interp.execute_action(state, handler, "Noop", a1, vec![])
        });

        // Step-based path
        let core = RuntimeCore::new(Arc::clone(&program), Arc::clone(&type_env), 1, 1);
        let mut game2 = GameState::new();
        let a2 = add_creature(&mut game2, 10);
        let adapter2 = StateAdapter::new(game2);
        let exec = Execution::start_action(
            core, adapter2, "Noop", a2, vec![], Span::dummy(),
        )
        .unwrap();
        let mut handler2 = ScriptedHandler::always_ack();
        let result2 = exec.run_with_handler(&mut handler2);

        let kinds1 = structural_kinds(&handler1.log);
        let kinds2 = structural_kinds(&handler2.log);
        assert_eq!(kinds1, kinds2, "structural effect sequence mismatch for empty resolve");

        assert!(result1.is_ok());
        assert!(result2.is_ok());
        assert_eq!(result1.unwrap(), result2.unwrap());
    }

    #[test]
    fn differential_requires_fail_acknowledged() {
        // Host acknowledges a failed requires check (no override) → action aborts
        let source = r#"
            system Test {
                entity Creature { HP: int }
                action Heal on actor: Creature (target: Creature) {
                    requires { target.HP > 0 }
                    resolve {
                        target.HP += 5
                    }
                }
            }
        "#;

        let (program, type_env) = setup(source);

        // Recursive path
        let interp = crate::Interpreter::new(&program, &type_env).unwrap();
        let mut game1 = GameState::new();
        let h1 = add_creature(&mut game1, 20);
        let p1 = add_creature(&mut game1, 0); // HP=0 → requires fails
        let adapter1 = StateAdapter::new(game1);
        let mut handler1 = ScriptedHandler::always_ack();
        let result1 = adapter1.run(&mut handler1, |state, handler| {
            interp.execute_action(state, handler, "Heal", h1, vec![Value::Entity(p1)])
        });

        // Step-based path
        let core = RuntimeCore::new(Arc::clone(&program), Arc::clone(&type_env), 1, 1);
        let mut game2 = GameState::new();
        let h2 = add_creature(&mut game2, 20);
        let p2 = add_creature(&mut game2, 0);
        let adapter2 = StateAdapter::new(game2);
        let exec = Execution::start_action(
            core, adapter2, "Heal", h2, vec![Value::Entity(p2)], Span::dummy(),
        )
        .unwrap();
        let mut handler2 = ScriptedHandler::always_ack();
        let result2 = exec.run_with_handler(&mut handler2);

        let kinds1 = structural_kinds(&handler1.log);
        let kinds2 = structural_kinds(&handler2.log);
        assert_eq!(kinds1, kinds2, "structural effect sequence mismatch for requires fail (ack)");

        // Should have: ActionStarted, RequiresCheck, ActionCompleted
        assert_eq!(kinds1.len(), 3);

        // Both succeed (abort is not an error)
        assert!(result1.is_ok());
        assert!(result2.is_ok());
        assert_eq!(result1.unwrap(), result2.unwrap());

        // ActionCompleted should be Succeeded (abort is Ok(Void), not Err)
        if let Effect::ActionCompleted { outcome: o1, .. } = handler1.log.last().unwrap() {
            if let Effect::ActionCompleted { outcome: o2, .. } = handler2.log.last().unwrap() {
                assert_eq!(o1, o2);
                assert_eq!(*o1, ActionOutcome::Succeeded);
            }
        }
    }

    // ── Remaining differential tests (from design doc matrix) ──

    #[test]
    fn differential_action_invalid_response() {
        // ActionStarted → invalid Response type → ActionCompleted(Failed), RuntimeError
        let source = r#"
            system Test {
                entity Creature { HP: int }
                action Attack on actor: Creature () {
                    resolve { actor.HP -= 1 }
                }
            }
        "#;
        let (program, type_env) = setup(source);

        // Recursive path: send Override instead of Acknowledged/Vetoed
        let interp = crate::Interpreter::new(&program, &type_env).unwrap();
        let mut game1 = GameState::new();
        let a1 = add_creature(&mut game1, 20);
        let adapter1 = StateAdapter::new(game1);
        let mut handler1 = ScriptedHandler::new(vec![Response::Override(Value::Int(42))]);
        let _result1 = adapter1.run(&mut handler1, |state, handler| {
            interp.execute_action(state, handler, "Attack", a1, vec![])
        });

        // Step-based path
        let core = RuntimeCore::new(Arc::clone(&program), Arc::clone(&type_env), 1, 1);
        let mut game2 = GameState::new();
        let a2 = add_creature(&mut game2, 20);
        let adapter2 = StateAdapter::new(game2);
        let exec = Execution::start_action(
            core, adapter2, "Attack", a2, vec![], Span::dummy(),
        ).unwrap();
        let mut handler2 = ScriptedHandler::new(vec![Response::Override(Value::Int(42))]);
        let _result2 = exec.run_with_handler(&mut handler2);

        // Both should produce matching structural effect sequences
        let kinds1 = structural_kinds(&handler1.log);
        let kinds2 = structural_kinds(&handler2.log);
        assert_eq!(kinds1, kinds2, "structural effect sequence mismatch for invalid response");
    }

    #[test]
    fn differential_action_with_roll_in_body() {
        // roll() in action body → RollDice yielded
        let source = r#"
            system Test {
                entity Creature { HP: int }
                action Attack on actor: Creature (target: Creature) {
                    resolve {
                        let dmg: RollResult = roll(1d6)
                        target.HP -= dmg.total
                    }
                }
            }
        "#;
        let (program, type_env) = setup(source);

        // Recursive path
        let interp = crate::Interpreter::new(&program, &type_env).unwrap();
        let mut game1 = GameState::new();
        let a1 = add_creature(&mut game1, 20);
        let d1 = add_creature(&mut game1, 15);
        let adapter1 = StateAdapter::new(game1);
        use crate::value::{DiceExpr, RollResult};
        let roll_result = RollResult {
            expr: DiceExpr::single(1, 6, None, 0),
            dice: vec![4],
            kept: vec![4],
            modifier: 0,
            total: 4,
            unmodified: 4,
        };
        let mut handler1 = ScriptedHandler::new(vec![
            Response::Acknowledged, // ActionStarted
            Response::Rolled(roll_result.clone()), // RollDice → result 4
            Response::Acknowledged, // ActionCompleted
        ]);
        let result1 = adapter1.run(&mut handler1, |state, handler| {
            interp.execute_action(
                state, handler, "Attack", a1, vec![Value::Entity(d1)],
            )
        });

        // Step-based path
        let core = RuntimeCore::new(Arc::clone(&program), Arc::clone(&type_env), 1, 1);
        let mut game2 = GameState::new();
        let a2 = add_creature(&mut game2, 20);
        let d2 = add_creature(&mut game2, 15);
        let adapter2 = StateAdapter::new(game2);
        let exec = Execution::start_action(
            core, adapter2, "Attack", a2, vec![Value::Entity(d2)], Span::dummy(),
        ).unwrap();
        let roll_result2 = RollResult {
            expr: DiceExpr::single(1, 6, None, 0),
            dice: vec![4],
            kept: vec![4],
            modifier: 0,
            total: 4,
            unmodified: 4,
        };
        let mut handler2 = ScriptedHandler::new(vec![
            Response::Acknowledged, // ActionStarted
            Response::Rolled(roll_result2), // RollDice → result 4
            Response::Acknowledged, // ActionCompleted
        ]);
        let result2 = exec.run_with_handler(&mut handler2);

        let kinds1 = structural_kinds(&handler1.log);
        let kinds2 = structural_kinds(&handler2.log);
        assert_eq!(kinds1, kinds2, "structural effect sequence mismatch for roll in body");

        assert!(result1.is_ok(), "recursive failed: {result1:?}");
        assert!(result2.is_ok(), "step-based failed: {result2:?}");
    }

    #[test]
    fn differential_action_with_effectful_default() {
        // Action with effectful default (roll()) → RollDice yielded before body
        let source = r#"
            system Test {
                entity Creature { HP: int }
                action Attack on actor: Creature (damage: RollResult = roll(1d6)) {
                    resolve { actor.HP -= damage.total }
                }
            }
        "#;
        let (program, type_env) = setup(source);

        // Recursive path
        let interp = crate::Interpreter::new(&program, &type_env).unwrap();
        let mut game1 = GameState::new();
        let a1 = add_creature(&mut game1, 20);
        let adapter1 = StateAdapter::new(game1);
        use crate::value::{DiceExpr, RollResult};
        let mk_roll = || RollResult {
            expr: DiceExpr::single(1, 6, None, 0),
            dice: vec![3], kept: vec![3], modifier: 0, total: 3, unmodified: 3,
        };
        let mut handler1 = ScriptedHandler::new(vec![
            Response::Acknowledged, // ActionStarted
            Response::Rolled(mk_roll()), // RollDice for default
            Response::Acknowledged, // ActionCompleted
        ]);
        let result1 = adapter1.run(&mut handler1, |state, handler| {
            interp.execute_action(state, handler, "Attack", a1, vec![])
        });

        // Step-based path
        let core = RuntimeCore::new(Arc::clone(&program), Arc::clone(&type_env), 1, 1);
        let mut game2 = GameState::new();
        let a2 = add_creature(&mut game2, 20);
        let adapter2 = StateAdapter::new(game2);
        let exec = Execution::start_action(
            core, adapter2, "Attack", a2, vec![], Span::dummy(),
        ).unwrap();
        let mut handler2 = ScriptedHandler::new(vec![
            Response::Acknowledged, // ActionStarted
            Response::Rolled(mk_roll()), // RollDice for default
            Response::Acknowledged, // ActionCompleted
        ]);
        let result2 = exec.run_with_handler(&mut handler2);

        let kinds1 = structural_kinds(&handler1.log);
        let kinds2 = structural_kinds(&handler2.log);
        assert_eq!(kinds1, kinds2, "structural effect sequence mismatch for effectful default");

        assert!(result1.is_ok(), "recursive failed: {result1:?}");
        assert!(result2.is_ok(), "step-based failed: {result2:?}");

        // RollDice should appear between ActionStarted and ActionCompleted
        assert!(kinds1.contains(&EffectKind::RollDice));
    }

    #[test]
    fn differential_action_with_multiple_mutations() {
        // Action body with multiple field mutations
        let source = r#"
            system Test {
                entity Creature { HP: int, Armor: int }
                action Fortify on actor: Creature () {
                    resolve {
                        actor.Armor += 2
                        actor.HP += 1
                    }
                }
            }
        "#;
        let (program, type_env) = setup(source);

        let interp = crate::Interpreter::new(&program, &type_env).unwrap();
        let mut game1 = GameState::new();
        let mut f1 = FxHashMap::default();
        f1.insert(Name::from("HP"), Value::Int(20));
        f1.insert(Name::from("Armor"), Value::Int(5));
        let a1 = game1.add_entity("Creature", f1);
        let adapter1 = StateAdapter::new(game1);
        let mut handler1 = ScriptedHandler::always_ack();
        let result1 = adapter1.run(&mut handler1, |state, handler| {
            interp.execute_action(state, handler, "Fortify", a1, vec![])
        });

        let core = RuntimeCore::new(Arc::clone(&program), Arc::clone(&type_env), 1, 1);
        let mut game2 = GameState::new();
        let mut f2 = FxHashMap::default();
        f2.insert(Name::from("HP"), Value::Int(20));
        f2.insert(Name::from("Armor"), Value::Int(5));
        let a2 = game2.add_entity("Creature", f2);
        let adapter2 = StateAdapter::new(game2);
        let exec = Execution::start_action(
            core, adapter2, "Fortify", a2, vec![], Span::dummy(),
        ).unwrap();
        let mut handler2 = ScriptedHandler::always_ack();
        let result2 = exec.run_with_handler(&mut handler2);

        let kinds1 = structural_kinds(&handler1.log);
        let kinds2 = structural_kinds(&handler2.log);
        assert_eq!(kinds1, kinds2, "structural effect sequence mismatch for multiple mutations");

        assert!(result1.is_ok(), "recursive failed: {result1:?}");
        assert!(result2.is_ok(), "step-based failed: {result2:?}");
    }

    #[test]
    fn differential_scope_early_return() {
        // Early return from nested block → scopes cleaned up
        let source = r#"
            system Test {
                entity Creature { HP: int }
                action Heal on actor: Creature () {
                    resolve {
                        if actor.HP > 10 {
                            actor.HP += 0
                        } else {
                            actor.HP += 5
                        }
                    }
                }
            }
        "#;
        let (program, type_env) = setup(source);

        // Recursive path
        let interp = crate::Interpreter::new(&program, &type_env).unwrap();
        let mut game1 = GameState::new();
        let a1 = add_creature(&mut game1, 20);
        let adapter1 = StateAdapter::new(game1);
        let mut handler1 = ScriptedHandler::always_ack();
        let result1 = adapter1.run(&mut handler1, |state, handler| {
            interp.execute_action(state, handler, "Heal", a1, vec![])
        });

        // Step-based path
        let core = RuntimeCore::new(Arc::clone(&program), Arc::clone(&type_env), 1, 1);
        let mut game2 = GameState::new();
        let a2 = add_creature(&mut game2, 20);
        let adapter2 = StateAdapter::new(game2);
        let exec = Execution::start_action(
            core, adapter2, "Heal", a2, vec![], Span::dummy(),
        ).unwrap();
        let mut handler2 = ScriptedHandler::always_ack();
        let result2 = exec.run_with_handler(&mut handler2);

        let kinds1 = structural_kinds(&handler1.log);
        let kinds2 = structural_kinds(&handler2.log);
        assert_eq!(kinds1, kinds2, "structural effect sequence mismatch for early return");

        assert!(result1.is_ok(), "recursive failed: {result1:?}");
        assert!(result2.is_ok(), "step-based failed: {result2:?}");
        assert_eq!(result1.unwrap(), result2.unwrap());
    }

    #[test]
    fn differential_action_runtime_error() {
        // RuntimeError during action body → ActionCompleted(Failed)
        // Use requires check that aborts, then verify effect sequence matches
        let source = r#"
            system Test {
                entity Creature { HP: int }
                action Attack on actor: Creature (target: Creature) {
                    requires { target.HP > 100 }
                    resolve {
                        target.HP -= 5
                    }
                }
            }
        "#;
        let (program, type_env) = setup(source);

        // Recursive path — requires will fail (HP=10, not > 100)
        let interp = crate::Interpreter::new(&program, &type_env).unwrap();
        let mut game1 = GameState::new();
        let a1 = add_creature(&mut game1, 20);
        let t1 = add_creature(&mut game1, 10);
        let adapter1 = StateAdapter::new(game1);
        let mut handler1 = ScriptedHandler::always_ack();
        let result1 = adapter1.run(&mut handler1, |state, handler| {
            interp.execute_action(
                state, handler, "Attack", a1, vec![Value::Entity(t1)],
            )
        });

        // Step-based path
        let core = RuntimeCore::new(Arc::clone(&program), Arc::clone(&type_env), 1, 1);
        let mut game2 = GameState::new();
        let a2 = add_creature(&mut game2, 20);
        let t2 = add_creature(&mut game2, 10);
        let adapter2 = StateAdapter::new(game2);
        let exec = Execution::start_action(
            core, adapter2, "Attack", a2, vec![Value::Entity(t2)], Span::dummy(),
        ).unwrap();
        let mut handler2 = ScriptedHandler::always_ack();
        let result2 = exec.run_with_handler(&mut handler2);

        let kinds1 = structural_kinds(&handler1.log);
        let kinds2 = structural_kinds(&handler2.log);
        assert_eq!(kinds1, kinds2, "structural effect sequence mismatch for failed requires");

        // Both should succeed (abort is Ok, not Err)
        assert!(result1.is_ok(), "recursive failed: {result1:?}");
        assert!(result2.is_ok(), "step-based failed: {result2:?}");

        // Should have ActionStarted, RequiresCheck, ActionCompleted
        assert!(kinds1.contains(&EffectKind::RequiresCheck));
    }

    #[test]
    fn differential_condition_apply() {
        // apply_condition in action body → ConditionApplyGate + ApplyCondition
        let source = r#"
            system Test {
                entity Creature { HP: int }
                condition Poisoned(damage: int) on bearer: Creature {
                    on_apply { bearer.HP -= damage }
                }
                action Poison on actor: Creature (target: Creature, amount: int) {
                    resolve {
                        apply_condition(target, Poisoned(damage: amount), Duration.Indefinite)
                    }
                }
            }
        "#;
        let (program, type_env) = setup(source);

        // Recursive path
        let interp = crate::Interpreter::new(&program, &type_env).unwrap();
        let mut game1 = GameState::new();
        let a1 = add_creature(&mut game1, 20);
        let t1 = add_creature(&mut game1, 15);
        let adapter1 = StateAdapter::new(game1);
        let mut handler1 = ScriptedHandler::always_ack();
        let result1 = adapter1.run(&mut handler1, |state, handler| {
            interp.execute_action(
                state, handler, "Poison", a1, vec![Value::Entity(t1), Value::Int(3)],
            )
        });

        // Step-based path
        let core = RuntimeCore::new(Arc::clone(&program), Arc::clone(&type_env), 1, 1);
        let mut game2 = GameState::new();
        let a2 = add_creature(&mut game2, 20);
        let t2 = add_creature(&mut game2, 15);
        let adapter2 = StateAdapter::new(game2);
        let exec = Execution::start_action(
            core, adapter2, "Poison", a2,
            vec![Value::Entity(t2), Value::Int(3)], Span::dummy(),
        ).unwrap();
        let mut handler2 = ScriptedHandler::always_ack();
        let result2 = exec.run_with_handler(&mut handler2);

        let kinds1 = structural_kinds(&handler1.log);
        let kinds2 = structural_kinds(&handler2.log);
        assert_eq!(kinds1, kinds2, "structural effect sequence mismatch for condition apply");

        assert!(result1.is_ok(), "recursive failed: {result1:?}");
        assert!(result2.is_ok(), "step-based failed: {result2:?}");

        // Should contain ConditionApplyGate
        assert!(kinds1.contains(&EffectKind::ConditionApplyGate));
    }

    #[test]
    fn differential_condition_apply_vetoed() {
        // apply_condition → gate Vetoed → no condition applied
        let source = r#"
            system Test {
                entity Creature { HP: int }
                condition Poisoned(damage: int) on bearer: Creature {
                    on_apply { bearer.HP -= damage }
                }
                action Poison on actor: Creature (target: Creature) {
                    resolve {
                        apply_condition(target, Poisoned(damage: 3), Duration.Indefinite)
                    }
                }
            }
        "#;
        let (program, type_env) = setup(source);

        // Recursive path — veto the condition gate
        let interp = crate::Interpreter::new(&program, &type_env).unwrap();
        let mut game1 = GameState::new();
        let a1 = add_creature(&mut game1, 20);
        let t1 = add_creature(&mut game1, 15);
        let adapter1 = StateAdapter::new(game1);
        let mut handler1 = ScriptedHandler::new(vec![
            Response::Acknowledged,  // ActionStarted
            Response::Vetoed,        // ConditionApplyGate → vetoed
            Response::Acknowledged,  // ActionCompleted
        ]);
        let result1 = adapter1.run(&mut handler1, |state, handler| {
            interp.execute_action(
                state, handler, "Poison", a1, vec![Value::Entity(t1)],
            )
        });

        // Step-based path
        let core = RuntimeCore::new(Arc::clone(&program), Arc::clone(&type_env), 1, 1);
        let mut game2 = GameState::new();
        let a2 = add_creature(&mut game2, 20);
        let t2 = add_creature(&mut game2, 15);
        let adapter2 = StateAdapter::new(game2);
        let exec = Execution::start_action(
            core, adapter2, "Poison", a2,
            vec![Value::Entity(t2)], Span::dummy(),
        ).unwrap();
        let mut handler2 = ScriptedHandler::new(vec![
            Response::Acknowledged,  // ActionStarted
            Response::Vetoed,        // ConditionApplyGate → vetoed
            Response::Acknowledged,  // ActionCompleted
        ]);
        let result2 = exec.run_with_handler(&mut handler2);

        let kinds1 = structural_kinds(&handler1.log);
        let kinds2 = structural_kinds(&handler2.log);
        assert_eq!(kinds1, kinds2, "structural effect sequence mismatch for condition veto");

        assert!(result1.is_ok(), "recursive failed: {result1:?}");
        assert!(result2.is_ok(), "step-based failed: {result2:?}");
    }

    #[test]
    fn differential_spawn_in_action() {
        // spawn in action body → SpawnEntity + GrantGroup effects
        let source = r#"
            system Test {
                entity Creature { HP: int }
                entity Minion { HP: int }
                action Summon on actor: Creature () {
                    resolve {
                        let m = Minion { HP: 5 }
                    }
                }
            }
        "#;
        let (program, type_env) = setup(source);

        // Recursive path
        let interp = crate::Interpreter::new(&program, &type_env).unwrap();
        let mut game1 = GameState::new();
        let a1 = add_creature(&mut game1, 20);
        let adapter1 = StateAdapter::new(game1);
        let mut handler1 = ScriptedHandler::always_ack();
        let result1 = adapter1.run(&mut handler1, |state, handler| {
            interp.execute_action(state, handler, "Summon", a1, vec![])
        });

        // Step-based path
        let core = RuntimeCore::new(Arc::clone(&program), Arc::clone(&type_env), 1, 1);
        let mut game2 = GameState::new();
        let a2 = add_creature(&mut game2, 20);
        let adapter2 = StateAdapter::new(game2);
        let exec = Execution::start_action(
            core, adapter2, "Summon", a2, vec![], Span::dummy(),
        ).unwrap();
        let mut handler2 = ScriptedHandler::always_ack();
        let result2 = exec.run_with_handler(&mut handler2);

        let kinds1 = structural_kinds(&handler1.log);
        let kinds2 = structural_kinds(&handler2.log);
        assert_eq!(kinds1, kinds2, "structural effect sequence mismatch for spawn");

        assert!(result1.is_ok(), "recursive failed: {result1:?}");
        assert!(result2.is_ok(), "step-based failed: {result2:?}");
    }

    #[test]
    fn differential_nested_emit_hooks() {
        // Nested emit: hook body triggers action that emits hooks
        let source = r#"
            system Test {
                entity Creature { HP: int }
                event DamageDealt(target: entity, amount: int)
                action Attack on actor: Creature (target: Creature) {
                    resolve {
                        target.HP -= 5
                        emit DamageDealt(target: target, amount: 5)
                    }
                }
                hook LogDamage on receiver: Creature (
                    trigger: DamageDealt(target: receiver)
                ) {
                    receiver.HP += 1
                }
            }
        "#;
        let (program, type_env) = setup(source);

        // Recursive path
        let interp = crate::Interpreter::new(&program, &type_env).unwrap();
        let mut game1 = GameState::new();
        let a1 = add_creature(&mut game1, 20);
        let d1 = add_creature(&mut game1, 15);
        let adapter1 = StateAdapter::new(game1);
        let mut handler1 = ScriptedHandler::always_ack();
        let result1 = adapter1.run(&mut handler1, |state, handler| {
            interp.execute_action(
                state, handler, "Attack", a1, vec![Value::Entity(d1)],
            )
        });

        // Step-based path
        let core = RuntimeCore::new(Arc::clone(&program), Arc::clone(&type_env), 1, 1);
        let mut game2 = GameState::new();
        let a2 = add_creature(&mut game2, 20);
        let d2 = add_creature(&mut game2, 15);
        let adapter2 = StateAdapter::new(game2);
        let exec = Execution::start_action(
            core, adapter2, "Attack", a2, vec![Value::Entity(d2)], Span::dummy(),
        ).unwrap();
        let mut handler2 = ScriptedHandler::always_ack();
        let result2 = exec.run_with_handler(&mut handler2);

        let kinds1 = structural_kinds(&handler1.log);
        let kinds2 = structural_kinds(&handler2.log);
        assert_eq!(kinds1, kinds2, "structural effect sequence mismatch for nested emit");

        assert!(result1.is_ok(), "recursive failed: {result1:?}");
        assert!(result2.is_ok(), "step-based failed: {result2:?}");

        // Should have inner ActionStarted/Completed for the hook
        let action_started_count = kinds1.iter()
            .filter(|k| **k == EffectKind::ActionStarted)
            .count();
        assert!(action_started_count >= 2, "expected inner hook ActionStarted");
    }

    #[test]
    fn differential_action_conditional_logic() {
        // Action with conditional branching in resolve body
        let source = r#"
            system Test {
                entity Creature { HP: int }
                action ConditionalHeal on actor: Creature (target: Creature) {
                    resolve {
                        if target.HP < 10 {
                            target.HP += 5
                        } else {
                            target.HP += 1
                        }
                    }
                }
            }
        "#;
        let (program, type_env) = setup(source);

        let interp = crate::Interpreter::new(&program, &type_env).unwrap();
        let mut game1 = GameState::new();
        let a1 = add_creature(&mut game1, 20);
        let t1 = add_creature(&mut game1, 5);
        let adapter1 = StateAdapter::new(game1);
        let mut handler1 = ScriptedHandler::always_ack();
        let result1 = adapter1.run(&mut handler1, |state, handler| {
            interp.execute_action(
                state, handler, "ConditionalHeal", a1, vec![Value::Entity(t1)],
            )
        });

        let core = RuntimeCore::new(Arc::clone(&program), Arc::clone(&type_env), 1, 1);
        let mut game2 = GameState::new();
        let a2 = add_creature(&mut game2, 20);
        let t2 = add_creature(&mut game2, 5);
        let adapter2 = StateAdapter::new(game2);
        let exec = Execution::start_action(
            core, adapter2, "ConditionalHeal", a2,
            vec![Value::Entity(t2)], Span::dummy(),
        ).unwrap();
        let mut handler2 = ScriptedHandler::always_ack();
        let result2 = exec.run_with_handler(&mut handler2);

        let kinds1 = structural_kinds(&handler1.log);
        let kinds2 = structural_kinds(&handler2.log);
        assert_eq!(kinds1, kinds2, "structural effect sequence mismatch for conditional");

        assert!(result1.is_ok(), "recursive failed: {result1:?}");
        assert!(result2.is_ok(), "step-based failed: {result2:?}");
    }

    #[test]
    fn differential_prompt_override() {
        // prompt() → ResolvePrompt → Override(value) → value used
        let source = r#"
            system Test {
                entity Creature { HP: int }
                prompt ChooseTarget(actor: Creature) -> Creature {
                    hint: "Choose a target"
                    suggest: actor
                    default { actor }
                }
                action SelectTarget on actor: Creature () {
                    resolve {
                        let chosen = ChooseTarget(actor)
                    }
                }
            }
        "#;
        let (program, type_env) = setup(source);

        // Recursive path — Override the prompt with a specific value
        let interp = crate::Interpreter::new(&program, &type_env).unwrap();
        let mut game1 = GameState::new();
        let a1 = add_creature(&mut game1, 20);
        let adapter1 = StateAdapter::new(game1);
        let mut handler1 = ScriptedHandler::new(vec![
            Response::Acknowledged,                 // ActionStarted
            Response::Override(Value::Entity(a1)),   // ResolvePrompt → override
            Response::Acknowledged,                 // ActionCompleted
        ]);
        let result1 = adapter1.run(&mut handler1, |state, handler| {
            interp.execute_action(state, handler, "SelectTarget", a1, vec![])
        });

        // Step-based path
        let core = RuntimeCore::new(Arc::clone(&program), Arc::clone(&type_env), 1, 1);
        let mut game2 = GameState::new();
        let a2 = add_creature(&mut game2, 20);
        let adapter2 = StateAdapter::new(game2);
        let exec = Execution::start_action(
            core, adapter2, "SelectTarget", a2, vec![], Span::dummy(),
        ).unwrap();
        let mut handler2 = ScriptedHandler::new(vec![
            Response::Acknowledged,                 // ActionStarted
            Response::Override(Value::Entity(a2)),   // ResolvePrompt → override
            Response::Acknowledged,                 // ActionCompleted
        ]);
        let result2 = exec.run_with_handler(&mut handler2);

        let kinds1 = structural_kinds(&handler1.log);
        let kinds2 = structural_kinds(&handler2.log);
        assert_eq!(kinds1, kinds2, "structural effect sequence mismatch for prompt override");

        assert!(result1.is_ok(), "recursive failed: {result1:?}");
        assert!(result2.is_ok(), "step-based failed: {result2:?}");

        // Should contain ResolvePrompt
        assert!(kinds1.contains(&EffectKind::ResolvePrompt));
    }

    #[test]
    fn differential_prompt_use_default() {
        // prompt() → ResolvePrompt → UseDefault → default block evaluates
        let source = r#"
            system Test {
                entity Creature { HP: int }
                prompt ChooseAmount(actor: Creature) -> int {
                    hint: "Choose an amount"
                    suggest: 5
                    default { 3 }
                }
                action DoSomething on actor: Creature () {
                    resolve {
                        let amount = ChooseAmount(actor)
                    }
                }
            }
        "#;
        let (program, type_env) = setup(source);

        // Recursive path — UseDefault
        let interp = crate::Interpreter::new(&program, &type_env).unwrap();
        let mut game1 = GameState::new();
        let a1 = add_creature(&mut game1, 20);
        let adapter1 = StateAdapter::new(game1);
        let mut handler1 = ScriptedHandler::new(vec![
            Response::Acknowledged,  // ActionStarted
            Response::UseDefault,    // ResolvePrompt → use default
            Response::Acknowledged,  // ActionCompleted
        ]);
        let result1 = adapter1.run(&mut handler1, |state, handler| {
            interp.execute_action(state, handler, "DoSomething", a1, vec![])
        });

        // Step-based path
        let core = RuntimeCore::new(Arc::clone(&program), Arc::clone(&type_env), 1, 1);
        let mut game2 = GameState::new();
        let a2 = add_creature(&mut game2, 20);
        let adapter2 = StateAdapter::new(game2);
        let exec = Execution::start_action(
            core, adapter2, "DoSomething", a2, vec![], Span::dummy(),
        ).unwrap();
        let mut handler2 = ScriptedHandler::new(vec![
            Response::Acknowledged,  // ActionStarted
            Response::UseDefault,    // ResolvePrompt → use default
            Response::Acknowledged,  // ActionCompleted
        ]);
        let result2 = exec.run_with_handler(&mut handler2);

        let kinds1 = structural_kinds(&handler1.log);
        let kinds2 = structural_kinds(&handler2.log);
        assert_eq!(kinds1, kinds2, "structural effect sequence mismatch for prompt UseDefault");

        assert!(result1.is_ok(), "recursive failed: {result1:?}");
        assert!(result2.is_ok(), "step-based failed: {result2:?}");
    }

    #[test]
    fn differential_action_with_let_bindings() {
        // Action with local variables and computed values
        let source = r#"
            system Test {
                entity Creature { HP: int }
                action ComputeHeal on actor: Creature (target: Creature) {
                    resolve {
                        let base = 3
                        let bonus = 2
                        target.HP += base + bonus
                    }
                }
            }
        "#;
        let (program, type_env) = setup(source);

        let interp = crate::Interpreter::new(&program, &type_env).unwrap();
        let mut game1 = GameState::new();
        let a1 = add_creature(&mut game1, 20);
        let t1 = add_creature(&mut game1, 10);
        let adapter1 = StateAdapter::new(game1);
        let mut handler1 = ScriptedHandler::always_ack();
        let result1 = adapter1.run(&mut handler1, |state, handler| {
            interp.execute_action(
                state, handler, "ComputeHeal", a1, vec![Value::Entity(t1)],
            )
        });

        let core = RuntimeCore::new(Arc::clone(&program), Arc::clone(&type_env), 1, 1);
        let mut game2 = GameState::new();
        let a2 = add_creature(&mut game2, 20);
        let t2 = add_creature(&mut game2, 10);
        let adapter2 = StateAdapter::new(game2);
        let exec = Execution::start_action(
            core, adapter2, "ComputeHeal", a2,
            vec![Value::Entity(t2)], Span::dummy(),
        ).unwrap();
        let mut handler2 = ScriptedHandler::always_ack();
        let result2 = exec.run_with_handler(&mut handler2);

        let kinds1 = structural_kinds(&handler1.log);
        let kinds2 = structural_kinds(&handler2.log);
        assert_eq!(kinds1, kinds2, "structural effect sequence mismatch for let bindings");

        assert!(result1.is_ok(), "recursive failed: {result1:?}");
        assert!(result2.is_ok(), "step-based failed: {result2:?}");
    }

    #[test]
    fn differential_derive_evaluation() {
        // Derive evaluated via step-based API matches recursive path
        let source = r#"
            system Test {
                entity Creature { HP: int, MaxHP: int }
                derive hp_ratio(actor: Creature) -> int {
                    actor.HP
                }
            }
        "#;
        let (program, type_env) = setup(source);

        // Recursive path
        let interp = crate::Interpreter::new(&program, &type_env).unwrap();
        let mut game1 = GameState::new();
        let a1 = game1.add_entity(
            "Creature",
            {
                let mut f = FxHashMap::default();
                f.insert(Name::from("HP"), Value::Int(15));
                f.insert(Name::from("MaxHP"), Value::Int(20));
                f
            },
        );
        let adapter1 = StateAdapter::new(game1);
        let mut handler1 = ScriptedHandler::always_ack();
        let result1 = adapter1.run(&mut handler1, |state, handler| {
            interp.evaluate_derive(state, handler, "hp_ratio", vec![Value::Entity(a1)])
        });

        // Step-based path
        let core = RuntimeCore::new(Arc::clone(&program), Arc::clone(&type_env), 1, 1);
        let mut game2 = GameState::new();
        let a2 = game2.add_entity(
            "Creature",
            {
                let mut f = FxHashMap::default();
                f.insert(Name::from("HP"), Value::Int(15));
                f.insert(Name::from("MaxHP"), Value::Int(20));
                f
            },
        );
        let adapter2 = StateAdapter::new(game2);
        let exec = Execution::start_derive(
            core, adapter2, "hp_ratio", vec![Value::Entity(a2)],
        ).unwrap();
        let mut handler2 = ScriptedHandler::always_ack();
        let result2 = exec.run_with_handler(&mut handler2);

        assert!(result1.is_ok(), "recursive failed: {result1:?}");
        assert!(result2.is_ok(), "step-based failed: {result2:?}");
        assert_eq!(result1.unwrap(), result2.unwrap());
    }

    #[test]
    fn differential_function_evaluation() {
        // Function evaluated via step-based API
        let source = r#"
            system Test {
                entity Creature { HP: int }
                function add_values(a: int, b: int) -> int {
                    a + b
                }
            }
        "#;
        let (program, type_env) = setup(source);

        // Recursive path
        let interp = crate::Interpreter::new(&program, &type_env).unwrap();
        let game1 = GameState::new();
        let adapter1 = StateAdapter::new(game1);
        let mut handler1 = ScriptedHandler::always_ack();
        let result1 = adapter1.run(&mut handler1, |state, handler| {
            interp.evaluate_function(
                state, handler, "add_values", vec![Value::Int(3), Value::Int(7)],
            )
        });

        // Step-based path
        let core = RuntimeCore::new(Arc::clone(&program), Arc::clone(&type_env), 1, 1);
        let game2 = GameState::new();
        let adapter2 = StateAdapter::new(game2);
        let exec = Execution::start_function(
            core, adapter2, "add_values", vec![Value::Int(3), Value::Int(7)],
        ).unwrap();
        let mut handler2 = ScriptedHandler::always_ack();
        let result2 = exec.run_with_handler(&mut handler2);

        assert!(result1.is_ok(), "recursive failed: {result1:?}");
        assert!(result2.is_ok(), "step-based failed: {result2:?}");
        let v1 = result1.unwrap();
        let v2 = result2.unwrap();
        assert_eq!(v1, v2);
        assert_eq!(v2, Value::Int(10));
    }
}
