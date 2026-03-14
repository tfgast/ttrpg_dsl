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
/// effects will panic (the caller must ensure the block only produces
/// locally-applied effects, or use frame-based evaluation instead).
fn bridge_eval_block<S: WritableState>(
    core: &RuntimeCore,
    env: &mut ExecEnv,
    state: &StateAdapter<S>,
    block: &Block,
) -> Result<Value, RuntimeError> {
    bridge_eval(core, env, state, |tmp_env| {
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
    bridge_eval(core, env, state, |tmp_env| {
        crate::eval::eval_expr(tmp_env, expr)
    })
}

/// Common bridge setup: snapshot ExecEnv into a temporary Env, run a
/// closure, and sync state back.
fn bridge_eval<S, F>(
    core: &RuntimeCore,
    env: &mut ExecEnv,
    state: &StateAdapter<S>,
    f: F,
) -> Result<Value, RuntimeError>
where
    S: WritableState,
    F: FnOnce(&mut Env) -> Result<Value, RuntimeError>,
{
    let interp = Interpreter::bridge(
        &core.program,
        &core.type_env,
        core.counters().0,
        core.counters().1,
    );

    struct NoYieldHandler;
    impl EffectHandler for NoYieldHandler {
        fn handle(&mut self, effect: Effect) -> Response {
            panic!(
                "unexpected forwarded effect in bridge evaluation: {:?}",
                EffectKind::of(&effect)
            )
        }
    }

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

    let mut inner = NoYieldHandler;
    let (result, out_scopes, out_lc_stack, out_ret_val) =
        state.run(&mut inner, |state_provider, effect_handler| {
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
}

// ── Frame advance implementation ───────────────────────────────

impl Frame {
    /// Advance the frame one step. Returns the action for the driver loop.
    fn advance<S: WritableState>(
        &mut self,
        core: &RuntimeCore,
        env: &mut ExecEnv,
        state: &StateAdapter<S>,
    ) -> Advance {
        match self {
            Frame::ActionLifecycle {
                name,
                actor,
                action_kind,
                call_span,
                has_return_type,
                inv_id,
                requires,
                resolve,
                receiver_name,
                bindings,
                default_params,
                step,
                pending,
                body_result,
                saved_turn_actor,
                saved_invocation,
                ..
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
                            None => return Advance::Continue, // shouldn't happen
                        };

                        match response {
                            Response::Acknowledged => {
                                // Save context
                                *saved_turn_actor = env.turn_actor.take();
                                *saved_invocation = env.current_invocation_id.take();
                                env.turn_actor = Some(*actor);
                                env.current_invocation_id = Some(*inv_id);
                                env.push_scope();

                                // Bind receiver and provided args
                                env.bind(
                                    receiver_name.clone(),
                                    Value::Entity(*actor),
                                );
                                for (pname, pval) in bindings.drain(..) {
                                    env.bind(pname, pval);
                                }

                                // Evaluate defaults via bridge (Phase 3 MVP:
                                // panics if defaults contain effectful builtins)
                                for (dname, dexpr) in default_params.drain(..) {
                                    match bridge_eval_expr(core, env, state, &dexpr) {
                                        Ok(val) => env.bind(dname, val),
                                        Err(e) => {
                                            *body_result = Some(Err(e));
                                            *step = ActionStep::EmitCompleted;
                                            return Advance::Continue;
                                        }
                                    }
                                }

                                // Move to requires (or directly to resolve)
                                if requires.is_some() {
                                    *step = ActionStep::EvalRequires;
                                } else {
                                    *step = ActionStep::RunResolve;
                                }
                                Advance::Continue
                            }

                            Response::Vetoed => {
                                *step = ActionStep::EmitVetoedCompleted;
                                Advance::Continue
                            }

                            other => {
                                // Protocol error — emit Failed completion
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
                            // Protocol error or error during setup
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
                        // Consume the ack (or ignore unexpected responses)
                        let _ = pending.take();
                        // If there was an error (protocol error path), return it
                        if let Some(Err(e)) = body_result.take() {
                            return Advance::Error(e);
                        }
                        Advance::Pop(abort_value)
                    }

                    ActionStep::EvalRequires => {
                        let req_expr = requires.as_ref().unwrap();
                        match bridge_eval_expr(core, env, state, req_expr) {
                            Ok(Value::Bool(passed)) => {
                                let effect = Effect::RequiresCheck {
                                    action: name.clone(),
                                    passed,
                                    reason: None,
                                };
                                // Store passed for AwaitRequires
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
                        env.return_value = None; // clear early-return flag
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
                        // Restore context
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

            // Phase 4-5 frames: not yet implemented
            Frame::ScopeGuard => Advance::Pop(Value::Void),
            _ => Advance::Error(RuntimeError::new(
                "frame type not yet implemented (Phase 4/5)",
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
    pub fn run_with_handler(
        mut self,
        handler: &mut dyn EffectHandler,
    ) -> Result<Value, RuntimeError> {
        loop {
            match self.poll() {
                Ok(Step::Yielded(effect)) => {
                    let response = handler.handle(*effect);
                    self.respond(response)
                        .expect("protocol error in run_with_handler");
                }
                Ok(Step::Done(value)) => return Ok(value),
                Err(PollError::Runtime(e)) => return Err(e),
                Err(PollError::Protocol(e)) => {
                    panic!("protocol error in run_with_handler: {e:?}")
                }
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
}
