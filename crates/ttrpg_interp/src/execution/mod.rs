//! Step-based execution API.
//!
//! The [`Execution`] object owns its game state and exposes a pull-based
//! `poll()`/`respond()` API, letting hosts drive execution at their own pace.
//! This is the complement to the callback-based `Interpreter` + `EffectHandler`
//! API, targeting async hosts, non-Rust embeddings, and step-debugging.

use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use rustc_hash::FxHashMap;

use ttrpg_ast::ast::{Arg, AssignOp, Block, CostClause, ExprKind, LValue, PatternKind, StmtKind};
use ttrpg_ast::{Name, Span, Spanned};

use crate::adapter::{MutationTracker, StateAdapter};
use crate::effect::{
    ActionKind, ActionOutcome, Effect, EffectHandler, EffectKind, Phase, Response, Step,
};
use crate::pipeline::OwnedModifier;
use crate::runtime_core::RuntimeCore;
use crate::select_action_overload;
use crate::state::{
    ActiveCondition, ConditionToken, EntityRef, InvocationId, StateProvider, WritableState,
};
use crate::value::DiceExpr;
use crate::value::Value;
use crate::{Env, Interpreter, RuntimeError, Scope};
use ttrpg_checker::env::FnInfo;
use ttrpg_checker::ty::Ty;

mod advance_action_lifecycle;
mod advance_block;
mod advance_condition;
mod advance_cost;
mod advance_derive;
mod advance_emit;
mod advance_host;
mod helpers;
mod walker;
pub(crate) use helpers::*;
pub(crate) use walker::*;

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

    pub(crate) fn push_scope(&mut self) {
        self.scopes.push(Scope::new());
    }

    pub(crate) fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    pub(crate) fn bind(&mut self, name: Name, value: Value) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.bindings.insert(name, value);
        }
    }

    pub(crate) fn lookup(&self, name: &str) -> Option<&Value> {
        for scope in self.scopes.iter().rev() {
            if let Some(val) = scope.bindings.get(name) {
                return Some(val);
            }
        }
        None
    }
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
    /// Evaluate requires clause (if present) via ExprEval child frame.
    EvalRequires,
    /// Requires expression evaluated; emit RequiresCheck with result.
    AwaitRequiresEval,
    /// Requires response received: check pass/fail.
    AwaitRequires,
    /// Evaluate cost (async path): push CostEval child frame if cost exists.
    EvalCost,
    /// Cost evaluation child frame completed.
    AwaitCostEval,
    /// Run the resolve body via bridge.
    RunResolve,
    /// Body completed: emit ActionCompleted.
    EmitCompleted,
    /// Completion ack received: restore context, pop with result.
    AwaitCompletedAck,
}

/// Phase within the CostEval frame's cost pipeline.
#[derive(Debug)]
pub(crate) enum CostEvalPhase {
    /// Initialize modifier collection: read conditions, compute stacking,
    /// build candidates for binding checks.
    CollectModifiers,
    /// Iterate binding-check candidates: process previous child result,
    /// push next BindingCheck child, or finish.
    CollectCheck,
    /// Set up scope for modifier at index, init walker, save old state.
    ApplyModifier(usize),
    /// Drive the walker: process modify stmts via ExprEval child frames.
    ExecCostModify(usize),
    /// Walker complete: pop scope, detect changes, build effect.
    CostModifyDone(usize),
    /// Yield the ModifyApplied effect for the modifier that just changed cost.
    /// After ack, advances to next modifier or transitions out.
    YieldModifyApplied(usize),
    /// Await host acknowledgement for a yielded ModifyApplied effect.
    AwaitModifyAck(usize),
    /// Build and push EmitHooks frame for modify_applied events.
    EmitModifyEvents,
    /// Awaiting EmitHooks child frame completion.
    AwaitModifyHooks,
    /// Budget pre-check: iterate tokens, check budget sufficiency.
    BudgetPreCheck(usize),
    /// Await budget pre-check host response.
    AwaitBudgetCheck(usize),
    /// Cost deduction: iterate tokens, yield DeductCost.
    Deduction(usize),
    /// Await deduction host response.
    AwaitDeduction(usize),
}

// ── CallTarget ─────────────────────────────────────────────────

/// Target for a `CallSetup` frame — determines what frame to push
/// once all arguments have been evaluated.
pub(crate) enum CallTarget {
    ApplyCondition {
        span: Span,
    },
    RemoveCondition {
        span: Span,
    },
    Revoke {
        span: Span,
    },
    Function {
        callee: Name,
        body: Block,
        slot_mapping: Vec<usize>,
        param_names: Vec<Name>,
        default_params: Vec<DefaultParam>,
    },
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
        /// Set to true when CostEval aborts (budget exhausted or cost vetoed).
        cost_aborted: bool,
        // Context save (populated when gate passes)
        saved_turn_actor: Option<EntityRef>,
        saved_invocation: Option<InvocationId>,
    },

    // ── Block / statement execution ─────────────────────────
    /// Block execution.
    Block {
        stmts: Vec<Spanned<StmtKind>>,
        index: usize,
        result: Value,
        expr_cache: Vec<Value>,
        /// When `Some`, a child frame (FunctionEval) was pushed to handle
        /// the current statement. The next `receive_child_result` stores
        /// the value here, and the next `advance()` uses it to complete
        /// the statement (bind for Let, set result for Expr).
        awaiting_fn: Option<AwaitingFn>,
        /// Error from a child frame dispatched via `awaiting_fn`.
        /// Checked before `awaiting_fn` in `advance()` so errors
        /// propagate instead of being silently dropped.
        awaiting_error: Option<RuntimeError>,
    },

    FillDefaults {
        params: Vec<DefaultParam>,
        index: usize,
        /// Result from ExprEval child evaluating a default expression.
        child_result: Option<Value>,
    },

    /// Materializes a bare condition name with default parameter values.
    /// Evaluates each default expression via child ExprEval frames, then
    /// pops a `Value::Condition { name, args }`.
    ConditionMaterialize {
        name: Name,
        params: Vec<DefaultParam>,
        index: usize,
        child_result: Option<Value>,
    },

    DeriveEval {
        name: Name,
        args: Vec<Value>,
        /// Whether this is a table (vs derive/mechanic).
        is_table: bool,
        base_value: Option<Value>,
        /// Phase of derive evaluation.
        phase: DeriveEvalPhase,
        /// Bound args (name→value) after mapping positional args.
        bound_args: Option<Vec<(Name, Value)>>,
        /// Modifiers collected during setup (for Phase 2 teardown).
        modifiers: Vec<OwnedModifier>,
        /// Function body, stored across phases for pushing FunctionEval.
        body: Option<Block>,
        /// Staged ModifyApplied effect for yield (Phase 1 or Phase 2).
        pending_modify_effect: Option<Effect>,
        /// Pending host response for yield/ack cycles.
        pending: Option<Response>,
        /// Accumulated params during Phase 1 modifier loop.
        phase1_params: Option<Vec<(Name, Value)>>,
        /// Accumulated result during Phase 2 modifier loop.
        phase2_result: Option<Value>,
        /// Cached FnInfo to avoid re-lookup across phase transitions.
        fn_info_cache: Option<FnInfo>,
        /// Result from EmitHooks child frame (modify_applied hooks).
        modify_hooks_result: Option<Result<Value, RuntimeError>>,
        /// Walker for inline modify stmt execution (Phase1/Phase2).
        modify_walker: Option<Box<ModifyStmtWalker>>,
        /// State for frame-based modifier collection (CollectCheck phase).
        collect_state: Option<Box<ModifierCollectState>>,
        /// Pre-built FillDefaults params from ExprWork dispatch path (named-arg
        /// mapping already done). When Some, Init phase uses these instead of
        /// building from positional `args`.
        pre_fill_params: Option<Vec<DefaultParam>>,
    },

    FunctionEval {
        name: Name,
        args: Vec<(Name, Value)>,
        /// Default expressions for missing optional params.
        default_params: Vec<(Name, Spanned<ExprKind>)>,
        body: Option<Block>,
        /// Whether defaults have been evaluated (via FillDefaults child).
        defaults_done: bool,
        /// Stores the child Block's result (Ok) or error (Err)
        /// for scope cleanup in the next advance() call.
        child_result: Option<Result<Value, RuntimeError>>,
    },

    EmitEval {
        event_name: Name,
        /// Argument expressions from the emit statement.
        args: Vec<Arg>,
        /// Index into args for per-arg evaluation via child frames.
        arg_index: usize,
        span: Span,
        phase: EmitEvalPhase,
        /// Accumulated param → value map from evaluated args.
        param_map: BTreeMap<Name, Value>,
        /// All fields (params + derived fields) for the payload.
        all_fields: BTreeMap<Name, Value>,
        /// Default expressions for missing params (collected from EventDecl).
        param_defaults: Vec<(Name, Spanned<ExprKind>)>,
        /// Default expressions for derived fields (collected from EventDecl).
        field_defaults: Vec<(Name, Spanned<ExprKind>)>,
        /// Index into param_defaults or field_defaults during iteration.
        default_index: usize,
        /// Saved emit_depth counter (restored on completion).
        saved_emit_depth: u32,
        /// Saved in_lifecycle_block counter (restored on completion).
        saved_lifecycle: u32,
        /// Whether a scope was pushed for field default evaluation.
        scope_pushed: bool,
        /// Result from child frame (EmitHooks/ExprEval/etc.).
        child_result: Option<Result<Value, RuntimeError>>,
    },

    EmitHooks {
        hooks: Vec<HookInfo>,
        condition_handlers: Vec<ConditionHandlerInfo>,
        index: usize,
        payload: Value,
        /// Whether emit_depth/lifecycle have been set up on first entry.
        initialized: bool,
        /// Result from child ActionLifecycle frame (hook execution).
        child_result: Option<Result<Value, RuntimeError>>,
    },

    EmitConditionHandlers {
        handlers: Vec<ConditionHandlerInfo>,
        index: usize,
        payload: Value,
        /// Result from child ConditionHandlerEpilogue frame.
        child_result: Option<Result<Value, RuntimeError>>,
    },

    /// After a condition handler body (Block) completes, read back mutated
    /// state fields, compare against snapshot, and emit SetConditionState
    /// if changed. Pushed by EmitConditionHandlers as a parent of Block.
    ConditionHandlerEpilogue {
        target: EntityRef,
        instance_id: u64,
        original_state: BTreeMap<Name, Value>,
        /// The block body to execute (pushed as a child Block on first advance).
        block_stmts: Option<Vec<Spanned<StmtKind>>>,
        /// Result from child Block or MutationYield frame.
        child_result: Option<Result<Value, RuntimeError>>,
        /// True when waiting for a MutationYield child to complete.
        awaiting_yield: bool,
    },

    ConditionApplyGate {
        target: EntityRef,
        condition_name: Name,
        params: Vec<(Name, Value)>,
        duration: Value,
        source: Value,
        tags: Vec<Name>,
        token: ConditionToken,
        pending: Option<Response>,
        /// State field defaults to evaluate (set after gate Acknowledged).
        state_defaults: Option<Vec<(Name, Spanned<ExprKind>)>>,
        /// Index into state_defaults for next field to evaluate.
        state_defaults_idx: usize,
        /// Accumulated state field values.
        state_fields_acc: BTreeMap<Name, Value>,
        /// CachingHandler cache for the current state field default.
        state_expr_cache: Vec<Value>,
        /// Whether a scope was pushed for the current default evaluation.
        default_scope_pushed: bool,
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
        /// Index into the condition declaration's clauses (on_apply blocks).
        clause_index: usize,
        /// Result from a child Block frame (on_apply body).
        child_result: Option<Result<Value, RuntimeError>>,
        /// Saved condition token to restore after lifecycle blocks.
        saved_condition_token: Option<ConditionToken>,
    },

    ConditionActivate {
        target: EntityRef,
        condition_name: Name,
        params: Vec<(Name, Value)>,
        duration: Value,
        source: Value,
        tags: Vec<Name>,
        token: ConditionToken,
        state_fields: BTreeMap<Name, Value>,
        pending: Option<Response>,
    },

    ConditionRemovalLoop {
        instances: Vec<(EntityRef, ActiveCondition)>,
        index: usize,
        first_error: Option<RuntimeError>,
        revoke_invocation: Option<InvocationId>,
        /// Result from child ConditionRemovalGate, ConditionOnRemove, or MutationYield frames.
        child_result: Option<Result<Value, RuntimeError>>,
        /// True when waiting for a MutationYield child (RevokeInvocation) to complete.
        awaiting_revoke: bool,
    },

    ConditionRemovalGate {
        target: EntityRef,
        condition_name: Name,
        instance_id: u64,
        pending: Option<Response>,
    },

    ConditionOnRemove {
        target: EntityRef,
        condition_name: Name,
        instance_id: u64,
        params: BTreeMap<Name, Value>,
        state_fields: BTreeMap<Name, Value>,
        /// Index into the condition declaration's clauses (on_remove blocks).
        clause_index: usize,
        /// Result from a child Block or MutationYield frame.
        child_result: Option<Result<Value, RuntimeError>>,
        /// Saved condition token to restore after lifecycle blocks.
        saved_condition_token: Option<ConditionToken>,
        /// Whether lifecycle context (counters) has been set up.
        lifecycle_setup: bool,
        /// Whether on_remove blocks have errored (still need to emit RemoveCondition).
        on_remove_error: Option<RuntimeError>,
        /// Cleanup phase after on_remove clauses complete:
        /// 0 = still running clauses, 1 = emit SetConditionState,
        /// 2 = emit RemoveCondition, 3 = emit RemoveSuspensionSource, 4 = done.
        cleanup_step: u8,
    },

    RollDiceWaiting {
        dice_expr: DiceExpr,
        span: Span,
        pending: Option<Response>,
    },

    PromptWaiting {
        prompt_name: Name,
        params: Vec<(Name, Value)>,
        return_type: Ty,
        hint: Option<String>,
        suggest: Option<Value>,
        default_block: Option<Block>,
        span: Span,
        pending: Option<Response>,
        /// Result from child frames (FillDefaults, ExprEval for suggest, UseDefault Block).
        /// Phase disambiguates the meaning.
        child_result: Option<Result<Value, RuntimeError>>,
        /// Current evaluation phase.
        phase: PromptPhase,
        /// Unevaluated suggest expression (evaluated via child ExprEval in EvalSuggest phase).
        suggest_expr: Option<Spanned<ExprKind>>,
        /// Param defaults to evaluate via FillDefaults.
        default_params: Vec<DefaultParam>,
    },

    SpawnEntity {
        entity_type: Name,
        base_fields: Vec<(Name, Value)>,
        groups: Vec<GroupInit>,
        phase: SpawnPhase,
        pending: Option<Response>,
        /// Entity ref returned by the host/adapter after SpawnEntity effect.
        entity_ref: Option<EntityRef>,
        span: Span,
    },

    BudgetGuard {
        actor: EntityRef,
        /// New budget to provision.
        budget: BTreeMap<Name, Value>,
        /// Previous budget to restore after body completes.
        saved_budget: Option<BTreeMap<Name, Value>>,
        body: Option<Block>,
        child_result: Option<Result<Value, RuntimeError>>,
        pending: Option<Response>,
        phase: BudgetGuardPhase,
        span: Span,
    },

    MultiBudgetGuard {
        entries: Vec<(EntityRef, BTreeMap<Name, Value>)>,
        saved_budgets: Vec<(EntityRef, Option<BTreeMap<Name, Value>>)>,
        provision_index: usize,
        phase: MultiBudgetPhase,
        body: Option<Block>,
        child_result: Option<Result<Value, RuntimeError>>,
        pending: Option<Response>,
        span: Span,
    },

    CostPayerGuard {
        saved_payer: Option<EntityRef>,
        body: Option<Block>,
        child_result: Option<Result<Value, RuntimeError>>,
    },

    /// Yield a GrantGroup or RevokeGroup effect and wait for host response.
    /// Acknowledged → Pop(Void), Vetoed → Error.
    GrantRevokeGate {
        effect: Effect,
        pending: Option<Response>,
        span: Span,
    },

    /// Yield a mutation effect (AdvanceTime, RemoveEntity, AddSuspension, etc.)
    /// and wait for host response. Acknowledged/Override/Vetoed → Pop(Void).
    MutationYield {
        effect: Effect,
        pending: Option<Response>,
        span: Span,
    },

    /// Cost evaluation frame for the async action lifecycle.
    /// Handles the full cost pipeline: modifier collection → apply → yield → budget → deduction.
    CostEval {
        cost: CostClause,
        actor: EntityRef,
        action_name: Name,
        call_span: Span,
        phase: CostEvalPhase,
        effective_cost: Option<CostClause>,
        pending: Option<Response>,
        abort_value: Value,
        /// Collected cost modifiers (populated by CollectModifiers phase).
        modifiers: Vec<crate::pipeline::OwnedModifier>,
        /// Pending ModifyApplied effect to yield (populated by ApplyModifier phase).
        pending_modify_effect: Option<Effect>,
        /// Result from EmitHooks child frame (modify_applied hooks).
        modify_hooks_result: Option<Result<Value, RuntimeError>>,
        /// Walker for inline cost modify stmt execution (ExecCostModify phase).
        modify_walker: Option<Box<ModifyStmtWalker>>,
        /// Saved old tokens/free for change detection during ExecCostModify.
        modify_old_tokens: Vec<String>,
        modify_old_free: bool,
        /// State for frame-based modifier collection (CollectCheck phase).
        collect_state: Option<Box<ModifierCollectState>>,
    },

    /// Evaluates call arguments one at a time via ExprEval children,
    /// then constructs and pushes the target frame (ConditionApplyGate,
    /// ConditionRemovalLoop, FunctionEval). Replaces the probe-then-build
    /// pattern that used TryEvalHandler.
    CallSetup {
        target: CallTarget,
        arg_exprs: Vec<Spanned<ExprKind>>,
        arg_index: usize,
        evaluated: Vec<Value>,
        child_result: Option<Result<Value, RuntimeError>>,
        /// true = waiting for target frame result, false = waiting for arg eval
        awaiting_child: bool,
        span: Span,
    },

    /// Step-based expression evaluator. Handles
    /// expressions that can be compiled to a work sequence.
    ExprEval {
        work: Vec<crate::expr_eval::ExprWork>,
        operands: Vec<Value>,
        pc: usize,
        child_result: Option<Result<Value, RuntimeError>>,
        scope_depth: usize,
    },

    /// For loop iteration frame. Iterates over materialized items,
    /// pushing Block child frames for each matching iteration body.
    ForLoop {
        items: Vec<Value>,
        index: usize,
        pattern: Box<Spanned<PatternKind>>,
        body: Vec<Spanned<StmtKind>>,
        /// Result from child Block frame executing the loop body.
        child_result: Option<Result<Value, RuntimeError>>,
    },

    /// List comprehension iteration frame. Iterates over materialized items,
    /// evaluating element expression for matching/filtered items, collecting
    /// results into a list.
    ListComp {
        items: Vec<Value>,
        index: usize,
        pattern: Box<Spanned<PatternKind>>,
        element: Box<Spanned<ExprKind>>,
        filter: Option<Box<Spanned<ExprKind>>>,
        collected: Vec<Value>,
        phase: ListCompPhase,
        span: Span,
        /// Result from child frame (filter or element evaluation).
        child_result: Option<Result<Value, RuntimeError>>,
    },

    /// Entry point frame for standalone expression evaluation.
    /// Used by `start_expr` and `start_expr_with_bindings`.
    ExprEntry {
        result: Option<Result<Value, RuntimeError>>,
        expr: Option<Spanned<ExprKind>>,
    },

    /// Evaluates modifier binding expressions and returns Bool.
    /// Iterates bindings, pushing ExprEval children for each expression,
    /// comparing results with bound parameter values via `value_eq`.
    BindingCheck {
        bindings: Vec<ttrpg_ast::ast::ModifyBinding>,
        bound_params: Vec<(Name, Value)>,
        scope_bindings: Vec<(Name, Value)>,
        scope_mode: BindingScopeMode,
        index: usize,
        child_result: Option<Result<Value, RuntimeError>>,
        /// Whether Owned scope has been pushed (for cleanup on error).
        scope_pushed: bool,
    },
}

/// Controls whether [`Frame::BindingCheck`] manages its own scope.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BindingScopeMode {
    /// Push scope on init with scope_bindings, pop on completion/early-exit.
    Owned,
    /// Caller manages scope. Frame does no push/pop.
    Caller,
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
    /// For bridge evaluation of locally-applied effects, `NoYieldHandler` is
    /// used. For user-facing expressions (ExprEntry, DeriveEval, etc.),
    /// `CachingHandler` provides replay-based yielding on the async path.
    fn advance(
        &mut self,
        core: &RuntimeCore,
        env: &mut ExecEnv,
        sp: &dyn StateProvider,
        eh: &mut dyn EffectHandler,
        tracker: &MutationTracker,
    ) -> Advance {
        Self::advance_action(self, core, env, sp, eh, tracker)
    }

    /// Advance the frame by one step. Uses frame-based dispatch for
    /// statements that may contain host-decided effects: function calls
    /// dispatch via CallSetup, emit statements via EmitEval, and all
    /// other expressions via ExprEval.
    fn advance_action(
        frame: &mut Frame,
        core: &RuntimeCore,
        env: &mut ExecEnv,
        sp: &dyn StateProvider,
        eh: &mut dyn EffectHandler,
        tracker: &MutationTracker,
    ) -> Advance {
        match frame {
            Frame::ActionLifecycle { .. } => advance_action_lifecycle::advance_action_lifecycle(
                frame, core, env, sp, eh, tracker,
            ),

            Frame::CallSetup { .. } => {
                advance_action_lifecycle::advance_call_setup(frame, core, env, sp, eh, tracker)
            }

            Frame::ExprEval {
                work,
                operands,
                pc,
                child_result,
                scope_depth,
            } => crate::expr_eval::advance_expr_eval(
                work,
                operands,
                pc,
                child_result,
                scope_depth,
                core,
                env,
                sp,
                &mut *eh,
            ),

            Frame::ForLoop { .. } => {
                advance_block::advance_for_loop(frame, core, env, sp, eh, tracker)
            }

            Frame::ListComp { .. } => {
                advance_block::advance_list_comp(frame, core, env, sp, eh, tracker)
            }

            Frame::CostEval { .. } => {
                advance_cost::advance_cost_eval(frame, core, env, sp, eh, tracker)
            }

            Frame::ExprEntry { .. } => {
                advance_block::advance_expr_entry(frame, core, env, sp, eh, tracker)
            }

            Frame::BindingCheck { .. } => {
                advance_derive::advance_binding_check(frame, core, env, sp, eh, tracker)
            }

            Frame::Block { .. } => advance_block::advance_block(frame, core, env, sp, eh, tracker),

            Frame::FillDefaults { .. } => {
                advance_block::advance_fill_defaults(frame, core, env, sp, eh, tracker)
            }

            Frame::ConditionMaterialize { .. } => {
                advance_condition::advance_condition_materialize(frame, core, env, sp, eh, tracker)
            }

            Frame::DeriveEval { .. } => {
                advance_derive::advance_derive_eval(frame, core, env, sp, eh, tracker)
            }

            Frame::FunctionEval { .. } => {
                advance_derive::advance_function_eval(frame, core, env, sp, eh, tracker)
            }

            Frame::RollDiceWaiting { .. } => {
                advance_host::advance_roll_dice_waiting(frame, core, env, sp, eh, tracker)
            }

            Frame::PromptWaiting { .. } => {
                advance_host::advance_prompt_waiting(frame, core, env, sp, eh, tracker)
            }

            Frame::SpawnEntity { .. } => {
                advance_host::advance_spawn_entity(frame, core, env, sp, eh, tracker)
            }

            Frame::BudgetGuard { .. } => {
                advance_cost::advance_budget_guard(frame, core, env, sp, eh, tracker)
            }

            Frame::MultiBudgetGuard { .. } => {
                advance_cost::advance_multi_budget_guard(frame, core, env, sp, eh, tracker)
            }

            Frame::CostPayerGuard { .. } => {
                advance_cost::advance_cost_payer_guard(frame, core, env, sp, eh, tracker)
            }

            Frame::EmitEval { .. } => {
                advance_emit::advance_emit_eval(frame, core, env, sp, eh, tracker)
            }

            // ── Condition apply frames (Phase 5.3) ──────────────
            Frame::ConditionApplyGate { .. } => {
                advance_condition::advance_condition_apply_gate(frame, core, env, sp, eh, tracker)
            }

            Frame::ConditionOnApply { .. } => {
                advance_condition::advance_condition_on_apply(frame, core, env, sp, eh, tracker)
            }

            Frame::ConditionActivate { .. } => {
                advance_condition::advance_condition_activate(frame, core, env, sp, eh, tracker)
            }

            // ── EmitHooks frame (Phase 5.2) ──────────────────────────
            Frame::EmitHooks { .. } => {
                advance_emit::advance_emit_hooks(frame, core, env, sp, eh, tracker)
            }

            // ── EmitConditionHandlers frame (Phase 5.2) ──────────────
            Frame::EmitConditionHandlers { .. } => {
                advance_emit::advance_emit_condition_handlers(frame, core, env, sp, eh, tracker)
            }

            // ── ConditionHandlerEpilogue frame (Phase 5.2) ──────────
            Frame::ConditionHandlerEpilogue { .. } => {
                advance_condition::advance_condition_handler_epilogue(
                    frame, core, env, sp, eh, tracker,
                )
            }

            // ── Condition removal frames (Phase 5.4) ──────────────
            Frame::ConditionRemovalLoop { .. } => {
                advance_condition::advance_condition_removal_loop(frame, core, env, sp, eh, tracker)
            }

            Frame::ConditionRemovalGate { .. } => {
                advance_condition::advance_condition_removal_gate(frame, core, env, sp, eh, tracker)
            }

            Frame::GrantRevokeGate { .. } => {
                advance_host::advance_grant_revoke_gate(frame, core, env, sp, eh, tracker)
            }

            Frame::MutationYield { .. } => {
                advance_host::advance_mutation_yield(frame, core, env, sp, eh, tracker)
            }

            Frame::ConditionOnRemove { .. } => {
                advance_condition::advance_condition_on_remove(frame, core, env, sp, eh, tracker)
            }
        }
    }

    /// Deliver a host response to this frame.
    fn receive_response(&mut self, response: Response) {
        match self {
            Frame::ActionLifecycle { pending, .. } => *pending = Some(response),
            Frame::RollDiceWaiting { pending, .. } => *pending = Some(response),
            Frame::PromptWaiting { pending, .. } => *pending = Some(response),
            Frame::SpawnEntity { pending, .. } => *pending = Some(response),
            Frame::ConditionApplyGate { pending, .. } => *pending = Some(response),
            Frame::ConditionActivate { pending, .. } => *pending = Some(response),
            Frame::ConditionRemovalGate { pending, .. } => *pending = Some(response),
            Frame::GrantRevokeGate { pending, .. } => *pending = Some(response),
            Frame::CostEval { pending, .. } => *pending = Some(response),
            Frame::DeriveEval { pending, .. } => *pending = Some(response),
            Frame::BudgetGuard { pending, .. } => *pending = Some(response),
            Frame::MultiBudgetGuard { pending, .. } => *pending = Some(response),
            Frame::MutationYield { pending, .. } => *pending = Some(response),
            _ => {}
        }
    }

    /// Deliver a child frame's completion value.
    fn receive_child_result(&mut self, value: Value) {
        match self {
            Frame::ActionLifecycle {
                step,
                body_result,
                cost_aborted,
                ..
            } => {
                match step {
                    ActionStep::RunResolve => {
                        *body_result = Some(Ok(value));
                        *step = ActionStep::EmitCompleted;
                    }
                    ActionStep::AwaitRequiresEval => {
                        // ExprEval child completed with requires result.
                        *body_result = Some(Ok(value));
                    }
                    ActionStep::AwaitCostEval => {
                        // CostEval child completed. Bool(false) is the abort sentinel.
                        if value == Value::Bool(false) {
                            *cost_aborted = true;
                        }
                        *body_result = Some(Ok(value));
                    }
                    _ => {}
                }
            }
            Frame::Block {
                expr_cache,
                awaiting_fn,
                result,
                ..
            } => {
                if awaiting_fn.is_some() {
                    // Child FunctionEval completed. Store the result
                    // in `result` temporarily — advance() will read it
                    // and complete the statement.
                    *result = value;
                } else {
                    // Child yield frame completed (RollDiceWaiting, etc.).
                    // Cache the result for replay-with-cache on the next
                    // advance(). The statement index was not advanced, so
                    // the same statement will be retried with the cached
                    // value available.
                    expr_cache.push(value);
                }
            }
            Frame::PromptWaiting { child_result, .. } => {
                // Child completed (FillDefaults, suggest ExprEval, or UseDefault Block).
                *child_result = Some(Ok(value));
            }
            Frame::FillDefaults { child_result, .. } => {
                // ExprEval child completed with default value.
                *child_result = Some(value);
            }
            Frame::ConditionMaterialize { child_result, .. } => {
                // ExprEval child completed with condition param default value.
                *child_result = Some(value);
            }
            Frame::FunctionEval { child_result, .. } => {
                // Block child completed.
                *child_result = Some(Ok(value));
            }
            Frame::BudgetGuard { child_result, .. } => {
                *child_result = Some(Ok(value));
            }
            Frame::MultiBudgetGuard { child_result, .. } => {
                *child_result = Some(Ok(value));
            }
            Frame::CostPayerGuard { child_result, .. } => {
                *child_result = Some(Ok(value));
            }
            Frame::EmitEval { child_result, .. } => {
                *child_result = Some(Ok(value));
            }
            Frame::ConditionOnApply { child_result, .. } => {
                *child_result = Some(Ok(value));
            }
            Frame::ConditionRemovalLoop { child_result, .. } => {
                *child_result = Some(Ok(value));
            }
            Frame::ConditionOnRemove { child_result, .. } => {
                *child_result = Some(Ok(value));
            }
            Frame::EmitHooks { child_result, .. } => {
                *child_result = Some(Ok(value));
            }
            Frame::EmitConditionHandlers { child_result, .. } => {
                *child_result = Some(Ok(value));
            }
            Frame::ConditionHandlerEpilogue { child_result, .. } => {
                *child_result = Some(Ok(value));
            }
            Frame::CallSetup { child_result, .. } => {
                *child_result = Some(Ok(value));
            }
            Frame::ExprEval { child_result, .. } => {
                *child_result = Some(Ok(value));
            }
            Frame::ForLoop { child_result, .. } => {
                *child_result = Some(Ok(value));
            }
            Frame::ListComp { child_result, .. } => {
                *child_result = Some(Ok(value));
            }
            Frame::ExprEntry { result, .. } => {
                // Child ExprEval completed.
                *result = Some(Ok(value));
            }
            Frame::BindingCheck { child_result, .. } => {
                *child_result = Some(Ok(value));
            }
            Frame::CostEval {
                phase,
                modify_hooks_result,
                modify_walker,
                collect_state,
                ..
            } => {
                if matches!(phase, CostEvalPhase::CollectCheck) {
                    // BindingCheck child completed for modifier collection.
                    if let Some(cs) = collect_state.as_mut() {
                        cs.child_result = Some(Ok(value));
                    }
                } else if matches!(phase, CostEvalPhase::ExecCostModify(_)) {
                    // ExprEval child completed for walker.
                    if let Some(walker) = modify_walker.as_mut() {
                        walker.receive_child(Ok(value));
                    }
                } else {
                    // EmitHooks child completed for modify_applied hooks.
                    *modify_hooks_result = Some(Ok(value));
                }
            }
            Frame::DeriveEval {
                base_value,
                phase,
                modify_hooks_result,
                modify_walker,
                collect_state,
                ..
            } => {
                if matches!(
                    phase,
                    DeriveEvalPhase::CollectCheck | DeriveEvalPhase::SuppressCheck
                ) {
                    // BindingCheck child completed for modifier collection/suppression.
                    if let Some(cs) = collect_state.as_mut() {
                        cs.child_result = Some(Ok(value));
                    }
                } else if matches!(
                    phase,
                    DeriveEvalPhase::ExecPhase1Modify(_) | DeriveEvalPhase::ExecPhase2Modify(_)
                ) {
                    // ExprEval child completed for walker.
                    if let Some(walker) = modify_walker.as_mut() {
                        walker.receive_child(Ok(value));
                    }
                } else if matches!(phase, DeriveEvalPhase::AwaitModifyHooks) {
                    *modify_hooks_result = Some(Ok(value));
                } else {
                    // FunctionEval child completed with body result.
                    *base_value = Some(value);
                }
            }
            Frame::ConditionApplyGate {
                state_expr_cache, ..
            } => {
                // ExprEval child completed for state default evaluation.
                // Store result; advance() will pop scope and process.
                state_expr_cache.push(value);
            }
            _ => {}
        }
    }

    /// Deliver a child frame's error. Returns `Ok(())` if the parent
    /// absorbed the error (e.g., ActionLifecycle stores it for
    /// ActionCompleted(Failed)). Returns `Err(e)` if the parent cannot
    /// handle the error and it should propagate.
    fn receive_child_error(&mut self, error: RuntimeError) -> Result<(), RuntimeError> {
        match self {
            Frame::ActionLifecycle {
                step, body_result, ..
            } if matches!(step, ActionStep::RunResolve | ActionStep::EvalRequires) => {
                *body_result = Some(Err(error));
                *step = ActionStep::EmitCompleted;
                Ok(())
            }
            Frame::Block { awaiting_error, .. } => {
                // Child frame errored (FunctionEval via awaiting_fn, or
                // ExprEval via expr_cache replay). Store the error so
                // advance() can propagate it after scope cleanup.
                *awaiting_error = Some(error);
                Ok(())
            }
            Frame::FunctionEval { child_result, .. }
            | Frame::BudgetGuard { child_result, .. }
            | Frame::MultiBudgetGuard { child_result, .. }
            | Frame::CostPayerGuard { child_result, .. }
            | Frame::EmitEval { child_result, .. }
            | Frame::ConditionOnApply { child_result, .. }
            | Frame::ConditionOnRemove { child_result, .. }
            | Frame::EmitHooks { child_result, .. }
            | Frame::EmitConditionHandlers { child_result, .. }
            | Frame::ConditionHandlerEpilogue { child_result, .. }
            | Frame::BindingCheck { child_result, .. } => {
                // Absorb the error so advance() can run cleanup
                // (scope pop, budget restore) before propagating.
                *child_result = Some(Err(error));
                Ok(())
            }
            Frame::CallSetup { child_result, .. } => {
                *child_result = Some(Err(error));
                Ok(())
            }
            Frame::ConditionRemovalLoop { child_result, .. } => {
                // Deferred error mode: absorb child errors so the loop
                // can stash them in first_error and continue processing
                // remaining instances.
                *child_result = Some(Err(error));
                Ok(())
            }
            Frame::ExprEntry { result, .. } => {
                // Child frame errored — store for advance() to return.
                *result = Some(Err(error));
                Ok(())
            }
            Frame::ExprEval { child_result, .. } => {
                *child_result = Some(Err(error));
                Ok(())
            }
            Frame::PromptWaiting { child_result, .. } => {
                *child_result = Some(Err(error));
                Ok(())
            }
            Frame::ForLoop { child_result, .. } => {
                *child_result = Some(Err(error));
                Ok(())
            }
            Frame::ListComp { child_result, .. } => {
                *child_result = Some(Err(error));
                Ok(())
            }
            Frame::CostEval {
                phase,
                modify_hooks_result,
                modify_walker,
                collect_state,
                ..
            } => {
                if matches!(phase, CostEvalPhase::CollectCheck) {
                    if let Some(cs) = collect_state.as_mut() {
                        cs.child_result = Some(Err(error));
                    }
                } else if matches!(phase, CostEvalPhase::ExecCostModify(_)) {
                    // ExprEval child errored during walker execution.
                    if let Some(walker) = modify_walker.as_mut() {
                        walker.receive_child(Err(error));
                    }
                } else {
                    *modify_hooks_result = Some(Err(error));
                }
                Ok(())
            }
            Frame::DeriveEval {
                phase,
                modify_hooks_result,
                modify_walker,
                collect_state,
                ..
            } => {
                if matches!(
                    phase,
                    DeriveEvalPhase::CollectCheck | DeriveEvalPhase::SuppressCheck
                ) {
                    if let Some(cs) = collect_state.as_mut() {
                        cs.child_result = Some(Err(error));
                    }
                } else if matches!(
                    phase,
                    DeriveEvalPhase::ExecPhase1Modify(_) | DeriveEvalPhase::ExecPhase2Modify(_)
                ) {
                    // ExprEval child errored during walker execution.
                    if let Some(walker) = modify_walker.as_mut() {
                        walker.receive_child(Err(error));
                    }
                } else {
                    *modify_hooks_result = Some(Err(error));
                }
                Ok(())
            }
            _ => Err(error),
        }
    }
}

// ── Supporting types for Frame variants ────────────────────────

/// Phase within a list comprehension iteration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ListCompPhase {
    /// Try pattern match on current item; if match, evaluate filter or element.
    TryMatch,
    /// Filter expression evaluated; check result and maybe evaluate element.
    FilterDone,
    /// Element expression evaluated; collect result.
    ElementDone,
}

/// Tracks that a child frame (FunctionEval) was pushed to handle a
/// statement's sub-expression on the async path.
#[derive(Debug)]
pub(crate) enum AwaitingFn {
    /// Bare expression statement — child result becomes block result.
    ExprStmt,
    /// Let binding — child result is bound to `name`.
    LetBinding { name: Name },
    /// Assignment — child result is the RHS value; apply the assign.
    Assign {
        target: LValue,
        op: AssignOp,
        span: Span,
    },
    /// Return statement — child result becomes the return value.
    Return,
    /// Assignment yielded a mutation effect via MutationYield child.
    /// Just advance the index when the child completes.
    AssignYield,
}

/// A parameter whose default expression may need evaluation.
#[derive(Clone)]
pub(crate) struct DefaultParam {
    pub name: Name,
    /// If provided by the caller, the value is here.
    pub provided_value: Option<Value>,
    /// Default expression to evaluate when `provided_value` is `None`.
    pub default_expr: Option<Spanned<ExprKind>>,
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

/// Phase within derive/mechanic evaluation.
#[derive(Debug)]
pub(crate) enum DeriveEvalPhase {
    /// Initial: look up decl, map positional args, push FillDefaults if needed.
    Init,
    /// Defaults filled: store bound_args and body, transition to CollectModifiers.
    DefaultsDone,
    /// Initialize modifier collection: iterate conditions + options,
    /// build candidates for binding checks.
    CollectModifiers,
    /// Iterate binding-check candidates for modifier collection.
    CollectCheck,
    /// Collection done: sort results, build suppression candidates.
    CollectDone,
    /// Iterate suppression binding-check candidates.
    SuppressCheck,
    /// Set up scope for Phase 1 modifier at index, init walker.
    ApplyPhase1(usize),
    /// Drive walker for Phase 1 modify stmts.
    ExecPhase1Modify(usize),
    /// Walker complete: pop scope, detect changes, build effect.
    Phase1ModifyDone(usize),
    /// Yield the pending ModifyApplied effect for Phase 1.
    YieldPhase1(usize),
    /// Await host ack for Phase 1 ModifyApplied.
    AwaitPhase1Ack(usize),
    /// Push FunctionEval child for body evaluation.
    PushBody,
    /// FunctionEval child completed with body result.
    BodyDone,
    /// Set up scope for Phase 2 modifier at index, init walker.
    ApplyPhase2(usize),
    /// Drive walker for Phase 2 modify stmts.
    ExecPhase2Modify(usize),
    /// Walker complete: pop scope, detect changes, build effect.
    Phase2ModifyDone(usize),
    /// Yield the pending ModifyApplied effect for Phase 2.
    YieldPhase2(usize),
    /// Await host ack for Phase 2 ModifyApplied.
    AwaitPhase2Ack(usize),
    /// Build and push EmitHooks frame for modify_applied events.
    EmitModifyEvents,
    /// Awaiting EmitHooks child frame completion.
    AwaitModifyHooks,
}

// ── ModifyStmtWalker ───────────────────────────────────────────
//
// Shared state machine for walking `ModifyStmt` lists. Owned as a field
// inside parent frames (CostEval, DeriveEval). Handles statement iteration,
// If-body recursion via an explicit stack, and ExprEval child result
// tracking. The parent interprets mode-specific results.

/// Group initialization data for entity construction.
#[derive(Debug, Clone)]
pub(crate) struct GroupInit {
    pub group_name: Name,
    pub fields: BTreeMap<Name, Value>,
}

/// Phase within prompt evaluation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PromptPhase {
    /// Evaluate param defaults via FillDefaults child.
    EvalDefaults,
    /// FillDefaults done; evaluate suggest expression via ExprEval child.
    EvalSuggest,
    /// Suggest done (or no suggest); emit ResolvePrompt yield.
    EmitPrompt,
    /// Waiting for host response.
    AwaitResponse,
    /// UseDefault block child running.
    RunningDefault,
}

/// Phase within entity spawn.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SpawnPhase {
    Defaults,
    Spawned,
    GrantingGroups { index: usize },
}

/// Phase within single-entity budget guard.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BudgetGuardPhase {
    /// Yield ProvisionBudget, await host response.
    Provision,
    /// Push body Block.
    Body,
    /// Yield restore effect (ProvisionBudget or ClearBudget), await host response.
    Restore,
}

/// Phase within multi-entity budget scope.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum MultiBudgetPhase {
    Provisioning,
    /// Rolling back already-provisioned budgets after a veto.
    Rollback {
        index: usize,
    },
    Body,
    Restoring {
        index: usize,
    },
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
    #[allow(dead_code)]
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

    // ── Raw mode: poll() bypasses StateAdapter auto-apply ──
    raw: bool,
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
            raw: false,
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
        let action_decl = select_action_overload(overloads, entity_type.as_ref())
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
                default_params.push((action_decl.params[i].name.clone(), default_expr.clone()));
            }
        }

        // Pre-allocate invocation ID
        let inv_id = InvocationId(core.alloc_invocation_id()?);

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
            cost_aborted: false,
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
            .ok_or_else(|| RuntimeError::new(format!("undefined reaction '{reaction_name}'")))?
            .clone();

        let inv_id = InvocationId(core.alloc_invocation_id()?);

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
            cost_aborted: false,
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
            .ok_or_else(|| RuntimeError::new(format!("undefined hook '{hook_name}'")))?
            .clone();

        let inv_id = InvocationId(core.alloc_invocation_id()?);

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
            cost_aborted: false,
            saved_turn_actor: None,
            saved_invocation: None,
        });

        Ok(exec)
    }

    /// Start executing all matching hooks as a single batch execution.
    ///
    /// Pushes an `EmitHooks` frame that dispatches each hook in order.
    /// Hosts that don't need per-hook control can fire all matching hooks
    /// as one `Execution` and drive the entire batch via `poll()`/`respond()`.
    ///
    /// `hooks` should come from [`event::find_matching_hooks`].
    pub fn start_hooks(
        core: Rc<RuntimeCore>,
        state: StateAdapter<S>,
        hooks: Vec<crate::event::HookInfo>,
        event_payload: Value,
        _call_span: Span,
    ) -> Self {
        let exec_hooks: Vec<HookInfo> = hooks
            .into_iter()
            .map(|h| HookInfo {
                hook_name: h.name,
                actor: h.target,
            })
            .collect();

        let mut exec = Self::new(core, state);

        if exec_hooks.is_empty() {
            // Push a trivial frame that immediately completes.
            exec.frames.push(Frame::ExprEntry {
                result: Some(Ok(Value::Void)),
                expr: None,
            });
        } else {
            exec.frames.push(Frame::EmitHooks {
                hooks: exec_hooks,
                condition_handlers: Vec::new(),
                index: 0,
                payload: event_payload,
                initialized: false,
                child_result: None,
            });
        }

        exec
    }

    /// Start executing a single condition event handler via the step-based
    /// frame stack.
    ///
    /// Looks up the condition declaration, verifies the condition instance
    /// still exists on the bearer, sets up scope bindings, and pushes a
    /// `ConditionHandlerEpilogue` frame that will execute the clause body
    /// and emit `SetConditionState` if state changed.
    ///
    /// `handler_info` should come from [`event::find_matching_condition_handlers`].
    pub fn start_condition_handler(
        core: Rc<RuntimeCore>,
        state: StateAdapter<S>,
        handler_info: &crate::event::ConditionHandlerInfo,
        event_payload: Value,
        call_span: Span,
    ) -> Result<Self, RuntimeError> {
        let decl = core
            .program
            .conditions
            .get(handler_info.condition_name.as_str())
            .ok_or_else(|| {
                RuntimeError::with_span(
                    format!(
                        "undefined condition '{}' in event handler",
                        handler_info.condition_name
                    ),
                    call_span,
                )
            })?
            .clone();

        // Read condition instance from state (verify it exists).
        let cond_instance = {
            let conditions = state
                .read_conditions(&handler_info.bearer)
                .unwrap_or_default();
            conditions
                .into_iter()
                .find(|c| c.id == handler_info.instance_id)
                .ok_or_else(|| {
                    RuntimeError::with_span(
                        format!(
                            "condition instance {} no longer exists on bearer {:?}",
                            handler_info.instance_id, handler_info.bearer
                        ),
                        call_span,
                    )
                })?
        };

        // Get the on-event clause body.
        let clause_body = match decl.clauses.get(handler_info.clause_index) {
            Some(ttrpg_ast::ast::ConditionClause::OnEvent(oe)) => oe.body.clone(),
            _ => {
                return Err(RuntimeError::with_span(
                    format!(
                        "condition '{}' clause {} is not an on-event clause",
                        handler_info.condition_name, handler_info.clause_index
                    ),
                    call_span,
                ));
            }
        };

        // Snapshot state for delta detection.
        let original_state = cond_instance.state_fields.clone();

        let mut exec = Self::new(core, state);

        // Push scope with bindings (receiver, self, params, state, trigger).
        exec.env.push_scope();
        exec.env.bind(
            decl.receiver_name.clone(),
            Value::Entity(handler_info.bearer),
        );
        exec.env.bind("self".into(), cond_instance.to_value());
        for (pname, pval) in &cond_instance.params {
            exec.env.bind(pname.clone(), pval.clone());
        }
        if !cond_instance.state_fields.is_empty() {
            exec.env.bind(
                Name::from("state"),
                Value::Struct {
                    name: Name::from("state"),
                    fields: cond_instance.state_fields.clone(),
                },
            );
        }
        exec.env.bind(Name::from("trigger"), event_payload);

        // Push ConditionHandlerEpilogue — it pushes the Block on first
        // advance, then does the state-diff + SetConditionState emit.
        exec.frames.push(Frame::ConditionHandlerEpilogue {
            target: handler_info.bearer,
            instance_id: handler_info.instance_id,
            original_state,
            block_stmts: Some(clause_body.node),
            child_result: None,
            awaiting_yield: false,
        });

        Ok(exec)
    }

    /// Start executing all matching condition event handlers as a single
    /// batch execution.
    ///
    /// Pushes an `EmitConditionHandlers` frame that dispatches each handler
    /// in order. For per-handler control, use [`start_condition_handler`] in
    /// a loop instead.
    ///
    /// `handlers` should come from [`event::find_matching_condition_handlers`].
    pub fn start_condition_handlers(
        core: Rc<RuntimeCore>,
        state: StateAdapter<S>,
        handlers: Vec<crate::event::ConditionHandlerInfo>,
        event_payload: Value,
    ) -> Self {
        let exec_handlers: Vec<ConditionHandlerInfo> = handlers
            .into_iter()
            .map(|h| ConditionHandlerInfo {
                target: h.bearer,
                condition_name: h.condition_name,
                instance_id: h.instance_id,
                handler_index: h.clause_index,
            })
            .collect();

        let mut exec = Self::new(core, state);

        if exec_handlers.is_empty() {
            exec.frames.push(Frame::ExprEntry {
                result: Some(Ok(Value::Void)),
                expr: None,
            });
        } else {
            exec.frames.push(Frame::EmitConditionHandlers {
                handlers: exec_handlers,
                index: 0,
                payload: event_payload,
                child_result: None,
            });
        }

        exec
    }

    // ── Non-action entry points (Phase 6) ──────────────────────

    /// Start evaluating a derive or table.
    ///
    /// Works on both sync (`run_with_handler`) and async (`poll/respond`)
    /// paths. On the async path, host-decided effects within the derive
    /// body (e.g., `roll()`) are yielded via CachingHandler replay.
    pub fn start_derive(
        core: Rc<RuntimeCore>,
        state: StateAdapter<S>,
        name: &str,
        args: Vec<Value>,
    ) -> Result<Self, RuntimeError> {
        let is_table = core.program.tables.contains_key(name);
        if !core.program.derives.contains_key(name) && !is_table {
            return Err(RuntimeError::new(format!(
                "undefined derive or table '{name}'"
            )));
        }
        let mut exec = Self::new(core, state);
        exec.frames.push(Frame::DeriveEval {
            name: Name::from(name),
            args,
            is_table,
            base_value: None,
            phase: DeriveEvalPhase::Init,
            bound_args: None,
            modifiers: Vec::new(),
            body: None,
            pending_modify_effect: None,
            phase1_params: None,
            phase2_result: None,
            fn_info_cache: None,
            pending: None,
            modify_hooks_result: None,
            modify_walker: None,
            collect_state: None,
            pre_fill_params: None,
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
            return Err(RuntimeError::new(format!("undefined mechanic '{name}'")));
        }
        let mut exec = Self::new(core, state);
        exec.frames.push(Frame::DeriveEval {
            name: Name::from(name),
            args,
            is_table: false,
            base_value: None,
            phase: DeriveEvalPhase::Init,
            bound_args: None,
            modifiers: Vec::new(),
            body: None,
            pending_modify_effect: None,
            phase1_params: None,
            phase2_result: None,
            fn_info_cache: None,
            pending: None,
            modify_hooks_result: None,
            modify_walker: None,
            collect_state: None,
            pre_fill_params: None,
        });
        Ok(exec)
    }

    /// Start evaluating a function.
    ///
    /// Looks up the function declaration, maps positional args, collects
    /// default expressions, and pushes a `FunctionEval` frame that pushes
    /// a `Block` frame for the body.
    pub fn start_function(
        core: Rc<RuntimeCore>,
        state: StateAdapter<S>,
        name: &str,
        args: Vec<Value>,
    ) -> Result<Self, RuntimeError> {
        let fn_decl = core
            .program
            .functions
            .get(name)
            .ok_or_else(|| RuntimeError::new(format!("undefined function '{name}'")))?
            .clone();

        let fn_info = core
            .type_env
            .lookup_fn(name)
            .ok_or_else(|| {
                RuntimeError::new(format!(
                    "internal error: no type info for function '{name}'"
                ))
            })?
            .clone();

        if args.len() > fn_info.params.len() {
            return Err(RuntimeError::new(format!(
                "too many arguments: '{}' takes {} params, got {}",
                name,
                fn_info.params.len(),
                args.len()
            )));
        }

        // Map positional args to param names
        let mut bound: Vec<(Name, Value)> = Vec::new();
        for (i, val) in args.into_iter().enumerate() {
            bound.push((fn_info.params[i].name.clone(), val));
        }

        // Collect default expressions for missing optional params.
        // They'll be evaluated in FunctionEval's advance method via bridge.
        let mut default_params = Vec::new();
        for i in bound.len()..fn_info.params.len() {
            if fn_info.params[i].has_default {
                if let Some(default_expr) = fn_decl.params.get(i).and_then(|p| p.default.as_ref()) {
                    default_params.push((fn_info.params[i].name.clone(), default_expr.clone()));
                }
            } else {
                return Err(RuntimeError::new(format!(
                    "missing required argument '{}' for '{}'",
                    fn_info.params[i].name, name
                )));
            }
        }

        let mut exec = Self::new(core, state);
        exec.frames.push(Frame::FunctionEval {
            name: Name::from(name),
            args: bound,
            default_params,
            body: Some(fn_decl.body.clone()),
            defaults_done: false,
            child_result: None,
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
        exec.frames.push(Frame::ExprEntry {
            result: None,
            expr: Some(expr),
        });
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
        exec.frames.push(Frame::ExprEntry {
            result: None,
            expr: Some(expr),
        });
        exec
    }

    // ── Poll / respond ─────────────────────────────────────────

    /// Poll for the next effect or completion.
    pub fn poll(&mut self) -> Result<Step, PollError> {
        match &self.protocol {
            ProtocolState::Pending => {
                return Err(PollError::Protocol(ProtocolError::EffectPending));
            }
            ProtocolState::Completed => {
                return Err(PollError::Protocol(ProtocolError::ExecutionCompleted));
            }
            ProtocolState::Idle | ProtocolState::Unwinding(_) => {}
        }

        let Execution {
            core,
            frames,
            env,
            state,
            final_result,
            protocol,
            pending_before_yield,
            raw,
            ..
        } = self;
        /// Handler that should never be reached — in raw poll mode, non-spawn
        /// effects are yielded to the host, not handled internally.
        struct NoYieldHandler;
        impl EffectHandler for NoYieldHandler {
            fn handle(&mut self, effect: Effect) -> Response {
                // This is an internal invariant violation: if we reach here,
                // a frame is trying to auto-resolve a host-decided effect
                // that should have been yielded instead.
                panic!(
                    "internal invariant violated: unexpected host-decided effect \
                     in synchronous poll: {:?}",
                    EffectKind::of(&effect)
                )
            }
        }

        let tracker = state.mutation_tracker();

        if *raw {
            // Raw mode: use state directly (not through AdaptedHandler) so we
            // can auto-apply SpawnEntity while bypassing adapter for everything
            // else.  SpawnEntity must be applied internally because subsequent
            // GrantGroup frames need a valid EntityRef.
            let mut handler = NoYieldHandler;
            loop {
                if frames.is_empty() {
                    if let ProtocolState::Unwinding(e) =
                        std::mem::replace(protocol, ProtocolState::Completed)
                    {
                        return Err(PollError::Runtime(e));
                    }
                    *protocol = ProtocolState::Completed;
                    let result = final_result.take().unwrap_or(Ok(Value::Void));
                    return match result {
                        Ok(v) => Ok(Step::Done(v)),
                        Err(e) => Err(PollError::Runtime(e)),
                    };
                }

                let frame = frames.last_mut().expect("frame stack non-empty (checked above)");
                let advance = frame.advance(core, env, &*state, &mut handler, tracker);

                match advance {
                    Advance::Yield(effect) if matches!(&effect, Effect::SpawnEntity { .. }) => {
                        // Auto-apply spawn and feed EntityRef back to frame.
                        let entity_ref =
                            state.with_state_mut(|gs| crate::adapter::apply_spawn(gs, &effect));
                        if let Some(frame) = frames.last_mut() {
                            frame.receive_response(Response::EntitySpawned(entity_ref));
                        }
                    }
                    Advance::Yield(effect) => {
                        *pending_before_yield =
                            Some(std::mem::replace(protocol, ProtocolState::Pending));
                        return Ok(Step::Yielded(Box::new(effect)));
                    }
                    Advance::Push(child) => {
                        frames.push(child);
                    }
                    Advance::Pop(value) => {
                        frames.pop();
                        if let Some(parent) = frames.last_mut() {
                            parent.receive_child_result(value);
                        } else {
                            *final_result = Some(Ok(value));
                        }
                    }
                    Advance::Continue => {}
                    Advance::Error(e) => {
                        frames.pop();
                        if let Some(parent) = frames.last_mut() {
                            match parent.receive_child_error(e) {
                                Ok(()) => {}
                                Err(e) => {
                                    *protocol = ProtocolState::Completed;
                                    return Err(PollError::Runtime(e));
                                }
                            }
                        } else {
                            *protocol = ProtocolState::Completed;
                            return Err(PollError::Runtime(e));
                        }
                    }
                }
            }
        } else {
            state.run(&mut NoYieldHandler, |sp, eh| {
                loop {
                    if frames.is_empty() {
                        if let ProtocolState::Unwinding(e) =
                            std::mem::replace(protocol, ProtocolState::Completed)
                        {
                            return Err(PollError::Runtime(e));
                        }
                        *protocol = ProtocolState::Completed;
                        let result = final_result.take().unwrap_or(Ok(Value::Void));
                        return match result {
                            Ok(v) => Ok(Step::Done(v)),
                            Err(e) => Err(PollError::Runtime(e)),
                        };
                    }

                    let frame = frames.last_mut().expect("frame stack non-empty (checked above)");
                    let advance = frame.advance(core, env, sp, eh, tracker);

                    match advance {
                        Advance::Yield(effect) => {
                            *pending_before_yield =
                                Some(std::mem::replace(protocol, ProtocolState::Pending));
                            return Ok(Step::Yielded(Box::new(effect)));
                        }
                        Advance::Push(child) => {
                            frames.push(child);
                        }
                        Advance::Pop(value) => {
                            frames.pop();
                            if let Some(parent) = frames.last_mut() {
                                parent.receive_child_result(value);
                            } else {
                                *final_result = Some(Ok(value));
                            }
                        }
                        Advance::Continue => {}
                        Advance::Error(e) => {
                            frames.pop();
                            if let Some(parent) = frames.last_mut() {
                                match parent.receive_child_error(e) {
                                    Ok(()) => {}
                                    Err(e) => {
                                        *protocol = ProtocolState::Completed;
                                        return Err(PollError::Runtime(e));
                                    }
                                }
                            } else {
                                *protocol = ProtocolState::Completed;
                                return Err(PollError::Runtime(e));
                            }
                        }
                    }
                }
            })
        }
    }

    /// Provide a host response to a yielded effect.
    pub fn respond(&mut self, response: Response) -> Result<(), ProtocolError> {
        match &self.protocol {
            ProtocolState::Idle | ProtocolState::Unwinding(_) => {
                return Err(ProtocolError::NoPendingEffect);
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
        self.drive(handler)
    }

    /// Like `run_with_handler`, but returns the inner state alongside the
    /// result. Useful when the caller needs the mutated state back (e.g.,
    /// the CLI runner which borrows `GameState` from a `RefCell`).
    pub fn run_returning_state(
        mut self,
        handler: &mut dyn EffectHandler,
    ) -> (Result<Value, RuntimeError>, S) {
        let result = self.drive(handler);
        (result, self.state.into_inner())
    }

    /// Inner loop shared by `run_with_handler` and `run_returning_state`.
    fn drive(&mut self, handler: &mut dyn EffectHandler) -> Result<Value, RuntimeError> {
        let Execution {
            core,
            frames,
            env,
            state,
            final_result,
            ..
        } = self;
        let tracker = state.mutation_tracker();
        state.run(handler, |sp, eh| {
            loop {
                if frames.is_empty() {
                    return final_result.take().unwrap_or(Ok(Value::Void));
                }

                let frame = frames.last_mut().expect("frame stack non-empty (checked above)");
                let advance = frame.advance(core, env, sp, eh, tracker);

                match advance {
                    Advance::Yield(effect) => {
                        let response = eh.handle(effect);
                        if let Some(frame) = frames.last_mut() {
                            frame.receive_response(response);
                        }
                    }
                    Advance::Push(child) => {
                        frames.push(child);
                    }
                    Advance::Pop(value) => {
                        frames.pop();
                        if let Some(parent) = frames.last_mut() {
                            parent.receive_child_result(value);
                        } else {
                            *final_result = Some(Ok(value));
                        }
                    }
                    Advance::Continue => {}
                    Advance::Error(e) => {
                        frames.pop();
                        if let Some(parent) = frames.last_mut() {
                            match parent.receive_child_error(e) {
                                Ok(()) => {}
                                Err(e) => return Err(e),
                            }
                        } else {
                            return Err(e);
                        }
                    }
                }
            }
        })
    }

    // ── Configuration ────────────────────────────────────────────

    /// Enable raw execution mode. When raw, `poll()` bypasses `StateAdapter`
    /// auto-apply — mutations flow through `Advance::Yield` to the host,
    /// which must call `apply_effect()` to apply them. The sync
    /// `run_with_handler`/`drive()` path is unaffected.
    pub fn raw(mut self) -> Self {
        self.raw = true;
        self
    }

    /// Returns whether raw mode is enabled.
    pub fn is_raw(&self) -> bool {
        self.raw
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
mod tests;
