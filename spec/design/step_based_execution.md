# Design: Resumable Step-Based Execution API

**Status:** Implemented (tdsl-qi09)

## Context

The interpreter is a synchronous recursive tree-walker. Every host interaction flows through `env.handler.handle(effect) -> Response` — 42 call sites across 9 source files. The host implements `EffectHandler`, a single-method trait:

```rust
pub trait EffectHandler {
    fn handle(&mut self, effect: Effect) -> Response;
}
```

This callback model has a fundamental constraint: the host must respond synchronously inside `handle()`. If the host is an async web server, a game UI waiting for player input, or a non-Rust embedding, it must block the calling thread until the response is available. There is no way for the host to receive an effect, do other work, and resume the interpreter later.

The `Interpreter<'p>` struct borrows `&'p Program` and `&'p TypeEnv`, which means it cannot be stored alongside the data it references. The execution environment (`Env`) is stack-allocated per API call, carrying mutable references to both the handler and the state provider. This tight coupling between the call stack, the execution state, and the host interface makes it impossible to pause execution at an effect boundary and resume it later without fundamental restructuring.

### Goals

1. **Single emission seam.** Replace scattered `handler.handle()` calls with a single interception point (`env.emit()`), making it possible to instrument, trace, or redirect all effects uniformly.

2. **Explicit inspectable state.** Move execution state that is currently implicit in Rust call frames (action lifecycle phase, block instruction pointer, emit dispatch index, condition lifecycle phase) into explicit data structures that can be inspected and resumed in-process. This makes the execution state a first-class value rather than an opaque stack, enabling step-debugging and host-driven control flow. (Serialization to disk is a future extension that this enables but is not a v1 deliverable — see Non-goals.)

3. **Pull-based execution API.** Expose an `Execution` object where the host polls for the next effect and provides a response, rather than implementing a callback trait. This enables async hosts, non-Rust embeddings, and step-debugging.

4. **Synchronous reads preserved.** The interpreter reads game state synchronously during evaluation (field access, condition queries, entity lookups). This must remain a direct function call, not a yielded effect. Only effect emissions (mutations, dice, prompts, gates) suspend.

5. **Dual API surface.** The existing `Interpreter` + `EffectHandler` callback API remains a first-class path for hosts that provide `&dyn StateProvider`. The step-based `Execution<S>` API is a separate entry point for hosts that can supply owned mutable state (`S: WritableState`). Both are supported long-term.

### Non-goals

- Thread-based suspension (threads are not preferred; the target is an internal resumable runner)
- Async/await transformation of the evaluator (viral, lifetime-hostile)
- Bytecode compilation (the tree-walking evaluator structure is fine; only the control flow needs restructuring)
- Replacing the `Interpreter` callback API — it continues to serve `StateProvider`-only hosts
- Concurrent execution sharing `RuntimeCore` across threads — v1 is single-threaded; `Send`/`Sync` and atomic counters can be added later if needed
- Serialization of `Execution` state to disk — v1 targets in-process resumability only; the explicit frame stack *enables* future serialization but does not require it (would need `Serialize` bounds on `S`, a reattach strategy for `RuntimeCore`, and round-trip parity tests)

## Current Architecture

### Execution state split

Today, durable execution state lives in two places:

1. **Explicit state in `Env`** (`lib.rs:579-605`):
   - `scopes: Vec<Scope>` — variable binding stack
   - `turn_actor`, `cost_payer` — entity context
   - `current_invocation_id` — action scope tracking
   - `emit_depth: u32` — nested emit recursion counter
   - `in_lifecycle_block: u32` — blocks nested apply/remove during on_apply/on_remove
   - `lifecycle_condition_stack: Vec<u64>` — condition IDs for active lifecycle blocks
   - `current_condition_token` — pre-allocated ID for upcoming condition
   - `return_value: Option<Value>` — early return propagation

2. **Implicit state in Rust call frames** (no single location — distributed across the recursive call chain):
   - Action lifecycle phase (started → requires → cost → body → completed)
   - Block execution progress (which statement index within `eval_block`'s loop)
   - Emit dispatch progress (which hook index, which condition handler index)
   - Condition lifecycle phase (gate → on_apply → activate)
   - Condition removal loop progress (which instance index, accumulated error)
   - Default argument evaluation progress (which parameter index in `fill_defaults`)
   - Prompt suggest/default body evaluation state
   - Scoped context save/restore (`scoped_execute` saves `turn_actor`/`invocation_id`, `scoped_budget` saves budget state)

The second category is the problem. When the evaluator yields at an effect boundary, these Rust call frames are destroyed. To resume, we need that state reconstructed — which means making it explicit.

### Recursive call structure

The principal recursive chains that cross effect boundaries:

```
execute_action (action.rs:212)
  └─ bind_args (positional only)                  ← no defaults yet
  └─ alloc_invocation_id()                        ← pre-allocated before gate (infallible pairing)
  └─ emit ActionStarted                          ← EFFECT
  └─ [if vetoed: emit ActionCompleted(Vetoed, invocation: None) ← EFFECT, return]
  └─ scoped_execute (action.rs:83)               ← receives pre-allocated inv_id
       └─ fill_defaults (args.rs:70)              ← eval_expr per default, may EFFECT
       └─ execute_pipeline (action.rs:126)
            ├─ eval_expr (requires clause)        ← may EFFECT (effectful builtins)
            ├─ emit RequiresCheck                 ← EFFECT
            ├─ collect_and_apply_cost_modifiers
            │    └─ emit ModifyApplied (×N)       ← EFFECT
            ├─ deduct_costs
            │    ├─ emit RequiresCheck (budget)   ← EFFECT
            │    └─ emit DeductCost (×N)          ← EFFECT
            └─ eval_block (resolve body)
                 └─ eval_stmt (×N)
                      ├─ eval_expr
                      │    └─ call builtins       ← may EFFECT (apply_condition, roll, prompt, etc.)
                      ├─ emit Grant/Revoke        ← EFFECT
                      │    └─ fill defaults       ← eval_expr per default, may EFFECT
                      ├─ eval_emit
                      │    ├─ find_matching_hooks (pure query)
                      │    ├─ execute_hook (×N)
                      │    │    ├─ emit ActionStarted  ← EFFECT
                      │    │    └─ eval_block           ← RECURSIVE
                      │    └─ execute_condition_event_handler (×N)
                      │         ├─ eval_block           ← RECURSIVE
                      │         └─ emit SetConditionState ← EFFECT
                      └─ eval_assign
                           └─ emit MutateField    ← EFFECT
  └─ emit ActionCompleted(invocation: Some(id))   ← EFFECT (always, regardless of outcome)

dispatch_prompt (call/functions.rs:468)
  └─ bind_args / fill_defaults                    ← eval_expr per default, may EFFECT
  └─ eval_expr (suggest body)                     ← may EFFECT
  └─ emit ResolvePrompt                           ← EFFECT
  └─ [if UseDefault: eval_block (default body)]   ← may EFFECT

spawn_entity (eval/dispatch.rs:433)
  └─ fill entity field defaults                   ← eval_expr per default, may EFFECT
  └─ emit SpawnEntity                             ← EFFECT
  └─ fill group field defaults (×N)               ← eval_expr per default, may EFFECT
  └─ emit GrantGroup (×N)                         ← EFFECT

apply_condition (builtins.rs:600)
  └─ emit ConditionApplyGate                      ← EFFECT (gate first, host can veto)
  └─ eval_expr per state field default            ← may EFFECT (only if gate passes)
  └─ eval on_apply blocks                         ← RECURSIVE, may EFFECT
  └─ emit ApplyCondition                          ← EFFECT

with_budget (eval/control.rs:411)
  └─ eval_expr per budget field                   ← may EFFECT
  └─ emit ProvisionBudget                         ← EFFECT
  └─ eval_block (body)                            ← RECURSIVE, may EFFECT
  └─ emit ClearBudget                             ← EFFECT
```

### Effect handler call sites

All 42 `env.handler.handle(effect)` calls, by file:

| File | Count | Effect kinds |
|------|-------|--------------|
| `builtins.rs` | 17 | RollDice, ConditionApplyGate, ApplyCondition, ConditionRemovalGate, RemoveCondition, SetConditionState, RequiresCheck, DeductCost, AddSuspension, RemoveSuspensionSource, RevokeInvocation, TransferConditions, AdvanceTime, RemoveEntity |
| `eval/control.rs` | 8 | GrantGroup, RevokeGroup, ProvisionBudget, ClearBudget |
| `action.rs` | 6 | ActionStarted, ActionCompleted, RequiresCheck, ModifyApplied, DeductCost |
| `eval/assign.rs` | 3 | MutateField, MutateTurnField |
| `eval/dispatch.rs` | 3 | SpawnEntity, GrantGroup (entity construction) |
| `pipeline.rs` | 2 | ModifyApplied |
| `eval/emit.rs` | 1 | SetConditionState |
| `call/functions.rs` | 1 | ResolvePrompt |
| `call/methods.rs` | 1 | RollDice |

### Public entry point coverage

Every public `Interpreter` method that can trigger effects, with v1 step-based coverage:

| Entry point | Can yield? | Effectful paths | v1 step-based? |
|-------------|-----------|-----------------|----------------|
| `execute_action` | Yes | Full action lifecycle, builtins | Yes (Phase 3) |
| `execute_reaction` | Yes | Same as action (different gate kind) | Yes (Phase 3) |
| `execute_hook` | Yes | Same as action (hooks are mini-actions) | Yes (Phase 3) |
| `fire_hooks` | Yes | Hook dispatch loop | Deferred — returns `Vec<(Name, EntityRef, Value)>`, not `Value` |
| `fire_condition_handlers` | Yes | Condition handler dispatch | Deferred — returns `usize`, not `Value` |
| `evaluate_derive` | Yes | Modify pipeline (hooks), RollDice | Yes (Phase 4) |
| `evaluate_mechanic` | Yes | Modify pipeline, RollDice | Yes (Phase 4) |
| `evaluate_function` | Yes | Builtins (roll, prompt, apply_condition, etc.) | Yes (Phase 4) |
| `evaluate_expr` | Yes | Builtins, nested calls | Yes (Phase 4) |
| `evaluate_expr_with_bindings` | Yes | Same as evaluate_expr | Yes (Phase 4) |
| `what_triggers` | No | Pure query | Stays recursive |
| `what_hooks` | No | Pure query | Stays recursive |
| `enum_variants` | No | Pure query | Stays recursive |
| `has_action` / `has_derive` / etc. | No | Pure query | Stays recursive |
| `resolve_resource_bounds` | No | Pure query | Stays recursive |

### Existing building blocks

- **`Step` enum** (`effect.rs:258-268`): Already defined with `Yielded(Box<Effect>)` and `Done(Value)` variants. Intended for exactly this purpose.

- **`StateAdapter`** (`adapter.rs`): Wraps an owned `WritableState`, intercepts mutation effects and applies them locally, forwards non-mutation effects to an inner handler. This is the template for how the `Execution` object manages owned state.

- **`GameState`** (`reference_state.rs`): Reference implementation of `WritableState`. Can serve as the owned state inside an `Execution`.

- **`TrackedInterpreter`** (`reference_state.rs:650-687`): RAII wrapper that syncs ID counters back to `GameState` on drop. The `Execution` type replaces this pattern by owning the counters in `RuntimeCore` (see [ID counter lifecycle](#id-counter-lifecycle) below).

## Design

### Overview

The design has three phases (not to be confused with the host integration layers 1/2/3 defined in [`doc/integration_layers.md`](../../doc/integration_layers.md)):

1. **Emission seam** — a single `env.emit()` method replaces all 42 `handler.handle()` calls. This is a pure refactor with no behavior change.

2. **Frame stack** — an explicit `Vec<Frame>` replaces implicit Rust call frames. Each `Frame` variant captures the state needed to resume after a yielded effect. A driver loop pops/pushes frames and yields effects to the host.

3. **Execution object** — an owning `Execution<S>` struct that holds the frame stack, all `Env` state, an owned `StateAdapter<S>`, and `Arc<RuntimeCore>`. Exposes `poll() -> Result<Step, PollError>` and `respond(Response) -> Result<(), ProtocolError>`. `PollError` distinguishes protocol misuse (`PollError::Protocol`) from DSL evaluation failures (`PollError::Runtime`).

### Emission seam

Add to `Env`:

```rust
impl<'a, 'p> Env<'a, 'p> {
    /// Single interception point for all effect emissions.
    pub(crate) fn emit(&mut self, effect: Effect) -> Response {
        self.handler.handle(effect)
    }
}
```

Mechanically replace all `env.handler.handle(effect)` with `env.emit(effect)`. This costs nothing at runtime (the compiler inlines it) but creates one place where the frame-based driver can later intercept emissions.

### Frame enum

Each frame variant represents a point where execution suspended waiting for an effect response, or a context boundary that needs cleanup on unwind.

```rust
enum Frame {
    // ── Action lifecycle ────────────────────────────────────

    /// Action has emitted ActionStarted, waiting for gate response.
    /// Invocation ID is pre-allocated before ActionStarted is emitted,
    /// so allocation failure cannot break the ActionStarted/ActionCompleted
    /// pairing guarantee. Note: pre-allocation consumes the ID regardless
    /// of outcome — a vetoed action still advances the counter. This is a
    /// deliberate change from the current recursive path (where allocation
    /// happens after the gate) to eliminate the pairing gap.
    /// On Acknowledged: push FillDefaults (if needed), then ActionBody.
    /// On Vetoed: emit ActionCompleted(Vetoed, invocation: None), pop.
    ActionGate {
        name: Name,
        actor: EntityRef,
        call_span: Span,
        has_return_type: bool,
        inv_id: InvocationId,  // pre-allocated before ActionStarted
        // Pipeline data needed after gate passes
        requires: Option<Spanned<ExprKind>>,
        cost: Option<CostClause>,
        resolve: Block,
        // Saved context (restored on pop)
        saved_turn_actor: Option<EntityRef>,
        saved_invocation: Option<InvocationId>,
    },

    /// Gate passed. Invocation ID already allocated in ActionGate.
    /// Sets up scoped context, then drives the pipeline
    /// (defaults → requires → cost → body).
    ActionBody {
        name: Name,
        actor: EntityRef,
        call_span: Span,
        has_return_type: bool,
        inv_id: InvocationId,
        requires: Option<Spanned<ExprKind>>,
        cost: Option<CostClause>,
        resolve: Block,
        phase: ActionBodyPhase,  // Requires | Cost | Resolve
    },

    /// Requires clause evaluated, RequiresCheck emitted, waiting for response.
    /// On Override(Bool(true)) or Acknowledged(passed=true): proceed to cost.
    /// On Override(Bool(false)) or Acknowledged(passed=false): abort with abort_value.
    ActionRequires {
        action_name: Name,
        passed: bool,
        abort_value: Value,
        // Remaining pipeline
        cost: Option<CostClause>,
        resolve: Block,
        actor: EntityRef,
        call_span: Span,
    },

    /// Cost deduction in progress. Yields DeductCost for each token.
    ActionCost {
        action_name: Name,
        tokens: Vec<CostToken>,
        index: usize,
        abort_value: Value,
        resolve: Block,
    },

    /// Action body has completed (or errored). Emits ActionCompleted.
    /// Restores saved context on pop.
    ActionEpilogue {
        name: Name,
        actor: EntityRef,
        inv_id: Option<InvocationId>,
        outcome: ActionOutcome,
        body_result: Result<Value, RuntimeError>,
        saved_turn_actor: Option<EntityRef>,
        saved_invocation: Option<InvocationId>,
    },

    // ── Block / statement execution ─────────────────────────

    /// Iterating statements in a block. Manages scope push/pop.
    Block {
        stmts: Vec<Spanned<StmtKind>>,
        index: usize,
        result: Value,
        /// Cached results from effectful sub-expressions during
        /// replay-with-cache evaluation. See "Replay-with-cache
        /// for multi-yield expressions" above.
        expr_cache: Vec<Value>,
    },

    /// A statement yielded mid-evaluation. Captures the continuation
    /// needed to process the host's response and advance to the next
    /// statement.
    StmtResume {
        kind: StmtResumeKind,
        /// See Block::expr_cache.
        expr_cache: Vec<Value>,
        // StmtResumeKind variants:
        //   GrantWaiting { entity, group_name, fields, span }
        //   RevokeWaiting { entity, group_name, span }
        //   AssignWaiting { path segments, op, span }
        //   BudgetProvisionWaiting { ... }
        //   BudgetClearWaiting { ... }
        //   SpawnWaiting { entity_type, fields, span }
    },

    // ── Default / setup evaluation ──────────────────────────

    /// Evaluating default argument expressions for an action,
    /// function, or prompt call. Drives `fill_defaults` as a
    /// frame so effectful defaults (e.g., `roll(1d6)`) can yield.
    /// On completion, delivers the resolved argument list to the
    /// parent frame.
    FillDefaults {
        params: Vec<ParamInfo>,
        resolved: Vec<(Name, Value)>,
        index: usize,
    },

    // ── Derive / mechanic evaluation ────────────────────────

    /// Derive or mechanic evaluation with modify pipeline.
    /// Evaluates base value, then runs matching modify hooks.
    DeriveEval {
        name: Name,
        base_value: Option<Value>,
        modify_hooks: Vec<HookInfo>,
        hook_index: usize,
    },

    /// Function evaluation. Pushes scope, evaluates body.
    FunctionEval {
        name: Name,
    },

    // ── Emit / hook dispatch ────────────────────────────────

    /// Evaluating an emit statement's argument expressions and field
    /// defaults before constructing the payload. eval_emit (emit.rs)
    /// evaluates positional args, fills param defaults (which may
    /// contain effectful builtins like roll()), then evaluates field
    /// defaults — all before the payload Value exists. This frame
    /// drives that evaluation, then pushes EmitHooks with the
    /// constructed payload.
    EmitEval {
        event_name: Name,
        params: Vec<ParamInfo>,
        resolved_args: Vec<(Name, Value)>,
        arg_index: usize,
        phase: EmitEvalPhase,  // Args | ParamDefaults | FieldDefaults | Ready
    },

    /// Dispatching hooks for an emitted event. Iterates hook list.
    /// Each hook pushes an ActionGate frame (hooks are mini-actions).
    EmitHooks {
        event_name: Name,
        hooks: Vec<HookInfo>,
        index: usize,
        payload: Value,
        saved_emit_depth: u32,
        saved_lifecycle: u32,
    },

    /// Dispatching condition event handlers after hooks complete.
    EmitConditionHandlers {
        handlers: Vec<ConditionHandlerInfo>,
        index: usize,
        payload: Value,
    },

    /// A condition event handler body has completed. Emits
    /// SetConditionState if state fields changed.
    ConditionHandlerEpilogue {
        target: EntityRef,
        condition_name: Name,
        instance_id: u64,
        original_state: BTreeMap<Name, Value>,
    },

    // ── Condition lifecycle ─────────────────────────────────

    /// apply_condition: gate emitted, waiting for response.
    /// On Acknowledged: evaluate state field defaults, then push ConditionOnApply.
    /// On Vetoed: return Option(None), no state defaults evaluated.
    ConditionApplyGate {
        target: EntityRef,
        condition_name: Name,
        params: Vec<(Name, Value)>,
        duration: Value,
        source: Value,
        tags: Vec<Name>,
        token: ConditionToken,
    },

    /// apply_condition: state field defaults evaluated, on_apply lifecycle
    /// blocks executing. After completion, emits ApplyCondition effect.
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

    /// apply_condition: ApplyCondition emitted, waiting for response.
    ConditionActivate {
        token: ConditionToken,
    },

    /// Iterates condition instances for removal. Manages per-instance
    /// gate → on_remove → emit RemoveCondition, accumulating the first
    /// error and continuing through all instances before propagating.
    ConditionRemovalLoop {
        target: EntityRef,
        condition_name: Name,
        instances: Vec<ActiveCondition>,
        index: usize,
        first_error: Option<RuntimeError>,
        removed_count: u32,
    },

    /// remove_condition: per-instance removal gate emitted.
    ConditionRemovalGate {
        target: EntityRef,
        condition_name: Name,
        instance_id: u64,
    },

    /// remove_condition: on_remove lifecycle block executing.
    ConditionOnRemove {
        target: EntityRef,
        condition_name: Name,
        instance_id: u64,
        state_fields: BTreeMap<Name, Value>,
    },

    // ── Effectful builtins ───────────────────────────────────

    /// roll() builtin: RollDice emitted, waiting for result.
    RollDiceWaiting {
        span: Span,
    },

    /// prompt() builtin: ResolvePrompt emitted, waiting for value
    /// or UseDefault (which pushes a Block frame for the default expr).
    PromptWaiting {
        default_block: Option<Block>,
        span: Span,
    },

    // ── Entity construction ─────────────────────────────────

    /// spawn: evaluating entity/group field defaults, then emitting
    /// SpawnEntity and GrantGroup effects.
    SpawnEntity {
        entity_type: Name,
        base_fields: Vec<(Name, Value)>,
        groups: Vec<GroupInit>,
        phase: SpawnPhase,  // Defaults | Spawned | GrantingGroups { index }
    },

    // ── Context / scope frames ──────────────────────────────

    /// Scope boundary. Pops a scope on unwind.
    ScopeGuard,

    /// Budget scope. Restores budget on pop.
    /// Note: BudgetGuard cleanup (ProvisionBudget/ClearBudget to restore
    /// saved budget) is locally-applied and must not suspend. If budget
    /// mutations are promoted to pass-through, cleanup-time budget
    /// mutations must be excluded — otherwise unwind yields would
    /// interleave with error propagation in undefined ways. v1 forbids
    /// pass-through for cleanup-time budget mutations.
    BudgetGuard {
        actor: EntityRef,
        saved_budget: Option<BTreeMap<Name, Value>>,
    },

    /// Multi-entity budget scope (with_budgets, eval/control.rs:436).
    /// Iterates (actor, budget) pairs, emitting ProvisionBudget for each
    /// before executing the body, then emitting ClearBudget/ProvisionBudget
    /// to restore each entity's budget after. Budget field expressions
    /// (eval_expr per field) can yield.
    MultiBudgetGuard {
        entries: Vec<(EntityRef, BTreeMap<Name, Value>)>,
        saved_budgets: Vec<(EntityRef, Option<BTreeMap<Name, Value>>)>,
        provision_index: usize,
        phase: MultiBudgetPhase,  // Provisioning | Body | Restoring { index }
    },

    /// Cost payer override. Restores on pop.
    CostPayerGuard {
        saved_payer: Option<EntityRef>,
    },
}
```

### Shared runtime core

The `Interpreter` today holds shared concerns (program, type_env, const cache, coverage, ID counters) alongside per-call state (Env). The step-based design separates these:

```rust
/// Shared across executions. Immutable program data + mutable caches.
/// Single-threaded: not Send/Sync. One RuntimeCore per host thread.
pub struct RuntimeCore {
    program: Arc<Program>,
    type_env: Arc<TypeEnv>,
    consts: RefCell<FxHashMap<Name, Value>>,
    coverage: Option<RefCell<CoverageData>>,
    next_invocation_id: Cell<u64>,
    next_condition_id: Cell<u64>,
}
```

Multiple `Execution` instances can share a single `Rc<RuntimeCore>` (sequential, not concurrent). The `Interpreter` callback API can also be backed by `RuntimeCore` internally, ensuring const caching and ID allocation are consistent across both paths.

ID counters use `Cell` since `RuntimeCore` is single-threaded. The const cache uses `RefCell` since const evaluation is rare after warmup. If concurrent executions become a goal later, these can be promoted to `AtomicU64` and `RwLock` respectively, and `Rc` to `Arc`.

#### ID counter lifecycle

Today `GameState` owns `next_invocation_id` and `next_condition_id` as persistent fields, and `TrackedInterpreter` seeds the `Interpreter` from these on construction and writes them back on drop. The step-based design moves the counters into `RuntimeCore`, which means they must be explicitly seeded and persisted:

1. **Seeding:** The primary constructor takes explicit counter values:

    ```rust
    impl RuntimeCore {
        /// Primary constructor. Caller provides counter start values.
        pub fn new(
            program: Arc<Program>,
            type_env: Arc<TypeEnv>,
            invocation_start: u64,
            condition_start: u64,
        ) -> Self { ... }

        /// Convenience for GameState, which exposes counter getters.
        pub fn from_game_state(
            program: Arc<Program>,
            type_env: Arc<TypeEnv>,
            state: &GameState,
        ) -> Self {
            Self::new(program, type_env,
                state.next_invocation_id(), state.next_condition_id())
        }
    }
    ```

    Counter getters are **not** added to `WritableState` — they are an implementation detail of `GameState`, not a fundamental state concern. The existing `allocate_condition_id()` on `WritableState` serves a different purpose (pre-allocation for condition tokens). Hosts with custom `WritableState` implementations pass counter values explicitly via `RuntimeCore::new()`.

2. **Persistence:** `Execution<S>` exposes the current counter values via a generic accessor:

    ```rust
    impl<S: WritableState> Execution<S> {
        /// Current ID counter values. Call after completion to persist.
        pub fn counters(&self) -> (u64, u64) {
            (self.core.next_invocation_id.get(),
             self.core.next_condition_id.get())
        }
    }
    ```

    The caller writes the values back to their state however they choose (e.g., `game_state.set_next_invocation_id(inv)` for `GameState`). This happens after `poll()` returns `Done` or `Err`, not in `Drop` — drop-based persistence is fragile if the `Execution` is forgotten or leaked.

3. **Multi-execution sharing:** When multiple sequential `Execution` instances share an `Rc<RuntimeCore>`, the counters are already correct in `RuntimeCore` between executions. The state only needs to be updated when the state is extracted from the last execution (e.g., for serialization or handoff to another system).

### Execution struct

```rust
pub struct Execution<S: WritableState> {
    // ── Shared runtime ──
    core: Rc<RuntimeCore>,

    // ── Frame stack ──
    frames: Vec<Frame>,

    // ── Per-execution state (was Env fields) ──
    scopes: Vec<Scope>,
    turn_actor: Option<EntityRef>,
    cost_payer: Option<EntityRef>,
    current_invocation_id: Option<InvocationId>,
    emit_depth: u32,
    in_lifecycle_block: u32,
    lifecycle_condition_stack: Vec<u64>,
    current_condition_token: Option<ConditionToken>,
    return_value: Option<Value>,

    // ── Owned game state ──
    state: StateAdapter<S>,

    // ── Protocol state ──
    protocol: ProtocolState,
    /// Saved protocol state before a Yield. Restored by respond()
    /// so that Unwinding mode survives across yield/respond cycles.
    pending_before_yield: Option<ProtocolState>,
}

/// Tracks the poll/respond protocol to prevent misuse.
enum ProtocolState {
    /// Ready to call poll(). No pending effect.
    Idle,
    /// poll() yielded an effect. Host must call respond().
    Pending,
    /// Unwinding after an error. Cleanup frames may still yield
    /// effects (e.g., ActionCompleted). The stashed error is
    /// returned after all cleanup frames complete.
    Unwinding(RuntimeError),
    /// Execution has completed (Done or Error). No further calls.
    Completed,
}

/// Errors from protocol misuse (not runtime evaluation errors).
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
pub enum PollError {
    /// Host violated the poll/respond protocol (programming error).
    Protocol(ProtocolError),
    /// DSL evaluation produced a runtime error (after unwind completed).
    Runtime(RuntimeError),
}
```

The generic parameter `S: WritableState` allows hosts to supply their own state implementation. `GameState` is the reference implementation, but any `WritableState` works.

Hosts should handle the two `PollError` variants differently: `Protocol` errors indicate a bug in the host's poll/respond sequencing (typically a panic or assertion), while `Runtime` errors are expected DSL evaluation failures to report to the user.

### Dual API boundary

The two APIs serve different host profiles:

| | `Interpreter` (callback) | `Execution<S>` (step-based) |
|---|---|---|
| State requirement | `&dyn StateProvider` (read-only) | `S: WritableState` (owned) |
| Host control flow | Synchronous callback | Pull-based polling |
| Mutation application | Host applies via `EffectHandler` | `StateAdapter<S>` applies locally |
| Async-friendly | No | Yes |
| Use case | Existing integrations, simple hosts | Web servers, game UIs, FFI |

The `Interpreter` API is not a compatibility shim — it is a first-class interface for hosts that only provide read access to state and handle mutations externally. The step-based API is for hosts that can supply owned mutable state and want pull-based control flow.

Both APIs should eventually share `RuntimeCore` to ensure behavioral consistency (const caching, ID allocation, coverage tracking).

### Driver loop

```rust
enum Advance {
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

impl<S: WritableState> Execution<S> {
    pub fn poll(&mut self) -> Result<Step, PollError> {
        match self.protocol {
            ProtocolState::Pending => return Err(PollError::Protocol(ProtocolError::EffectPending)),
            ProtocolState::Completed => return Err(PollError::Protocol(ProtocolError::ExecutionCompleted)),
            ProtocolState::Idle | ProtocolState::Unwinding(_) => {}
        }

        loop {
            let frame = match self.frames.last_mut() {
                Some(f) => f,
                None => {
                    // If we were unwinding, return the stashed error.
                    if let ProtocolState::Unwinding(e) =
                        std::mem::replace(&mut self.protocol, ProtocolState::Completed)
                    {
                        return Err(PollError::Runtime(e));
                    }
                    self.protocol = ProtocolState::Completed;
                    let result = self.final_result
                        .take()
                        .unwrap_or(Ok(Value::Void));
                    return match result {
                        Ok(v) => Ok(Step::Done(v)),
                        Err(e) => Err(PollError::Runtime(e)),
                    };
                }
            };

            match frame.advance(&mut self.exec_state) {
                Advance::Yield(effect) => {
                    self.pending_before_yield = self.protocol.clone();
                    self.protocol = ProtocolState::Pending;
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
                    // Enter unwinding mode: cleanup frames may still
                    // yield effects (e.g., ActionCompleted on error path).
                    self.protocol = ProtocolState::Unwinding(e);
                    self.begin_unwind();
                    // Continue the loop — unwind frames will either
                    // Yield (suspending for host) or Pop (cleanup done).
                    // When all frames are popped, the empty-stack branch
                    // above returns Err(stashed_error).
                }
            }
        }
    }

    pub fn respond(&mut self, response: Response) -> Result<(), ProtocolError> {
        match self.protocol {
            ProtocolState::Idle | ProtocolState::Unwinding(_) => {
                return Err(ProtocolError::NoPendingEffect)
            }
            ProtocolState::Completed => return Err(ProtocolError::ExecutionCompleted),
            ProtocolState::Pending => {}
        }
        // Restore the pre-yield state: Idle for normal flow,
        // Unwinding(e) if we yielded during error cleanup.
        self.protocol = self.pending_before_yield
            .take()
            .unwrap_or(ProtocolState::Idle);
        // Deliver response to the top frame
        if let Some(frame) = self.frames.last_mut() {
            frame.receive_response(response);
        }
        Ok(())
    }
}
```

### How frames replace recursion

**Example: action execution**

Today (`action.rs`):
```rust
fn execute_action(env, name, actor, args) {
    emit ActionStarted           // ← handler.handle()
    if vetoed {
        emit ActionCompleted(Vetoed, invocation: None)
        return abort_value
    }
    scoped_execute(env, || {     // ← allocates invocation ID here
        fill_defaults(env, args) // ← defaults evaluated after gate
        execute_pipeline(env, requires, cost, resolve)
    })                           // always emits ActionCompleted
}
```

As frames:
```
Initial:  alloc invocation ID, push ActionGate { inv_id, ... }
          → advance(): emit ActionStarted → Yield

          Case 1: host responds Vetoed
          → receive_response(): emit ActionCompleted(Vetoed, invocation: None)
          → Pop(abort_value)

          Case 2: host responds Acknowledged
          → receive_response(): push FillDefaults (if any defaults needed)
          FillDefaults.advance(): eval default exprs (may Yield for effectful defaults)
          → Pop(resolved_args)
          ActionGate.receive_child_result(): push ActionBody { inv_id }
          ActionBody.advance(): eval requires expr (sync), emit RequiresCheck → Yield
          → host responds Acknowledged
          → advance(): deduct costs → push ActionCost
          ActionCost.advance(): emit DeductCost → Yield
          → host responds Acknowledged
          → advance(): all tokens done → Pop
          ActionBody.receive_child_result(): push Block { resolve body }
          Block.advance(): run statements...
          Block.advance(): ... → Pop(result)
          ActionBody.receive_child_result(): push ActionEpilogue { inv_id: Some(id) }
          ActionEpilogue.advance(): emit ActionCompleted → Yield
          → host responds Acknowledged
          → advance(): restore context → Pop(final_value)
```

**Example: eval_block**

Today (`eval/control.rs:269`):
```rust
fn eval_block(env, block) {
    push_scope();
    for stmt in block {
        eval_stmt(env, stmt)?;
        if env.return_value.is_some() { break; }
    }
    pop_scope();
}
```

As a Block frame:
```
Block { stmts, index: 0, result: Void }
  → advance(): push ScopeGuard
  → advance(): eval stmts[0] synchronously → Continue, index = 1
  → advance(): eval stmts[1] — needs effect (e.g., Grant)
       → compute fields (sync), emit GrantGroup → Yield
  → host responds Acknowledged
  → receive_response(): index = 2 → Continue
  → advance(): eval stmts[2] — return statement
       → set return_value → Pop(return_value)
  ScopeGuard popped (scope cleanup)
```

### Expression evaluation

Pure expression evaluation (arithmetic, field access, comparisons, string operations, control flow like if/match) remains synchronous — called as helper functions within a frame's `advance()` method. This is the vast majority of expression evaluation.

The exception is expressions that trigger effectful builtins. The current interpreter yields effects from these builtins:

| Builtin | Effects emitted |
|---------|----------------|
| `apply_condition()` | ConditionApplyGate, on_apply block, ApplyCondition |
| `remove_condition()` | ConditionRemovalGate (×N), on_remove blocks (×N), RemoveCondition (×N) |
| `revoke()` | Same as remove_condition, plus RevokeInvocation |
| `roll()` | RollDice |
| `prompt()` | ResolvePrompt (+ optional default block on UseDefault) |
| `spawn()` | SpawnEntity, GrantGroup (×N) |
| `despawn()` | RemoveEntity |
| `advance_time()` | AdvanceTime |
| `suspend()` / `suspend_with_source()` | AddSuspension |
| `remove_suspension_source()` | RemoveSuspensionSource |
| `transfer_conditions()` | TransferConditions |

When `eval_expr` encounters an effectful builtin, the builtin pushes its own frames onto the stack. The calling frame (typically `Block` or `StmtResume`) records that it's waiting for an expression result and will resume at the current statement when the child frames complete.

For example, `roll()` pushes a `RollDiceWaiting` frame which yields `RollDice` and expects `Override(Value::RollResult(...))` back. `prompt()` pushes a `PromptWaiting` frame which yields `ResolvePrompt`; if the host responds `UseDefault`, the frame pushes a `Block` frame for the default expression rather than directly returning.

#### Replay-with-cache for multi-yield expressions

An expression can contain multiple effectful sub-expressions (e.g., `roll(2d6) + roll(1d8)`). Since expression evaluation is synchronous within a frame's `advance()`, the frame cannot yield in the middle of `eval_expr` and resume at the same point in the expression tree.

The solution is a **replay-with-cache** mechanism. Each frame that evaluates expressions keeps an `expr_cache: Vec<Value>` of pre-computed effectful results:

1. The frame calls `eval_expr_resumable(expr, &mut expr_cache)`, which walks the expression tree left-to-right.
2. For each effectful builtin encountered, it first checks the cache — if a cached value exists at the current index, it consumes the value and continues synchronous evaluation.
3. If no cached value exists, the builtin constructs its child frame and returns `ExprSuspended(child_frame)`. The calling frame returns `Advance::Push(child_frame)`.
4. When the child frame pops, `receive_child_result(value)` appends the value to `expr_cache`.
5. The frame re-enters `eval_expr_resumable` with the same cache. Previously-evaluated builtins hit the cache; evaluation continues until the next uncached builtin or full completion.
6. On full completion, `expr_cache` is cleared for the next statement.

This is lightweight — expressions rarely contain more than one effectful call — and avoids CPS transformation of the evaluator. The `Block` and `StmtResume` frame variants carry `expr_cache: Vec<Value>` for this purpose.

```
Example: roll(2d6) + roll(1d8)

  advance() → eval_expr_resumable(expr, cache=[])
    → encounters roll(2d6), cache empty → ExprSuspended(RollDiceWaiting)
  → Advance::Push(RollDiceWaiting)
  ... host provides RollResult(7) ...
  receive_child_result(7) → cache=[7]
  advance() → eval_expr_resumable(expr, cache=[7])
    → encounters roll(2d6), cache[0]=7 → continue with 7
    → encounters roll(1d8), cache empty at index 1 → ExprSuspended(RollDiceWaiting)
  → Advance::Push(RollDiceWaiting)
  ... host provides RollResult(3) ...
  receive_child_result(3) → cache=[7, 3]
  advance() → eval_expr_resumable(expr, cache=[7, 3])
    → roll(2d6) → 7, roll(1d8) → 3, result = 10
  → expression complete, clear cache
```

#### Effectful setup and default evaluation

Several code paths evaluate expressions that can yield *before* the main body executes:

- **Default arguments** (`call/args.rs`): `fill_defaults()` calls `eval_expr()` for each parameter with a default expression. A default like `damage = roll(2d6)` will yield `RollDice`. The `FillDefaults` frame iterates parameters, yielding when a default triggers an effectful builtin. Scope management follows the existing pattern: a temporary scope is pushed so later defaults can reference earlier ones. **Note:** For actions, defaults are evaluated *after* `ActionStarted` is acknowledged and the veto check passes — not before. This is locked by the `action_default_not_evaluated_on_veto` regression test (`action_default_ordering.rs:78`). The `ActionGate` frame pushes `FillDefaults` in its post-response phase (on Acknowledged), before pushing `ActionBody`.

- **Prompt suggest expressions** (`call/functions.rs`): The `suggest` body is evaluated with `eval_expr()` before `ResolvePrompt` is emitted. If the suggest expression triggers builtins (e.g., computing a suggestion via `roll()`), it yields via the standard expression frame mechanism.

- **Entity/group field defaults** (`eval/dispatch.rs`, `eval/control.rs`): During `spawn` and `grant`, missing fields are filled from defaults via `eval_expr()`. The `SpawnEntity` frame handles this in its `Defaults` phase before emitting `SpawnEntity` / `GrantGroup` effects.

- **Condition state field defaults** (`builtins.rs`): During `apply_condition`, the `ConditionApplyGate` is emitted first. State field defaults are evaluated with `eval_expr()` only after the gate passes (host responds `Acknowledged`). If the host vetoes, no defaults are evaluated. The `ConditionApplyGate` frame evaluates defaults in its post-response phase, then pushes `ConditionOnApply`.

- **Budget field expressions** (`eval/control.rs`): `with_budget` evaluates budget field expressions via `eval_expr()` before emitting `ProvisionBudget`. Handled by a setup phase in the budget frame.

All of these paths use the same mechanism: when `eval_expr()` encounters an effectful builtin, the builtin pushes its own child frames. The parent frame (e.g., `FillDefaults`, `SpawnEntity`) waits for the child result and then continues to the next item.

### Owned program data

`Interpreter<'p>` borrows `&'p Program` and `&'p TypeEnv`. The `Execution` object must own its program data so it can outlive any particular scope. This is handled by `Rc<RuntimeCore>`, which wraps `Arc<Program>` and `Arc<TypeEnv>`. The caller wraps their program/type_env in Arc when creating a `RuntimeCore`. Multiple sequential executions can share the same core via `Rc`.

The `Interpreter` type continues to exist for the callback-based API (no Arc needed there). `Execution` is a separate entry point.

### State ownership and effect suspension contract

`Execution<S>` owns a `StateAdapter<S>` where `S: WritableState`. Not all effects suspend execution — the adapter handles some effects locally, and only effects that require host input yield from `poll()`.

Effects fall into four categories:

| Category | Behavior | Examples |
|----------|----------|----------|
| **Host-decided** | Always yielded. Execution suspends. Host must `respond()`. | `ActionStarted`, `ConditionApplyGate`, `ConditionRemovalGate`, `RequiresCheck`, `RollDice`, `ResolvePrompt`, `DeductCost` |
| **Informational** | Always yielded. Host must `respond()` with `Acknowledged`. These carry telemetry or lifecycle signals the host needs to observe but cannot alter. | `ActionCompleted`, `ModifyApplied` |
| **Locally-applied** | Applied by `StateAdapter` immediately. Execution continues without suspending. Host does not see these. | `MutateField`, `MutateTurnField`, `GrantGroup`, `RevokeGroup`, `ApplyCondition`, `RemoveCondition`, `SetConditionState`, `ProvisionBudget`, `ClearBudget`, `SpawnEntity`, `RemoveEntity`, `AddSuspension`, `RemoveSuspensionSource`, `RevokeInvocation`, `AdvanceTime`, `TransferConditions` |
| **Pass-through** | Configured per effect kind via `StateAdapter::pass_through()`. Promoted from locally-applied to host-decided: yielded, host responds, adapter syncs local state based on response (Acknowledged → apply, Vetoed → skip). | Any mutation kind the host opts into |

This matches the existing `StateAdapter` contract, with two corrections:
- `DeductCost` is a **decision effect** — it is always passed through to the host, and the adapter applies the mutation based on the host's response (`adapter.rs:34`). Classifying it as locally-applied would remove host control over cost waivers and overrides.
- `ModifyApplied` is **informational** — it is always forwarded and requires `Acknowledged` (`pipeline.rs:722`). Classifying it as locally-applied would hide modifier telemetry from the host.

The remaining contract is unchanged:
- When a mutation effect kind is **not** in the `pass_through` set, the adapter applies the mutation locally and returns `Response::Acknowledged` without forwarding to any inner handler.
- When a mutation effect kind **is** in the `pass_through` set, the adapter forwards the effect, and the host's response controls whether the mutation is applied locally (Acknowledged/Override → apply, Vetoed → skip).
- Non-mutation effects (gates, value effects, informational effects) are always forwarded.

In the step-based API, "forwarded" becomes "yielded from `poll()`". The host configures which mutations it wants to see and potentially veto by calling `pass_through()` on the adapter at construction time. By default, all mutations are local and non-suspending.

**Reads** (`StateProvider` queries) are always synchronous direct method calls on the adapter — no yielding, no effects.

### Error handling and unwinding

When a `RuntimeError` occurs:

1. The error propagates as `Advance::Error` from the frame that detected it.
2. The driver loop stashes the error and enters **unwinding mode** rather than immediately returning `Err`.
3. In unwinding mode, the driver pops frames in reverse order. Each frame's `unwind()` method runs:
   - Guard frames (`ScopeGuard`, `BudgetGuard`, `MultiBudgetGuard`, `CostPayerGuard`) perform cleanup synchronously (pop scope, restore budget, restore cost payer). `BudgetGuard`/`MultiBudgetGuard` emit `ProvisionBudget`/`ClearBudget` through the adapter to restore the budget — these are locally-applied and do not suspend. **v1 constraint:** budget mutation effects must not be promoted to pass-through during cleanup (unwind). If the host has configured pass-through for budget mutations, the adapter must suppress forwarding during unwind-triggered budget restoration to prevent cleanup yields from interleaving with error propagation.

     **Behavior change from recursive API:** In the recursive interpreter (`eval/control.rs:552-578`), cleanup budget mutations are emitted through the handler and can be vetoed, which produces an error during error cleanup — a problematic pattern since the cleanup error masks or competes with the original error. The step-based API intentionally makes cleanup budget mutations locally-applied during unwind, ensuring cleanup cannot fail. Hosts that need visibility into budget restoration during error paths can observe the `ProvisionBudget`/`ClearBudget` effects through the event log (if enabled) but cannot veto them. This eliminates the "error during error cleanup" failure mode.
   - `ActionEpilogue` frames emit `ActionCompleted(Failed)` — this is an informational effect that **yields to the host**. The driver returns `Ok(Step::Yielded(ActionCompleted(...)))` and the host must `respond(Acknowledged)`. The next `poll()` continues the unwind.
4. After all frames are unwound, the next `poll()` returns `Err(PollError::Runtime(stashed_error))` and transitions to `ProtocolState::Completed`.

This design preserves the current behavior where cleanup effects (ActionCompleted, budget restoration) are visible to the host even on error paths. Without this, an async host would never observe the ActionCompleted that pairs with an ActionStarted when the action body errors.

The `ProtocolState::Unwinding(RuntimeError)` variant (defined above in the `Execution` struct) carries the stashed error through the unwind phase.

#### Deferred error mode

Not all errors trigger immediate unwinding. The current interpreter has paths where errors are accumulated and cleanup continues before propagation. The frame model must preserve this.

**Condition removal and revoke:** Today, `remove_condition_instances` (builtins.rs:796-880) iterates all matching condition instances. For each instance:
1. Emit `ConditionRemovalGate` — skip if vetoed
2. Execute `on_remove` lifecycle block — if it errors, capture the error but continue
3. Emit `RemoveCondition` — **always**, even if `on_remove` errored
4. Clean up suspension records

The first error is captured; all remaining instances still complete their full removal sequence; the error is propagated only after the loop finishes.

The `ConditionRemovalLoop` frame handles this by carrying `first_error: Option<RuntimeError>`. When a child `ConditionOnRemove` frame completes with an error, the loop frame captures it but advances `index` and continues to the next instance. When all instances are processed, if `first_error` is `Some`, the loop frame returns `Advance::Error` — but only then.

The same pattern applies to `revoke()`, which iterates conditions tagged with an invocation ID and removes them using the same per-instance loop.

**Key invariant:** `ConditionRemovalLoop` and its child frames (`ConditionRemovalGate`, `ConditionOnRemove`) must never trigger the driver's global `unwind()`. Errors within these frames are routed to the loop's `first_error` field, not to `Advance::Error`, until the loop completes.

### Compatibility shim

The step-based API can be driven synchronously:

```rust
impl<S: WritableState> Execution<S> {
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
                    panic!("protocol error in run_with_handler: {:?}", e)
                }
            }
        }
    }
}
```

This is useful for hosts that want owned state management (via `StateAdapter<S>`) but don't need async control flow. It is **not** a replacement for the `Interpreter` callback API, which serves a different purpose: hosts that provide `&dyn StateProvider` and handle mutations externally.

## Implementation Phases

### Phase 1: Emission seam

Replace all 42 `env.handler.handle(effect)` calls with `env.emit(effect)`. Pure mechanical refactor. The `emit()` method just delegates to `handler.handle()`. No behavior change.

This is a prerequisite for everything else and delivers immediate value: a single place to add tracing, validation, or coverage instrumentation.

**Scope:** ~42 line changes across 9 files + 5-line method addition.

**Parity bar:** All existing tests pass. No behavior change.

### Phase 2: Types and driver loop

Define `Frame`, `Advance`, `RuntimeCore`, `Execution<S>`, `ProtocolState`, `ProtocolError`, and the `poll`/`respond`/`run_with_handler` API. No frame `advance()` implementations yet — just the structural types.

**Scope:** New `execution.rs` and `runtime_core.rs` modules. Compiles but is not yet callable.

**Parity bar:** Type-checks. No runtime behavior yet.

### Phase 3: Action lifecycle frames

Convert `execute_action` / `execute_reaction` / `execute_hook` / `scoped_execute` / `execute_pipeline` to frame-based execution. This is the outermost and most structurally regular code path.

Includes `FillDefaults` for action/function default argument evaluation — this is part of the action call path and must yield correctly when defaults contain effectful builtins like `roll()`.

Test by constructing an `Execution` for simple actions and asserting the yielded effect sequence matches the recursive path (using `ScriptedHandler`-style response scripts).

**Entry points covered:** `execute_action`, `execute_reaction`, `execute_hook`.

**Parity bar:** Differential test suite (see below) passes for all action-lifecycle scenarios. Effect sequences match the recursive path exactly.

### Phase 4: Block, statement, and expression frames

Convert `eval_block` / `eval_stmt` to `Block` and `StmtResume` frames. Synchronous statements execute inline; effectful statements (Grant, Revoke, Assign with mutation, Emit) push continuation frames.

Add `DeriveEval`, `FunctionEval`, `RollDiceWaiting`, `PromptWaiting`, and `SpawnEntity` frames for the non-action entry points. Includes prompt suggest/default body evaluation paths and entity/group field default evaluation during spawn and grant.

**Resume sites covered in this phase:**
- `eval/control.rs`: Grant/Revoke with field defaults, `with_budget`/`with_budgets` field expression evaluation, multi-entity budget provision/restore loops, budget rollback
- `eval/dispatch.rs`: Entity field defaults, group field defaults during spawn
- `call/functions.rs`: Prompt suggest expression, prompt default block on `UseDefault`
- `builtins.rs`: Condition state field defaults during `apply_condition`

**Entry points covered:** `evaluate_derive`, `evaluate_mechanic`, `evaluate_function`, `evaluate_expr`, `evaluate_expr_with_bindings`.

**Phase 5 dependency:** `evaluate_derive` and `evaluate_mechanic` can trigger `emit_modify_applied_events()` (`pipeline.rs:1128`), which dispatches hooks via `emit_depth`-tracked recursion. Hook dispatch requires the Phase 5 emit dispatch frames. Phase 4 parity testing covers these entry points **only for scenarios where no `modify_applied` hooks are registered** (the fast-path at `pipeline.rs:1134` short-circuits). Full parity including hook-triggering derives is validated after Phase 5.

**Parity bar:** All entry points produce identical effect sequences for scenarios without `modify_applied` hook dispatch. Prompt `UseDefault` correctly pushes a block frame for the default expression. Default arguments with effectful builtins yield correctly. Derive/mechanic entry points validated with and without `modify_applied` hooks separately (pre- and post-Phase 5).

### Phase 5: Emit dispatch and condition lifecycle frames

Convert `eval_emit` (hook dispatch + condition handler dispatch) and `apply_condition` / `remove_condition` / `revoke` to frames. These are the most state-heavy conversions (emit_depth tracking, lifecycle block counters, condition token pre-allocation, per-instance removal loops with deferred error propagation).

**Note:** The internal frame conversion for emit dispatch and condition lifecycle is needed by Phase 3-4 entry points (actions that contain `emit` statements or call `apply_condition`/`remove_condition`). The *public* `fire_hooks` and `fire_condition_handlers` entry points are deferred because their return types (`Vec<(Name, EntityRef, Value)>` and `usize`) do not fit the `Step::Done(Value)` completion type.

**Parity bar:** Condition removal with `on_remove` errors still completes all instances. Nested emit dispatch preserves ordering. All differential test scenarios pass.

### Phase 6: Public API and migration

Add `Execution::start_action`, `start_reaction`, `start_derive`, `start_mechanic`, `start_function`, `start_expr`, etc. Update the CLI runner and test harness to support the new API (or keep both paths).

**Scope:** `lib.rs` additions, `ttrpg_cli` integration.

**Parity bar:** Full `.ttrpg-cli` test suite passes through both the recursive and step-based paths.

### Differential test matrix

Differential tests run each scenario through both the recursive and step-based paths and assert identical effect sequences. Priority scenarios:

| Category | Scenario | Key invariant |
|----------|----------|---------------|
| **Action lifecycle** | ActionStarted → Vetoed | ActionCompleted emitted with `invocation: None`. Pre-allocation consumes the ID (counter advances) but `invocation` field is `None`. |
| **Action lifecycle** | ActionStarted → invalid Response type | ActionCompleted(Failed) emitted, RuntimeError returned |
| **Action lifecycle** | Nested action (hook triggers action) | Inner action gets its own invocation ID, outer resumes after |
| **Defaults** | Action with effectful default (`roll()`) | ActionStarted yielded first, then RollDice for default, default value used in body |
| **Defaults** | Prompt with effectful suggest expr | Effectful suggest evaluated before ResolvePrompt yielded |
| **Defaults** | Entity spawn with field defaults | Defaults evaluated before SpawnEntity, GrantGroup effects |
| **Requires** | RequiresCheck → Override(false) | Action aborts with abort_value, ActionCompleted(Succeeded) — abort returns `Ok(abort_value)` so `is_ok()` → Succeeded. See note below. |
| **Cost** | Budget insufficient (RequiresCheck → Acknowledged with passed=false) | Action aborts with abort_value, budget not mutated, no DeductCost emitted |
| **Cost** | Cost deduction vetoed (DeductCost → Vetoed) | Cost waived, action body still executes, ActionCompleted(Succeeded) |
| **Condition** | apply_condition → gate Vetoed | No condition applied, no on_apply executed |
| **Condition** | apply_condition with effectful state field default | ConditionApplyGate yielded first, state default yields after gate passes |
| **Condition** | remove_condition with on_remove error | All instances still removed, error propagated after loop |
| **Condition** | revoke(invocation) with multiple conditions | All tagged conditions removed, first error deferred |
| **Prompt** | ResolvePrompt → UseDefault | Default block evaluates, result used as prompt value |
| **Prompt** | ResolvePrompt → Override(value) | Value used directly |
| **Emit** | Nested emit (hook body emits event) | emit_depth incremented, inner hooks fire, outer resumes |
| **Emit** | Condition handler modifies state fields | SetConditionState emitted with delta |
| **Budget** | with_budget scope + error during body | Budget restored to saved state |
| **Budget** | with_budget with effectful field expr | Budget field expression yields before ProvisionBudget |
| **Budget** | with_budgets (multi-entity) | ProvisionBudget emitted per entity, restore emitted per entity on exit |
| **Emit** | Emit with effectful argument default | Argument default (e.g., `roll()`) yields before payload is constructed |
| **Scope** | Early return from nested block | All scope guards popped, return_value propagated |
| **Spawn** | spawn in action body | SpawnEntity + GrantGroup(×N) emitted, entity ref returned |
| **Roll** | roll() in expression | RollDice yielded, Override(RollResult) consumed |
| **Error path** | RuntimeError during action body | ActionCompleted(Failed) yielded during unwind, budget restored |
| **Error path** | alloc_invocation_id overflow | With pre-allocation: RuntimeError before ActionStarted, no pairing needed (see note below) |

**Note on abort outcomes:** The current interpreter returns `Ok(abort_value)` when `RequiresCheck` or cost checks fail (`action.rs:170, 184`), so `scoped_execute` derives the outcome from `result.is_ok()` → `ActionOutcome::Succeeded`. This means graceful aborts report Succeeded, not Failed, even though the action did not execute its body. If a future change wants to report these as Failed, it should be tracked as a separate behavior-change issue with its own differential test, not introduced silently as part of the step-based migration.

**Note on `fire_hooks` / `fire_condition_handlers` return types:** These entry points return `Vec<(Name, EntityRef, Value)>` and `usize` respectively, which do not fit `Step::Done(Value)`. This spec defers step-based versions of these entry points to a future phase. The v1 scope (Phases 3-6) covers `execute_action`, `execute_reaction`, `execute_hook`, `evaluate_derive`, `evaluate_mechanic`, `evaluate_function`, and `evaluate_expr` — all of which return `Value`. A future extension can either wrap these results in `Value` encodings or parameterize `Execution` over its result type.

**Note on invocation ID allocation:** The recursive path now pre-allocates the invocation ID before emitting `ActionStarted` (`action.rs:228`). If allocation fails (u64 overflow), no `ActionStarted` is emitted and no pairing is needed. This closes the previous gap where `scoped_execute` called `alloc_invocation_id()?` after `ActionStarted`, which could leave an unpaired `ActionStarted` on allocation failure. The `ActionGate` frame follows the same pattern: it receives a pre-allocated `inv_id: InvocationId` at construction time. A vetoed action consumes the invocation ID (the counter advances) but `ActionCompleted` reports `invocation: None`. Invocation IDs are not required to be dense.

## Alternatives Considered

### Thread + channel

One OS thread per `Execution`. The evaluator runs unchanged on the worker thread, sending effects through a channel and blocking on responses. The host drives from the main thread.

**Rejected because:**
- `Interpreter` carries `Cell<u64>`, `Rc<RefCell<_>>`, and `RefCell<_>` — none are `Send`. The entire ownership model would need redesigning.
- Fighting the goal of keeping synchronous state reads (reads would need to cross the thread boundary).
- Worse for foreign embedding — the host must manage thread lifetime, and the execution state is opaque on the worker's stack.
- Does not produce an inspectable execution state.

### Stackful coroutines (corosensei, genawaiter)

Library-provided stackful coroutines. The evaluator runs on a coroutine stack, yields at each `emit()` call.

**Rejected because:**
- The suspended state lives on an opaque platform-specific stack, not in inspectable Rust data structures. This blocks debugging, cancellation, and foreign embedding.
- Adds a dependency with platform-specific unsafe code for stack switching.
- Gains yielding but not a clean continuation model.

Viable as a learning/prototyping step, but does not satisfy the long-term goals.

### Async transform

Make all eval functions `async`, use a custom single-threaded executor that extracts effects at yield points.

**Rejected because:**
- `async` is viral — every function in the eval chain must become async, including pure expression evaluation that never yields.
- `Env<'a, 'p>` with trait object references creates severe lifetime challenges inside `Future` bounds.
- Recursive async functions require `Box::pin` at every recursion point.
- A custom executor that extracts effects from futures is itself complex to build and debug.
- The resulting code would be harder to read than explicit frames, with no additional capability.

## Risks

1. **Frame explosion.** The number of `Frame` variants may grow large as every effectful code path needs representation. Mitigation: keep synchronous code paths as helper functions, only frame-ify paths that cross effect boundaries. Consider extracting recurring patterns (ordered list evaluation, iterate-with-cleanup) into reusable generic frames if the variant count becomes unwieldy.

2. **AST cloning cost.** Frames own AST node copies (blocks, expressions). For typical TTRPG rulesets (small blocks, few statements), this is negligible. If it becomes measurable, `Arc`-wrap frequently-cloned AST nodes.

3. **Semantic divergence.** Two code paths (recursive and frame-based) executing the same logic risks subtle behavioral differences. Mitigation: run the full `.ttrpg-cli` test suite through both paths and diff the effect sequences. The differential test matrix (above) targets the highest-risk scenarios.

4. **Incremental adoption friction.** During the transition, new effectful features must be added to both the recursive evaluator and the frame-based evaluator. Mitigation: complete the migration before adding new effectful features, or add them only to the frame-based path once it's the primary path.

5. **Expression evaluation boundary.** The division between "synchronous expression evaluation" and "effectful builtins that need frames" must be maintained carefully. Any new builtin that emits effects must use the frame mechanism. Expressions with multiple effectful sub-expressions are handled by replay-with-cache (see [above](#replay-with-cache-for-multi-yield-expressions)), which is correct but re-walks the expression tree once per yield point — acceptable given that multi-yield expressions are rare in practice.