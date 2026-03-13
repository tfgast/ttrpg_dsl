# Design: Resumable Step-Based Execution API

**Status:** Proposed (tdsl-qi09)

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

2. **Explicit durable state.** Move execution state that is currently implicit in Rust call frames (action lifecycle phase, block instruction pointer, emit dispatch index, condition lifecycle phase) into explicit data structures that can be inspected, serialized, and resumed.

3. **Pull-based execution API.** Expose an `Execution` object where the host polls for the next effect and provides a response, rather than implementing a callback trait. This enables async hosts, non-Rust embeddings, and step-debugging.

4. **Synchronous reads preserved.** The interpreter reads game state synchronously during evaluation (field access, condition queries, entity lookups). This must remain a direct function call, not a yielded effect. Only effect emissions (mutations, dice, prompts, gates) suspend.

5. **Callback API as compatibility shim.** The existing `EffectHandler`-based public API (`execute_action`, `evaluate_derive`, etc.) continues to work, implemented as a thin loop over the new step-based API.

### Non-goals

- Thread-based suspension (threads are not preferred; the target is an internal resumable runner)
- Async/await transformation of the evaluator (viral, lifetime-hostile)
- Bytecode compilation (the tree-walking evaluator structure is fine; only the control flow needs restructuring)

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
   - Scoped context save/restore (`scoped_execute` saves `turn_actor`/`invocation_id`, `scoped_budget` saves budget state)

The second category is the problem. When the evaluator yields at an effect boundary, these Rust call frames are destroyed. To resume, we need that state reconstructed — which means making it explicit.

### Recursive call structure

The principal recursive chains that cross effect boundaries:

```
execute_action (action.rs:199)
  └─ emit ActionStarted                          ← EFFECT
  └─ scoped_execute (action.rs:79)
       └─ execute_pipeline (action.rs:120)
            ├─ eval_expr (requires clause)
            ├─ emit RequiresCheck                 ← EFFECT
            ├─ collect_and_apply_cost_modifiers
            │    └─ emit ModifyApplied (×N)       ← EFFECT
            ├─ deduct_costs
            │    ├─ emit RequiresCheck (budget)   ← EFFECT
            │    └─ emit DeductCost (×N)          ← EFFECT
            └─ eval_block (resolve body)
                 └─ eval_stmt (×N)
                      ├─ eval_expr
                      │    └─ call builtins       ← may EFFECT (apply_condition, etc.)
                      ├─ emit Grant/Revoke        ← EFFECT
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
  └─ emit ActionCompleted                         ← EFFECT (always, regardless of outcome)
```

### Effect handler call sites

All 42 `env.handler.handle(effect)` calls, by file:

| File | Count | Effect kinds |
|------|-------|-------------|
| `builtins.rs` | 17 | ConditionApplyGate, ApplyCondition, ConditionRemovalGate, RemoveCondition, SetConditionState, RequiresCheck, DeductCost, RemoveSuspensionSource, RevokeInvocation, TransferConditions |
| `eval/control.rs` | 8 | GrantGroup, RevokeGroup, ProvisionBudget, ClearBudget |
| `action.rs` | 6 | ActionStarted, ActionCompleted, RequiresCheck, ModifyApplied, DeductCost |
| `eval/assign.rs` | 3 | MutateField, MutateTurnField |
| `eval/dispatch.rs` | 3 | SpawnEntity, GrantGroup (entity construction) |
| `pipeline.rs` | 2 | SetConditionState |
| `eval/emit.rs` | 1 | (delegated — hooks dispatch through action.rs) |
| `call/functions.rs` | 1 | AdvanceTime |
| `call/methods.rs` | 1 | RemoveEntity |

### Existing building blocks

- **`Step` enum** (`effect.rs:258-268`): Already defined with `Yielded(Box<Effect>)` and `Done(Value)` variants. Intended for exactly this purpose.

- **`StateAdapter`** (`adapter.rs`): Wraps an owned `WritableState`, intercepts mutation effects and applies them locally, forwards non-mutation effects to an inner handler. This is the template for how the `Execution` object manages owned state.

- **`GameState`** (`reference_state.rs`): Reference implementation of `WritableState`. Can serve as the owned state inside an `Execution`.

- **`TrackedInterpreter`** (`reference_state.rs:650-687`): RAII wrapper that syncs ID counters back to `GameState` on drop. The `Execution` type replaces this pattern by owning the counters directly.

## Design

### Overview

The design has three layers:

1. **Emission seam** — a single `env.emit()` method replaces all 42 `handler.handle()` calls. This is a pure refactor with no behavior change.

2. **Frame stack** — an explicit `Vec<Frame>` replaces implicit Rust call frames. Each `Frame` variant captures the state needed to resume after a yielded effect. A driver loop pops/pushes frames and yields effects to the host.

3. **Execution object** — an owning `Execution` struct that holds the frame stack, all `Env` state, an owned `StateAdapter<GameState>`, and `Arc<Program>` / `Arc<TypeEnv>`. Exposes `poll() -> Step` and `respond(Response)`.

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
    /// On Acknowledged: push pipeline frames (requires → cost → body).
    /// On Vetoed: transition to ActionEpilogue with Vetoed outcome.
    ActionGate {
        name: Name,
        actor: EntityRef,
        call_span: Span,
        has_return_type: bool,
        // Pipeline data needed after gate passes
        requires: Option<Spanned<ExprKind>>,
        cost: Option<CostClause>,
        resolve: Block,
        // Saved context (restored on pop)
        saved_turn_actor: Option<EntityRef>,
        saved_invocation: Option<InvocationId>,
        inv_id: InvocationId,
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
        inv_id: InvocationId,
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
    },

    /// A statement yielded mid-evaluation. Captures the continuation
    /// needed to process the host's response and advance to the next
    /// statement.
    StmtResume {
        kind: StmtResumeKind,
        // StmtResumeKind variants:
        //   GrantWaiting { entity, group_name, fields, span }
        //   RevokeWaiting { entity, group_name, span }
        //   AssignWaiting { path segments, op, span }
        //   BudgetProvisionWaiting { ... }
        //   BudgetClearWaiting { ... }
        //   SpawnWaiting { entity_type, fields, span }
    },

    // ── Emit / hook dispatch ────────────────────────────────

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
    ConditionApplyGate {
        target: EntityRef,
        condition_name: Name,
        params: Vec<(Name, Value)>,
        duration: Value,
        source: Value,
        tags: Vec<Name>,
        token: ConditionToken,
    },

    /// apply_condition: on_apply lifecycle blocks executing.
    /// After completion, emits ApplyCondition effect.
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

    /// remove_condition: per-instance removal gate emitted.
    ConditionRemovalGate {
        target: EntityRef,
        condition_name: Name,
        instance_id: u64,
        remaining_instances: Vec<ActiveCondition>,
    },

    /// remove_condition: on_remove lifecycle block executing.
    ConditionOnRemove {
        target: EntityRef,
        condition_name: Name,
        instance_id: u64,
        remaining_instances: Vec<ActiveCondition>,
        state_fields: BTreeMap<Name, Value>,
    },

    // ── Context / scope frames ──────────────────────────────

    /// Scope boundary. Pops a scope on unwind.
    ScopeGuard,

    /// Budget scope. Restores budget on pop.
    BudgetGuard {
        actor: EntityRef,
        saved_budget: Option<BTreeMap<Name, Value>>,
    },

    /// Cost payer override. Restores on pop.
    CostPayerGuard {
        saved_payer: Option<EntityRef>,
    },
}
```

### Execution struct

```rust
pub struct Execution {
    // ── Owned program data ──
    program: Arc<Program>,
    type_env: Arc<TypeEnv>,

    // ── Frame stack ──
    frames: Vec<Frame>,

    // ── Execution state (was Env fields) ──
    scopes: Vec<Scope>,
    turn_actor: Option<EntityRef>,
    cost_payer: Option<EntityRef>,
    current_invocation_id: Option<InvocationId>,
    emit_depth: u32,
    in_lifecycle_block: u32,
    lifecycle_condition_stack: Vec<u64>,
    current_condition_token: Option<ConditionToken>,
    return_value: Option<Value>,

    // ── ID counters (was Cell<u64> on Interpreter) ──
    next_invocation_id: u64,
    next_condition_id: u64,

    // ── Owned game state ──
    state: StateAdapter<GameState>,

    // ── Result / pending ──
    final_result: Option<Result<Value, RuntimeError>>,
    pending_effect: bool,
}
```

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

impl Execution {
    pub fn poll(&mut self) -> Step {
        loop {
            let frame = match self.frames.last_mut() {
                Some(f) => f,
                None => {
                    let result = self.final_result
                        .take()
                        .unwrap_or(Ok(Value::Void));
                    return match result {
                        Ok(v) => Step::Done(v),
                        Err(e) => Step::Error(e),
                    };
                }
            };

            match frame.advance(&mut self.exec_state) {
                Advance::Yield(effect) => {
                    self.pending_effect = true;
                    return Step::Yielded(Box::new(effect));
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
                    // Unwind: pop all frames, run cleanup (scope pops, budget restores)
                    self.unwind(e.clone());
                    return Step::Error(e);
                }
            }
        }
    }

    pub fn respond(&mut self, response: Response) {
        assert!(self.pending_effect, "respond() called without pending effect");
        self.pending_effect = false;
        // Deliver response to the top frame
        if let Some(frame) = self.frames.last_mut() {
            frame.receive_response(response);
        }
    }
}
```

### How frames replace recursion

**Example: action execution**

Today (`action.rs`):
```rust
fn execute_action(env, name, actor, args) {
    emit ActionStarted           // ← handler.handle()
    scoped_execute(env, || {
        execute_pipeline(env, requires, cost, resolve)
    })                           // always emits ActionCompleted
}
```

As frames:
```
Initial:  push ActionGate { ... }
          → advance(): emit ActionStarted → Yield
          → host responds Acknowledged
          → receive_response(): transition to pipeline phase
          → advance(): eval requires expr (sync), emit RequiresCheck → Yield
          → host responds Acknowledged
          → advance(): deduct costs → push ActionCost
          ActionCost.advance(): emit DeductCost → Yield
          → host responds Acknowledged
          → advance(): all tokens done → Pop
          ActionGate.receive_child_result(): push Block { resolve body }
          Block.advance(): run statements...
          Block.advance(): ... → Pop(result)
          ActionGate.receive_child_result(): push ActionEpilogue
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

The exception is expressions that trigger effectful builtins. When `eval_expr` encounters `apply_condition(...)`, the builtin needs to emit effects. Two approaches:

**Option A — Yield-from-expr:** `eval_expr` returns `Result<Value, EvalYield>` where `EvalYield` carries the effect and a continuation token. The frame catches this and yields. On resume, the frame re-invokes the continuation.

**Option B — Frame-from-expr:** Effectful builtins push their own frames (ConditionApplyGate, etc.) and return a sentinel. The parent frame knows to wait for a child result.

Option B is cleaner because it reuses the frame mechanism uniformly. The calling frame's `advance()` calls `eval_expr()`, which detects an effectful builtin, pushes frames, and returns `Advance::Push(...)` through the frame's advance method. The frame notes that it's waiting for an expression result and will resume at the current statement when the child frames complete.

### Owned program data

`Interpreter<'p>` borrows `&'p Program` and `&'p TypeEnv`. The `Execution` object must own its program data so it can outlive any particular scope. Two options:

1. **`Arc<Program>` + `Arc<TypeEnv>`** — The caller wraps their program/type_env in Arc before creating executions. Multiple executions can share the same program data. This is the recommended approach.

2. **Owned copies** — Clone the program and type_env into each execution. Wasteful for large programs.

The `Interpreter` type continues to exist for the callback-based API (no Arc needed there). `Execution` is a separate entry point.

### State ownership

`Execution` owns a `StateAdapter<GameState>`:

- **Reads** (`StateProvider` queries) are direct method calls on the adapter — synchronous, no yielding.
- **Mutation effects** are intercepted by the adapter and applied locally. They are also yielded to the host as effects, so the host can observe and optionally apply them to its own authoritative state.
- **Gate effects** (ActionStarted, ConditionApplyGate, etc.) are always yielded — the host decides whether to veto.
- **Value effects** (RollDice, ResolvePrompt) are always yielded — only the host can provide these.

This matches the existing `StateAdapter` pattern exactly. The adapter's `pass_through` set controls which mutations the host sees.

### Error handling and unwinding

When a `RuntimeError` occurs:

1. The error propagates as `Advance::Error` from the frame that detected it.
2. The driver loop calls `self.unwind(error)`, which pops all frames in reverse order.
3. Guard frames (`ScopeGuard`, `BudgetGuard`, `CostPayerGuard`) perform cleanup during unwind (pop scope, restore budget, restore cost payer).
4. `ActionEpilogue` frames emit `ActionCompleted(Failed)` during unwind if they haven't already — preserving the invariant that every `ActionStarted` is paired with an `ActionCompleted`.
5. The error is returned as `Step::Error`.

### Compatibility shim

The existing callback API becomes:

```rust
impl Execution {
    /// Drive execution to completion using a callback handler.
    pub fn run_with_handler(
        mut self,
        handler: &mut dyn EffectHandler,
    ) -> Result<Value, RuntimeError> {
        loop {
            match self.poll() {
                Step::Yielded(effect) => {
                    let response = handler.handle(*effect);
                    self.respond(response);
                }
                Step::Done(value) => return Ok(value),
                Step::Error(e) => return Err(e),
            }
        }
    }
}
```

The existing `Interpreter` methods (`execute_action`, etc.) can optionally be rewritten to create an `Execution` internally and drive it with `run_with_handler`. Or they can coexist with the recursive implementation during a transition period.

## Implementation Phases

### Phase 1: Emission seam

Replace all 42 `env.handler.handle(effect)` calls with `env.emit(effect)`. Pure mechanical refactor. The `emit()` method just delegates to `handler.handle()`. No behavior change.

This is a prerequisite for everything else and delivers immediate value: a single place to add tracing, validation, or coverage instrumentation.

**Scope:** ~42 line changes across 9 files + 5-line method addition.

### Phase 2: Types and driver loop

Define `Frame`, `Advance`, `Execution`, and the `poll`/`respond`/`run_with_handler` API. Add `Step::Error` to the existing `Step` enum. No frame `advance()` implementations yet — just the structural types.

**Scope:** New `execution.rs` module. Compiles but is not yet callable.

### Phase 3: Action lifecycle frames

Convert `execute_action` / `scoped_execute` / `execute_pipeline` to frame-based execution. This is the outermost and most structurally regular code path.

Test by constructing an `Execution` for simple actions and asserting the yielded effect sequence matches the recursive path (using `ScriptedHandler`-style response scripts).

**Scope:** `frame/action.rs` (new), integration tests.

### Phase 4: Block and statement frames

Convert `eval_block` / `eval_stmt` to `Block` and `StmtResume` frames. Synchronous statements execute inline; effectful statements (Grant, Revoke, Assign with mutation, Emit) push continuation frames.

**Scope:** `frame/block.rs` (new). This is where expression evaluation integration happens.

### Phase 5: Emit dispatch and condition lifecycle frames

Convert `eval_emit` (hook dispatch + condition handler dispatch) and `apply_condition` / `remove_condition` / `revoke` to frames. These are the most state-heavy conversions (emit_depth tracking, lifecycle block counters, condition token pre-allocation, per-instance removal loops).

**Scope:** `frame/emit.rs`, `frame/condition.rs` (new).

### Phase 6: Public API and migration

Add `Interpreter::start_action`, `start_reaction`, `start_mechanic`, `start_derive`, etc. Optionally rewrite the callback-based methods as shims. Update the CLI runner and test harness to use the new API (or keep both paths).

**Scope:** `lib.rs` additions, `ttrpg_cli` integration.

## Alternatives Considered

### Thread + channel

One OS thread per `Execution`. The evaluator runs unchanged on the worker thread, sending effects through a channel and blocking on responses. The host drives from the main thread.

**Rejected because:**
- `Interpreter` carries `Cell<u64>`, `Rc<RefCell<_>>`, and `RefCell<_>` — none are `Send`. The entire ownership model would need redesigning.
- Fighting the goal of keeping synchronous state reads (reads would need to cross the thread boundary).
- Worse for foreign embedding — the host must manage thread lifetime, and the execution state is opaque on the worker's stack.
- Does not produce an inspectable/serializable execution state.

### Stackful coroutines (corosensei, genawaiter)

Library-provided stackful coroutines. The evaluator runs on a coroutine stack, yields at each `emit()` call.

**Rejected because:**
- The suspended state lives on an opaque platform-specific stack, not in inspectable Rust data structures. This blocks debugging, cancellation, state serialization, and foreign embedding.
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

1. **Frame explosion.** The number of `Frame` variants may grow large as every effectful code path needs representation. Mitigation: keep synchronous code paths as helper functions, only frame-ify paths that cross effect boundaries.

2. **AST cloning cost.** Frames own AST node copies (blocks, expressions). For typical TTRPG rulesets (small blocks, few statements), this is negligible. If it becomes measurable, `Arc`-wrap frequently-cloned AST nodes.

3. **Semantic divergence.** Two code paths (recursive and frame-based) executing the same logic risks subtle behavioral differences. Mitigation: run the full `.ttrpg-cli` test suite through both paths and diff the effect sequences.

4. **Incremental adoption friction.** During the transition, new effectful features must be added to both the recursive evaluator and the frame-based evaluator. Mitigation: complete the migration before adding new effectful features, or add them only to the frame-based path once it's the primary path.

5. **Expression evaluation boundary.** The division between "synchronous expression evaluation" and "effectful builtins that need frames" must be maintained carefully. Any new builtin that emits effects must use the frame mechanism.
