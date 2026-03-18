# Step-Based Expression Evaluator — Design Document

> **Terminology note:** This document describes the migration of the *internal expression evaluator* from recursive to step-based execution. The terms "recursive evaluator" and "step-based frames" refer to internal execution architecture, not the host integration layers (Layer 1/2/3) defined in [`integration_layers.md`](integration_layers.md).

## Problem

The step-based execution engine (`Execution<S>`) currently delegates expression and statement evaluation to the recursive evaluator (`eval_expr`/`eval_stmt`) via **bridge calls**. The `ResumableBridge` frame wraps these recursive calls with a `CachingHandler` replay mechanism — when a host-decided effect (RollDice, ResolvePrompt) is encountered mid-evaluation, the bridge captures it, yields to the host, then **replays the entire expression from scratch** with cached responses.

This works but has fundamental problems:

1. **Replay unsoundness** — If a local mutation occurs before a host-decided effect, replaying re-applies the mutation. The `MutationTracker` detects this and fails fast, but it means some valid programs can't execute on the async path.

2. **O(n) replay cost** — Each host-decided effect in a single expression replays all prior work. An expression like `roll(1d6) + roll(1d6) + roll(1d6)` replays 1+2+3=6 evaluations instead of 3.

3. **Architectural ceiling** — The bridge pattern prevents us from eliminating the recursive evaluator entirely. Every `ResumableBridge` creates a temporary `Interpreter` + `Env`, copies state in, runs recursively, and copies state back. This is the last major bridge category remaining.

4. **Two code paths** — The sync path uses `bridge_eval_stmt` directly; the async path uses `ResumableBridge` with replay. Both call into the same recursive evaluator but with different handler stacks, making bugs hard to reproduce across paths.

## Goal

Replace `ResumableBridge` with native frame-based expression evaluation. Every expression and statement becomes a sequence of `Advance::{Push,Pop,Continue}` steps — no recursion, no replay, no `CachingHandler`.

## Current Architecture (What We're Replacing)

### Already step-based (frame-driven)
```
ActionLifecycle → Block → FunctionEval → DeriveEval → EmitEval → ...
                          CallSetup → ConditionApplyGate → ...
```

### Still recursive (via bridges)

**In Block frame:**
```
Block frame
  ├─ try_frame_dispatch_stmt()  → FunctionEval/CallSetup (calls only)
  ├─ EmitEval (emit statements)
  ├─ native dispatch (Return(None), WithBudget, Grant, Revoke, ...)
  └─ extract_resumable_expr()   → ResumableBridge (everything else)
       └─ bridge_eval_with() → recursive eval_expr() with CachingHandler
```

**Outside Block — other frames that push ResumableBridge:**
- `ActionLifecycle` — evaluates `requires` clause expression
- `FillDefaults` — evaluates default parameter expressions one at a time
- `EmitEval` — evaluates emit argument expressions, param defaults, field defaults
- `ConditionApplyGate` — evaluates state field default expressions
- `BridgeCall` entry point — evaluates arbitrary expressions dispatched by callers
- `CallSetup` — evaluates call argument expressions one at a time

All of these push `ResumableBridge` children and receive results via `receive_child_result`. They all need to be migrated to push `ExprEval` instead.

### What ResumableBridge handles today

Any expression evaluation that can't be handled by a more specialized frame. This includes:
- Arithmetic: `let x = a + b`
- Field access: `target.hp`
- Method calls: `dice.roll()` (host-decided effect!)
- Nested calls: `max(roll(1d6), roll(1d8))`
- Control flow: `if x > 0 { a } else { b }`
- Constructors: `Foo { x: 1, y: roll(1d6) }`
- List/map literals with effectful elements
- `has`/`is` checks
- Pattern match with effectful bodies

## Design: ExprEval Frame

### Core Idea

Replace `ResumableBridge` with an `ExprEval` frame that evaluates expressions iteratively using an explicit operand stack and a micro-instruction sequence. When a host-decided effect is needed, the frame pushes a child waiting frame (e.g., `RollDiceWaiting`) — exactly like other frames do today. The child's result is received via `receive_child_result` and pushed onto the operand stack. No replay needed, because all intermediate results live on the operand stack.

**Resume model**: Always `Advance::Push` for effects, never `Advance::Yield`. This matches the existing driver's `receive_child_result`/`receive_response` split — `ExprEval` only uses child frames, so it only needs `receive_child_result`. The waiting frames (RollDiceWaiting, PromptWaiting) handle the yield/respond cycle internally.

### Frame Definition

```rust
ExprEval {
    /// Micro-instruction sequence (compiled from expression tree).
    work: Vec<ExprWork>,
    /// Operand stack: intermediate values accumulate here.
    operands: Vec<Value>,
    /// Program counter into work items.
    pc: usize,
    /// Result from a child frame (FunctionEval, RollDiceWaiting, etc.).
    child_result: Option<Result<Value, RuntimeError>>,
    /// Number of scopes currently pushed by this frame (for cleanup
    /// on error — must pop all before propagating).
    scope_depth: usize,
}
```

### Work Items (Micro-instructions)

Flatten the expression tree into a postfix work sequence. Each work item is either "evaluate this sub-expression and push result" or "consume N operands and push a result."

```rust
enum ExprWork {
    // ── Values ──────────────────────────────────────────────

    /// Evaluate a trivially-pure leaf: IntLit, StringLit, BoolLit,
    /// NoneLit, DiceLit, UnitLit. Pushes one value.
    /// Does NOT include Ident (may trigger lazy const eval) or
    /// StructLit (may spawn entities).
    Literal(Value, Span),

    /// Resolve an identifier. This is NOT just a scope lookup — it
    /// covers the full `eval_ident` resolution chain:
    ///   1. Local scope lookup
    ///   2. Lazy const evaluation (with cycle detection via Void sentinel)
    ///   3. Bare enum variant (fieldless → EnumVariant value)
    ///   4. Condition name (bare use → materialize with default params)
    ///   5. Function reference (bare fn name → FnRef value)
    ///   6. Enum namespace (enum type name → EnumNamespace for qualified access)
    ///   7. Module alias (use "..." as X → ModuleAlias value)
    ///   8. `turn` keyword (→ TurnBudget struct from state)
    ///
    /// Most of these are synchronous lookups that resolve inline.
    /// Step 2 (lazy const) may need a child ExprEval frame — uses
    /// ConstWriteback for the result. Step 4 (bare condition name)
    /// may need multiple child frames to evaluate default params —
    /// uses ConditionMaterialize for multi-step default evaluation.
    Ident(Name, Span),

    /// After a lazy const child frame completes: pop the evaluated
    /// value, write it to `RuntimeCore::consts` (replacing the Void
    /// sentinel), and push the value back onto the operand stack.
    /// If the value IS Void, that means a circular const reference
    /// was detected — error out.
    ConstWriteback(Name, Span),

    /// Materialize a bare condition name with default params.
    /// Condition params may have default expressions that are
    /// effectful, so this can't be done inline. The work item
    /// pushes a ConditionMaterialize child frame that evaluates
    /// each default param expression in sequence (via ExprEval
    /// children), then assembles Value::Condition.
    ConditionMaterialize {
        condition_name: Name,
        params: Vec<ConditionParamDefault>,
        span: Span,
    },

    // ── Operators ───────────────────────────────────────────

    /// Binary op: pop 2, push 1.
    BinOp(BinOp, Span),

    /// Unary op: pop 1, push 1.
    UnaryOp(UnaryOp, Span),

    /// Short-circuit binary (and/or): LHS value is on stack.
    /// For `and`: if LHS is not Bool, error. If false, skip RHS
    /// (jump to skip_to, LHS stays on stack as result). If true,
    /// pop LHS and fall through to RHS evaluation.
    /// For `or`: if LHS is not Bool, error. If true, skip RHS.
    /// If false, pop LHS and fall through to RHS.
    /// Matches current eval_binop semantics which reject non-Bool.
    ShortCircuit { op: BinOp, skip_to: usize, span: Span },

    // ── Access ──────────────────────────────────────────────

    /// Index access: pop index + object, push result.
    Index(Span),

    /// Field access: pop object, push field value.
    Field(Name, Span),

    // ── Calls ───────────────────────────────────────────────

    /// Call where the callee is a simple identifier (the common case).
    /// Args are on the operand stack. Dispatches through the full
    /// call resolution path (user fn, builtin, enum ctor, etc.).
    CallNamed {
        callee: Name,
        arg_meta: Vec<ArgMeta>,
        span: Span,
    },

    /// Field-access call: `receiver.field(args)`. The receiver value
    /// is on the operand stack (below the args). The compiler evaluates
    /// the receiver expression before the args, so by the time this
    /// work item executes, the receiver is already a Value — no
    /// re-evaluation needed.
    ///
    /// Dispatch depends on receiver type (matching call/dispatch.rs):
    /// - EnumNamespace → enum constructor: `Duration.Rounds(3)`
    /// - ModuleAlias → alias-qualified call: `Core.foo()`
    /// - Entity → action method: `target.attack(...)`
    /// - DiceExpr → effectful method: `.roll()` → RollDiceWaiting
    /// - List/Map/String → pure method: `.len()`, `.contains()`, etc.
    /// - Struct with FnRef field → indirect call via field value
    CallMethod {
        method: Name,
        arg_meta: Vec<ArgMeta>,
        span: Span,
    },

    /// Callable-value call: `callee_value(args)` where callee_value
    /// is on the operand stack (below args). Used when the callee is
    /// a FnRef (produced by bare function names in value position),
    /// or any other non-identifier, non-field-access callee expression.
    CallValue {
        arg_meta: Vec<ArgMeta>,
        span: Span,
    },

    // ── Aggregates ──────────────────────────────────────────

    /// List literal: pop N elements, push list.
    MakeList(usize, Span),

    /// Map literal: pop N*2 (key, value pairs), push map.
    MakeMap(usize, Span),

    /// has-check: pop entity, push bool.
    Has { group: Name, span: Span },

    /// is-check: pop value, push bool. Uses the full `TypeExpr`
    /// (not just a name) to support primitive types, containers,
    /// Option<T>, and other non-named type checks.
    Is { target_type: Spanned<TypeExpr>, span: Span },

    // ── Control flow ────────────────────────────────────────

    /// Conditional branch: pop condition, jump to then_pc or else_pc.
    Branch { then_pc: usize, else_pc: usize },

    /// Unconditional jump.
    Jump(usize),

    /// Push a new scope (for if_let bindings, pattern arms, for bodies).
    PushScope,

    /// Pop a scope.
    PopScope,

    /// Pop and discard top of stack.
    Pop,

    // ── Child frame delegation ──────────────────────────────

    /// Push a Block child frame for a branch body. The block's
    /// result (Pop value) is pushed onto the operand stack.
    /// Used for if/if_let/match arms that contain statements.
    PushBlock(Block, Span),

    /// Push a dedicated child frame for complex expressions that
    /// have their own frame type (SpawnEntity, ForEval, etc.).
    /// Result is pushed onto operand stack.
    PushChildFrame(ChildFrameTemplate),
}
```

#### ArgMeta — Preserving Call Argument Shape

The AST `Arg` type carries both the expression and optional name. Since `ExprEval` evaluates arg expressions onto the operand stack before reaching the `Call` work item, we need a separate metadata struct:

```rust
/// Metadata for a call argument (value is on the operand stack).
struct ArgMeta {
    /// Named argument label, if present (e.g., `target: foo`).
    name: Option<Name>,
    /// Original span for error reporting.
    span: Span,
}
```

**Important**: today's `bind_args` uses `try_eval_with_hint` to resolve bare enum variant names using the target parameter's type as a hint (e.g., if a param expects `Duration`, a bare `Rounds` is resolved as `Duration.Rounds`). This hint-based resolution happens *during* argument evaluation, before the value is produced.

In the ExprEval model, args are evaluated *before* the Call work item executes, so the parameter type hint is not yet available. This is acceptable because:
- The checker's `resolved_variants` table already resolves most ambiguous variants at check time via span-keyed lookups
- `eval_ident`'s fallback `unique_variant_owner()` handles unambiguous cases
- `try_eval_with_hint` only activates when *both* checker resolution and unique-owner lookup fail — a narrow edge case for CLI eval expressions that bypass the checker

If this edge case proves problematic, the compiler can emit a `CallWithHints` variant that carries parameter type info alongside `ArgMeta`, allowing pre-evaluation hint resolution. But this is unlikely to be needed for checked programs.

The `CallNamed` work item pops `arg_meta.len()` values from the operand stack, pairs them with their `ArgMeta`, and dispatches through the full call resolution path. `CallMethod` also pops the receiver (one slot below the args). The compiler determines which variant to emit by examining the callee expression shape:

- `Ident(name)` → `CallNamed { callee: name }` — covers user functions, builtins, conditions
- `FieldAccess { object, field }` → compile `object` first (pushes receiver Value), then `CallMethod { method: field }` — covers enum constructors (`Duration.Rounds`), alias-qualified calls (`Core.foo`), action methods (`target.attack`), value methods (`.roll()`, `.len()`), and struct-field FnRef calls
- Other → compile callee expr (pushes callable Value), then `CallValue` — covers FnRef calls (bare function names produce `FnRef` values via `Ident` resolution)

This way, by the time any Call work item executes, all sub-expressions (receiver, callee, args) are already Values on the operand stack. No AST re-evaluation is needed at dispatch time. The dispatch logic in each Call variant mirrors the receiver-type-based routing in `call/dispatch.rs`.

### Compilation: Expression → Work Sequence

A compile step (not codegen — just tree → vec) walks the `ExprKind` tree and emits work items in postfix order:

```
Expression: a + roll(1d6)
Compiles to:
  [0] Ident("a")               // push a's value
  [1] Literal(DiceExpr(1d6))   // push DiceExpr
  [2] CallNamed { callee: "roll", args: [positional] }
                                // pop 1 arg, dispatch roll() → push RollDiceWaiting child
  [3] BinOp(Add)               // pop 2, push sum

Expression: target.weapon.roll()
Compiles to:
  [0] Ident("target")          // push target entity
  [1] Field("weapon")          // pop entity, push weapon field value
  [2] CallMethod { method: "roll", args: [] }
                                // pop receiver (DiceExpr), push RollDiceWaiting child
```

For short-circuit operators:
```
Expression: a and b
Compiles to:
  [0] Ident("a")
  [1] ShortCircuit { op: And, skip_to: 3 }  // if falsy, skip to 3
  [2] Ident("b")                              // RHS (only reached if LHS truthy)
  [3] (end)
```

### Branch Bodies: Block Children, Not Inlined Instructions

`if`/`if_let`/`pattern_match` branches contain statement blocks, not just expressions. These blocks can contain arbitrary statements (let bindings, assignments, emit, return, nested control flow). Flattening them into ExprWork instructions would require reimplementing all of Block's dispatch logic.

Instead, branch bodies push `Block` child frames:

```
Expression: if x > 0 { let y = x * 2; y } else { 0 }
Compiles to:
  [0] Ident("x")
  [1] Literal(0)
  [2] BinOp(Gt)
  [3] Branch { then_pc: 4, else_pc: 6 }
  [4] PushBlock(then_body)     // push Block child frame, result → operand stack
  [5] Jump(7)
  [6] PushBlock(else_body)     // push Block child frame
  [7] (end)
```

When `ExprEval` reaches a `PushBlock`, it returns `Advance::Push(Frame::Block { ... })`. The Block frame executes the body (with its full statement dispatch, scope management, etc.), and when it pops, `ExprEval::receive_child_result` pushes the value onto the operand stack.

This preserves the recursive-descent structure for block bodies while keeping expression evaluation flat. The key insight is that **blocks are the unit of statement execution** — ExprEval handles expression composition, Block handles statement sequencing, and they delegate to each other.

### advance() Implementation

```rust
fn advance_expr_eval(...) -> Advance {
    // Handle child frame result from previous push.
    if let Some(result) = child_result.take() {
        match result {
            Ok(val) => operands.push(val),
            Err(e) => return Advance::Error(e),
        }
        return Advance::Continue;
    }

    loop {
        if pc >= work.len() {
            return Advance::Pop(operands.pop().unwrap_or(Value::Void));
        }
        match &work[pc] {
            ExprWork::Literal(val, _) => {
                operands.push(val.clone());
                pc += 1;
            }
            ExprWork::Ident(name, span) => {
                // Look up in scope stack. If it's a lazy const,
                // may need to push a child frame to evaluate it.
                match resolve_ident(core, env, sp, name, *span) {
                    IdentResult::Value(val) => {
                        operands.push(val);
                        pc += 1;
                    }
                    IdentResult::NeedsEval(const_expr) => {
                        // Install Void sentinel for cycle detection.
                        core.consts.borrow_mut().insert(name.clone(), Value::Void);
                        // The next work item is ConstWriteback, which
                        // will store the result and detect cycles.
                        pc += 1;
                        return Advance::Push(Frame::ExprEval {
                            work: compile_expr(&const_expr),
                            operands: Vec::new(),
                            pc: 0,
                            child_result: None,
                        });
                    }
                    IdentResult::CircularConst => {
                        return Advance::Error(RuntimeError::with_span(
                            format!("circular const reference: '{}'", name),
                            *span,
                        ));
                    }
                }
            }
            ExprWork::ConstWriteback(name, span) => {
                let val = operands.last().unwrap().clone();
                if matches!(val, Value::Void) {
                    return Advance::Error(RuntimeError::with_span(
                        format!("circular const reference: '{}'", name),
                        *span,
                    ));
                }
                core.consts.borrow_mut().insert(name.clone(), val);
                pc += 1;
                // Value stays on operand stack — it's the result.
            }
            ExprWork::BinOp(op, span) => {
                let rhs = operands.pop().unwrap();
                let lhs = operands.pop().unwrap();
                match apply_binop(*op, lhs, rhs, *span) {
                    Ok(val) => { operands.push(val); pc += 1; }
                    Err(e) => return Advance::Error(e),
                }
            }
            ExprWork::CallNamed { callee, arg_meta, span } => {
                let arg_values = operands.split_off(
                    operands.len() - arg_meta.len()
                );
                pc += 1;
                // Full call dispatch: user fn, builtin, enum ctor, etc.
                match dispatch_call_named(core, env, sp, eh,
                    callee, arg_meta, arg_values, *span)
                {
                    CallResult::Value(val) => {
                        operands.push(val);
                        // stay in loop — no child needed
                    }
                    CallResult::PushChild(frame) => {
                        return Advance::Push(frame);
                    }
                    CallResult::Error(e) => {
                        return Advance::Error(e);
                    }
                }
            }
            ExprWork::CallMethod { method, arg_meta, span } => {
                let arg_values = operands.split_off(
                    operands.len() - arg_meta.len()
                );
                let receiver = operands.pop().unwrap();
                pc += 1;
                // Dispatch: pure methods inline, effectful push child.
                match dispatch_method(core, env, sp, eh,
                    receiver, method, arg_meta, arg_values, *span)
                {
                    CallResult::Value(val) => {
                        operands.push(val);
                    }
                    CallResult::PushChild(frame) => {
                        return Advance::Push(frame);
                    }
                    CallResult::Error(e) => {
                        return Advance::Error(e);
                    }
                }
            }
            ExprWork::PushBlock(block, _span) => {
                pc += 1;
                return Advance::Push(Frame::Block {
                    stmts: block.node.clone(),
                    index: 0,
                    result: Value::Void,
                    expr_cache: Vec::new(),
                    awaiting_fn: None,
                    awaiting_error: None,
                });
            }
            ExprWork::Branch { then_pc, else_pc } => {
                let cond = operands.pop().unwrap();
                match cond {
                    Value::Bool(true) => pc = *then_pc,
                    Value::Bool(false) => pc = *else_pc,
                    _ => return Advance::Error(RuntimeError::with_span(
                        "condition must be a boolean", /* span from Branch */
                        Span::dummy(),
                    )),
                }
            }
            ExprWork::Jump(target) => {
                pc = *target;
            }
            // ... other work items
        }
    }
}
```

Key property: the `loop` handles pure operations in a tight loop without returning `Continue`. It only breaks out when it needs to `Push` a child frame. This avoids per-instruction overhead for simple expressions.

### Child Frame Results and Error Handling

When `ExprEval` pushes a child frame (FunctionEval, RollDiceWaiting, Block, etc.), the child's `Pop(value)` is received by `ExprEval::receive_child_result`, which stores it in `child_result`. The next `advance()` call pushes it onto the operand stack and returns `Continue` to re-enter the work loop.

**Error handling**: `ExprEval` must implement `receive_child_error` to handle errors from child frames. Before propagating the error, it must unwind any scopes it has pushed (tracked by a `scope_depth: usize` counter on the frame). This is critical for control-flow expressions (`if_let`, pattern match) that push scopes via `PushScope` work items — if a child frame errors inside a scoped branch body, the scope must be popped before the error propagates.

```rust
fn receive_child_error(&mut self, err: RuntimeError, env: &mut ExecEnv) {
    // Unwind any scopes this ExprEval pushed.
    for _ in 0..self.scope_depth {
        env.pop_scope();
    }
    // Store error for propagation on next advance().
    self.child_result = Some(Err(err));
}
```

The `advance()` method checks `child_result` first and, if it contains `Err`, propagates via `Advance::Error` after cleanup.

### Statement Integration

The `Block` frame's dispatch changes from:

```
// Current: three-way dispatch
try_frame_dispatch_stmt()     → FunctionEval (calls)
extract_resumable_expr()      → ResumableBridge (non-call expressions)
native dispatch               → inline (Return, Grant, etc.)
```

To:

```
// New: two-way dispatch
native dispatch               → inline (Return, Grant, etc.)
everything else               → ExprEval child frame
```

For `Let`/`Assign`/`Return(Some)`, the `Block` frame still uses `AwaitingFn` to know how to consume the `ExprEval` result.

Note: the AST has no statement-level `for`, `if`, or `pattern_match` nodes — these are all expression-level (`ExprKind::For`, `ExprKind::If`, etc.) that appear as `StmtKind::Expr(expr)`. They're handled by ExprEval when the Block frame dispatches the `Expr` statement's inner expression.

### Migration of Non-Block ResumableBridge Users

Every frame that currently pushes `ResumableBridge` children switches to pushing `ExprEval` instead. The frame type swap is straightforward, but several parents need bespoke state cleanup because they carry replay-specific fields or have non-trivial `receive_child_result` contracts:

| Frame | What it evaluates | Migration complexity |
|-------|-------------------|---------------------|
| `FillDefaults` | Default parameter expressions | Simple swap — already stores result in `child_result: Option<Value>` |
| `BridgeCall` | Arbitrary entry-point expressions | Simple swap — just changes which child frame type is pushed |
| `EmitEval` | Emit arg/default expressions | Moderate — has `child_result: Option<Result<Value, RuntimeError>>` with phase-dependent handling |
| `CallSetup` | Call argument expressions | Moderate — manages `arg_index` and `evaluated` vec; also carries its own `expr_cache` for replay that becomes dead |
| `ActionLifecycle` | `requires` clause expression | Moderate — mutates `step` and `body_result` on child completion; replay `expr_cache` in Block children becomes dead |
| `ConditionApplyGate` | State field defaults | Moderate — stores into `state_expr_cache` for replay; this field becomes dead after migration and the `default_scope_pushed` flag needs review |

The replay-specific fields (`expr_cache`, `state_expr_cache`) on parent frames become dead code after migration and should be removed in Phase 6. The `receive_child_result` implementations themselves don't change — they already receive `Value` regardless of which child frame produced it.

### Inline Bridge Calls (`eval_expr_via_handler`)

Beyond `ResumableBridge` child frames, there are ~25 direct `eval_expr_via_handler()` calls scattered across native dispatch paths in `execution.rs`. These are synchronous bridge calls used for "leaf" expression evaluation within frame `advance()` methods:

- **Block native dispatch**: `with_budget`/`with_budgets` entity + budget field evaluation, `grant` entity + field evaluation, `revoke` entity evaluation, `with_cost_payer` entity evaluation
- **Modifier pipeline**: binding value evaluation, suppression condition evaluation, let/if/override statement evaluation within modifier bodies
- **DeriveEval**: argument binding evaluation, body setup expressions

These calls are safe on the sync path (no host-decided effects possible in the expressions they evaluate — entity refs, field values, budget amounts). But they still create temporary `Interpreter` + `Env` instances via `bridge_eval_with`, which is what we want to eliminate.

**Migration strategy**: For truly-simple expressions (single ident, field access, literal), evaluate inline without ExprEval overhead. For compound expressions, push ExprEval child and restructure the parent to accept the result asynchronously (converting the inline-synchronous pattern to push-then-receive). This is the hardest part of the migration because these call sites assume synchronous completion — each needs to be split into a "before" state (push ExprEval) and "after" state (receive result, continue).

## Phased Implementation

### Phase 1: ExprEval for Trivially-Pure Expressions

**Scope**: True literals only (IntLit, StringLit, BoolLit, NoneLit, DiceLit, UnitLit), plus binary/unary ops on already-evaluated operands, field access, index access, `Paren`.

**Explicitly excluded from Phase 1** (not trivially pure):
- `Ident` — can trigger lazy const evaluation (which may itself be effectful)
- `StructLit` — can trigger entity spawning (SpawnEntity effect), group grants, default field evaluation, `..base` spreading, `with_conditions`
- `Call` — any call can be effectful
- `ListLit`/`MapLit` — elements may be effectful
- Control flow — bodies are blocks

This phase validates the frame machinery, operand stack, and compilation pipeline with expressions that always complete in a single `advance()` call.

**What changes**:
- Add `Frame::ExprEval` variant with `receive_child_result`
- Add `ExprWork` enum (Literal, BinOp, UnaryOp, Field, Index, Pop subset)
- Add `compile_expr()` function (partial — returns `None` for non-trivial expressions)
- `Block` frame: for non-call RHS expressions, try `compile_expr()` first; fall back to `ResumableBridge` if it returns `None`

**Validation**: Differential fuzzer confirms parity. All existing tests pass unchanged.

### Phase 2: Identifiers and Simple Calls

**Scope**: `Ident` (with lazy const eval support), user-function `Call` (direct name, positional and named args), pure builtins (min, max, abs, len, etc.).

**What changes**:
- `ExprWork::Ident` with `IdentResult::NeedsEval` path for lazy consts
- `ExprWork::CallNamed` with full `ArgMeta` + `dispatch_call_named()` routing
- `compile_expr()` handles `ExprKind::Call` and `ExprKind::Ident`
- `CallSetup` frame users can switch to ExprEval for arg evaluation

### Phase 3: Effectful Calls and Methods

**Scope**: `.roll()` → `RollDiceWaiting`, `prompt()` → `PromptWaiting`, `apply_condition()` → `ConditionApplyGate`, `remove_condition()` → `ConditionRemovalLoop`, enum constructors, action methods, alias-qualified calls.

**What changes**:
- `dispatch_call()` handles the full call resolution matrix from `call/dispatch.rs`
- Effectful methods push waiting child frames (result → operand stack on resume)
- `ListLit`/`MapLit` become compilable (elements are now handled)
- **No more replay** — the operand stack preserves all values computed before the yield

**Validation**: Critical phase. After this, `ResumableBridge` should only remain for control-flow expressions. The `MutationTracker` unsoundness check should fire on zero test cases.

### Phase 4: Control-Flow Expressions and StructLit

**Scope**: `ExprKind::If`, `ExprKind::IfLet`, `ExprKind::PatternMatch`, `ExprKind::GuardMatch`, `ExprKind::For` (returns Void, used as statement via `StmtKind::Expr`), `ExprKind::ListComprehension` (returns list — distinct from For), `ExprKind::StructLit` (with entity spawning).

Note: `For` and `ListComprehension` are separate AST nodes with different semantics — `eval_for` returns `Value::Void` (statement-like), while `eval_list_comprehension` collects results into a list.

**What changes**:
- `Branch`/`Jump`/`PushScope`/`PopScope`/`PushBlock` work items
- Branch bodies compile to `PushBlock` items (delegate to Block frame)
- `ExprKind::For` pushes a dedicated `ForEval` child frame that iterates and returns Void
- `ExprKind::ListComprehension` pushes a dedicated `ListComprehensionEval` child frame that iterates and collects into a list
- `StructLit` for entity types pushes a new `EntityConstruction` child frame (not just `SpawnEntity`) that handles the full construction pipeline: evaluate explicit field values, evaluate omitted-field defaults, compute required groups, apply `..base` spreading, evaluate `with_conditions` expressions, then push `SpawnEntity` + `GrantGroup` effects. The existing `Frame::SpawnEntity` only handles the final effect emission step — it expects all values pre-computed. For plain struct types (non-entity), field evaluation can be compiled inline with a `MakeStruct` work item.
- Pattern match compiles to a chain of test + Branch items per arm, with `PushBlock` for arm bodies
- `if_let` compiles to a pattern test + Branch with scope push for the binding

### Phase 5: Migrate Non-Block ResumableBridge Users

**Scope**: Switch every frame that pushes `ResumableBridge` children to push `ExprEval` instead, and clean up replay-specific parent state.

**What changes** (per migration table above):
- `FillDefaults`, `BridgeCall`: simple frame type swap
- `EmitEval`: swap + review phase-dependent child_result handling
- `CallSetup`: swap + remove `expr_cache` replay field (dead after migration)
- `ActionLifecycle`: swap + verify `step`/`body_result` mutation in `receive_child_result` still correct
- `ConditionApplyGate`: swap + remove `state_expr_cache` replay field + review `default_scope_pushed` flag

Validate after each frame migration with the differential fuzzer. The replay-specific fields don't need to be removed in this phase — they can be left as dead code and cleaned up in Phase 7.

### Phase 6: Migrate Inline Bridge Calls (`eval_expr_via_handler`)

**Scope**: Replace all ~25 direct `eval_expr_via_handler()` calls in frame `advance()` methods with either inline evaluation (for trivially-pure expressions) or ExprEval child frame pushes.

**Subcategories**:

**6a — Trivially-pure inline calls** (can stay inline, just remove bridge wrapper):
- Entity identifier resolution (single Ident → scope lookup)
- Budget field literal evaluation
- Simple field access chains

For these, a direct `resolve_ident()` or `eval_leaf()` call replaces the bridge — no ExprEval needed.

**6b — Compound expressions in native dispatch** (need state machine conversion):
- `try_dispatch_with_budget`: entity expr + N budget field exprs → need multi-step evaluation
- `try_dispatch_with_budgets`: specs expr evaluation
- `try_dispatch_grant`: entity expr + N field init exprs
- `try_dispatch_revoke_stmt`: entity expr

These currently evaluate all sub-expressions synchronously before pushing the child Block frame. Converting to async requires splitting each into a state machine: push ExprEval for first expr → receive result → push ExprEval for next expr → ... → all evaluated → push Block child.

**6c — Modifier pipeline inline evaluation** (~15 calls in native modifier code):
- Binding value evaluation, suppression checks, let/if/override in modifier bodies
- These are called from `collect_cost_modifiers_native()`, `apply_single_cost_modifier_native()`, etc.

These are the hardest to migrate because the modifier pipeline functions are called from within frame `advance()` methods but are themselves multi-step. They may need their own sub-frame or state machine treatment.

**Strategy**: 6a is immediate cleanup. 6b converts native dispatch helpers to frame-based state machines. 6c may be deferred or handled by converting modifier pipeline functions into frames themselves.

### Phase 7: Remove Bridge Infrastructure

**Scope**: Delete `ResumableBridge` frame variant, `CachingHandler`, `ExprCache`, `extract_resumable_expr()`, `bridge_eval_with()`, `bridge_eval_expr()`, `bridge_eval_stmt()`, `bridge_eval_block()`, `bridge_run()`, `eval_expr_via_handler()`, `ComposedHandler`, `MutationTracker`.

**What changes**:
- Remove all bridge infrastructure
- Remove `BridgeStats` counters (or repurpose for other metrics)
- `Block` frame sync/async paths unify — same dispatch logic everywhere
- `try_frame_dispatch_stmt()` absorbed into ExprEval compilation
- `Interpreter::bridge()` constructor removed
- Replay-specific fields on parent frames (`expr_cache`, `state_expr_cache`) removed

## Risks and Considerations

### Compilation Cost
The `compile_expr()` step adds allocation (Vec<ExprWork>) per expression. For simple expressions this is overhead vs. direct evaluation. Mitigation: the `Block` frame can evaluate truly trivial RHS expressions (single IntLit, single Ident) inline without constructing ExprEval at all.

### Scope Management
The recursive evaluator manages scopes implicitly via Rust's call stack. ExprEval must manage scopes explicitly for `if_let` bindings and pattern match arm bindings. This adds `PushScope`/`PopScope` work items. Scope lifetime errors (forgetting to pop) will cause test failures, not silent corruption.

### Struct Literal Complexity
`StructLit` evaluation for entity types involves a multi-step pipeline: evaluate explicit fields (possibly with type-hinted resolution), evaluate omitted-field defaults, determine and materialize required groups, apply `..base` spreading (copy fields from base entity), evaluate `with_conditions` expressions, then emit `SpawnEntity` + `GrantGroup` effects. The existing `Frame::SpawnEntity` only handles the final effect emission — it expects all values pre-computed. A new `EntityConstruction` child frame (pushed by ExprEval) is needed to orchestrate the full pipeline, evaluating sub-expressions via ExprEval children as needed. For plain struct types (non-entity), field evaluation can be compiled into the work sequence with a `MakeStruct` work item.

### For-Loop Expressions
`for` as an expression (collecting results into a list) needs iterator state. A dedicated `ForEval` child frame handles iteration, pushing ExprEval/Block children for each iteration body. This is simpler and more consistent than loop control in ExprWork (which would need backward jumps + iterator state on the operand stack).

### Binary Short-Circuit
`and`/`or` operators need short-circuit evaluation. The `ShortCircuit` work item validates that the LHS is `Bool` (matching current `eval_binop` semantics which reject non-Bool operands), then either keeps it on stack (skipping RHS via jump) or pops it and falls through to RHS evaluation.

### Error Spans
Every `ExprWork` variant carries a `Span` for error reporting. This adds some memory overhead per work item but is essential for usable error messages.

### Lazy Const Evaluation
`Ident` resolution can trigger lazy const evaluation, which may itself be effectful (e.g., a const that calls a function which rolls dice). The protocol is:

1. Check `RuntimeCore::consts` cache — if present and non-Void, use cached value
2. If present and Void, circular reference detected — error
3. If absent, insert Void sentinel, push child ExprEval for the const expression
4. Compiler emits `ConstWriteback(name)` after `Ident(name)` for const candidates
5. `ConstWriteback` pops the child result, writes it to the const cache (replacing sentinel), and pushes it back onto the operand stack

This matches the current `eval_ident` cycle-detection semantics without requiring recursion.

## What This Unlocks

1. **Unified sync/async path** — No more dual dispatch in Block. One code path, always step-based.
2. **True interruptibility** — Any expression can yield at any point without replay overhead.
3. **Elimination of Interpreter+Env bridge** — No more temporary recursive interpreter instances.
4. **Foundation for debugging** — Step-through debugging, expression-level breakpoints, value inspection at any point in evaluation.
5. **Simpler mental model** — The frame stack is the only execution model. No hidden recursion.
