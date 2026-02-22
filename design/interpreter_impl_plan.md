# TTRPG DSL Interpreter — Implementation Plan

## Architecture

### Suspension mechanism

The interpreter uses a **callback-based** execution model. The host provides an `EffectHandler` implementation; the interpreter calls it synchronously whenever an effect is produced. This keeps the tree-walking evaluator simple and recursive — no threads, no async, no explicit state machines.

```rust
pub trait EffectHandler {
    fn handle(&mut self, effect: Effect) -> Response;
}
```

If the host needs async behavior (e.g., waiting for UI input), it blocks inside `handle`.

### Crate layout

```
ttrpg_interp/
  src/
    lib.rs              — public API, Interpreter
    lower.rs            — Phase 0: move desugaring (MoveDecl → mechanic + action)
    value.rs            — Value enum, DiceExpr, RollResult, DurationValue
    effect.rs           — Effect, Response, Step, EffectHandler trait
    state.rs            — StateProvider, WritableState, EntityRef, ActiveCondition
    eval.rs             — expression evaluator (tree-walking)
    exec.rs             — statement executor, block runner, LValue resolution
    call.rs             — function dispatch, argument binding
    builtins.rs         — floor, ceil, min, max, distance, multiply_dice, roll
    action.rs           — action/reaction pipeline
    pipeline.rs         — modify pipeline, suppression checking
    event.rs            — event firing, trigger matching
    adapter.rs          — StateAdapter (Layer 2)
    reference_state.rs  — GameState (Layer 3)
```

### Dependencies

- `ttrpg_ast` — AST nodes, `DiceFilter`, `Span`, `AssignOp`, `LValue`, etc.
- `ttrpg_checker` — `TypeEnv`, `Ty`, `FnInfo`, `FnKind`, `ConditionInfo`, `EventInfo`, etc.

### Assumptions

- The interpreter trusts that the program has passed type-checking. Runtime type errors are treated as checker bugs, not user errors.

---

## Phase 0: Move Lowering

**Files:** `lower.rs`

**Goal:** Lower `MoveDecl` nodes into canonical `FnDecl` (mechanic) + `ActionDecl` pairs. This runs after parsing but **before type-checking**, so the synthesized declarations are validated by the checker naturally. The checker never sees `MoveDecl` nodes — by the time it runs, all moves have been desugared into mechanics and actions.

The grammar spec (Section 7) defines the desugaring rule. A move like:

```
move GoAggro on actor: Character (target: Character) {
    trigger: "threaten with force"
    roll: 2d6 + actor.stats[Hard]
    on strong_hit { ... }
    on weak_hit   { ... }
    on miss       { ... }
}
```

Becomes:

```
mechanic __go_aggro_roll(actor: Character, target: Character) -> RollResult {
    roll(2d6 + actor.stats[Hard])
}

action GoAggro on actor: Character (target: Character) {
    cost { action }
    resolve {
        let result = __go_aggro_roll(actor, target)
        match {
            result >= 10 => { /* strong_hit body */ },
            result >= 7  => { /* weak_hit body */ },
            _            => { /* miss body */ }
        }
    }
}
```

### 0.1 Lowering function

```rust
pub fn lower_moves(program: Program, diags: &mut Vec<Diagnostic>) -> Program
```

Lowering is purely syntactic — it does not need type information. It runs before the checker, so there is no `TypeEnv` to consult. The checker's collect pass will pick up the synthesized mechanic and action declarations naturally, validating their types, parameter lists, and body expressions just like user-written declarations.

The accumulator pattern (`&mut Vec<Diagnostic>`) matches the checker's error-reporting convention. Lowering errors are recoverable — the lowering function skips malformed moves (leaving them as `DeclKind::Move`) and continues processing the rest of the program. Any surviving `DeclKind::Move` nodes will cause explicit checker errors — the checker's `collect` and `check` passes emit "move declarations must be lowered before type-checking" diagnostics for any `DeclKind::Move` they encounter (see "Phase 0 deliverable" below).

The AST uses `Program → Vec<TopLevel> → SystemBlock → Vec<DeclKind>`. Lowering iterates over each `TopLevel::System` block and scans its `decls` for `DeclKind::Move(m)`:

1. **Validate outcomes:** The outcome set must be exactly `{strong_hit, weak_hit, miss}` — no missing, extra, or duplicate names. Any deviation is a lowering error. (Custom outcome labels are not supported in v0.)

2. **Check for collision:** Verify that no other `DeclKind` in the same `SystemBlock` already uses the synthetic mechanic name `__{snake_case(m.name)}_roll`. If it does, emit a lowering error. (The checker also reserves the `__` prefix — see "Checker prerequisite" below — so user-declared collisions are impossible in well-checked programs; this catches only move-vs-move collisions within the same lowering pass.)

3. **Synthesize mechanic:** Create a `FnDecl` named `__{snake_case(m.name)}_roll` with `synthetic: true`, the receiver **and all move params** as parameters, return type `RollResult`, and body `roll(m.roll_expr)`. The `__` prefix is reserved for synthetic names (matching the existing `__event_<name>` convention for synthetic types).

4. **Synthesize action:** Create an `ActionDecl` with the same name, receiver, and params as the move. Set `trigger_text` to `Some(m.trigger_text.clone())` to preserve the move's trigger string as action metadata (per spec: no runtime semantics in v0, but available for UI/documentation). Cost is `{ action }`. The resolve block contains:

   **AST prerequisite:** Add `pub trigger_text: Option<String>` and `pub synthetic: bool` to `ActionDecl` in `ttrpg_ast/src/ast.rs`. `trigger_text` is `None` for user-written actions and `Some(...)` for actions synthesized from moves. `synthetic` is `false` for user-written actions and `true` for actions synthesized from moves. The parser sets both to their default values; only `lower_moves` populates them. Similarly, add `pub synthetic: bool` to `FnDecl` (parser sets `false`; lowering sets `true` for synthesized mechanics).
   - `let result = {mechanic_name}(receiver_name, param1, param2, ...)` — forwarding all move params
   - A `GuardMatch` with arms for each outcome, using PbtA thresholds:
     - `strong_hit` → `result.total >= 10`
     - `weak_hit` → `result.total >= 7`
     - `miss` → wildcard (`_`)

5. **Replace** the `DeclKind::Move` with the two synthesized `DeclKind` entries within the same `SystemBlock`. The checker's collect pass will register both the synthesized mechanic and action in `TypeEnv` automatically — no manual `TypeEnv` updates are needed.

**Checker prerequisite:** The checker's collect pass should reject all names starting with `__` on declarations where `synthetic == false` (structs, enums, functions, mechanics, derives, actions, reactions, events, conditions, options). Declarations with `synthetic == true` (produced by `lower_moves`) are exempt — they are internal names that the checker should register normally. This reserves the `__` prefix for synthetic names (`__event_<name>`, `__{move}_roll`) and prevents user-declared collisions by construction. Emit a diagnostic: "names starting with `__` are reserved for internal use". Note: entity type names are not independently declared — they derive from struct declarations. Rejecting struct names starting with `__` transitively prevents `Ty::Entity("__event_*")` from existing, which is required for the synthetic event payload field resolution in the checker (`check_expr.rs` matches `Ty::Struct | Ty::Entity` on `__event_*` prefixes). Declarations that do not have a `synthetic` field (e.g., `StructDecl`, `EnumDecl`, `EventDecl`, `ConditionDecl`) always reject `__` — only `FnDecl` and `ActionDecl` carry the flag since those are the only kinds lowering synthesizes.

### Phase 0 deliverable

`lower_moves` transforms a `Program` containing `MoveDecl` nodes into one with only canonical declarations. Because lowering runs before the checker, the synthesized mechanic and action are validated naturally by the collect and check passes — no manual `TypeEnv` registration or re-checking is needed. This preserves the "interpreter trusts checked programs" invariant: every AST node the interpreter sees has been type-checked.

Lowering errors are accumulated into `&mut Vec<Diagnostic>` (matching the checker's error-reporting pattern); malformed moves are skipped. The lowered action preserves the move's trigger text as metadata via the new `ActionDecl::trigger_text` field. Round-trip test: parse a move, lower it, check the lowered program, verify no `DeclKind::Move` nodes remain, verify trigger text is preserved on the synthesized action, interpret the synthesized action. Missing/extra/duplicate outcomes, non-standard outcome names, and synthetic name collisions produce lowering diagnostics.

Because lowering runs before checking, `FnKind::Move` is no longer needed — the checker never sees a move declaration. The following checker changes are required:

1. **Remove `FnKind::Move`** from the `FnKind` enum.
2. **Replace `DeclKind::Move` handling in `collect.rs`** (`collect_move` call) with a diagnostic: "move declarations must be lowered before type-checking". Delete the `collect_move` function.
3. **Replace `DeclKind::Move` handling in `check.rs`** (`check_move` call) with the same diagnostic. Delete the `check_move` function.

This ensures that any surviving `DeclKind::Move` nodes (from a caller that forgot to run `lower_moves`) produce explicit checker errors rather than silently passing through.

Prerequisite AST changes: add `trigger_text: Option<String>` and `synthetic: bool` to `ActionDecl`; add `synthetic: bool` to `FnDecl`. Prerequisite checker changes: (1) reject names starting with `__` on declarations where `synthetic == false` (see "Checker prerequisite" above); (2) remove `FnKind::Move` and replace `DeclKind::Move` handling with diagnostics as described above; (3) reject direct reaction calls (see Phase 4.2); (4) reject `Position` as a set element type or map key type (`set<Position>`, `map<Position, _>`) — this invariant is relied upon by `PositionValue`'s pointer-based `Ord` impl (see Phase 1.1).

---

## Phase 1: Foundation Types

**Files:** `value.rs`, `effect.rs`, `state.rs`

**Goal:** All types from design doc Sections 2–4 compile and have basic trait impls.

### 1.1 Value enum (`value.rs`)

```rust
pub enum Value {
    Int(i64),
    Float(f64),
    Bool(bool),
    Str(String),
    None,

    DiceExpr(DiceExpr),
    RollResult(RollResult),

    List(Vec<Value>),
    Set(BTreeSet<Value>),
    Map(BTreeMap<Value, Value>),
    Option(Option<Box<Value>>),

    Struct { name: String, fields: BTreeMap<String, Value> },
    Entity(EntityRef),
    EnumVariant { enum_name: String, variant: String, fields: BTreeMap<String, Value> },

    Position(PositionValue),

    Duration(DurationValue),
    Condition(String),
}
```

Supporting types:

```rust
pub struct DiceExpr {
    pub count: u32,
    pub sides: u32,
    pub filter: Option<DiceFilter>,  // re-use from ttrpg_ast
    pub modifier: i64,
}

pub struct RollResult {
    pub expr: DiceExpr,
    pub dice: Vec<i64>,       // all dice rolled
    pub kept: Vec<i64>,       // dice after filtering
    pub modifier: i64,
    pub total: i64,           // sum(kept) + modifier
    pub unmodified: i64,      // sum(kept), no modifier
}

pub enum DurationValue {
    EndOfTurn,
    StartOfNextTurn,
    Rounds(i64),
    Minutes(i64),
    Indefinite,
}
```

`Position` is opaque to the interpreter. Wrap it so `Value` can implement `Clone`, `Debug`, and `Ord`:

```rust
pub struct PositionValue(pub Arc<dyn Any + Send + Sync>);
```

Use `Arc` rather than `Box` so `Value` can derive `Clone`. `Ord` on `PositionValue` orders by `Arc` pointer (deterministic but arbitrary) — this is a safety net since the checker prevents `Position` in sets/maps (see Phase 0 prerequisite: reject `set<Position>` and `map<Position, _>`). `PartialEq` on `PositionValue` uses `Arc::ptr_eq` — same `Arc` allocation means same position. This gives correct equality for the common case (position values originating from the same read). For cross-object comparison (different `Arc` allocations that may represent the same logical position), the evaluator routes through `value_eq()` which delegates to `StateProvider::position_eq`.

**Trait impls on Value:**
- `PartialEq` / `Eq` — structural equality for all variants; Float uses `f64::to_bits()` comparison (total-order semantics: NaN == NaN, +0 != -0) to satisfy `Eq` invariants for `BTreeSet`/`BTreeMap` usage; Position uses `Arc::ptr_eq` (see `value_eq` below for semantic equality)
- `PartialOrd` / `Ord` — discriminant ordering across variants; `f64::total_cmp` for Float (consistent with the `to_bits`-based `Eq`); lexicographic for composites; pointer for Position
- `Clone`, `Debug`

**Non-finite float handling:** Division by zero (integer or float) produces a `RuntimeError`, consistent with the design doc's rule that NaN and infinity are not producible by the language. The total-order-based `Eq`/`Ord` impls (`to_bits`, `total_cmp`) exist as a defensive safety net — if a non-finite float somehow enters the value space (which would be an interpreter bug), it will order deterministically rather than panic. The DSL's type system does not expose float-keyed collections, so the total-order edge cases are unlikely to surface in practice.

**Semantic value comparison (`eval.rs`):**

All runtime equality checks (BinOp `==`/`!=`, pattern matching, trigger binding comparisons, composite value equality) go through a `value_eq` helper instead of `Value::eq`:

```rust
fn value_eq(env: &Env, a: &Value, b: &Value) -> bool
```

This walks composite structures recursively. Special cases:
- **Position** leaf values: delegates to `env.state.position_eq(a, b)`.
- **Float** leaf values: uses standard `f64` equality (`==`), which treats `-0.0 == +0.0` and `NaN != NaN`. This gives user-expected semantics. (The `to_bits`-based `Eq` on `Value` is only for `BTreeSet`/`BTreeMap` structural invariants and is never used for runtime equality checks.)
- All other leaf values: falls through to `Value::eq`.

This ensures consistent equality semantics regardless of the comparison path — `==` in user code, pattern match arms, and trigger binding checks all use the same logic.

### 1.2 Effects and responses (`effect.rs`)

Direct translation from design doc Section 2. All effect variants, all response variants, `Step` enum, `EffectHandler` trait, `EffectKind` discriminant enum, plus supporting types.

`EffectKind` is a fieldless enum mirroring `Effect` variant names (e.g., `MutateField`, `ApplyCondition`, `RollDice`, `ActionStarted`, etc.). Used by `StateAdapter::pass_through` (Phase 7.1) to configure which mutation effects are forwarded to the inner handler vs. intercepted locally.

Supporting types:

```rust
pub enum FieldPathSegment { Field(String), Index(Value) }
pub enum ActionKind { Action, Reaction { event: String, trigger: Value } }
pub enum ModifySource { Condition(String), Option(String) }
pub enum Phase { Phase1, Phase2 }
pub struct FieldChange { pub name: String, pub old: Value, pub new: Value }
```

### 1.3 State traits (`state.rs`)

```rust
pub struct EntityRef(pub u64);

pub struct ActiveCondition {
    pub id: u64,
    pub name: String,
    pub bearer: EntityRef,
    pub gained_at: u64,
    pub duration: Value,
}

pub trait StateProvider {
    fn read_field(&self, entity: &EntityRef, field: &str) -> Option<Value>;
    fn read_conditions(&self, entity: &EntityRef) -> Option<Vec<ActiveCondition>>;
    fn read_turn_budget(&self, entity: &EntityRef) -> Option<BTreeMap<String, Value>>;
    fn read_enabled_options(&self) -> Vec<String>;
    fn position_eq(&self, a: &Value, b: &Value) -> bool;
    fn distance(&self, a: &Value, b: &Value) -> Option<i64>;
}
```

`distance` is on `StateProvider` alongside `position_eq` — both are host-delegated operations on opaque `Position` values. Returns `Option` to signal invalid inputs.

```rust
pub trait WritableState: StateProvider {
    fn write_field(&mut self, entity: &EntityRef, path: &[FieldPathSegment], value: Value);
    fn add_condition(&mut self, entity: &EntityRef, cond: ActiveCondition);
    fn remove_condition(&mut self, entity: &EntityRef, name: &str);
    fn write_turn_field(&mut self, entity: &EntityRef, field: &str, value: Value);
}
```

### Phase 1 deliverable

All types compile. Unit tests for Value equality, ordering, and construction.

---

## Phase 2: Interpreter Core & Expression Evaluation

**Files:** `lib.rs`, `eval.rs`

**Goal:** Evaluate all `ExprKind` variants in isolation (no function calls yet — those come in Phase 4).

### 2.1 Interpreter and execution environment

```rust
pub struct Interpreter<'p> {
    program: &'p Program,
    type_env: &'p TypeEnv,
    index: DeclIndex<'p>,
}
```

`Interpreter::new` returns `Result<Self, RuntimeError>`. Construction fails if any `DeclKind::Move` nodes remain in the program — this catches callers who forgot to run `lower_moves` before checking, turning a potential runtime trap into an explicit construction error. (In practice, the checker would already have rejected unlowered moves, so this is a belt-and-suspenders check.)

`DeclIndex` is built once at construction. It walks `Program.items → TopLevel::System → system.decls` and indexes every declaration by name for O(1) lookup:

```rust
struct DeclIndex<'p> {
    actions: HashMap<&'p str, &'p ActionDecl>,
    derives: HashMap<&'p str, &'p FnDecl>,
    mechanics: HashMap<&'p str, &'p FnDecl>,
    reactions: HashMap<&'p str, &'p ReactionDecl>,
    conditions: HashMap<&'p str, &'p ConditionDecl>,
    events: HashMap<&'p str, &'p EventDecl>,
    prompts: HashMap<&'p str, &'p PromptDecl>,
    options: HashMap<&'p str, &'p OptionDecl>,
}
```

`DeclIndex` borrows from `Program` with the same lifetime `'p`, so `Interpreter` can own it.

The mutable execution environment is separate:

```rust
struct Env<'a, 'p> {
    state: &'a dyn StateProvider,
    handler: &'a mut dyn EffectHandler,
    interp: &'a Interpreter<'p>,
    scopes: Vec<Scope>,
    turn_actor: Option<EntityRef>,  // set during action/reaction execution
}

struct Scope {
    bindings: HashMap<String, Value>,
}
```

`Env` is created fresh for each public API call and destroyed when it completes.

### 2.2 Expression evaluator (`eval.rs`)

```rust
fn eval_expr(env: &mut Env, expr: &Spanned<ExprKind>) -> Result<Value, RuntimeError>
```

Implementation order, building on dependencies:

| Priority | Variant | Notes |
|----------|---------|-------|
| 1 | `IntLit`, `StringLit`, `BoolLit`, `NoneLit` | Direct Value construction |
| 2 | `DiceLit` | Construct `Value::DiceExpr` |
| 3 | `Paren` | Evaluate inner |
| 4 | `Ident` | Scope lookup; fall through to enum type namespace for qualified access |
| 5 | `UnaryOp` | `Neg` (Int/Float), `Not` (Bool) |
| 6 | `BinOp` | Arithmetic, comparison, logical, `in`. Special cases below. |
| 7 | `FieldAccess` | Entity fields via `state.read_field()`; struct/enum variant fields; RollResult built-in fields; turn budget fields (handled by Struct arm — turn budget is `Value::Struct { name: "TurnBudget", .. }`) |
| 8 | `Index` | List by Int index (negative indexes from end, e.g. `list[-1]` is last element); Map by key |
| 9 | `ListLit` | Evaluate elements, construct `Value::List` |
| 10 | `StructLit` | Evaluate field values, construct `Value::Struct` |
| 11 | `If` | Evaluate condition, branch |
| 12 | `PatternMatch` | Match scrutinee against arms |
| 13 | `GuardMatch` | Evaluate guards in order |
| 14 | `Call` | Stub returning `RuntimeError` — real dispatch in Phase 4 |

**BinOp special cases:**
- `RollResult` coerces to `Int` (via `.total`) in arithmetic/comparison contexts
- Equality (`==`, `!=`): use `value_eq(env, &lhs, &rhs)` for all comparisons, which handles Position delegation to `state.position_eq()` and recursive composite comparison
- `Int / Int` → `Float` (not integer division)
- `in` operator: check membership in List, Set, or Map keys (uses `value_eq` for element comparison)
- **Integer overflow:** All integer arithmetic (`+`, `-`, `*`, unary `-`) uses checked operations (`checked_add`, `checked_sub`, `checked_mul`, `checked_neg`). Overflow produces a `RuntimeError` ("integer overflow in <op>"). Division cannot overflow since `Int / Int` promotes to `Float`.

**Pattern matching** needs a helper:

```rust
fn match_pattern(
    env: &Env,
    pattern: &PatternKind,
    value: &Value,
    bindings: &mut HashMap<String, Value>,
) -> bool
```

Takes `env` so literal comparisons can route through `value_eq`. Handles: `Wildcard`, `IntLit`, `StringLit`, `BoolLit`, `Ident` (binding), `QualifiedVariant`, `QualifiedDestructure`, `BareDestructure`.

### Phase 2 deliverable

All expression variants except `Call` evaluate correctly. Tests for each variant using a mock `StateProvider` and a no-op `EffectHandler`.

---

## Phase 3: Statement Execution

**Files:** `exec.rs`

**Goal:** Execute blocks and statements. LValue resolution emits mutation effects.

### 3.1 Block and statement execution

```rust
fn exec_block(env: &mut Env, block: &Block) -> Result<Value, RuntimeError>
fn exec_stmt(env: &mut Env, stmt: &Spanned<StmtKind>) -> Result<Value, RuntimeError>
```

`exec_block` pushes a scope, executes statements in order, pops scope. Returns the value of the last expression-statement (or `Value::None` if the last statement is a let/assign).

### 3.2 Statements

**Let:** Evaluate RHS, bind `name → value` in current scope.

**Expr:** Evaluate expression, return value.

**Assign:** The complex one. Steps:

1. Evaluate RHS expression.
2. Resolve LValue root (`lvalue.root`):
   - If root is `turn` → turn budget mutation path
   - If root resolves to `Value::Entity(ref)` → entity field mutation path
   - Otherwise → local variable mutation path
3. Apply segments (`lvalue.segments`):
   - **Entity path:** Convert `LValueSegment::Field`/`Index` to `Vec<FieldPathSegment>`. Emit `MutateField` effect. For resource-typed fields, look up bounds from `TypeEnv` and include in effect.
   - **Turn path:** The first segment must be `Field(name)`. Emit `MutateTurnField` effect.
   - **Local path:** Navigate into the local Value in-place. For `Field(f)` on a Struct, mutate `fields[f]`. For `Index(i)` on a List, mutate `list[i]`. For `Index(k)` on a Map, mutate `map[k]`. Apply `AssignOp` (=, +=, -=).

   **Error rules for local path mutations:**
   - List index out of bounds → `RuntimeError` ("list index N out of bounds, length M"). Negative indices count from the end (`-1` is the last element, `-len` is the first); indices beyond `-len` are out of bounds.
   - Map missing key with `=` → insert new entry (create on assign)
   - Map missing key with `+=` / `-=` → `RuntimeError` ("cannot apply += to absent map key 'K'")
   - Struct missing field → `RuntimeError` (should not occur in checked programs — internal error)
   - `+=` / `-=` on incompatible types (e.g., `Int += String`) → `RuntimeError` ("cannot apply += to Int and String")

### 3.3 AssignOp application

```rust
fn apply_assign_op(op: AssignOp, current: Value, rhs: Value) -> Result<Value, RuntimeError>
```

- `Eq` → replace with rhs
- `PlusEq` → current + rhs (Int+Int, Float+Float). Integer addition uses `checked_add`; overflow produces `RuntimeError`.
- `MinusEq` → current - rhs (Int, Float). Integer subtraction uses `checked_sub`; overflow produces `RuntimeError`.

For entity mutations, `current` is not available locally (the host owns it). The effect carries `op` and `value` and the host applies it. For local mutations, the interpreter applies `op` directly.

### Phase 3 deliverable

Blocks, lets, and assignments work. Entity field assignments emit `MutateField`. Turn assignments emit `MutateTurnField`. Local variable mutations happen in-place. Tests with a recording `EffectHandler` that captures emitted effects.

---

## Phase 4: Function Calling & Builtins

**Files:** `call.rs`, `builtins.rs`

**Goal:** The `Call` expression variant dispatches to derives, mechanics, prompts, builtins, and enum constructors.

### 4.1 Call dispatch (`call.rs`)

When evaluating `ExprKind::Call { callee, args }`:

1. **Resolve callee syntactically** — function names are not first-class values. Match on `callee.node`:
   - `ExprKind::Ident(name)` → look up `name` in `TypeEnv::functions` (or builtins).
   - `ExprKind::FieldAccess { object, field }` → qualified enum constructor (e.g., `Duration.rounds(3)`).
   - Any other expression → runtime error (the checker rejects these).
2. For function names, get `FnInfo` and dispatch based on `FnInfo::kind`:

| Kind | Dispatch |
|------|----------|
| `Derive` | Bind params, run modify pipeline Phase 1, execute body, run modify pipeline Phase 2, return result |
| `Mechanic` | Same as Derive (mechanics can produce dice effects during body execution) |
| `Prompt` | Evaluate hint/suggest, emit `ResolvePrompt` effect, return response value |
| `Builtin` | Dispatch to builtin implementation |
| `Action` | Resolve receiver from call arguments (see "Receiver handling" below), then dispatch through `execute_action`. Must be inside an action/reaction resolve context — runtime error otherwise (should not occur in checked programs since the checker restricts action calls to resolve blocks). |
| `Reaction` | Unreachable — the checker rejects direct reaction calls (see "Checker prerequisite" below). Reactions are triggered via `what_triggers` + host dispatch, not called from DSL code. If encountered, this is an internal error. |

4. If callee is a qualified enum variant access (e.g., `Duration.rounds(3)`): construct `Value::EnumVariant`.
5. If callee is a bare enum variant with fields (e.g., `rounds(3)` where `rounds` is unambiguous via `variant_to_enum`): construct `Value::EnumVariant`.

### 4.2 Argument binding

```rust
fn bind_args(
    params: &[ParamInfo],
    args: &[Arg],
    env: &mut Env,
) -> Result<Vec<(String, Value)>, RuntimeError>
```

- Match args by name (if `arg.name` is `Some`) or by position.
- Fill missing optional params with default values (evaluate default expressions).

**Receiver handling for action calls:** The checker treats the receiver as the first parameter in the effective parameter list — callers pass it explicitly (by name or position) alongside the other arguments. The interpreter must match this: when dispatching an action call from within a resolve block, the receiver `EntityRef` is extracted from the first effective argument (which must be `Value::Entity`). The remaining arguments bind to the action's declared parameters. `turn_actor` is only used for turn budget access (`turn.actions` etc.), not for implicit receiver resolution.

**Checker prerequisite — reject direct reaction calls:** The checker must reject call expressions that resolve to `FnKind::Reaction`. Reactions are not callable from DSL code — they are triggered by events and dispatched by the host via `Interpreter::execute_reaction`. The checker already builds an effective parameter list for reactions (receiver only), but this should only be used for trigger binding validation, not call checking. Emit a diagnostic: "reactions cannot be called directly; they are triggered by events".

### 4.3 Builtins (`builtins.rs`)

| Builtin | Implementation |
|---------|---------------|
| `floor(x)` | `Float → Int` via `f64::floor` |
| `ceil(x)` | `Float → Int` via `f64::ceil` |
| `min(a, b)` | Compare two `Int` values |
| `max(a, b)` | Compare two `Int` values |
| `distance(a, b)` | Delegate to `state.distance(a, b)`. If `None` is returned (invalid inputs), produce `RuntimeError`. |
| `multiply_dice(expr, factor)` | `factor` must be a positive `Int`; `RuntimeError` if `factor <= 0`. Uses `checked_mul` on `DiceExpr.count`; `RuntimeError` on overflow. Result: `DiceExpr { count: count * factor, .. }` |
| `roll(expr)` | Emit `RollDice` effect, return response as `Value::RollResult` |
| `apply_condition(target, cond, dur)` | Emit `ApplyCondition` effect, return `Value::None` |
| `remove_condition(target, cond)` | Emit `RemoveCondition` effect, return `Value::None` |

`roll` is the key effectful builtin — it emits `RollDice` and expects `Rolled(RollResult)` or `Override(RollResult)` back.

### Phase 4 deliverable

Function calls work end-to-end. A derive that does arithmetic can be called from an expression. A mechanic that calls `roll()` emits `RollDice` and processes the response. Builtins pass their tests. Prompt calls emit `ResolvePrompt`.

---

## Phase 5: Action/Reaction Pipeline

**Files:** `action.rs`

**Goal:** Full action/reaction lifecycle with all gate and decision effects.

### 5.1 Action execution

```rust
pub fn execute_action(
    env: &mut Env,
    action: &ActionDecl,
    actor: EntityRef,
    args: Vec<Value>,
) -> Result<Value, RuntimeError>
```

Pipeline (design doc Section 6):

1. **Emit `ActionStarted`** with `kind: Action`.
   - `Vetoed` → emit `ActionCompleted`, return `Value::None`.
2. **Bind scope**: push scope with receiver + params bound, save previous `turn_actor`, set `turn_actor` to current actor. (Save/restore enables nested action calls without clobbering outer context.) Note: for the public API entry point (`Interpreter::execute_action`), the actor is provided directly. For nested action calls from within a resolve block, the receiver is extracted from the call arguments (see Phase 4.2 "Receiver handling"). Bindings must be established before the requires clause because the checker allows requires expressions to reference receiver, params, and `turn`.
3. **Requires clause** (if present): evaluate expression to Bool, emit `RequiresCheck`.
   - `Override(Bool(true))` forces pass; `Override(Bool(false))` forces fail.
   - If failed: pop scope, restore previous `turn_actor`, emit `ActionCompleted`, return `Value::None` — no cost spent.
4. **Cost deduction**: for each token in `cost.tokens` (declaration order), emit `DeductCost`.
   - Map token → budget_field using the fixed table (`action` → `actions`, etc.).
   - `Acknowledged` → the host is responsible for applying the deduction (Layer 1). `Override(Str(replacement))` → validate replacement is in table, host applies deduction to replacement's field. `Vetoed` → cost waived. **Note:** In Layer 2, the adapter takes over deduction responsibility — the host's handler only decides (acknowledge/override/veto) and the adapter calls `write_turn_field`. See Phase 7.1.
5. **Execute resolve block**: execute body, pop scope, restore previous `turn_actor`.
6. **Emit `ActionCompleted`**.

### 5.2 Reaction execution

```rust
pub fn execute_reaction(
    env: &mut Env,
    reaction: &ReactionDecl,
    reactor: EntityRef,
    event_payload: Value,
) -> Result<Value, RuntimeError>
```

Same structure as action:
1. Emit `ActionStarted` with `kind: Reaction { event, trigger: payload }`.
   - `Vetoed` → emit `ActionCompleted`, return `Value::None`.
2. Bind scope: push scope with receiver + `trigger` bound to event_payload. Save previous `turn_actor`, set to reactor.
3. No requires clause for reactions.
4. Deduct cost.
5. Execute resolve block. Pop scope, restore previous `turn_actor`.
6. Emit `ActionCompleted`.

### Phase 5 deliverable

A full action (with requires, cost, resolve) executes correctly with a scripted `EffectHandler`. Tests cover: requires pass/fail, cost acknowledged/vetoed/overridden, ActionStarted veto, reaction trigger binding.

---

## Phase 6: Modify Pipeline & Events

**Files:** `pipeline.rs`, `event.rs`

**Goal:** Condition/option modifiers rewrite function params and results. Events match triggers and check suppression.

### 6.1 Modify pipeline (`pipeline.rs`)

The 8-step algorithm from design doc Section 5. Called from `call.rs` when dispatching a derive or mechanic call.

```rust
pub struct ModifyContext<'a> {
    pub fn_name: &'a str,
    pub params: Vec<(String, Value)>,
    pub modifiers: Vec<ResolvedModifier<'a>>,
}

pub struct ResolvedModifier<'a> {
    pub source: ModifySource,
    pub clause: &'a ModifyClause,
}
```

**Collecting modifiers:**

1. For each entity-typed param, query `state.read_conditions(entity)`.
2. For each condition, check its `modify` clauses: does the target function name match? Does the binding (e.g., `attacker: bearer`) match when the param value equals the condition's bearer?
3. **Deduplicate:** If multiple entity-typed params reference the same entity, the same condition can be collected more than once. Deduplicate collected condition modifiers by `condition.id` before proceeding. Each `ActiveCondition` carries a unique `id: u64` assigned by the host (or by `GameState` in Layer 3), which distinguishes distinct condition instances even if they share the same name, bearer, and `gained_at`.
4. Query `state.read_enabled_options()`. For each enabled option found in `DeclIndex::options`, check its `when_enabled` modify clauses using the same signature matching.
5. Order: condition modifiers by `gained_at` (within a condition: declaration order); option modifiers after all conditions (within an option: declaration order).

**Phase 1 — rewrite inputs:**

For each modifier, evaluate its `ModifyStmt` list in a temporary scope:
- `ParamOverride { name, value }` → evaluate value, update `params[name]`
- `Let { name, value }` → bind in modifier scope
- `If { condition, then, else }` → conditional
- `ResultOverride` → skip (Phase 2 only)
- Emit `ModifyApplied` with Phase 1, listing changed params.

**Phase 2 — rewrite outputs:**

After the function body executes and produces a result:
- `ResultOverride { field, value }` → evaluate value, update `result.field`
- `ParamOverride` → skip (Phase 1 only)
- Emit `ModifyApplied` with Phase 2, listing changed result fields.

### 6.2 Event firing (`event.rs`)

```rust
pub fn what_triggers(
    interp: &Interpreter,
    state: &dyn StateProvider,
    event_name: &str,
    payload: Value,
    candidates: &[EntityRef],
) -> Result<EventResult, RuntimeError>
```

No effects emitted — this is a pure query. Binding expressions are evaluated during matching and must be side-effect-free.

**Checker prerequisite:** The current checker checks trigger bindings inside `BlockKind::ReactionResolve`, which permits dice rolls and mutations. Before implementing this phase, add a new `BlockKind::TriggerBinding` that disallows dice, mutation, turn access, action/reaction calls, **and all other effectful calls (prompts, mechanics)**. Only side-effect-free builtins (`floor`, `ceil`, `min`, `max`, `distance`) are permitted — no derive or mechanic calls, since derives can transitively call effectful functions and there is no purity analysis in v0. Push this block kind around trigger binding expression checking in `check_reaction` (and similarly for suppress binding checking in `check_condition`). This ensures `what_triggers` can remain a pure query by construction — no effect handler is needed and no effects can be emitted during trigger/suppress evaluation.

The host provides `candidates` — the set of entities to consider as potential reactors. This keeps entity enumeration in the host's hands (e.g., the host can filter by proximity, initiative order, or other game-specific criteria).

**Trigger matching:**

1. Scan all reactions in `DeclIndex::reactions` whose `trigger.event_name` matches.
2. For each matching reaction, iterate over `candidates`. For each candidate entity, tentatively bind it as the reaction's receiver and evaluate trigger bindings against event params and fields. Bindings can reference either `EventInfo::params` (positional event arguments) or `EventInfo::fields` (computed fields on the event's synthetic struct type).
3. Binding resolution uses **fill-the-gaps** semantics (matching the checker): all named bindings claim their slots first, then positional bindings fill the remaining unclaimed param slots left-to-right. This is more permissive than strict positional ordering.
   - **Named** (`name: expr`): look up `name` in event params first, then event fields. The value must equal the evaluated expr (where the expr may reference the tentatively-bound receiver, e.g., `actor: reactor`).
   - **Positional** (bare `expr`): fills the next unclaimed param slot (skipping any slots already claimed by named bindings). The param value must equal the evaluated expr.
4. All bindings must match for a given (reaction, candidate) pair. Collect matching pairs.

**Suppression checking:**

For each matched (reaction, reactor) pair, check all conditions on all entity-typed event params and fields:
- For each condition's `suppress` clauses: does the event name match? Are the suppress bindings satisfied? Bindings can reference event params or fields (same lookup as trigger bindings — params first, then fields). Does the binding match (e.g., `entity: bearer` when event param `entity` equals the condition's bearer)?
- If any suppress matches → add to `suppressed` list.
- Otherwise → add to `triggerable` list.

```rust
pub struct EventResult {
    pub suppressed: Vec<ReactionInfo>,
    pub triggerable: Vec<ReactionInfo>,
}

pub struct ReactionInfo {
    pub name: String,
    pub reactor: EntityRef,
}
```

### Phase 6 deliverable

Modify pipeline rewrites params and results. Multiple conditions ordered correctly. Option modifiers layer on top. Events match triggers and check suppression. Comprehensive tests for each sub-step.

---

## Phase 7: Integration Layers

**Files:** `adapter.rs`, `reference_state.rs`

**Goal:** Layer 2 and Layer 3 from design doc Section 7.

### 7.1 StateAdapter — Layer 2 (`adapter.rs`)

**Aliasing design:** The interpreter's public API takes `state: &dyn StateProvider` and `handler: &mut dyn EffectHandler` as separate parameters. `StateAdapter` wraps the `WritableState` in a `RefCell` and implements `StateProvider` directly. Each `StateProvider` method does a short-lived `borrow()` that is dropped before the method returns — since all return types are owned (`Value`, `Vec<ActiveCondition>`, etc.), the `Ref` guard never outlives the call. The `AdaptedHandler` uses `borrow_mut()` the same way — one short-lived mutable borrow per mutation, dropped before returning. Because `RefCell` borrows are scoped to individual trait method calls (not held across execution), they never overlap and cannot panic.

```rust
pub struct StateAdapter<S: WritableState> {
    state: RefCell<S>,
    pass_through: HashSet<EffectKind>,
}

impl<S: WritableState> StateProvider for StateAdapter<S> {
    fn read_field(&self, entity: &EntityRef, field: &str) -> Option<Value> {
        self.state.borrow().read_field(entity, field)
        // Ref<S> dropped here — borrow released before caller resumes
    }
    fn read_conditions(&self, entity: &EntityRef) -> Option<Vec<ActiveCondition>> {
        self.state.borrow().read_conditions(entity)
    }
    // ... all other StateProvider methods follow the same pattern
}

impl<S: WritableState> StateAdapter<S> {
    pub fn new(state: S) -> Self;
    pub fn pass_through(mut self, kind: EffectKind) -> Self;

    /// Execute a closure providing read and write access to the adapted state.
    /// `&self` serves as `&dyn StateProvider` (per-call borrows via RefCell).
    /// An `AdaptedHandler` serves as `&mut dyn EffectHandler` (per-call borrow_mut).
    pub fn run<H: EffectHandler, R>(
        &self,
        inner: &mut H,
        f: impl FnOnce(&dyn StateProvider, &mut dyn EffectHandler) -> R,
    ) -> R;

    pub fn into_inner(self) -> S;
}
```

Layer-2 usage pattern:

```rust
let adapter = StateAdapter::new(my_writable_state);
let mut host_handler = MyHandler::new();

adapter.run(&mut host_handler, |state, handler| {
    interp.execute_action(state, handler, "Attack", actor, args)
})?;

// Recover the state when done
let final_state = adapter.into_inner();
```

Inside `run`, the adapter passes `&self` as `&dyn StateProvider` (it implements the trait) and constructs an `AdaptedHandler` that holds a shared `&StateAdapter<S>` reference for mutations via `borrow_mut()`:

```rust
pub struct AdaptedHandler<'a, S: WritableState, H: EffectHandler> {
    adapter: &'a StateAdapter<S>,  // shared ref — mutations use borrow_mut()
    inner: &'a mut H,
}

impl<S: WritableState, H: EffectHandler> EffectHandler for AdaptedHandler<'_, S, H> {
    fn handle(&mut self, effect: Effect) -> Response {
        // Intercepted mutations: self.adapter.state.borrow_mut().write_field(...)
        // RefMut<S> dropped before returning — no overlap with reads
        /* ... */
    }
}
```

**Mutation handling rules:**

There are three distinct paths depending on the effect category and pass-through configuration:

1. **Intercepted mutation** (mutation effect, NOT in `pass_through` set): The adapter applies the mutation locally via `WritableState` methods and returns `Response::Acknowledged` without forwarding to the inner handler. The host never sees these effects.

2. **Pass-through mutation** (mutation effect, IN `pass_through` set): The adapter forwards the effect to the inner handler. Based on the response:
   - `Acknowledged` → adapter also applies the mutation locally (keeps adapter state in sync with the host's intent).
   - `Override(value)` → adapter applies the overridden value locally.
   - `Vetoed` → adapter does nothing (no local mutation).

3. **Non-mutation effects** (informational, decision, dice): Always forwarded to the inner handler. The adapter does not intercept these.

`apply_mutation` dispatches to `WritableState` methods:
- `MutateField` → `write_field` (applying op + bounds clamping)
- `ApplyCondition` → `add_condition`
- `RemoveCondition` → `remove_condition`
- `MutateTurnField` → `write_turn_field` (applying op)

`DeductCost` is always passed through (it's a decision effect, not a mutation — the host must decide whether to acknowledge, override, or veto). The adapter takes over deduction responsibility from the host: the host's inner handler only makes the decision, and the adapter applies the actual state mutation. On `Acknowledged` from the inner handler, the adapter calls `write_turn_field` to decrement. On `Override(replacement)`, it decrements the replacement token's field. On `Vetoed`, no mutation. The host's inner handler **must not** also decrement — the adapter owns the `WritableState` and is the sole writer.

**Design doc update required:** The design doc (`design/interpreter.md`, line 104) currently says "the host decrements `budget_field` by 1" for `DeductCost` on `Acknowledged`. This describes Layer 1 semantics (bare `EffectHandler`, no adapter). At Layer 2, the adapter owns the `WritableState` and is the sole writer — the host's handler only makes the decision. The design doc should be updated to clarify that line 104 applies to Layer 1 only, and that at Layer 2 the adapter handles the mutation (consistent with line 475 which already says the adapter "calls `write_turn_field` on `Acknowledged`").

### 7.2 GameState — Layer 3 (`reference_state.rs`)

```rust
pub struct GameState {
    entities: HashMap<u64, EntityState>,
    conditions: HashMap<u64, Vec<ActiveCondition>>,
    turn_budgets: HashMap<u64, BTreeMap<String, Value>>,
    enabled_options: HashSet<String>,
    next_entity_id: u64,
    next_condition_ts: u64,
}

struct EntityState {
    name: String,
    fields: HashMap<String, Value>,
}
```

Public API:

```rust
impl GameState {
    pub fn new() -> Self;
    pub fn add_entity(&mut self, name: &str, fields: HashMap<String, Value>) -> EntityRef;
    pub fn set_turn_budget(&mut self, entity: &EntityRef, budget: BTreeMap<String, Value>);
    pub fn apply_condition(&mut self, entity: &EntityRef, name: &str, duration: Value);
    pub fn enable_option(&mut self, name: &str);
    pub fn disable_option(&mut self, name: &str);
}

impl StateProvider for GameState { /* ... */ }
impl WritableState for GameState { /* ... */ }
```

`position_eq` and `distance` on `GameState` need a concrete Position representation. `GameState` uses a simple grid position `(i64, i64)` as default, with Chebyshev distance (`max(|dx|, |dy|)`) — this matches D&D 5e's standard movement rules where diagonal movement costs the same as orthogonal. The result is always a non-negative integer, so no rounding is needed. Hosts using Layer 3 that need different Position representations or distance metrics can wrap `GameState` with their own `StateProvider`.

### Phase 7 deliverable

`StateAdapter` correctly auto-applies mutation effects and passes through configured kinds. `GameState` supports entity CRUD, condition management, option toggling. Integration test: full action execution using `GameState` + `StateAdapter`.

---

## Phase 8: Public API

**Files:** `lib.rs`

**Goal:** Clean public API surface matching design doc Section 6.

### 8.1 Callback API (primary)

```rust
impl<'p> Interpreter<'p> {
    pub fn new(program: &'p Program, type_env: &'p TypeEnv) -> Result<Self, RuntimeError>;

    pub fn execute_action(
        &self, state: &dyn StateProvider, handler: &mut dyn EffectHandler,
        name: &str, actor: EntityRef, args: Vec<Value>,
    ) -> Result<Value, RuntimeError>;

    pub fn execute_reaction(
        &self, state: &dyn StateProvider, handler: &mut dyn EffectHandler,
        name: &str, reactor: EntityRef, event_payload: Value,
    ) -> Result<Value, RuntimeError>;

    pub fn evaluate_mechanic(
        &self, state: &dyn StateProvider, handler: &mut dyn EffectHandler,
        name: &str, args: Vec<Value>,
    ) -> Result<Value, RuntimeError>;

    pub fn evaluate_derive(
        &self, state: &dyn StateProvider, handler: &mut dyn EffectHandler,
        name: &str, args: Vec<Value>,
    ) -> Result<Value, RuntimeError>;

    pub fn what_triggers(
        &self, state: &dyn StateProvider,
        name: &str, payload: Value, candidates: &[EntityRef],
    ) -> Result<EventResult, RuntimeError>;
}
```

All entry points except `what_triggers` take a handler because the modify pipeline can emit `ModifyApplied` informational effects even for pure derives. `what_triggers` takes `candidates` — the host-provided set of entities to consider as potential reactors (see Phase 6.2).

**Layer-2 callers** use `StateAdapter::run()` which provides both the `&dyn StateProvider` and `&mut dyn EffectHandler` to a closure, managing `RefCell` borrow discipline internally (see Phase 7.1).

### 8.2 RuntimeError

```rust
pub struct RuntimeError {
    pub message: String,
    pub span: Option<Span>,  // AST location if available
}
```

Categories:
- State sync errors: `read_field` returned `None` for a field the checker says exists
- Protocol errors: host sent invalid response for an effect (e.g., `Vetoed` on `RollDice`)
- Arithmetic errors: division by zero, integer overflow
- Internal errors: unreachable states that indicate checker bugs

---

## Testing Strategy

### Test infrastructure

```rust
/// Records effects and replays scripted responses.
struct ScriptedHandler {
    script: VecDeque<Response>,
    log: Vec<Effect>,
}

impl EffectHandler for ScriptedHandler {
    fn handle(&mut self, effect: Effect) -> Response {
        self.log.push(effect);
        self.script.pop_front().unwrap_or(Response::Acknowledged)
    }
}

/// Minimal StateProvider for tests.
struct TestState {
    fields: HashMap<(u64, String), Value>,
    conditions: HashMap<u64, Vec<ActiveCondition>>,
    turn_budgets: HashMap<u64, BTreeMap<String, Value>>,
    enabled_options: HashSet<String>,
}
```

### Per-phase tests

| Phase | Test focus |
|-------|-----------|
| 0 | Move lowering: parse a move, lower, pass through checker, verify synthesized mechanic + action structure. Checker validates synthesized AST. |
| 1 | Value equality, ordering, construction. Effect/Response construction. |
| 2 | Each ExprKind variant. Pattern matching via `value_eq`. Type coercions. Position equality delegation. |
| 3 | Let bindings. Local/entity/turn assignments. LValue path resolution. Local mutation error cases (list OOB, map missing key with +=/-=). |
| 4 | Derive/mechanic calls. Named args. Defaults. Builtins. Prompts. |
| 5 | Action pipeline steps. Requires pass/fail. Cost deduction. Veto. |
| 6 | Modify Phase 1+2. Modifier ordering. Suppression. Trigger matching with candidate iteration. |
| 7 | StateAdapter intercepted vs. pass-through vs. forward-then-sync. GameState CRUD. |
| 8 | End-to-end: parse → check → interpret. Response-validity matrix: verify `RuntimeError` for invalid responses (e.g., `Vetoed` on `RollDice`, wrong type in `Override`). |

### Integration tests

Use DSL source strings as test fixtures: parse, check, then interpret. Start with small focused programs and build toward exercising the `spec/v0/04_dnd5e_example.ttrpg` patterns (attack rolls with advantage/disadvantage, condition modifiers, reaction triggers).

---

## Implementation Order

```
Phase 0 (atomic PR — AST prereq + checker fixes + lowering):
  - Add trigger_text: Option<String> and synthetic: bool to ActionDecl; add synthetic: bool to FnDecl
  - Reserve __ prefix in collect pass (exempt synthetic == true declarations)
  - Remove FnKind::Move; replace DeclKind::Move handling with diagnostics
  - Reject direct reaction calls in checker
  - Reject Position in set element / map key types
  - Add BlockKind::TriggerBinding (prerequisite for Phase 6)
  - Implement lower_moves
   ↓
Phase 1: Foundation Types
   ↓
Phase 2: Expression Evaluation
   ↓
Phase 3: Statement Execution
   ↓
Phase 4: Function Calling & Builtins
   ↓
Phase 5: Action/Reaction Pipeline
   ↓
Phase 6: Modify Pipeline & Events
   ↓
Phase 7: Integration Layers ←── can start after Phase 1
   ↓
Phase 8: Public API
```

Phase 0 is delivered as a single atomic PR containing all AST, checker, and lowering changes. This avoids transient breakage — removing `FnKind::Move` and replacing `DeclKind::Move` handling with diagnostics in the same PR as the lowering function ensures no intermediate state where the checker references a nonexistent `FnKind` variant. The PR includes: (1) `ActionDecl::trigger_text` and `ActionDecl::synthetic` AST additions, plus `FnDecl::synthetic`; (2) reserving the `__` prefix in the collect pass (exempting `synthetic == true` declarations); (3) removing `FnKind::Move` and replacing `collect_move`/`check_move` with diagnostic emissions; (4) rejecting direct reaction calls; (5) rejecting `Position` in set element / map key types; (6) adding `BlockKind::TriggerBinding`; and (7) `lower_moves` implementation. Phase 0 is purely syntactic — it operates on the raw AST only, has no `TypeEnv` dependency, and runs in the pipeline as: parse → lower → check → interpret. Phase 7 (integration layers) depends only on Phase 1 types and can be developed in parallel with Phases 2–6. All other phases are sequential.

---

## Design Decisions

### Callback-only execution model

The callback `EffectHandler` is the sole execution API. Rationale: the rest of the codebase is synchronous Rust; a callback model avoids async infection and thread requirements. If the host needs async behavior, it blocks inside `handle`. A pull-based step-loop API (where the host calls `step()`/`respond()` to drive execution) is deferred to a future version — implementing it correctly requires either `std::thread::spawn` with `'static` ownership (incompatible with the borrowed `&'p Program` design) or a state-machine transformation of the tree-walking evaluator, both of which are out of scope for v0.

### DeclIndex at construction

Building the declaration index once at `Interpreter::new` avoids repeated linear scans through the AST during execution. The index traverses `Program.items → TopLevel::System → system.decls` to find all declarations. It borrows from the `Program` with the same lifetime, so no cloning is needed.

### Position via Arc

`Arc<dyn Any + Send + Sync>` rather than `Box<dyn Any>` enables `Value: Clone + Send` without sacrificing opacity. The `Send + Sync` bounds future-proof for potential multi-threaded host integrations. The `Arc` overhead is negligible given the design doc's "performance is a non-goal" stance.

### Position equality via `value_eq`

`PartialEq` on `PositionValue` uses `Arc::ptr_eq` — fast and correct for the common case (same allocation). All runtime equality paths (BinOp `==`/`!=`, pattern matching, trigger binding, composite equality) route through `value_eq(env, &a, &b)` which delegates Position leaves to `StateProvider::position_eq`. This avoids the semantic inconsistency of `PartialEq` returning `false` for logically-equal positions while keeping `Value: Eq` derivable.

### Layer-2 aliasing

`StateAdapter` uses `RefCell<S>` with per-call borrow discipline. Each `StateProvider` method does `borrow()` → read → drop, and each `AdaptedHandler` mutation does `borrow_mut()` → write → drop. Because all `StateProvider` methods return owned values (not references into the `RefCell`), the `Ref` guard is always dropped before the caller resumes. This means the `RefCell` borrows are scoped to individual trait method calls, not held across execution, so they never overlap and cannot panic. No `unsafe` is needed. The `run` method takes `&self`, and `AdaptedHandler` holds a shared `&StateAdapter<S>` reference.

### Event reactor enumeration

`what_triggers` takes `candidates: &[EntityRef]` from the host rather than enumerating entities itself. This keeps `StateProvider` simple (no `all_entities()` method) and gives hosts control over filtering (e.g., by proximity, initiative order, faction).

### Reserved `__` prefix

The `__` prefix is reserved for synthetic/internal names: `__event_<name>` (synthetic struct types for event payloads) and `__{move}_roll` (synthesized move mechanics). The checker rejects names starting with `__` on declarations where `synthetic == false` — this covers all declaration kinds (structs, enums, functions, mechanics, derives, actions, reactions, events, conditions, options) to prevent user-declared collisions with any current or future synthetic names. Declarations with `synthetic == true` (produced by `lower_moves`) are exempt and register normally. Only `FnDecl` and `ActionDecl` carry the `synthetic` flag, since those are the only kinds lowering synthesizes; all other declaration kinds always reject `__`. Entity type names are not independently declared — they derive from struct names, so the struct reservation transitively prevents `Ty::Entity("__*")` from existing. This is critical because the checker's `__event_*` field resolution path matches both `Ty::Struct` and `Ty::Entity`. Because lowering runs before checking, the synthesized `__` names are registered by the checker's own collect pass; the lowering function only checks for move-vs-move collisions within the same pass.

### distance on StateProvider

`distance(Position, Position) -> int` is a builtin in the DSL but operates on opaque host data. Rather than introducing a separate trait or a new effect, it lives on `StateProvider` alongside `position_eq` — both are synchronous host-delegated operations on opaque values.
