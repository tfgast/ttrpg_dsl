# TTRPG DSL Interpreter — Implementation Checklist

Companion to [`interpreter_impl_plan.md`](interpreter_impl_plan.md). Check items off as completed.

---

## Phase 0: Move Lowering (atomic PR)

### AST prerequisites
- [x] Add `synthetic: bool` to `FnDecl` (parser defaults to `false`)
- [x] Add `trigger_text: Option<String>` to `ActionDecl` (parser defaults to `None`)
- [x] Add `synthetic: bool` to `ActionDecl` (parser defaults to `false`)

### Checker prerequisites
- [x] Reject `__` prefix on declarations where `synthetic == false`
- [x] Remove `FnKind::Move` from `FnKind` enum
- [x] Replace `DeclKind::Move` handling in `collect.rs` with diagnostic; delete `collect_move`
- [x] Replace `DeclKind::Move` handling in `check.rs` with diagnostic; delete `check_move`
- [x] Reject direct reaction calls (`FnKind::Reaction` in call position)
- [x] Reject `Position` as set element type (`set<Position>`)
- [x] Reject `Position` as map key type (`map<Position, _>`)
- [x] Add `BlockKind::TriggerBinding` (disallows dice, mutations, turn access, action/reaction/prompt/mechanic calls)
- [x] Push `BlockKind::TriggerBinding` around trigger binding checking in `check_reaction`
- [x] Push `BlockKind::TriggerBinding` around suppress binding checking in `check_condition`

### Lowering implementation (`lower.rs`)
- [x] `lower_moves(program, diags) -> Program` function signature
- [x] Validate outcome set is exactly `{strong_hit, weak_hit, miss}`
- [x] Check for synthetic name collisions (`__{snake}_roll`)
- [x] Synthesize mechanic `FnDecl` with `synthetic: true`
- [x] Synthesize `ActionDecl` with `synthetic: true` and `trigger_text`
- [x] Build resolve block: let-binding + `GuardMatch` with PbtA thresholds
- [x] Replace `DeclKind::Move` with synthesized mechanic + action
- [x] Skip malformed moves (leave as `DeclKind::Move` for checker to catch)

### Tests
- [x] Round-trip: parse move → lower → check → verify no `DeclKind::Move` remains
- [x] Verify trigger text preserved on synthesized action
- [x] Missing/extra/duplicate outcomes produce diagnostics
- [x] Synthetic name collision produces diagnostic
- [x] `__` prefix rejected on user-declared names
- [x] `__` prefix accepted on synthetic declarations
- [x] Direct reaction call rejected by checker
- [x] `set<Position>` rejected by checker
- [x] `map<Position, _>` rejected by checker
- [x] `BlockKind::TriggerBinding` restricts effectful calls

---

## Phase 1: Foundation Types

### Value enum (`value.rs`)
- [x] `Value` enum with all 17 variants
- [x] `DiceExpr` struct
- [x] `RollResult` struct
- [x] `TurnBudget` struct
- [x] `DurationValue` enum
- [x] `PositionValue` wrapper (`Arc<dyn Any + Send + Sync>`)
- [x] `PartialEq`/`Eq` on `Value` (Float via `to_bits`, Position via `Arc::ptr_eq`)
- [x] `PartialOrd`/`Ord` on `Value` (Float via `total_cmp`, Position via pointer)
- [x] `Clone`, `Debug` on `Value`

### Effects and responses (`effect.rs`)
- [x] `Effect` enum (all variants from design doc Section 2)
- [x] `Response` enum
- [x] `Step` enum
- [x] `EffectHandler` trait
- [x] `EffectKind` fieldless discriminant enum
- [x] Supporting types: `FieldPathSegment`, `ActionKind`, `ModifySource`, `Phase`, `FieldChange`

### State traits (`state.rs`)
- [x] `EntityRef(u64)` struct
- [x] `ActiveCondition` struct (with `id: u64`)
- [x] `StateProvider` trait (6 methods including `position_eq`, `distance`)
- [x] `WritableState` trait (4 methods)

### RuntimeError (`lib.rs`)
- [x] `RuntimeError` struct with `message` and `span: Option<Span>`

### Tests
- [x] Value equality: Int, Float, Bool, Str, None
- [x] Value equality: composites (List, Set, Map, Struct, EnumVariant)
- [x] Value ordering: cross-variant discriminant ordering
- [x] Float `to_bits` equality (NaN == NaN, +0 != -0 for structural)
- [x] PositionValue `Arc::ptr_eq` equality
- [x] Effect/Response construction

---

## Phase 2: Interpreter Core & Expression Evaluation

### Interpreter structure (`lib.rs`)
- [ ] `Interpreter` struct with `program`, `type_env`, `index`
- [ ] `DeclIndex` struct with 8 `HashMap` fields
- [ ] `Interpreter::new` — build `DeclIndex`, reject surviving `DeclKind::Move`
- [ ] `Env` struct with `state`, `handler`, `interp`, `scopes`, `turn_actor`
- [ ] `Scope` struct with `bindings: HashMap<String, Value>`

### Expression evaluator (`eval.rs`)
- [ ] `eval_expr` dispatcher
- [ ] `IntLit`, `StringLit`, `BoolLit`, `NoneLit`
- [ ] `DiceLit` → `Value::DiceExpr`
- [ ] `Paren`
- [ ] `Ident` — scope lookup + enum type namespace fallback
- [ ] `UnaryOp` — `Neg` (Int/Float), `Not` (Bool)
- [ ] `BinOp` — arithmetic (`+`, `-`, `*`, `/`)
- [ ] `BinOp` — comparison (`<`, `<=`, `>`, `>=`)
- [ ] `BinOp` — equality (`==`, `!=`) via `value_eq`
- [ ] `BinOp` — logical (`&&`, `||`)
- [ ] `BinOp` — `in` operator (List, Set, Map)
- [ ] `BinOp` — RollResult coercion to Int in arithmetic/comparison
- [ ] `BinOp` — `Int / Int` → Float promotion
- [ ] `BinOp` — division by zero → RuntimeError
- [ ] `BinOp` — checked integer overflow for `+`, `-`, `*`
- [ ] `FieldAccess` — entity fields via `state.read_field()`
- [ ] `FieldAccess` — struct fields
- [ ] `FieldAccess` — enum variant fields
- [ ] `FieldAccess` — RollResult built-in fields (`.total`, `.unmodified`, `.dice`, `.kept`)
- [ ] `FieldAccess` — TurnBudget fields
- [ ] `Index` — List by Int
- [ ] `Index` — Map by key
- [ ] `ListLit`
- [ ] `StructLit`
- [ ] `If` — condition + branches
- [ ] `PatternMatch` — scrutinee + arms
- [ ] `GuardMatch` — guard conditions in order
- [ ] `Call` — stub returning RuntimeError (real dispatch in Phase 4)

### Semantic equality (`eval.rs`)
- [ ] `value_eq(env, a, b)` helper
- [ ] Float: standard `f64 ==` (-0.0 == +0.0)
- [ ] Position: delegate to `state.position_eq()`
- [ ] Composite: recursive walk

### Pattern matching (`eval.rs`)
- [ ] `match_pattern` helper
- [ ] `Wildcard`
- [ ] `IntLit`, `StringLit`, `BoolLit`
- [ ] `Ident` (binding)
- [ ] `QualifiedVariant`
- [ ] `QualifiedDestructure`
- [ ] `BareDestructure`

### Tests
- [ ] Each literal type evaluates correctly
- [ ] Arithmetic on Int, Float, mixed
- [ ] Comparison operators
- [ ] Equality via `value_eq` (including Float -0.0, Position delegation)
- [ ] Logical short-circuit
- [ ] `in` operator on List, Set, Map
- [ ] Integer overflow produces RuntimeError
- [ ] Division by zero produces RuntimeError
- [ ] Field access on entities, structs, RollResult, TurnBudget
- [ ] Index on List (valid + out-of-bounds), Map (present + absent)
- [ ] If/else branching
- [ ] Pattern match: all pattern kinds
- [ ] Guard match: first-matching semantics

---

## Phase 3: Statement Execution

### Block and statement execution (`exec.rs`)
- [ ] `exec_block` — push scope, execute stmts, pop scope, return last value
- [ ] `exec_stmt` dispatcher
- [ ] `Let` — evaluate RHS, bind in current scope
- [ ] `Expr` — evaluate and return

### Assignment (`exec.rs`)
- [ ] LValue root resolution (turn / entity / local)
- [ ] Entity path: convert segments to `FieldPathSegment`, emit `MutateField`
- [ ] Entity path: include resource bounds from `TypeEnv` in effect
- [ ] Turn path: emit `MutateTurnField`
- [ ] Local path: navigate into struct fields
- [ ] Local path: navigate into list by index
- [ ] Local path: navigate into map by key
- [ ] `AssignOp` application (=, +=, -=)
- [ ] `apply_assign_op` — checked overflow for `+=`, `-=`

### Error cases
- [ ] List index out of bounds → RuntimeError
- [ ] Map missing key with `=` → insert
- [ ] Map missing key with `+=`/`-=` → RuntimeError
- [ ] Struct missing field → RuntimeError (internal)
- [ ] `+=`/`-=` on incompatible types → RuntimeError

### Tests
- [ ] Let bindings visible in scope
- [ ] Nested scopes: shadowing and isolation
- [ ] Entity field assignment emits `MutateField`
- [ ] Turn assignment emits `MutateTurnField`
- [ ] Local struct field mutation
- [ ] Local list index mutation
- [ ] Local map key mutation (insert + update)
- [ ] All error cases produce correct RuntimeError messages

---

## Phase 4: Function Calling & Builtins

### Call dispatch (`call.rs`)
- [ ] Resolve callee: `Ident` → function lookup
- [ ] Resolve callee: `FieldAccess` → qualified enum constructor
- [ ] Resolve callee: other expression → RuntimeError
- [ ] Dispatch `Derive` — bind params, modify Phase 1, body, modify Phase 2
- [ ] Dispatch `Mechanic` — same as Derive
- [ ] Dispatch `Prompt` — evaluate hint/suggest, emit `ResolvePrompt`
- [ ] Dispatch `Builtin` — route to builtin impl
- [ ] Dispatch `Action` — extract receiver, call `execute_action`
- [ ] Dispatch `Reaction` — unreachable (internal error)
- [ ] Qualified enum variant construction
- [ ] Bare enum variant construction (via `variant_to_enum`)

### Argument binding (`call.rs`)
- [ ] `bind_args` — positional matching
- [ ] `bind_args` — named matching
- [ ] `bind_args` — default value evaluation for optional params
- [ ] Receiver handling: extract from first effective argument

### Builtins (`builtins.rs`)
- [ ] `floor(Float) -> Int`
- [ ] `ceil(Float) -> Int`
- [ ] `min(Int, Int) -> Int`
- [ ] `max(Int, Int) -> Int`
- [ ] `distance(Position, Position) -> Int` via `state.distance()`
- [ ] `multiply_dice(DiceExpr, Int) -> DiceExpr` (checked, factor > 0)
- [ ] `roll(DiceExpr)` → emit `RollDice`, process response
- [ ] `apply_condition(Entity, String, Duration)` → emit `ApplyCondition`
- [ ] `remove_condition(Entity, String)` → emit `RemoveCondition`

### Tests
- [ ] Derive call: arithmetic body returns correct value
- [ ] Mechanic call: body with `roll()` emits `RollDice`
- [ ] Prompt call: emits `ResolvePrompt` with hint/suggest
- [ ] Named args, positional args, default values
- [ ] Each builtin: correct result or effect
- [ ] `multiply_dice`: factor <= 0 → RuntimeError, overflow → RuntimeError
- [ ] `roll`: processes `Rolled` and `Override` responses
- [ ] Enum variant construction (qualified + bare)

---

## Phase 5: Action/Reaction Pipeline

### Action execution (`action.rs`)
- [ ] `execute_action` function
- [ ] Emit `ActionStarted` (kind: Action)
- [ ] Handle `Vetoed` → emit `ActionCompleted`, return None
- [ ] Bind scope: receiver + params
- [ ] Save/restore `turn_actor`
- [ ] Requires clause: evaluate, emit `RequiresCheck`
- [ ] Requires: `Override(true)` forces pass, `Override(false)` forces fail
- [ ] Requires fail: pop scope, restore turn_actor, emit `ActionCompleted`
- [ ] Cost deduction: emit `DeductCost` per token
- [ ] Cost: `Acknowledged` → host decrements
- [ ] Cost: `Override(replacement)` → validate + apply replacement
- [ ] Cost: `Vetoed` → waived
- [ ] Execute resolve block
- [ ] Emit `ActionCompleted`

### Reaction execution (`action.rs`)
- [ ] `execute_reaction` function
- [ ] Emit `ActionStarted` (kind: Reaction)
- [ ] Bind scope: receiver + trigger payload
- [ ] Save/restore `turn_actor`
- [ ] Cost deduction (same as action)
- [ ] Execute resolve block
- [ ] Emit `ActionCompleted`

### Tests
- [ ] Full action: requires pass → cost → resolve
- [ ] Requires fail: no cost spent, action completed
- [ ] ActionStarted veto: immediate completion
- [ ] Cost acknowledged / vetoed / overridden
- [ ] Nested action calls: turn_actor save/restore
- [ ] Reaction: trigger payload bound correctly
- [ ] Reaction: cost deduction works

---

## Phase 6: Modify Pipeline & Events

### Modify pipeline (`pipeline.rs`)
- [ ] `ModifyContext` and `ResolvedModifier` structs
- [ ] Collect modifiers from conditions (query `read_conditions`)
- [ ] Signature matching: function name + binding match
- [ ] Deduplicate by `condition.id`
- [ ] Collect modifiers from enabled options
- [ ] Order: conditions by `gained_at`, then options; declaration order within
- [ ] Phase 1 — rewrite inputs: `ParamOverride`, `Let`, `If`
- [ ] Phase 1 — emit `ModifyApplied` with changed params
- [ ] Phase 2 — rewrite outputs: `ResultOverride`
- [ ] Phase 2 — emit `ModifyApplied` with changed fields

### Event firing (`event.rs`)
- [ ] `fire_event` function (pure query, no effects)
- [ ] `EventResult` and `ReactionInfo` structs
- [ ] Scan reactions by event name
- [ ] Iterate candidates for each matching reaction
- [ ] Trigger binding: named bindings (params first, then fields)
- [ ] Trigger binding: positional bindings (fill-the-gaps)
- [ ] Binding evaluation: side-effect-free expressions only
- [ ] Suppression checking: scan conditions on entity-typed params/fields
- [ ] Suppress binding matching (same lookup as trigger)
- [ ] Partition into `suppressed` vs `triggerable`

### Tests
- [ ] Modify Phase 1: param overridden correctly
- [ ] Modify Phase 2: result field overridden correctly
- [ ] Multiple conditions ordered by `gained_at`
- [ ] Option modifiers applied after conditions
- [ ] Modifier deduplication (same condition via multiple params)
- [ ] Trigger matching: named bindings
- [ ] Trigger matching: positional bindings
- [ ] Trigger matching: fill-the-gaps semantics
- [ ] Trigger matching: candidate iteration
- [ ] Suppression: condition suppress clause blocks reaction
- [ ] Suppression: non-matching suppress passes through

---

## Phase 7: Integration Layers

### StateAdapter — Layer 2 (`adapter.rs`)
- [ ] `StateAdapter<S: WritableState>` struct with `RefCell<S>` + `HashSet<EffectKind>`
- [ ] `StateProvider` impl for `StateAdapter` (per-call `borrow()`)
- [ ] `AdaptedHandler` struct
- [ ] `EffectHandler` impl for `AdaptedHandler`
- [ ] `StateAdapter::new(state)`
- [ ] `StateAdapter::pass_through(kind)` builder
- [ ] `StateAdapter::run(inner, closure)` — borrow discipline
- [ ] `StateAdapter::into_inner()`
- [ ] Intercepted mutation: apply locally, return `Acknowledged`
- [ ] Pass-through mutation: forward, then sync on `Acknowledged`/`Override`
- [ ] Pass-through mutation: `Vetoed` → no local mutation
- [ ] Non-mutation effects: always forwarded
- [ ] `DeductCost`: always passed through; adapter applies mutation based on response
- [ ] `apply_mutation` dispatch: `MutateField` → `write_field`
- [ ] `apply_mutation` dispatch: `ApplyCondition` → `add_condition`
- [ ] `apply_mutation` dispatch: `RemoveCondition` → `remove_condition`
- [ ] `apply_mutation` dispatch: `MutateTurnField` → `write_turn_field`

### GameState — Layer 3 (`reference_state.rs`)
- [ ] `GameState` struct (entities, conditions, turn_budgets, options, counters)
- [ ] `EntityState` struct
- [ ] `GameState::new()`
- [ ] `GameState::add_entity(name, fields) -> EntityRef`
- [ ] `GameState::set_turn_budget(entity, budget)`
- [ ] `GameState::apply_condition(entity, name, duration)` (auto-assign `id`)
- [ ] `GameState::enable_option(name)` / `disable_option(name)`
- [ ] `StateProvider` impl for `GameState`
- [ ] `WritableState` impl for `GameState`
- [ ] Grid position `(i64, i64)` concrete type
- [ ] `position_eq`: downcast + structural equality
- [ ] `distance`: Chebyshev (`max(|dx|, |dy|)`)

### Tests
- [ ] Adapter: intercepted mutation applies locally
- [ ] Adapter: pass-through mutation forwards + syncs
- [ ] Adapter: pass-through vetoed → no local change
- [ ] Adapter: non-mutation effects forwarded
- [ ] Adapter: `DeductCost` decision + mutation
- [ ] GameState: add entity, read fields
- [ ] GameState: write field, read back
- [ ] GameState: condition add/remove/query
- [ ] GameState: turn budget set/read/write
- [ ] GameState: option enable/disable/query
- [ ] GameState: position equality and Chebyshev distance
- [ ] Integration: full action via `GameState` + `StateAdapter`

---

## Phase 8: Public API

### API surface (`lib.rs`)
- [ ] `Interpreter::new(program, type_env) -> Result<Self, RuntimeError>`
- [ ] `Interpreter::execute_action(state, handler, name, actor, args)`
- [ ] `Interpreter::execute_reaction(state, handler, name, reactor, payload)`
- [ ] `Interpreter::evaluate_mechanic(state, handler, name, args)`
- [ ] `Interpreter::evaluate_derive(state, handler, name, args)`
- [ ] `Interpreter::fire_event(state, name, payload, candidates)`

### Tests
- [ ] End-to-end: parse → lower → check → interpret (small program)
- [ ] End-to-end: action with requires + cost + resolve
- [ ] End-to-end: derive with modify pipeline
- [ ] End-to-end: event fire + reaction execution
- [ ] Response-validity matrix: invalid response → RuntimeError
- [ ] Integration with D&D 5e patterns from spec

---

## Cross-cutting concerns

- [ ] Test infrastructure: `ScriptedHandler` (records effects, replays responses)
- [ ] Test infrastructure: `TestState` (minimal `StateProvider`)
- [ ] Design doc update: `DeductCost` Layer 1 vs Layer 2 semantics (`interpreter.md` line 104)
- [x] Crate setup: `ttrpg_interp/Cargo.toml` with deps on `ttrpg_ast` + `ttrpg_checker`
