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
- [x] `Value` enum with all 16 variants
- [x] `DiceExpr` struct
- [x] `RollResult` struct
- [x] ~`TurnBudget` struct~ (removed — turn budgets now use `Value::Struct { name: "TurnBudget", fields }`; `default_turn_budget()` helper creates the default 5e budget)
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
- [x] `Interpreter` struct with `program`, `type_env`, `index`
- [x] `DeclIndex` struct with 8 `HashMap` fields
- [x] `Interpreter::new` — build `DeclIndex`, reject surviving `DeclKind::Move`
- [x] `Env` struct with `state`, `handler`, `interp`, `scopes`, `turn_actor`
- [x] `Scope` struct with `bindings: HashMap<String, Value>`

### Expression evaluator (`eval.rs`)
- [x] `eval_expr` dispatcher
- [x] `IntLit`, `StringLit`, `BoolLit`, `NoneLit`
- [x] `DiceLit` → `Value::DiceExpr`
- [x] `Paren`
- [x] `Ident` — scope lookup + enum type namespace fallback
- [x] `UnaryOp` — `Neg` (Int/Float), `Not` (Bool)
- [x] `BinOp` — arithmetic (`+`, `-`, `*`, `/`)
- [x] `BinOp` — comparison (`<`, `<=`, `>`, `>=`)
- [x] `BinOp` — equality (`==`, `!=`) via `value_eq`
- [x] `BinOp` — logical (`&&`, `||`)
- [x] `BinOp` — `in` operator (List, Set, Map)
- [x] `BinOp` — RollResult coercion to Int in arithmetic/comparison
- [x] `BinOp` — `Int / Int` → Float promotion
- [x] `BinOp` — division by zero → RuntimeError
- [x] `BinOp` — checked integer overflow for `+`, `-`, `*`
- [x] `FieldAccess` — entity fields via `state.read_field()`
- [x] `FieldAccess` — struct fields
- [x] `FieldAccess` — enum variant fields
- [x] `FieldAccess` — RollResult built-in fields (`.total`, `.unmodified`, `.dice`, `.kept`)
- [x] `FieldAccess` — TurnBudget fields (handled by Struct arm — turn budget is `Value::Struct { name: "TurnBudget", .. }`)
- [x] `Index` — List by Int
- [x] `Index` — Map by key
- [x] `ListLit`
- [x] `StructLit`
- [x] `If` — condition + branches
- [x] `PatternMatch` — scrutinee + arms
- [x] `GuardMatch` — guard conditions in order
- [x] `Call` — stub returning RuntimeError (real dispatch in Phase 4)

### Semantic equality (`eval.rs`)
- [x] `value_eq(env, a, b)` helper
- [x] Float: standard `f64 ==` (-0.0 == +0.0)
- [x] Position: delegate to `state.position_eq()`
- [x] Composite: recursive walk

### Pattern matching (`eval.rs`)
- [x] `match_pattern` helper
- [x] `Wildcard`
- [x] `IntLit`, `StringLit`, `BoolLit`
- [x] `Ident` (binding)
- [x] `QualifiedVariant`
- [x] `QualifiedDestructure`
- [x] `BareDestructure`

### Tests
- [x] Each literal type evaluates correctly
- [x] Arithmetic on Int, Float, mixed
- [x] Comparison operators
- [x] Equality via `value_eq` (including Float -0.0, Position delegation)
- [x] Logical short-circuit
- [x] `in` operator on List, Set, Map
- [x] Integer overflow produces RuntimeError
- [x] Division by zero produces RuntimeError
- [x] Field access on entities, structs, RollResult, turn budget (via Struct arm)
- [x] Index on List (valid + out-of-bounds), Map (present + absent)
- [x] If/else branching
- [x] Pattern match: all pattern kinds
- [x] Guard match: first-matching semantics

---

## Phase 3: Statement Execution

### Block and statement execution (`eval.rs`)
- [x] `eval_block` — push scope, execute stmts, pop scope, return last value
- [x] `eval_stmt` dispatcher
- [x] `Let` — evaluate RHS, bind in current scope
- [x] `Expr` — evaluate and return

### Assignment (`eval.rs`)
- [x] LValue root resolution (turn / entity / local)
- [x] Entity path: convert segments to `FieldPathSegment`, emit `MutateField`
- [x] Entity path: resource bounds passed as `None` (`Ty::Resource` doesn't carry bounds; evaluating AST bound expressions requires derive calls from Phase 4)
- [x] Turn path: emit `MutateTurnField`
- [x] Local path: navigate into struct fields
- [x] Local path: navigate into list by index (with negative indexing)
- [x] Local path: navigate into map by key
- [x] `AssignOp` application (=, +=, -=)
- [x] `apply_assign_op` — checked overflow for `+=`, `-=`
- [x] Entity-through-struct path: `trigger.entity.HP -= 5` switches to entity mutation when Entity encountered during local walk

### Error cases
- [x] List index out of bounds → RuntimeError
- [x] Map missing key with `=` → insert
- [x] Map missing key with `+=`/`-=` → RuntimeError
- [x] Struct missing field → RuntimeError (internal)
- [x] `+=`/`-=` on incompatible types → RuntimeError

### Tests
- [x] Let bindings visible in scope
- [x] Nested scopes: shadowing and isolation
- [x] Entity field assignment emits `MutateField`
- [x] Entity nested path (e.g. `target.stats[STR]`) emits `MutateField`
- [x] Entity through struct (e.g. `trigger.entity.HP`) emits `MutateField`
- [x] Turn assignment emits `MutateTurnField`
- [x] Turn without actor → RuntimeError
- [x] Turn with no segments → RuntimeError
- [x] Local struct field mutation (= and +=)
- [x] Local list index mutation (positive and negative indices)
- [x] Local list index out of bounds → RuntimeError
- [x] Local map key mutation (insert + update + +=)
- [x] Map missing key with `+=`/`-=` → RuntimeError
- [x] Direct variable reassignment (=, +=, -=)
- [x] Undefined variable → RuntimeError
- [x] Incompatible types in `+=` → RuntimeError
- [x] Integer overflow in `+=`/`-=` → RuntimeError
- [x] Float `+=`/`-=` operations
- [x] RollResult coerced to Int in `+=`
- [x] Assignment returns `Value::None` as block value
- [x] Local mutations emit no effects

---

## Phase 4: Function Calling & Builtins

### Call dispatch (`call.rs`)
- [x] Resolve callee: `Ident` → function lookup
- [x] Resolve callee: `FieldAccess` → qualified enum constructor
- [x] Resolve callee: other expression → RuntimeError
- [x] Dispatch `Derive` — bind params, body (modify Phase 1/2 deferred to Phase 6)
- [x] Dispatch `Mechanic` — same as Derive
- [x] Dispatch `Prompt` — evaluate hint/suggest, emit `ResolvePrompt`
- [x] Dispatch `Builtin` — route to builtin impl
- [x] Dispatch `Action` — extract receiver, call `execute_action` (stub, deferred to Phase 5)
- [x] Dispatch `Reaction` — unreachable (internal error)
- [x] Qualified enum variant construction
- [x] Bare enum variant construction (via `variant_to_enum`)

### Argument binding (`call.rs`)
- [x] `bind_args` — positional matching
- [x] `bind_args` — named matching
- [x] `bind_args` — default value evaluation for optional params
- [x] Receiver handling: extract from first effective argument

### Builtins (`builtins.rs`)
- [x] `floor(Float) -> Int`
- [x] `ceil(Float) -> Int`
- [x] `min(Int, Int) -> Int`
- [x] `max(Int, Int) -> Int`
- [x] `distance(Position, Position) -> Int` via `state.distance()`
- [x] `multiply_dice(DiceExpr, Int) -> DiceExpr` (checked, factor > 0)
- [x] `roll(DiceExpr)` → emit `RollDice`, process response
- [x] `apply_condition(Entity, String, Duration)` → emit `ApplyCondition`
- [x] `remove_condition(Entity, String)` → emit `RemoveCondition`

### Tests
- [x] Derive call: arithmetic body returns correct value
- [x] Mechanic call: body with `roll()` emits `RollDice`
- [x] Prompt call: emits `ResolvePrompt` with hint/suggest
- [x] Named args, positional args, default values
- [x] Each builtin: correct result or effect
- [x] `multiply_dice`: factor <= 0 → RuntimeError, overflow → RuntimeError
- [x] `roll`: processes `Rolled` and `Override` responses
- [x] Enum variant construction (qualified + bare)

---

## Phase 5: Action/Reaction Pipeline

### Action execution (`action.rs`)
- [x] `execute_action` function
- [x] Emit `ActionStarted` (kind: Action)
- [x] Handle `Vetoed` → emit `ActionCompleted`, return None
- [x] Bind scope: receiver + params
- [x] Save/restore `turn_actor`
- [x] Requires clause: evaluate, emit `RequiresCheck`
- [x] Requires: `Override(true)` forces pass, `Override(false)` forces fail
- [x] Requires fail: pop scope, restore turn_actor, emit `ActionCompleted`
- [x] Cost deduction: emit `DeductCost` per token
- [x] Cost: `Acknowledged` → host decrements
- [x] Cost: `Override(replacement)` → validate + apply replacement
- [x] Cost: `Vetoed` → waived
- [x] Execute resolve block
- [x] Emit `ActionCompleted`

### Reaction execution (`action.rs`)
- [x] `execute_reaction` function
- [x] Emit `ActionStarted` (kind: Reaction)
- [x] Bind scope: receiver + trigger payload
- [x] Save/restore `turn_actor`
- [x] Cost deduction (same as action)
- [x] Execute resolve block
- [x] Emit `ActionCompleted`

### Tests
- [x] Full action: requires pass → cost → resolve
- [x] Requires fail: no cost spent, action completed
- [x] ActionStarted veto: immediate completion
- [x] Cost acknowledged / vetoed / overridden
- [x] Nested action calls: turn_actor save/restore
- [x] Reaction: trigger payload bound correctly
- [x] Reaction: cost deduction works

---

## Phase 6: Modify Pipeline & Events

### Modify pipeline (`pipeline.rs`)
- [x] `ModifyContext` and `ResolvedModifier` structs
- [x] Collect modifiers from conditions (query `read_conditions`)
- [x] Signature matching: function name + binding match
- [x] Deduplicate by `condition.id`
- [x] Collect modifiers from enabled options
- [x] Order: conditions by `gained_at`, then options; declaration order within
- [x] Phase 1 — rewrite inputs: `ParamOverride`, `Let`, `If`
- [x] Phase 1 — emit `ModifyApplied` with changed params
- [x] Phase 2 — rewrite outputs: `ResultOverride`
- [x] Phase 2 — emit `ModifyApplied` with changed fields

### Event firing (`event.rs`)
- [x] `fire_event` function (pure query, no effects)
- [x] `EventResult` and `ReactionInfo` structs
- [x] Scan reactions by event name
- [x] Iterate candidates for each matching reaction
- [x] Trigger binding: named bindings (params first, then fields)
- [x] Trigger binding: positional bindings (fill-the-gaps)
- [x] Binding evaluation: side-effect-free expressions only
- [x] Suppression checking: scan conditions on entity-typed params/fields
- [x] Suppress binding matching (same lookup as trigger)
- [x] Partition into `suppressed` vs `triggerable`

### Tests
- [x] Modify Phase 1: param overridden correctly
- [x] Modify Phase 2: result field overridden correctly
- [x] Multiple conditions ordered by `gained_at`
- [x] Option modifiers applied after conditions
- [x] Modifier deduplication (same condition via multiple params)
- [x] Trigger matching: named bindings
- [x] Trigger matching: positional bindings
- [x] Trigger matching: fill-the-gaps semantics
- [x] Trigger matching: candidate iteration
- [x] Suppression: condition suppress clause blocks reaction
- [x] Suppression: non-matching suppress passes through

---

## Phase 7: Integration Layers

### StateAdapter — Layer 2 (`adapter.rs`)
- [x] `StateAdapter<S: WritableState>` struct with `RefCell<S>` + `HashSet<EffectKind>`
- [x] `StateProvider` impl for `StateAdapter` (per-call `borrow()`)
- [x] `AdaptedHandler` struct
- [x] `EffectHandler` impl for `AdaptedHandler`
- [x] `StateAdapter::new(state)`
- [x] `StateAdapter::pass_through(kind)` builder
- [x] `StateAdapter::run(inner, closure)` — borrow discipline
- [x] `StateAdapter::into_inner()`
- [x] Intercepted mutation: apply locally, return `Acknowledged`
- [x] Pass-through mutation: forward, then sync on `Acknowledged`/`Override`
- [x] Pass-through mutation: `Vetoed` → no local mutation
- [x] Non-mutation effects: always forwarded
- [x] `DeductCost`: always passed through; adapter applies mutation based on response
- [x] `apply_mutation` dispatch: `MutateField` → `write_field`
- [x] `apply_mutation` dispatch: `ApplyCondition` → `add_condition`
- [x] `apply_mutation` dispatch: `RemoveCondition` → `remove_condition`
- [x] `apply_mutation` dispatch: `MutateTurnField` → `write_turn_field`

### GameState — Layer 3 (`reference_state.rs`)
- [x] `GameState` struct (entities, conditions, turn_budgets, options, counters)
- [x] `EntityState` struct
- [x] `GameState::new()`
- [x] `GameState::add_entity(name, fields) -> EntityRef`
- [x] `GameState::set_turn_budget(entity, budget)`
- [x] `GameState::apply_condition(entity, name, duration)` (auto-assign `id`)
- [x] `GameState::enable_option(name)` / `disable_option(name)`
- [x] `StateProvider` impl for `GameState`
- [x] `WritableState` impl for `GameState`
- [x] Grid position `(i64, i64)` concrete type
- [x] `position_eq`: downcast + structural equality
- [x] `distance`: Chebyshev (`max(|dx|, |dy|)`)

### Tests
- [x] Adapter: intercepted mutation applies locally
- [x] Adapter: pass-through mutation forwards + syncs
- [x] Adapter: pass-through vetoed → no local change
- [x] Adapter: non-mutation effects forwarded
- [x] Adapter: `DeductCost` decision + mutation
- [x] GameState: add entity, read fields
- [x] GameState: write field, read back
- [x] GameState: condition add/remove/query
- [x] GameState: turn budget set/read/write
- [x] GameState: option enable/disable/query
- [x] GameState: position equality and Chebyshev distance
- [x] Integration: full action via `GameState` + `StateAdapter`

---

## Phase 8: Public API

### API surface (`lib.rs`)
- [x] `Interpreter::new(program, type_env) -> Result<Self, RuntimeError>`
- [x] `Interpreter::execute_action(state, handler, name, actor, args)`
- [x] `Interpreter::execute_reaction(state, handler, name, reactor, payload)`
- [x] `Interpreter::evaluate_mechanic(state, handler, name, args)`
- [x] `Interpreter::evaluate_derive(state, handler, name, args)`
- [x] `Interpreter::fire_event(state, name, payload, candidates)`

### Tests
- [x] End-to-end: parse → lower → check → interpret (small program)
- [x] End-to-end: action with requires + cost + resolve
- [x] End-to-end: derive with modify pipeline
- [x] End-to-end: event fire + reaction execution
- [x] Response-validity matrix: invalid response → RuntimeError
- [x] Integration with D&D 5e patterns from spec

---

## Cross-cutting concerns

- [x] Test infrastructure: `ScriptedHandler` (records effects, replays responses)
- [x] Test infrastructure: `TestState` (minimal `StateProvider`)
- [x] Design doc update: `DeductCost` Layer 1 vs Layer 2 semantics (`interpreter.md` line 104)
- [x] Crate setup: `ttrpg_interp/Cargo.toml` with deps on `ttrpg_ast` + `ttrpg_checker`
