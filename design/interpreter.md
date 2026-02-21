# TTRPG DSL Interpreter — Design Document

## Design Goals

1. **Easy integration** into host applications (VTTs, character builders, Discord bots, etc.). The interpreter should be embeddable with a small, clear API surface.

2. **Performance is a non-goal.** TTRPG mechanics are designed for mental arithmetic — a tree-walking interpreter is more than sufficient. Simplicity and correctness take priority.

3. **Maximum customizability.** Players and GMs differ in how much automation they want. The runtime must support:
   - Full automation (dice rolled, state applied, no confirmation)
   - Semi-automation (dice rolled, host confirms before applying)
   - Manual mode (host provides physical dice results)
   - GM override at any point (veto, reroll, substitute values)

---

## 1. Execution Model — Effects, Not Side Effects

The interpreter does NOT directly perform side effects. Instead, it describes what it wants to do and yields control to the host application. The host decides how to fulfill each request and feeds the result back.

This is the core architectural decision. Every observable behavior — dice rolls, state mutations, prompts, condition changes — is expressed as an **Effect** that the host intercepts.

### The step loop

The host drives execution:

```rust
let exec = interpreter.begin_action("Attack", actor, &[target, weapon]);

loop {
    match exec.step() {
        Step::Effect(effect) => {
            let response = host.handle(effect);
            exec.respond(response);
        }
        Step::Complete(value) => break,
        Step::Error(err)     => { /* handle */ }
    }
}
```

The interpreter runs synchronously until it encounters an effect, then suspends. The host processes the effect (which may involve async UI, network calls, or user input) and resumes the interpreter with a response. This maps naturally onto any concurrency model the host uses.

---

## 2. Effects and Responses

Effects are what the interpreter yields to the host. Responses are what the host sends back.

### Effect variants

Effects fall into five categories: **value effects** (interpreter needs a value back), **mutation effects** (state changes, auto-applied in Layer 2/3 by default), **decision effects** (state changes, always passed through to host), **gate effects** (host can alter control flow), and **informational effects** (fire-and-forget notifications). Section 8 is the authoritative reference for which responses are valid on each effect.

#### Value effects

The interpreter cannot continue without a value. `Vetoed` is not valid.

**`RollDice { expr: DiceExpr }`**

The interpreter needs a dice expression evaluated. The host can auto-roll, animate, prompt for physical dice, or have the GM set a result.

**`ResolvePrompt { name: String, params: Vec<Value>, hint: Option<String>, suggest: Option<Value> }`**

The interpreter has reached a `prompt` declaration and needs human input. If the prompt declaration includes a `suggest: expr` clause, the interpreter evaluates it and passes the result in `suggest`. The host can display this as a default or pre-selected choice.

#### Mutation effects

State changes that the host can acknowledge, override, or veto. In the Layer 2/3 adapters, these are auto-applied by default (see Section 7 for configurable pass-through).

**`MutateField { entity: EntityRef, path: Vec<FieldPathSegment>, op: AssignOp, value: Value, bounds: Option<(Value, Value)> }`**

The interpreter wants to change an entity's field. `path` encodes the lvalue target — a simple field access like `target.HP` is `[Field("HP")]`, while a nested access like `target.stats[STR]` is `[Field("stats"), Index(Value::Str("STR"))]`.

```rust
enum FieldPathSegment {
    Field(String),
    Index(Value),
}
```

For resource fields (e.g., `HP: resource(0..max_HP)`), `bounds` contains `Some((min, max))`. The host must clamp the final field value to this range after applying the operation. For non-resource fields, `bounds` is `None`.

**`ApplyCondition { target: EntityRef, condition: String, duration: Value }`**

The interpreter wants to add a condition to an entity. The host records it with a `gained_at` timestamp for ordering.

**`RemoveCondition { target: EntityRef, condition: String }`**

The interpreter wants to remove a condition from an entity.

**`MutateTurnField { actor: EntityRef, field: String, op: AssignOp, value: Value }`**

The interpreter wants to modify a field of the current turn's `TurnBudget` (e.g., `turn.movement += actor.speed` in a Dash action's resolve block). This is distinct from `DeductCost`, which handles the declarative `cost { ... }` clause. `MutateTurnField` handles imperative turn-state mutations in resolve blocks.

#### Decision effects

State changes that are **always** passed through to the host, even in Layer 2/3 adapters. These are inherently interactive — the host may need to confirm, display context, or involve the GM.

**`DeductCost { actor: EntityRef, token: String, budget_field: String }`**

The interpreter wants to spend an action economy token. `token` is the singular cost name from the DSL source (e.g., `action`), and `budget_field` is the corresponding `TurnBudget` field name (e.g., `actions`). The mapping is fixed:

| `token` | `budget_field` | Semantics |
|---------|---------------|-----------|
| `action` | `actions` | `turn.actions -= 1` |
| `bonus_action` | `bonus_actions` | `turn.bonus_actions -= 1` |
| `reaction` | `reactions` | `turn.reactions -= 1` |

On `Acknowledged`, the host decrements `budget_field` by 1. On `Override(Value::Str(replacement_token))`, the replacement token must be a valid token name from the mapping table above — if it is not, the interpreter yields `Step::Error`. On `Vetoed`, the cost is waived entirely.

#### Gate effects

The host can alter execution flow — cancel an action or override a check result. These are **not** informational despite having `Acknowledged` as the default response.

**`ActionStarted { name: String, kind: ActionKind, actor: EntityRef, params: Vec<Value> }`**

Yielded before an action or reaction executes. The host can `Vetoed` to cancel (interpreter skips to `ActionCompleted`).

`ActionKind` distinguishes the context:

```rust
enum ActionKind {
    Action,
    Reaction { event: String, trigger: Value },
}
```

For reactions, `event` is the triggering event name and `trigger` is the event payload struct. This lets the host display context ("Opportunity Attack triggered by entity_leaves_reach") and make informed veto decisions.

**`RequiresCheck { action: String, passed: bool, reason: Option<String> }`**

Yielded after evaluating a requires clause. The host can `Override(Bool)` to force the check to pass or fail regardless of the actual result.

#### Informational effects

Fire-and-forget notifications. Only `Acknowledged` is valid. These exist for display, logging, and GM awareness.

| Effect | Fields |
|--------|--------|
| `ActionCompleted` | `name`, `actor: EntityRef` |
| `ModifyApplied` | `source: ModifySource`, `target_fn`, `phase: Phase`, `changes: Vec<FieldChange>` |

`ModifySource` identifies whether the modifier came from a condition or an option:

```rust
enum ModifySource {
    Condition(String),  // condition name
    Option(String),     // option name
}
```

### Response variants

| Response | Meaning |
|----------|---------|
| `Rolled(RollResult)` | Dice result (expected response for `RollDice`) |
| `PromptResult(Value)` | Human decision (expected response for `ResolvePrompt`) |
| `Acknowledged` | Host accepts the effect |
| `Override(Value)` | GM substitutes a different value |
| `Vetoed` | GM blocks the effect |

Both `Override` and `Vetoed` are restricted to specific effect types. Not every effect supports every response. Section 8 is the authoritative reference for which responses are valid on which effects. Sending an unsupported response yields `Step::Error`.

---

## 3. State Ownership — Host-Owned, Interpreter-Driven

The host application owns all game state:
- Entity field values (HP, AC, abilities, position, etc.)
- Active conditions (which conditions on which entities)
- Turn budgets (action economy per turn)
- Enabled options (which variant/homebrew rules are active)

The interpreter does not persist state between executions. It reads state through a `StateProvider` trait and writes state through effects.

### StateProvider trait

The host implements this trait to give the interpreter synchronous read access to game state:

```rust
trait StateProvider {
    /// Read a single field from an entity.
    /// Returns None if the entity doesn't exist or the field is missing.
    fn read_field(&self, entity: &EntityRef, field: &str) -> Option<Value>;

    /// Active conditions on an entity, ordered by gained_at (oldest first).
    /// Returns None if the entity doesn't exist.
    fn read_conditions(&self, entity: &EntityRef) -> Option<Vec<ActiveCondition>>;

    /// Current turn budget for an entity.
    /// Returns None if the entity doesn't exist.
    fn read_turn_budget(&self, entity: &EntityRef) -> Option<TurnBudget>;

    /// Names of currently enabled options.
    /// The host is responsible for honoring `default: on/off` from option
    /// declarations during its own initialization. The interpreter does not
    /// bootstrap option defaults — it only queries what the host reports.
    fn read_enabled_options(&self) -> Vec<String>;

    /// Test equality of two opaque Position values.
    /// The interpreter calls this when evaluating `==` or `!=` on Positions.
    fn position_eq(&self, a: &Value, b: &Value) -> bool;
}
```

**Reads are synchronous** and do not yield effects. Field access like `target.HP` happens inline during expression evaluation without a round trip through the effect loop. This keeps the step loop focused on decisions that actually need host involvement.

**Reads are fallible.** If a read returns `None`, the interpreter yields `Step::Error` with a descriptive message. Since the program has passed type-checking, a `None` return indicates the host's state is out of sync with the DSL program (missing entity, missing field), not a user error. This lets the host signal problems cleanly rather than panicking.

**Writes go through effects** (`MutateField`, `ApplyCondition`, etc.) so the host can intercept, confirm, or veto them.

This asymmetry — synchronous reads, effectful writes — is the key design choice. Reads are high-frequency and low-stakes. Writes are low-frequency and high-stakes.

### ActiveCondition

The host stores conditions as:

```rust
struct ActiveCondition {
    name: String,           // condition name (e.g., "Prone")
    bearer: EntityRef,      // entity bearing this condition
    gained_at: u64,         // ordering timestamp (oldest first)
    duration: Value,        // Duration enum value
}
```

The interpreter uses `gained_at` for modifier ordering (see Section 5). The host is responsible for removing expired conditions based on duration semantics (start of turn, end of turn, etc.).

### EntityRef

Entities are referenced by an opaque handle:

```rust
struct EntityRef(u64);
```

The host maps these to its own entity representation. The interpreter never constructs `EntityRef`s — they come from function parameters or `StateProvider` reads.

---

## 4. Runtime Values

The interpreter uses a single `Value` enum for all runtime data:

```rust
enum Value {
    Int(i64),
    Float(f64),
    Bool(bool),
    Str(String),
    None,

    // Dice pipeline
    DiceExpr(DiceExpr),
    RollResult(RollResult),

    // Composite
    List(Vec<Value>),
    Set(BTreeSet<Value>),
    Map(BTreeMap<Value, Value>),
    Option(Option<Box<Value>>),

    // Structured
    Struct { name: String, fields: BTreeMap<String, Value> },
    Entity(EntityRef),
    EnumVariant { enum_name: String, variant: String, fields: BTreeMap<String, Value> },

    // Opaque
    Position(Box<dyn Any>),

    // Special
    TurnBudget(TurnBudget),
    Duration(DurationValue),
    Condition(String),
}
```

Values are the currency of the interpreter. Expressions evaluate to values, effects carry values, the host sends values back.

### Position

`Position` is an opaque, host-defined type. The interpreter never inspects its contents — it only passes `Position` values to builtins (`distance`) and through effects/state reads. The host provides `Position` values via `StateProvider::read_field` (entity fields like `actor.position`) and event payloads (`trigger.from_position`). Internally, `Position` wraps a trait object (`Box<dyn Any>`) that the host downcasts to its own coordinate representation (grid, hex, theater-of-the-mind, etc.).

`Position` does not implement `Ord`. The type checker prevents `Position` from appearing as a set element or map key. Equality comparison is delegated to the host via `StateProvider::position_eq`.

### Type coercions at runtime

- `RollResult` coerces to `Int` (via `.total`) in comparison contexts. This matches the checker's coercion rules — the interpreter applies the same coercion when evaluating `BinOp(>=, <=, etc.)` with a `RollResult` operand.
- `Float` -> `Int` coercion is explicit: `floor()` and `ceil()` only.
- Division of two `Int`s produces `Float`.

### Ordering and Float

`Value` must implement `Ord` for use as `BTreeSet`/`BTreeMap` keys. Since `f64` has no natural total ordering (NaN), the following rules apply:

- The **type checker prevents** `Float` from appearing as a set element type or map key type. `set<float>` and `map<float, V>` are rejected at check time.
- The `Value::Ord` implementation uses **IEEE 754 total ordering** (`f64::total_cmp`) as a safety net. If a `Float` value somehow reaches a set/map operation (which would be a checker bug), it will order deterministically rather than panic.
- NaN is not producible by the language (no inf/NaN literals, division by zero is a runtime error), so this is purely defensive.

---

## 5. Modify Pipeline

The modify pipeline is the most complex runtime feature. The interpreter owns the pipeline logic; the host just stores which conditions are active and which options are enabled.

### When a mechanic or derive is called

Before executing the body of a mechanic/derive, the interpreter checks for active modifiers targeting that function. Modifiers come from two sources: **active conditions** on entities and **enabled options**.

**Example:** calling `attack_roll(attacker, target, weapon)`

1. **Query conditions:**
   ```
   conditions_on_attacker = state.read_conditions(attacker)
   conditions_on_target   = state.read_conditions(target)
   ```

2. **Query enabled options:**
   ```
   enabled_options = state.read_enabled_options()
   ```

3. **Filter to relevant modifiers:**
   For each condition, check its `modify` clauses. A clause like `modify attack_roll(attacker: bearer)` matches when the condition's bearer is the `attacker` argument. For each enabled option, check its `when enabled { modify ... }` clauses using the same signature matching.

4. **Order modifiers:**
   Condition modifiers are ordered by `gained_at` (oldest first). Within a single condition, clauses apply in declaration order. Option modifiers are applied **after** all condition modifiers, in option declaration order. Within a single option, clauses apply in declaration order. This ensures session-wide rules layer on top of entity-specific condition effects.

5. **Phase 1 — rewrite inputs:**
   For each matching modifier, evaluate its Phase 1 body. Phase 1 assignments like `mode = disadvantage` rewrite the function's input parameters before the body executes. Each modifier sees the result of all previous modifiers. Yield `ModifyApplied` informational effect for each.

6. **Execute function body** with (possibly rewritten) parameters.

7. **Phase 2 — rewrite outputs:**
   For each matching modifier, evaluate its Phase 2 body. Phase 2 assignments like `result.movement = result.movement - 15` rewrite the function's return value. Each modifier sees the result of all previous modifiers. Yield `ModifyApplied` informational effect for each.

8. **Return** the (possibly rewritten) result.

### Event suppression

Conditions can suppress events:
```
suppress entity_leaves_reach(entity: bearer)
```

Before firing an event, the interpreter must check all active conditions on all relevant entities for suppression clauses matching that event. If any match, the event is not fired (and reactions are not triggered).

Suppression checks are done via `StateProvider` reads — no effects. The interpreter handles the matching logic.

---

## 6. Execution Contexts

The host can invoke the interpreter in several contexts:

### Execute an action

```rust
interpreter.begin_action(name, actor, args)
```

Runs the full action pipeline:
1. Yield `ActionStarted`
2. Evaluate requires clause (yield `RequiresCheck`)
   - If failed: yield `ActionCompleted`, done — no cost spent
3. Deduct cost from turn budget — yield one `DeductCost` per token in declaration order (e.g., `cost { action, bonus_action }` yields two `DeductCost` effects)
   - Each can be independently `Acknowledged`, `Override`d, or `Vetoed`
   - If vetoed: that token's cost is waived, action continues
4. Execute resolve block (may yield `RollDice`, `MutateField`, `MutateTurnField`, etc.)
5. Yield `ActionCompleted`

Requires is checked **before** cost deduction. If the precondition fails, no resources are consumed. This matches the intuition that an impossible action shouldn't cost anything.

### Execute a reaction

```rust
interpreter.begin_reaction(name, reactor, event_payload)
```

Same as action but triggered by an event:
1. Yield `ActionStarted` (with `kind: Reaction { event, trigger }`)
2. Bind `trigger` to event payload
3. Deduct cost (yield `DeductCost`)
4. Execute resolve block
5. Yield `ActionCompleted`

### Evaluate a mechanic

```rust
interpreter.evaluate_mechanic(name, args)
```

Called by the host to compute a value outside of an action. Runs the condition modify pipeline and returns a value. Useful for "what would happen if..." previews.

### Evaluate a derive

```rust
interpreter.evaluate_derive(name, args)
```

Pure computation. Still runs the modify pipeline (conditions can modify derives). Returns a value.

### Fire an event

```rust
interpreter.fire_event(name, payload)
```

The host tells the interpreter an event occurred. The interpreter checks suppression and returns a single result:

```rust
struct EventResult {
    /// Reactions that matched but are suppressed by active conditions.
    suppressed: Vec<ReactionInfo>,
    /// Reactions available for the host to execute.
    triggerable: Vec<ReactionInfo>,
}
```

The host then decides which triggerable reactions to execute and in what order. This keeps initiative/priority logic in the host's hands. The `suppressed` list is provided for display/logging ("Disengaging prevents opportunity attacks").

**Trigger matching algorithm:** When an event is fired, the interpreter scans all reaction declarations whose trigger event name matches. For each reaction, the trigger bindings are evaluated against the event's parameter list. Bindings come in two forms:

- **Named:** `reactor: reactor` — matches when the event parameter named `reactor` equals the reaction's `reactor` argument.
- **Positional:** a bare identifier — matches against the event parameter at the same position in the event's parameter list.

All bindings must match for the reaction to be triggerable. Unmatched reactions are excluded from both `suppressed` and `triggerable` lists. The same matching algorithm applies to condition `suppress` clauses — a clause like `suppress entity_leaves_reach(entity: bearer)` matches when the event parameter `entity` equals the condition's bearer.

---

## 7. Integration Layers

The crate provides three layers of integration, from most control to least:

### Layer 1: Raw Effect Stream

The host implements `StateProvider` and handles all effects manually. Maximum control. Every read and write is visible. The host is responsible for all state management.

**Use when:** You have an existing entity system and want full control over how DSL execution interacts with it.

```rust
struct MyVTT { /* ... */ }

impl StateProvider for MyVTT {
    fn read_field(&self, entity: &EntityRef, field: &str) -> Option<Value> { /* ... */ }
    fn read_conditions(&self, entity: &EntityRef) -> Option<Vec<ActiveCondition>> { /* ... */ }
    fn read_turn_budget(&self, entity: &EntityRef) -> Option<TurnBudget> { /* ... */ }
    fn read_enabled_options(&self) -> Vec<String> { /* ... */ }
    fn position_eq(&self, a: &Value, b: &Value) -> bool { /* ... */ }
}

let interp = Interpreter::new(program, type_env);
let exec = interp.begin_action_with(&my_vtt, "Attack", actor, &args);
// ... drive step loop manually ...
```

### Layer 2: State Adapter

The host implements `StateProvider` for reads. Writes still go through effects, but a provided adapter translates `MutateField`, `ApplyCondition`, etc. into trait method calls on a `WritableState` trait, reducing boilerplate.

```rust
trait WritableState: StateProvider {
    fn write_field(&mut self, entity: &EntityRef, path: &[FieldPathSegment], value: Value);
    fn add_condition(&mut self, entity: &EntityRef, cond: ActiveCondition);
    fn remove_condition(&mut self, entity: &EntityRef, name: &str);
    fn write_turn_field(&mut self, entity: &EntityRef, field: &str, value: Value);
}
```

The adapter classifies effects into two categories:

**Auto-applied by default** — mutation effects (adapter handles via `WritableState` trait calls, host doesn't see them):
- `MutateField` — calls `write_field`
- `ApplyCondition` — calls `add_condition`
- `RemoveCondition` — calls `remove_condition`
- `MutateTurnField` — calls `write_turn_field`

**Always passed through** — value, decision, gate, and informational effects (host must handle):
- `RollDice` — host provides the roll result
- `ResolvePrompt` — host gets player input
- `DeductCost` — host confirms/waives/overrides cost spending (calls `write_turn_field` on `Acknowledged`; on `Override`, calls `write_turn_field` with the replacement token's budget field instead)
- All gate and informational effects

#### Configurable pass-through

By default, mutation effects (`MutateField`, `ApplyCondition`, `RemoveCondition`, `MutateTurnField`) are auto-applied for ease of integration. However, this means the host loses the ability to `Override` or `Vetoed` those mutations (see Section 8). Decision effects like `DeductCost` are always passed through regardless of configuration. For hosts that need GM review of state changes, the adapter accepts a configuration:

```rust
let adapter = StateAdapter::new(my_state)
    .pass_through(EffectKind::MutateField)      // GM reviews HP changes etc.
    .pass_through(EffectKind::ApplyCondition);   // GM reviews condition application
```

When an effect kind is set to pass-through, the adapter yields it to the host instead of auto-applying. The host can then respond with `Acknowledged`, `Override`, or `Vetoed` as in Layer 1. On `Acknowledged` (or `Override`), the adapter applies the (possibly modified) mutation via `WritableState`.

**Trade-off:** Auto-apply is simpler but loses GM fiat on mutations. Pass-through preserves GM fiat but requires the host to handle more effects. The default (auto-apply) optimizes for fast setup; hosts that need GM review opt in per effect kind.

**Use when:** You have your own entity storage but want the crate to handle the write-effect boilerplate.

### Layer 3: Batteries Included

A reference `GameState` implementation is provided:

```rust
let mut state = GameState::new();
state.add_entity("goblin_1", entity_values);
state.apply_condition("goblin_1", prone_condition);
state.enable_option("flanking");

let interp = Interpreter::with_state(program, type_env, &mut state);
let exec = interp.begin_action("Attack", actor, &args);
```

`GameState` implements `WritableState` with `HashMap`s. By default, mutation effects are auto-applied internally. The host handles value effects (`RollDice`, `ResolvePrompt`), the decision effect (`DeductCost`), and gate/informational effects.

The same `pass_through` configuration from Layer 2 is available — hosts that need GM review of mutations can opt specific mutation effect kinds into the step loop. `DeductCost` is always passed through regardless of configuration.

**Use when:** Getting started quickly, prototyping, testing, or you don't have an existing entity system.

---

## 8. GM Override Protocol

`Override` and `Vetoed` are the mechanisms for GM fiat. **Neither is universally valid** — each effect type defines which responses it accepts. Sending an unsupported response yields `Step::Error`.

### Complete response validity table

This is the authoritative reference for all effect/response combinations.

**Value effects** — interpreter needs a value back, cannot be skipped:

| Effect | `Acknowledged` | `Override(Value)` | `Vetoed` | Expected response |
|--------|:-:|:-:|:-:|-------------------|
| **`RollDice`** | — | replacement `RollResult` | — | `Rolled(RollResult)` |
| **`ResolvePrompt`** | — | GM-chosen selection (`Value`) | — | `PromptResult(Value)` |

**Mutation effects** — state changes, auto-applied in Layer 2/3 by default (configurable):

| Effect | `Acknowledged` | `Override(Value)` | `Vetoed` | Expected response |
|--------|:-:|:-:|:-:|-------------------|
| **`MutateField`** | apply mutation | replacement RHS value (op preserved) | skip mutation | `Acknowledged` |
| **`MutateTurnField`** | apply mutation | replacement RHS value (op preserved) | skip mutation | `Acknowledged` |
| **`ApplyCondition`** | apply condition | replacement duration (`Value::Duration`) | skip, condition not applied | `Acknowledged` |
| **`RemoveCondition`** | remove condition | replacement condition name (`Value::Str`) | skip, condition remains | `Acknowledged` |

**Decision effects** — state changes, always passed through to host (never auto-applied):

| Effect | `Acknowledged` | `Override(Value)` | `Vetoed` | Expected response |
|--------|:-:|:-:|:-:|-------------------|
| **`DeductCost`** | spend token | replacement token name (`Value::Str`) | waive cost, action continues | `Acknowledged` |

**Gate effects** — host can alter control flow:

| Effect | `Acknowledged` | `Override(Value)` | `Vetoed` | Expected response |
|--------|:-:|:-:|:-:|-------------------|
| **`ActionStarted`** | continue | — | cancel entire action | `Acknowledged` |
| **`RequiresCheck`** | accept result | force pass or fail (`Value::Bool`) | — | `Acknowledged` |

**Informational effects** — only `Acknowledged` is valid:

| Effect | `Acknowledged` | `Override(Value)` | `Vetoed` | Expected response |
|--------|:-:|:-:|:-:|-------------------|
| **`ActionCompleted`** | continue | — | — | `Acknowledged` |
| **`ModifyApplied`** | continue | — | — | `Acknowledged` |

**Legend:** "—" means the response is not valid for that effect and yields `Step::Error`.

### Override semantics

The override value's meaning is effect-specific:

- **`RollDice`**: Replacement `RollResult`. Example: `Override(Value::RollResult { unmodified: 20, ... })` — GM decides it's a natural 20.
- **`MutateField`**: Replacement **RHS value**. The operator is preserved. Example: `MutateField { goblin.HP -= 15 }` with `Override(Value::Int(10))` means `goblin.HP -= 10` — GM reduces the damage, the `-=` is kept.
- **`MutateTurnField`**: Same as `MutateField` — replacement RHS value, operator preserved. Example: `MutateTurnField { turn.movement += 30 }` with `Override(Value::Int(15))` means `turn.movement += 15`.
- **`DeductCost`**: Replacement token name. Example: `Override(Value::Str("bonus_action"))` — GM lets the player spend a bonus action instead of an action.
- **`ApplyCondition`**: Replacement duration. Example: `Override(Value::Duration(EndOfNextTurn))` — GM shortens the effect.
- **`RemoveCondition`**: Replacement condition name. Example: `Override(Value::Str("Frightened"))` — GM removes a different condition instead.
- **`ResolvePrompt`**: GM-chosen selection value. Bypasses player input entirely.
- **`RequiresCheck`**: `Override(Value::Bool(true))` forces the action to proceed even if requires would fail. `Override(Value::Bool(false))` blocks it even if requires would pass.

### Vetoed semantics

Vetoed means "skip this effect, continue execution." It is only valid when the interpreter can safely proceed without a return value:

- **`ActionStarted`**: Entire action is cancelled (interpreter skips to `ActionCompleted`).
- **`DeductCost`**: Cost is waived; action continues without spending the token.
- **`MutateField`**: Field is not changed; execution continues.
- **`MutateTurnField`**: Turn field is not changed; execution continues.
- **`ApplyCondition`**: Condition is not applied; execution continues.
- **`RemoveCondition`**: Condition remains; execution continues.

Vetoed is **not valid** for `RollDice` and `ResolvePrompt` because the interpreter needs a value to continue — a fabricated "zero" or "empty" result would silently corrupt control flow (crit detection, advantage paths, check thresholds). Use `Override` with a specific value instead.

### Automation levels

The host controls automation by how it handles effects:

| Level | RollDice | MutateField | DeductCost | Informational |
|-------|----------|-------------|------------|---------------|
| **Full auto** | Auto-roll, return `Rolled` | Apply immediately, return `Acknowledged` | Apply, return `Acknowledged` | Log and return `Acknowledged` |
| **Semi-auto** | Auto-roll, show result, wait for "OK" | Show pending change, wait for confirm | Show cost, wait for confirm | Display to players |
| **Manual** | Prompt player for physical dice result | Display instruction ("reduce goblin HP by 15") | Display cost to spend | Step-by-step narration |
| **GM review** | Show to GM, let them Override | Show to GM, let them Acknowledge/Override/Vetoed | Show to GM, let them Acknowledge/Vetoed | Show to GM |

---

## 9. Crate Structure

```
ttrpg_interp/
  src/
    lib.rs              — public API, Interpreter, Execution handle
    value.rs            — Value enum, runtime type representations
    effect.rs           — Effect and EffectResponse enums
    state.rs            — StateProvider, WritableState traits
    eval.rs             — expression evaluator (tree-walking)
    exec.rs             — statement executor, block runner
    condition.rs        — modify pipeline, suppression checking
    builtins.rs         — floor, ceil, min, max, distance, multiply_dice
    reference_state.rs  — GameState (Layer 3 batteries-included)
```

### Dependencies

- `ttrpg_ast` — AST node types (walked by the interpreter)
- `ttrpg_checker` — `TypeEnv`, `Ty`, `FnInfo`, etc. (used for type-directed dispatch)

The interpreter takes a checked `Program` and its `TypeEnv`. It trusts that the program has passed type-checking — runtime type errors are bugs in the checker, not user errors.

---

## 10. What the Interpreter Does NOT Do

- **Initiative and turn order:** Host's responsibility. The interpreter executes one action/reaction at a time when told to.
- **Duration tracking:** The host tracks game time and removes expired conditions. The interpreter only reads what's currently active.
- **Event firing decisions:** The host decides when events occur (e.g., entity movement triggers `entity_leaves_reach`). The interpreter just checks suppression and finds matching reactions.
- **Reaction ordering:** When multiple reactions could trigger, the host decides priority (e.g., initiative order, player choice).
- **Persistence:** The host owns all state storage. The interpreter is stateless between executions.
- **Networking:** The interpreter is single-threaded and synchronous. The host handles multiplayer, sync, etc.

The interpreter is a pure rules engine. Everything around it — timing, ordering, persistence, presentation — belongs to the host.
