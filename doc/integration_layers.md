# Host Integration Layers

The interpreter provides three layers of integration, from most control to least. These layers describe **how the host manages game state and handles effects** — they apply regardless of whether the host uses the callback API (`Interpreter` + `EffectHandler`) or the poll-based API (`Execution<S>` + `poll()`/`respond()`).

---

## Layer 1: Raw Effect Stream

The host implements `StateProvider` (read-only) and handles **all** effects manually. The interpreter yields every effect — mutations, dice, prompts, gates, informational — to the host. Nothing is auto-applied.

**Use when:** You have an existing entity system (ECS, database, custom storage) and want full control over how DSL execution interacts with it.

**Host responsibilities:**
- Implement `StateProvider` for synchronous reads
- Handle every `Effect` and return a valid `Response`
- Apply all mutations (field writes, condition changes, budget deductions) to your own state

### Callback API (Layer 1)

```rust
impl StateProvider for MyVTT { /* ... */ }
impl EffectHandler for MyHandler { /* ... */ }

let interp = Interpreter::new(program, type_env)?;
let result = interp.execute_action(&my_vtt, &mut my_handler, "Attack", actor, args)?;
```

### Poll API (Layer 1)

```rust
let adapter = StateAdapter::new(my_writable_state);
let exec = Execution::start_action(core, adapter, "Attack", actor, args, span)?
    .raw();  // ← raw mode: bypass auto-apply, yield all effects

loop {
    match exec.poll()? {
        Step::Yielded(effect) => {
            let response = decide(&effect);
            exec.respond(response)?;
        }
        Step::Done(value) => break,
    }
}
```

Raw mode on `Execution<S>` achieves Layer 1 semantics over the poll-based API. All effects — including `SpawnEntity` — are yielded to the host. For `SpawnEntity`, the host must respond with `EntitySpawned(ref)` or `Vetoed`.

---

## Layer 2: State Adapter

The host implements `WritableState` (extends `StateProvider` with write methods). A `StateAdapter<S>` wraps the state and **auto-applies mutation effects** by default — the host only handles effects that require decisions (dice, prompts, gates, informational).

**Use when:** You have your own entity storage but want the crate to handle the mutation-effect boilerplate.

**What the adapter auto-applies (by default):**
- `MutateField`, `MutateTurnField` → calls `write_field()` / `write_turn_field()`
- `ApplyCondition`, `RemoveCondition`, `SetConditionState` → calls condition methods
- `GrantGroup`, `RevokeGroup` → calls group methods
- `SpawnEntity`, `RemoveEntity` → calls entity lifecycle methods
- `ProvisionBudget`, `ClearBudget` → calls budget methods
- `AddSuspension`, `RemoveSuspensionSource` → calls suspension methods
- `AdvanceTime`, `TransferConditions`, `RevokeInvocation` → calls corresponding methods

**What always passes through to the host:**
- Value effects: `RollDice`, `ResolvePrompt`
- Decision effects: `DeductCost` (host confirms/overrides/waives)
- Gate effects: `ActionStarted`, `RequiresCheck`, `ConditionApplyGate`, `ConditionRemovalGate`
- Informational effects: `ActionCompleted`, `ModifyApplied`

**Configurable pass-through:** For hosts that need GM review of specific mutations:

```rust
let adapter = StateAdapter::new(my_state)
    .pass_through(EffectKind::MutateField)      // GM reviews HP changes
    .pass_through(EffectKind::ApplyCondition);   // GM reviews conditions
```

When a mutation kind is set to pass-through, the adapter yields it to the host. On `Acknowledged`/`Override`, the adapter applies the (possibly modified) mutation. On `Vetoed`, the mutation is skipped.

### Callback API (Layer 2)

```rust
impl WritableState for MyState { /* ... */ }

let adapter = StateAdapter::new(my_state);
adapter.run(&mut my_handler, |state, handler| {
    interp.execute_action(state, handler, "Attack", actor, args)
})?;
```

### Poll API (Layer 2)

```rust
let adapter = StateAdapter::new(my_state);
let exec = Execution::start_action(core, adapter, "Attack", actor, args, span)?;
// No .raw() — adapter auto-applies mutations, only host-decided effects yield
```

---

## Layer 3: Batteries Included

A reference `GameState` implementation provides a complete `WritableState` with `HashMap`-based storage. Used via `StateAdapter` — effect routing is identical to Layer 2.

**Use when:** Getting started, prototyping, testing, or you don't have an existing entity system.

```rust
let mut state = GameState::new();
state.add_entity("goblin_1", entity_values);

let adapter = StateAdapter::new(state);
// Then use via callback or poll API, same as Layer 2
```

---

## Summary

| | Layer 1 | Layer 2 | Layer 3 |
|---|---------|---------|---------|
| **State reads** | Host implements `StateProvider` | Host implements `WritableState` | Provided `GameState` |
| **Mutation effects** | Host handles all | Auto-applied (configurable) | Auto-applied (configurable) |
| **Value/gate/decision effects** | Host handles all | Host handles all | Host handles all |
| **Callback API** | `Interpreter` + `StateProvider` + `EffectHandler` | `StateAdapter<S>` wrapping `WritableState` | `StateAdapter<GameState>` |
| **Poll API** | `Execution<S>.raw()` | `Execution<S>` (default) | `Execution<GameState>` |
| **Use case** | Existing entity systems, full control | Custom storage, less boilerplate | Quick start, prototyping, tests |

The layers describe **effect routing**, not API surface. Both the callback and poll APIs support all three layers.
