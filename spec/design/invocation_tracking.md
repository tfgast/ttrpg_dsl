# Language-Level Invocation Tracking

## Context

When a spell or action applies conditions to entities, there's no way to link those conditions back to their source execution. A host-level approach (tagging effects with execution context like `EffectProvenance`) places concentration/cleanup *policy* in the host. That means every host for every TTRPG system must reimplement concentration tracking: pending/committed group management, one-active-per-caster enforcement, cleanup on concentration break, and system-specific break triggers.

This design takes a different approach: expose effect groups as DSL-level primitives. The interpreter tracks invocation IDs internally and provides two builtins (`invocation()` and `revoke()`) that let ruleset authors write concentration rules entirely in the DSL. Different TTRPG systems express their own rules (5e concentration, PF2e sustained spells, Shadowrun sustaining) using existing DSL features — events, hooks, reactions — without any host-specific concentration code.

## Design

### Core Types

```rust
/// Unique identifier for an action/reaction/hook execution.
/// All conditions applied during that execution share this ID.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct InvocationId(pub u64);
```

- `InvocationId` is a newtype over `u64`, following the same pattern as `EntityRef(pub u64)`, to prevent accidental misuse with other identifiers
- At the DSL level the type is called `Invocation` — a handle that represents "all the conditions applied by a specific action execution"
- Invocation values can be stored on entity fields, passed through events, compared with `==`/`!=`, and wrapped in `option<Invocation>` for nullable fields

```rust
/// Outcome of an action execution, reported in `ActionCompleted`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ActionOutcome {
    /// Body completed without error.
    Succeeded,
    /// Host vetoed the action at the gate.
    Vetoed,
    /// Body returned RuntimeError, or host returned unexpected response.
    Failed,
}
```

- `ActionOutcome` on `ActionCompleted` provides host-level failure signaling — hosts can observe when actions fail and perform defensive cleanup of partially-applied conditions
- `ActionCompleted` carries both `outcome` and `invocation: Option<InvocationId>` — the host observes `ActionCompleted { outcome: Failed, invocation: Some(id) }` and can call `remove_conditions_by_invocation(id)` to clean up orphaned conditions
- The DSL handles the happy path (concentration tracking via hooks/events); `ActionOutcome` + invocation is a secondary safety net

### Builtins

```
invocation() -> Invocation
```

Returns the current execution scope's invocation handle. Can only be called inside an action, reaction, or hook body — rejected by the checker at compile time (see section 11) and errors at runtime if somehow reached outside that context. Every action/reaction/hook execution is automatically assigned an invocation ID (even if the body never calls `invocation()`), so this always succeeds within scope.

```
revoke(inv: Invocation) -> unit
```

Removes all conditions tagged with the given invocation, across all entities. Emits an `Effect::RevokeInvocation` that flows through the effect handler to the state. This is the DSL-level equivalent of the previous design's `WritableState::remove_conditions_by_group`.

**Scope of removal:** Conditions with `invocation: None` (CLI-granted, host-injected, applied outside action scope) are never affected — they have no invocation membership.

**Type handling:** `revoke` is registered with parameter type `Invocation`. The checker additionally permits `option<Invocation>` arguments for this parameter, since the common usage pattern passes nullable entity fields (e.g., `caster.concentrating_on`). At runtime, `none` values are treated as a no-op — this avoids requiring explicit unwrapping when revoking from nullable fields.

**Design rationale:** This targeted coercion prioritizes ergonomics for the most common `revoke` usage pattern — nullable entity fields — where explicit unwrapping (`if field != none { revoke(unwrap(field)) }`) would add ceremony at every call site with no safety benefit (the runtime semantics are identical). The trade-off is a type-system special case for one builtin. If the DSL adds function overloading in the future, this should be migrated to proper overloads (`revoke(Invocation)` and `revoke(option<Invocation>)`) to eliminate the special case.

### Tags on Actions

Actions gain a `tags` field (matching the existing pattern on derives/mechanics):

```
tag #concentration

action CastBless on caster: Character (targets: list<Character>) #concentration {
    // ...
}
```

Full grammar:

```
action_decl ::= "action" IDENT "on" IDENT ":" type [with_clause] "(" params ")" [tag_list] block
with_clause ::= "with" IDENT ("," IDENT)*
tag_list    ::= ("#" IDENT)*
```

Tags on actions follow the same syntax (`#tagname` after the closing `)` of the parameter list and before `{`), validation (must be declared via `tag #name`), and storage (in `FnInfo.tags` via `collect_fn`) as tags on derives and mechanics. This enables selector-based modify clauses targeting actions, and gives ruleset authors metadata to categorize their actions.

### DSL Example: D&D 5e Concentration

```
tag #concentration

event ConcentrationStarted(caster: Character, inv: Invocation)

entity Character {
    concentrating_on: option<Invocation>
    // ... other fields ...
}

action CastBless on caster: Character (targets: list<Character>) #concentration {
    let inv = invocation()
    // Apply all conditions FIRST
    for target in targets {
        apply_condition(target, Blessed, rounds(10))
    }
    // Register concentration LAST — only reached if all conditions applied
    emit ConcentrationStarted(caster: self, inv: inv)
}

action CastHex on caster: Character (target: Character) #concentration {
    let inv = invocation()
    apply_condition(target, Hexed(source: self), indefinite)
    emit ConcentrationStarted(caster: self, inv: inv)
}

// When any concentration spell starts, clean up the previous one
hook on_conc(caster: Character, inv: Invocation)
    when ConcentrationStarted(caster: caster, inv: inv) {
    revoke(caster.concentrating_on)  // no-op if none (first concentration)
    caster.concentrating_on = some(inv)
}

// Concentration save on damage (5e-specific rule)
reaction ConcentrationSave on caster: Character
    when DamageTaken(target: caster, amount: damage) {
    requires caster.concentrating_on != none
    let dc = max(10, damage / 2)
    let result = roll(1d20 + caster.con_save)
    if result < dc {
        revoke(caster.concentrating_on)
        caster.concentrating_on = none
    }
}
```

**Key design points:**
- The `#concentration` tag is metadata only — it doesn't trigger anything automatically. Ruleset authors explicitly `emit` events that fire their hooks.
- The action passes `invocation()` through the event payload because the hook has its own invocation scope (each hook/reaction gets its own invocation ID). The action needs to capture its own invocation handle before the hook fires.
- Conditions are applied **before** the concentration event is emitted — see Failure Ordering Guidance below.
- Concentration rules are fully expressed in the DSL — hosts don't need system-specific concentration logic.
- `some(inv)` wraps the `Invocation` value for assignment to the `option<Invocation>` field.

### PF2e Sustained Spells (Different System, Same Primitives)

```
tag #sustained

event SpellSustained(caster: Character, inv: Invocation)
event SustainedSpellLapsed(caster: Character, inv: Invocation)

entity Character {
    sustained_spells: list<Invocation>
    // ... other fields ...
}

action CastFlaming_Sphere on caster: Character (target_pos: Position) #sustained {
    let inv = invocation()
    apply_condition(self, Sustaining_Flaming_Sphere, indefinite)
    emit SpellSustained(caster: self, inv: inv)
}

// PF2e: multiple sustained spells allowed, tracked entirely in DSL state
hook track_sustain(caster: Character, inv: Invocation)
    when SpellSustained(caster: caster, inv: inv) {
    caster.sustained_spells = append(caster.sustained_spells, inv)
}

// End-of-turn: if the caster didn't sustain, the spell lapses
// (triggered by end-of-turn logic in the ruleset)
hook on_lapse(caster: Character, inv: Invocation)
    when SustainedSpellLapsed(caster: caster, inv: inv) {
    revoke(inv)
    caster.sustained_spells = remove(caster.sustained_spells, inv)
}
```

Different system, different rules, same language primitives. PF2e's multi-slot sustained spells use a `list<Invocation>` on the entity — no host-specific tracking needed.

### Failure Ordering Guidance

When an action applies conditions and registers for tracking (concentration, sustained, etc.), **apply conditions before emitting tracking events**:

```
action CastBless on caster: Character (targets: list<Character>) #concentration {
    let inv = invocation()
    // 1. Apply all conditions FIRST
    for target in targets {
        apply_condition(target, Blessed, rounds(10))
    }
    // 2. Register concentration LAST — only reached if all conditions applied
    emit ConcentrationStarted(caster: self, inv: inv)
}
```

If the action fails during condition application, the concentration event is never emitted — old concentration is preserved. Orphaned conditions from the failed invocation can be cleaned up by the host, which observes `ActionCompleted { outcome: Failed, invocation: Some(inv_id) }` and can call `remove_conditions_by_invocation(inv_id)` to remove partially-applied conditions.

Hosts observe `ActionCompleted { outcome: Failed }` and may perform defensive cleanup. This is a secondary safety net — the primary mechanism is the DSL-level ordering pattern above.

> **Future consideration:** Once the invocation/revoke primitives have been validated across multiple rulesets, packaging common invocation lifecycle patterns into a standard library (e.g., reusable templates for one-active-per-caster concentration, multi-slot sustained spells, channeled effects with tick-based duration) would reduce boilerplate and codify tested ordering rules. This is deferred until the primitives are battle-tested, but the design intentionally supports it — the patterns in the examples above are regular enough to template.

### InvocationId Allocation

**Automatic allocation:** Every action, reaction, and hook execution gets an `InvocationId` allocated when its body begins execution (inside `scoped_execute`, after gating). This is automatic — the DSL author doesn't need to opt in. Even if the body never calls `invocation()`, all conditions applied during that scope carry the invocation ID.

**Vetoed actions:** When the host vetoes an `ActionStarted`, `scoped_execute` is never entered and no `InvocationId` is allocated. This is correct — a vetoed action has no body execution, no conditions to tag, and nothing to revoke.

**Counter ownership:** `Interpreter` owns a `next_invocation_id: Cell<u64>` field, seeded from the host's durable counter at construction time. `Interpreter` exposes `alloc_invocation_id() -> InvocationId` (bumps and returns) and `next_invocation_id() -> u64` (reads current counter for persistence). `Env` stores the active invocation as `current_invocation_id: Option<InvocationId>`, set/restored by `scoped_execute`.

**Counter persistence:** `GameState` owns a `next_invocation_id: u64` field (starting at 1), following the same pattern as `next_entity_id` and `next_condition_id`. The host passes `state.next_invocation_id()` when constructing `Interpreter`, and reads back `interp.next_invocation_id()` after execution completes. The `Runner` uses a centralized helper (`with_interpreter`) that handles seeding and write-back on all return paths.

**Uniqueness:** `InvocationId` values must be unique within the lifetime of the game state. The monotonic `u64` counter guarantees this. IDs are never reused — once allocated, an `InvocationId` is consumed regardless of whether the action succeeds or fails. (Vetoed actions do not allocate IDs since their body never executes.)

### Action Lifecycle

**Always-paired guarantee:** The interpreter emits exactly one `ActionCompleted` for every `ActionStarted`, across all paths: normal completion, body failure (including default evaluation failure), veto, and unexpected handler responses. This is a behavioral change from the current code, where body failures skip `ActionCompleted`.

**`ActionStarted` does not carry invocation:** The invocation is allocated inside `scoped_execute` (phase 2), which occurs after `ActionStarted` is emitted (phase 1) and after the host's gate response. Vetoed actions never enter `scoped_execute` and never allocate an invocation — this avoids wasting IDs on actions that never execute. The host receives the invocation on `ActionCompleted`, which is sufficient for failure cleanup and observability.

**`ActionCompleted` carries invocation:** `ActionCompleted` includes `invocation: Option<InvocationId>` alongside `outcome: ActionOutcome`. Vetoed actions emit `ActionCompleted { outcome: Vetoed, invocation: None }` (no invocation allocated). Succeeded and failed actions emit `ActionCompleted { outcome: Succeeded|Failed, invocation: Some(id) }`. This gives the host the information needed for defensive cleanup on failure paths.

**Execution phase ordering:**

| Phase | Description | Error behavior |
|---|---|---|
| 1. Emit `ActionStarted` | Host gates the action | Vetoed → `ActionCompleted(Vetoed, invocation: None)`, return. Unexpected → `ActionCompleted(Failed, invocation: None)`, error. |
| 2. Enter `scoped_execute` | Allocate `InvocationId`, set scope | Infallible |
| 3. Bind receiver + supplied args | Bind known parameters in scope | Infallible |
| 4. Evaluate defaults | Default expressions for missing optional params | Error → `ActionCompleted(Failed, invocation: Some(id))` |
| 5. Execute pipeline | `requires`, `cost`, `resolve` | Error → `ActionCompleted(Failed, invocation: Some(id))` |
| 6. Restore scope | Pop scope, restore previous invocation | Infallible |
| 7. Emit `ActionCompleted` | Always emitted with appropriate `outcome` and `invocation` | Body error takes precedence |

Default parameter evaluation (phase 4) occurs **inside** `scoped_execute`, after invocation context is established (phase 2). This ensures that any conditions applied as side effects of default expression evaluation carry the correct invocation tagging, and that default evaluation failures are covered by the always-emit `ActionCompleted` guarantee.

Reactions and hooks follow the same phase ordering but skip phase 4 (no default parameters).

**Emission error handling:** On the success path, completion emission errors propagate. On the error path, the original body error takes precedence — completion is emitted but if the handler also fails, the body error is returned.

**Host recovery rule:** When execution returns `Err` and the host has a pending `ActionStarted` without an observed `ActionCompleted`, the host should treat the error as an implicit `ActionCompleted { outcome: Failed }` for that pending action. In practice, the always-paired guarantee means this is a fallback for catastrophic errors only.

### Invocation Invariants

| Context | `invocation` on conditions | Rationale |
|---|---|---|
| `apply_condition` inside action/reaction/hook body | `Some(InvocationId)` | `scoped_execute` always sets `current_invocation_id` |
| `apply_condition` outside action context (top-level script, CLI `grant`) | `None` | No enclosing action scope |
| Host-injected conditions (manual state manipulation) | `None` | Host's choice |

### Nested Invocation Trace

Action `Bless` (invocation A) applies conditions, then emits an event which triggers hook `OnConc` (invocation B). The hook revokes old concentration and stores the new invocation.

```
Interpreter counter starts at: next_invocation_id = 5

1. execute_action("Bless", caster=Entity(1))
   ├─ emit ActionStarted { name: "Bless", kind: Action, actor: Entity(1) }
   │   → Host: Acknowledged
   ├─ scoped_execute begins
   │   ├─ alloc_invocation_id() → InvocationId(5), counter becomes 6
   │   ├─ set: current_invocation_id = Some(InvocationId(5))
   │   ├─ body begins
   │   │   ├─ let inv = invocation() → Value::Invocation(InvocationId(5))
   │   │   ├─ apply_condition(target=Entity(2), Blessed, 10 rounds)
   │   │   │   └─ emit ApplyCondition { invocation: Some(InvocationId(5)), ... }
   │   │   ├─ apply_condition(target=Entity(3), Blessed, 10 rounds)
   │   │   │   └─ emit ApplyCondition { invocation: Some(InvocationId(5)), ... }
   │   │   │
   │   │   ├─ emit ConcentrationStarted(caster: Entity(1), inv: Invocation(5))
   │   │   │   └─ hook on_conc fires with inv=Invocation(5)
   │   │   │       ├─ emit ActionStarted { name: "on_conc", kind: Hook, actor: Entity(1) }
   │   │   │       │   → Host: Acknowledged
   │   │   │       ├─ scoped_execute begins for hook
   │   │   │       │   ├─ alloc_invocation_id() → InvocationId(6), counter becomes 7
   │   │   │       │   ├─ save: prev_invocation = Some(InvocationId(5))
   │   │   │       │   ├─ set: current_invocation_id = Some(InvocationId(6))
   │   │   │       │   ├─ hook body: revoke(old_inv), store some(Invocation(5)) on caster.concentrating_on
   │   │   │       │   └─ restore: current_invocation_id = Some(InvocationId(5))
   │   │   │       ├─ emit ActionCompleted { name: "on_conc", outcome: Succeeded, invocation: Some(InvocationId(6)) }
   │   │   │
   │   │   └─ body completes
   │   └─ restore: current_invocation_id = None
   ├─ emit ActionCompleted { name: "Bless", outcome: Succeeded, invocation: Some(InvocationId(5)) }

Interpreter counter ends at: next_invocation_id = 7
→ Host persists 7 to GameState.next_invocation_id

Result: Entity(2) and Entity(3) have Blessed with invocation=5
        revoke(Invocation(5)) removes both conditions
        The hook's own invocation (6) tagged nothing (hook applied no conditions)
```

### Parser Disambiguation: `revoke` Statement vs `revoke()` Call

The DSL already uses `revoke` as a statement keyword for entity group revocation: `revoke entity.GroupName`. The new `revoke()` builtin is a function call. These are disambiguated at parse time:

```rust
// In parse_stmt:
if self.at_ident("revoke") && !matches!(self.peek_at(1), TokenKind::LParen) {
    return self.parse_revoke_stmt();
}
// Falls through to expression statement parsing → handles revoke(inv) as function call
```

When the parser sees `revoke(`, it skips revoke statement parsing and falls through to expression parsing, which parses `revoke(inv)` as a function call. When it sees `revoke entity.Group`, it enters the existing `parse_revoke_stmt` path. No ambiguity.

### Debugging

Invocation data is accessible through the existing `StateProvider::read_conditions` path — any host that displays conditions can surface the `invocation` field alongside them. The CLI's `inspect` command will show invocation IDs on conditions once `ActiveCondition` carries the field.

> **Future consideration:** Dedicated query capabilities for invocation data would improve operability: filtering conditions by invocation ID, listing all conditions tied to a stored entity field value, and querying which invocation a specific condition belongs to. These are natural extensions of the `inspect` command and are deferred to future work.

> **Future consideration:** Invocation tracking currently scopes to conditions (via `ActiveCondition.invocation`), but the abstraction is general enough to extend to other persistent effects — summoned entities, conjured zones, temporary resources — that should be revoked together when their source action is undone. Extending `revoke(inv)` to remove non-condition effects would require invocation tagging on those effect types and corresponding `WritableState` cleanup methods. The current design is forward-compatible with this extension: `InvocationId` and `revoke()` can broaden their scope without changing the DSL-level API.

## Effect Contract Table

| Effect | Emitter | New/Changed Fields | Handler | Expected Response |
|---|---|---|---|---|
| `ApplyCondition` | Interpreter | + `invocation: Option<InvocationId>` | Adapter → State | `Acknowledged` |
| `ActionCompleted` | Interpreter | + `outcome: ActionOutcome`, + `invocation: Option<InvocationId>` | Host (`EffectHandler`) | `Acknowledged` |
| `RevokeInvocation` | Interpreter (via `revoke()` builtin) | New variant: `{ invocation: InvocationId }` | Adapter → State | `Acknowledged` |

`ActionStarted` is unchanged — no new fields.

## Files to Modify

### 1. `crates/ttrpg_ast/src/ast.rs` — AST types

- Add `Invocation` variant to `TypeExpr`
- Add `pub tags: Vec<Name>` to `ActionDecl`

### 2. `crates/ttrpg_interp/src/state.rs` — Core types

- Add `InvocationId(pub u64)` newtype (after `EntityRef`, same derive set)
- Add `invocation: Option<InvocationId>` field to `ActiveCondition`
- Add `remove_conditions_by_invocation(&mut self, invocation: InvocationId)` as a required method on `WritableState`
- Fix `ActiveCondition` literals in tests: add `invocation: None`

### 3. `crates/ttrpg_interp/src/value.rs` — Runtime values

- Add `Value::Invocation(InvocationId)` variant
- Update `discriminant()`, `PartialEq`, `Ord`, `Hash`, `type_name()`

### 4. `crates/ttrpg_interp/src/effect.rs` — Effect types

- Add `ActionOutcome` enum (after `FieldChange`, before `Effect`)
- Add `invocation: Option<InvocationId>` to `Effect::ApplyCondition`
- Add `outcome: ActionOutcome` and `invocation: Option<InvocationId>` to `Effect::ActionCompleted`
- Add `Effect::RevokeInvocation { invocation: InvocationId }` variant
- Add `RevokeInvocation` to `EffectKind` enum and `EffectKind::of()`
- Fix `Effect::ApplyCondition` / `ActionCompleted` literals in tests

### 5. `crates/ttrpg_interp/src/lib.rs` — Interpreter and Env

Add counter to `Interpreter` with interior mutability:
```rust
use std::cell::Cell;

pub struct Interpreter<'p> {
    pub(crate) type_env: &'p TypeEnv,
    pub(crate) program: &'p Program,
    next_invocation_id: Cell<u64>,
}

impl<'p> Interpreter<'p> {
    /// Existing constructor — defaults invocation counter to 1.
    pub fn new(program: &'p Program, type_env: &'p TypeEnv) -> Result<Self, RuntimeError> {
        // ... existing validation ...
        Ok(Interpreter { type_env, program, next_invocation_id: Cell::new(1) })
    }

    /// Constructor with explicit counter start for hosts that persist the counter.
    pub fn new_with_invocation_start(
        program: &'p Program,
        type_env: &'p TypeEnv,
        start: u64,
    ) -> Result<Self, RuntimeError> {
        let interp = Self::new(program, type_env)?;
        interp.next_invocation_id.set(start);
        Ok(interp)
    }

    /// Allocate and return the next InvocationId. Bumps the internal counter.
    /// Panics on u64 overflow (not practically reachable, but prevents silent wraparound).
    pub(crate) fn alloc_invocation_id(&self) -> InvocationId {
        let id = self.next_invocation_id.get();
        self.next_invocation_id.set(
            id.checked_add(1).expect("InvocationId counter overflow (u64 exhausted)")
        );
        InvocationId(id)
    }

    /// Read the current counter value (for host persistence after execution).
    pub fn next_invocation_id(&self) -> u64 {
        self.next_invocation_id.get()
    }
}
```

Add scope-tracking field to `Env`:
```rust
pub(crate) struct Env<'a, 'p> {
    // ... existing fields ...
    pub current_invocation_id: Option<InvocationId>,
}
```

`Env::new()` signature is **unchanged**. New field defaults to `None`.

### 6. `crates/ttrpg_interp/src/action.rs` — Execution pipeline

Key changes:
1. `execute_action`: veto/unexpected paths emit `ActionCompleted` with `outcome` and `invocation: None` before returning
2. `scoped_execute`: allocate invocation, set/restore scope, always emit `ActionCompleted` with outcome and `invocation: Some(id)`
3. Default parameter evaluation moves *inside* `scoped_execute`'s body closure (after invocation context is set)

In `execute_action`, update gate handling:
```rust
match response {
    Response::Acknowledged => {},
    Response::Vetoed => {
        emit_action_completed(env, &action_name, actor, ActionOutcome::Vetoed, None, call_span)?;
        return Ok(Value::None);
    }
    other => {
        let _ = emit_action_completed(env, &action_name, actor, ActionOutcome::Failed, None, call_span);
        return Err(RuntimeError::with_span(
            format!("protocol error: expected Acknowledged or Vetoed for ActionStarted, got {:?}", other),
            call_span,
        ));
    }
}
```

Modify `scoped_execute` to allocate invocation, set/restore scope, and always emit `ActionCompleted`:
```rust
fn scoped_execute(
    env: &mut Env,
    name: &str,
    actor: EntityRef,
    call_span: Span,
    body: impl FnOnce(&mut Env) -> Result<Value, RuntimeError>,
) -> Result<Value, RuntimeError> {
    let prev_turn_actor = env.turn_actor.take();
    let prev_invocation = env.current_invocation_id.take();

    env.turn_actor = Some(actor);
    let inv_id = env.interp.alloc_invocation_id();
    env.current_invocation_id = Some(inv_id);
    env.push_scope();

    let result = body(env);

    env.pop_scope();
    env.turn_actor = prev_turn_actor;
    env.current_invocation_id = prev_invocation;

    // Always emit ActionCompleted with outcome and invocation
    let outcome = if result.is_ok() { ActionOutcome::Succeeded } else { ActionOutcome::Failed };
    let completion = emit_action_completed(env, name, actor, outcome, Some(inv_id), call_span);

    match result {
        Ok(val) => {
            // Success path: completion emission errors propagate
            completion?;
            Ok(val)
        }
        Err(e) => {
            // Error path: body error takes precedence (completion was attempted)
            Err(e)
        }
    }
}
```

**Behavioral change from current code:** The current `scoped_execute` only emits `ActionCompleted` when `result.is_ok()`. The new version restores scope first, then always emits `ActionCompleted` with explicit error-precedence handling.

`execute_reaction` and `execute_hook` follow the same pattern. They skip default parameter evaluation since reactions and hooks have no default parameters.

> **Design note:** The three execution paths (`execute_action`, `execute_reaction`, `execute_hook`) share the same lifecycle pattern: emit `ActionStarted` → handle gate response → `scoped_execute` → emit `ActionCompleted`. During implementation, consider extracting this shared lifecycle into a helper (e.g., `execute_with_lifecycle`) that takes the path-specific binding/body logic as a closure. This would reduce duplication and ensure protocol changes are applied uniformly across all three paths.

### 7. `crates/ttrpg_interp/src/builtins.rs` — Builtin implementations

Add `invocation()` and `revoke()` to dispatch and implement:

```rust
fn builtin_invocation(env: &Env, _args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    match env.current_invocation_id {
        Some(id) => Ok(Value::Invocation(id)),
        None => Err(RuntimeError::with_span(
            "invocation() can only be called inside an action, reaction, or hook",
            span,
        )),
    }
}

fn builtin_revoke(env: &mut Env, args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    match args.first() {
        Some(Value::Invocation(inv_id)) => {
            let effect = Effect::RevokeInvocation { invocation: *inv_id };
            validate_mutation_response(env.handler.handle(effect), "RevokeInvocation", span)?;
            Ok(Value::None)
        }
        Some(Value::None) => Ok(Value::None),  // no-op for option<Invocation> = none
        // ... error cases ...
    }
}
```

Auto-tag `apply_condition` (both arms):
```rust
let effect = Effect::ApplyCondition {
    target: *target,
    condition: cond_name.clone(),
    params: cond_args.clone(),
    duration: duration.clone(),
    invocation: env.current_invocation_id,
};
```

### 8. `crates/ttrpg_interp/src/reference_state.rs` — GameState

- Add `next_invocation_id: u64` field (init to 1), with accessor/setter
- Update `apply_condition` to accept `invocation: Option<InvocationId>`, pass to `ActiveCondition`
- Implement `remove_conditions_by_invocation`:
  ```rust
  fn remove_conditions_by_invocation(&mut self, invocation: InvocationId) {
      for conds in self.conditions.values_mut() {
          conds.retain(|c| c.invocation != Some(invocation));
      }
  }
  ```

### 9. `crates/ttrpg_interp/src/adapter.rs` — StateAdapter

- Pass `invocation` through in `apply_mutation` `ApplyCondition` arm → include in `ActiveCondition`
- Same for `apply_mutation_with_override`
- Add `RevokeInvocation` arm: `state.remove_conditions_by_invocation(invocation)`
- Update `MUTATION_KINDS` from `[EffectKind; 6]` to `[EffectKind; 7]`

### 10. `crates/ttrpg_checker/src/ty.rs` — Checker types

- Add `Ty::Invocation` variant, update `display()` → `"Invocation"`

### 11. `crates/ttrpg_checker/src/builtins.rs` — Builtin signatures

```rust
builtin("invocation", vec![], Ty::Invocation),
builtin("revoke", vec![param("inv", Ty::Invocation)], Ty::Unit),
```

**Scope validation for `invocation()`:** Add `"invocation"` to `check_builtin_permissions` following the same pattern as `"roll"` and `"apply_condition"`:

```rust
"invocation" => {
    if !self.scope.allows_invocation() {
        self.error(
            "invocation() can only be called in action, reaction, or hook blocks".to_string(),
            span,
        );
    }
}
```

Add `allows_invocation()` to `BlockKind` in `scope.rs` — same permission set as `allows_mutation()`:
```rust
pub fn allows_invocation(&self) -> bool {
    matches!(self, BlockKind::ActionResolve | BlockKind::ReactionResolve | BlockKind::HookResolve)
}
```

**Scope context for action defaults:** Action parameter default expressions are checked within the action's `ActionResolve` block scope (via `bind_params` called inside the action body check), so `invocation()` is permitted in default expressions and will work correctly at runtime (defaults are evaluated inside `scoped_execute` after invocation context is established). Reactions and hooks have no default parameters, so this is relevant only to actions.

**Type coercion for `revoke`:** In the argument type-checking path, permit `option<Invocation>` where `Invocation` is expected for the `revoke` builtin. This is a targeted special case — `revoke` is the only builtin that commonly receives nullable entity field values. See the Design rationale under Builtins above for the trade-off analysis.

### 12. `crates/ttrpg_checker/src/env.rs` — Type resolution

- Add `TypeExpr::Invocation => Ty::Invocation` in `resolve_type_inner`

### 13. `crates/ttrpg_checker/src/collect.rs` — Action tag collection

- Line 942: change `&[]` to `&a.tags` in `collect_action`'s call to `collect_fn`

### 14. `crates/ttrpg_parser/src/decl.rs` — Parse tags on actions

In `parse_action_decl`, after the closing `RParen` of the parameter list (line 418) and before `LBrace` (line 419), parse tags:

```rust
let mut tags = Vec::new();
while matches!(self.peek(), TokenKind::Hash) {
    self.advance();
    let (tag_name, _) = self.expect_ident()?;
    tags.push(tag_name);
}
```

Same pattern as `parse_fn_body` (lines 298-304). The parameter list follows the receiver clause in the action grammar (`action Name on receiver: Type (params) #tags { ... }`), so this position is unambiguously after the receiver has been parsed.

### 15. `crates/ttrpg_parser/src/types.rs` — Parse `Invocation` type

- Add `"Invocation"` to the type keyword match

### 16. `crates/ttrpg_parser/src/stmt.rs` — Disambiguate `revoke`

- Line 49: `if self.at_ident("revoke") && !matches!(self.peek_at(1), TokenKind::LParen)`

### 17. `crates/ttrpg_cli/src/effects.rs` — CliHandler

- Pass `invocation` through in `ApplyCondition` handler
- Handle `ActionCompleted` with new `outcome` and `invocation` fields — log outcome:
  - `[ActionCompleted] Bless (inv=5) by Entity(1) — succeeded`
  - `[ActionCompleted] Bless by Entity(1) — vetoed`
  - `[ActionCompleted] Bless (inv=5) by Entity(1) — failed`
- Add `RevokeInvocation` handler: call `game_state.remove_conditions_by_invocation()`, log it

### 18. `crates/ttrpg_cli/src/runner/` — Runner

Add a centralized helper in `runner/mod.rs`:
```rust
fn with_interpreter<F, T>(&mut self, f: F) -> Result<T, CliError>
where
    F: FnOnce(&Interpreter, &RefCellState, &mut CliHandler) -> Result<T, RuntimeError>,
{
    let inv_start = self.game_state.borrow().next_invocation_id();
    let interp = Interpreter::new_with_invocation_start(
        &self.program, &self.type_env, inv_start,
    ).map_err(|e| CliError::Message(format!("interpreter error: {}", e)))?;
    let state = RefCellState(&self.game_state);
    let mut handler = CliHandler::new(
        &self.game_state, &self.reverse_handles, &mut self.rng, &mut self.roll_queue,
    );
    let result = f(&interp, &state, &mut handler);
    // Always writes back, regardless of success or failure
    self.game_state.borrow_mut().set_next_invocation_id(interp.next_invocation_id());
    for line in handler.log.drain(..) {
        self.output.push(line);
    }
    result.map_err(|e| CliError::Message(format!("runtime error: {}", e)))
}
```

Call site migration: `cmd_do` (action execution) and `cmd_call` (mechanic execution) use `with_interpreter`. Other `Interpreter::new` call sites (validation-only, expression evaluation) continue unchanged.

### 19. Fix all remaining struct literal compilation errors

Run `cargo check` — the compiler will flag every site. Known hotspots:
- `ActiveCondition { ... }` literals → add `invocation: None`
- `Effect::ApplyCondition { ... }` matches → add `invocation`
- `Effect::ActionCompleted { ... }` matches → add `outcome` and `invocation`
- `ActionDecl { ... }` literals → add `tags: vec![]`
- `WritableState` implementations → add `remove_conditions_by_invocation`

### 20. Display + type utilities

- `crates/ttrpg_cli/src/format.rs`: `Value::Invocation(id) => format!("Invocation({})", id.0)`
- `crates/ttrpg_cli/src/runner/util.rs`: `value_matches_ty` and `value_type_display`

## Breaking Changes & Migration

### Signature Delta

| Item | Change | Detail |
|---|---|---|
| **New types** | | |
| `InvocationId(pub u64)` | Added | Execution invocation identifier newtype |
| `ActionOutcome` | Added | `Succeeded \| Vetoed \| Failed` |
| **Modified structs** | | |
| `ActiveCondition` | + field | `invocation: Option<InvocationId>` |
| `ActionDecl` | + field | `tags: Vec<Name>` |
| `Interpreter` | + field | `next_invocation_id: Cell<u64>` (private) |
| `Env` | + field | `current_invocation_id: Option<InvocationId>` |
| **Modified enum variants** | | |
| `Effect::ApplyCondition` | + field | `invocation: Option<InvocationId>` |
| `Effect::ActionCompleted` | + fields | `outcome: ActionOutcome`, `invocation: Option<InvocationId>` |
| `TypeExpr` | + variant | `Invocation` |
| `Ty` | + variant | `Invocation` |
| `Value` | + variant | `Invocation(InvocationId)` |
| **New enum variant** | | |
| `Effect::RevokeInvocation` | Added | `{ invocation: InvocationId }` |
| `EffectKind::RevokeInvocation` | Added | Discriminant for adapter routing |
| **Modified traits** | | |
| `WritableState` | + method | `remove_conditions_by_invocation(&mut self, invocation: InvocationId)` |
| **New `Interpreter` methods** | | |
| `new_with_invocation_start(...)` | Added | Constructor with explicit counter start |
| `alloc_invocation_id()` | Added | `pub(crate)` — allocate next invocation ID |
| `next_invocation_id()` | Added | `pub` — read counter for persistence |

**Migration approach:** Compatibility constructors (`Interpreter::new()` with default counter, `Env::new()` unchanged) mean the vast majority of call sites require no changes. The `ActiveCondition` field addition and `Effect` variant changes are mechanical (compiler-guided).

### Serialization Compatibility

- **`ActiveCondition.invocation`**: Default to `None` when the field is absent. Preserves semantics of "applied externally" for pre-change conditions.
- **`GameState.next_invocation_id`**: This field is authoritative post-migration and must be persisted. When the field is absent during deserialization from pre-change data, default to `1` if no invocation-tagged data exists. For corrupt state recovery where the counter is lost but other data survives, derive from `max(InvocationId)` across all invocation references in the state — active conditions (`ActiveCondition.invocation`) **and** entity field values of type `Invocation` or `option<Invocation>` (e.g., `concentrating_on`) — plus one. Note that transient structures (event payloads, in-flight variables) are not scannable; the persisted counter is the only reliable source for normal operation.
- A **compatibility test** should load a pre-change state fixture and verify that deserialization produces correct defaults and that the resulting state passes basic read/write operations.

## Implementation Order

1. `state.rs` — `InvocationId` newtype, `ActiveCondition.invocation`, `WritableState::remove_conditions_by_invocation`
2. `value.rs` — `Value::Invocation(InvocationId)` with full trait impls
3. `effect.rs` — `ActionOutcome` enum, `Effect::ApplyCondition.invocation`, `Effect::ActionCompleted.outcome` + `.invocation`, `Effect::RevokeInvocation`, `EffectKind`
4. `ast.rs` — `TypeExpr::Invocation`, `ActionDecl.tags`
5. `ty.rs` — `Ty::Invocation`
6. Fix all struct literal compilation errors (compiler-guided)
7. `types.rs` (parser) — parse `Invocation` type keyword
8. `decl.rs` (parser) — parse `#tag` on actions
9. `stmt.rs` (parser) — disambiguate `revoke` statement vs `revoke()` call
10. `env.rs` (checker) — resolve `TypeExpr::Invocation`
11. `collect.rs` (checker) — pass `&a.tags` to `collect_fn`
12. `builtins.rs` (checker) — register `invocation()` and `revoke()` signatures; add `allows_invocation()` to `BlockKind`; add scope validation in `check_builtin_permissions`; add `option<Invocation>` coercion for `revoke` argument
13. `lib.rs` (interp) — `Interpreter` counter with `checked_add`, `Env.current_invocation_id`
14. `action.rs` (interp) — allocate invocation in `scoped_execute`, always emit `ActionCompleted` with outcome and invocation, veto/unexpected handling with paired completion
15. `builtins.rs` (interp) — implement `invocation()`, `revoke()` (with `none` no-op), auto-tag `apply_condition`
16. `reference_state.rs` — `GameState` counter, `remove_conditions_by_invocation`, updated `apply_condition`
17. `adapter.rs` — pass invocation through, handle `RevokeInvocation`, update `MUTATION_KINDS`
18. `effects.rs` (CLI) — handle `ActionCompleted.outcome` + `.invocation`, handle `RevokeInvocation` in `CliHandler`
19. `runner/` (CLI) — `with_interpreter` helper, migrate `cmd_do`/`cmd_call`
20. Display/type utilities
21. Tests

## Tests

**Unit tests in `state.rs`:**
- `InvocationId` equality, ordering, hashing

**Unit tests in `reference_state.rs`:**
- Invocation round-trip: apply condition with invocation, read it back, assert match
- Invocation removal: apply 3 conditions (two from invocation 1, one from invocation 2, one with None), remove invocation 1, assert only 2 remain
- Cross-entity removal: conditions on 3 different entities from same invocation, remove invocation, assert all removed
- Counter persistence: `next_invocation_id()`, `set_next_invocation_id()`, verify round-trip

**Unit tests in `builtins.rs`:**
- `invocation()` returns `Value::Invocation(id)` inside action scope
- `invocation()` errors outside action scope
- `revoke(inv)` emits `RevokeInvocation` effect
- `revoke(none)` is a no-op (no effect emitted)

**Parser tests:**
- Parse `Invocation` type in event/field declarations
- Parse `#concentration` tag on action declaration
- `revoke entity.GroupName` still parses as revoke statement
- `revoke(inv)` parses as expression statement (function call)

**Checker tests:**
- Checker accepts `invocation()` call in action body
- Checker accepts `invocation()` call in reaction body
- Checker accepts `invocation()` call in hook body
- Checker **rejects** `invocation()` call in derive body (compile-time error)
- Checker **rejects** `invocation()` call at top level (compile-time error)
- Checker accepts `revoke(inv)` call with `Invocation` type
- Checker accepts `revoke(field)` call with `option<Invocation>` type
- Checker rejects undeclared tags on actions

**Interpreter counter tests:**
- `alloc_invocation_id` returns monotonically increasing IDs
- `new_with_invocation_start` seeds correctly
- Counter continuity across error paths (IDs consumed even on failure)
- No ID reuse across interpreter invocations
- Overflow behavior: `checked_add` panics on `u64::MAX`

**ActionCompleted lifecycle tests:**
- Successful action emits `ActionCompleted { outcome: Succeeded, invocation: Some(id) }`
- Failed action emits `ActionCompleted { outcome: Failed, invocation: Some(id) }`
- Vetoed action emits `ActionCompleted { outcome: Vetoed, invocation: None }`
- Unexpected response emits `ActionCompleted { outcome: Failed, invocation: None }` before error
- Every `ActionStarted` is paired with exactly one `ActionCompleted`

**Integration tests:**
- Full concentration scenario: CastBless → hook stores invocation → CastHex → hook revokes first → first conditions gone, second conditions present
- Action without `invocation()` call still tags conditions with invocation ID
- Nested invocations: hook inside action gets its own invocation ID
- `revoke()` with stored invocation from previous action removes correct conditions
- `revoke(none)` is a no-op — no conditions removed
- InvocationId continuity: two actions across separate interpreter invocations (same GameState), distinct invocation IDs
- Failure scenario: action fails mid-body, `ActionCompleted { outcome: Failed, invocation: Some(id) }` emitted, conditions from that invocation exist and can be revoked

**Existing tests:** `cargo test` — all pass with mechanical `invocation: None` / `tags: vec![]` / `outcome` / `invocation` additions.

## Verification

```bash
cargo check                   # no errors
cargo test                    # all existing + new tests pass
cargo clippy                  # clean
```