# Design: Condition Event Handlers

**Status:** Implemented

---

## Problem

Conditions that need to react to events currently require a separate top-level
`hook` declaration, disconnected from the condition that grants the behavior:

```
condition FireShield on bearer: Character stacking first {
    modify damage_roll(target: bearer) #fire {
        result = result - 2
    }
}

// Separate hook — not scoped to the condition's lifetime
hook FireShieldRetaliation on target: Character (
    trigger: MeleeHit(target: target)
) {
    // Must manually guard against condition absence
    if has_condition(target, FireShield) {
        let attacker = trigger.attacker
        apply_damage(attacker, roll(1d6 + 1).total, "fire")
    }
}
```

This has several problems:

- **Scattered behavior.** The condition's reactive logic lives in a different
  declaration, potentially in a different file.
- **Manual lifetime management.** The hook fires whether or not the condition
  is active. The author must add a `has_condition` guard and keep it in sync.
- **No stacking awareness.** If three `FireShield` instances exist with
  `stacking first`, the hook has no way to know which instance won. All three
  would pass the `has_condition` check.
- **No state access.** The hook cannot read or write the condition's private
  `state` fields.
- **No parameter access.** The hook cannot read the condition's parameters
  (e.g., caster level) without re-deriving them from the event payload.

Periodic blocks solved the analogous problem for phase-based effects. This
design solves it for event-driven effects.

## Goals

- Co-locate event-reactive logic with the condition that grants it
- Automatically scope handler lifetime to the condition's active duration
- Apply stacking winner filtering so only winning instances fire
- Provide access to `bearer`, `self`, `state`, condition params, and `trigger`
- Integrate into the existing `emit` → hook dispatch pipeline

## Non-Goals

- Replacing top-level hooks — hooks remain the right choice for unconditional
  reactions to events (e.g., `SpellInterruption`)
- Replacing periodic blocks — periodic blocks remain the right choice for
  phase-based processing with explicit combat-loop ordering
- Adding suppressibility — condition event handlers are mandatory (like hooks),
  not optional (like reactions). If the condition is active, the handler fires.
- Condition event handlers for reactions — only hook-like (mandatory) semantics.
  If player choice is needed, use a top-level `reaction`.

## Design

### Syntax

A new `on` clause inside condition blocks, with a trigger expression using the
same syntax as hook trigger bindings:

```
condition FireShield(caster_level: int) on bearer: Character
    stacking first
{
    modify damage_roll(target: bearer) #fire {
        result = result - 2
    }

    on MeleeHit(target: bearer) {
        let attacker = trigger.attacker
        let damage = roll(1d6 + caster_level).total
        apply_damage(attacker, damage, "fire")
        emit FireShieldDamage(source: bearer, target: attacker, amount: damage)
    }
}
```

The trigger expression follows the same fill-the-gaps binding semantics as
hooks and reactions:

```
on EventName(param: expr, ...)
```

- Named bindings claim their param slot by name
- Binding expressions are evaluated against event params (first) then fields
- The condition's receiver and params are in scope for binding expressions

### Scope Inside the Block

The handler body has access to:

- **`bearer`** — the entity carrying the condition (receiver)
- **`self`** — the `ActiveCondition` instance, same as periodic blocks
- **`trigger`** — the event payload as a struct (same as hooks)
- **Condition parameters** — bound from the active condition's parameter map
- **`state`** — mutable condition state fields (if declared)

This is the union of periodic block scope (bearer, self, state, params) and
hook scope (trigger). The body uses the same statement grammar as function
bodies.

**Unlike lifecycle blocks**, condition event handlers are not restricted from
calling `apply_condition()` or `remove_condition()`. They execute during event
dispatch, not during condition application.

#### Reserved Names

The following names are reserved inside conditions that declare `on` handlers
and cannot be used as receiver names or parameter names:

- **`self`** — bound to the `ActiveCondition` instance (already reserved in
  periodic blocks)
- **`state`** — bound to the mutable condition state struct (already reserved
  in all condition blocks)
- **`trigger`** — bound to the event payload struct (new reservation for `on`
  handlers)

The checker emits a diagnostic if a condition's receiver or parameter name
shadows any of these reserved names. For `trigger`, the diagnostic is emitted
only when the condition declares at least one `on` handler.

### Multiple Handlers

A condition may declare multiple `on` handlers for different events:

```
condition MageArmor on bearer: Character stacking first {
    on MeleeHit(target: bearer) {
        // deflection effect
    }
    on SpellTargeted(target: bearer) {
        // spell resistance effect
    }
}
```

A condition may also declare multiple `on` handlers for the same event. All
matching handlers fire in clause order (the order they appear in the source):

```
condition Guardian on bearer: Character stacking first {
    on Damaged(target: bearer) {
        // self-damage reaction
    }
    on Damaged(target: ward) {
        // protect-the-ward reaction (ward is a condition param)
    }
}
```

If an event matches both handlers (e.g., `bearer` and `ward` are different
entities but both appear in the payload), both fire in clause order with state
threaded between them.

### Execution Semantics

When `emit EventName(...)` fires, the dispatch pipeline is:

1. Find and execute matching top-level hooks (existing behavior, unchanged)
2. Find and execute matching condition event handlers (new, against post-hook
   state)

Hooks execute first because they represent system-level invariants (e.g.,
`SpellInterruption` must resolve before condition-level effects). Condition
handlers execute second against post-hook state, ensuring they see any
mutations hooks made (conditions applied/removed, fields changed, etc.).

This also preserves backward compatibility — existing hook ordering is
unchanged.

#### Condition Handler Matching

After all top-level hooks for the event have executed, condition handler
discovery begins:

1. Collect all entity-typed values from the event payload, in **event parameter
   declaration order**, then **event field declaration order**
2. Deduplicate by entity ID, keeping the first occurrence's position for
   ordering purposes (prevents the same handler from firing multiple times
   because the entity appears in multiple payload slots)
3. For each unique entity, in the order established above:
   a. Snapshot that entity's active conditions
   b. Compute stacking winners
   c. For each winning condition instance (in application order):
      - Look up the condition declaration
      - For each `on` clause matching the event name (in clause order):
        - Evaluate trigger bindings in scope (receiver + condition params)
        - If all bindings match, the handler fires

#### Snapshot Semantics

The condition list for each entity is snapshotted before dispatching handlers
for that entity. This provides the same safety guarantees as periodic blocks:

- **Removed conditions are not revisited.** If a handler removes another
  condition on the same bearer, remaining snapshot entries for removed
  conditions are skipped.
- **Same-bearer applies do not fire.** Conditions applied to the same bearer
  during handler dispatch do not execute their handlers in this emit pass.
- **Already-started handlers complete.** Removing a condition does not cancel
  a handler that has already begun executing.

**Cross-bearer mutations are order-dependent.** The snapshot is per-entity.
If entity A's handler applies a condition to entity B (not yet processed),
entity B's snapshot will include the new condition.

#### Stacking Winner Filtering

Only stacking winners execute event handlers, using the same
`compute_stacking_winners()` as periodic blocks and modifier collection:

- **`stacking all`**: Every instance fires separately with its own `self`
- **`stacking first`**: Only the oldest instance fires
- **`stacking best by`**: Only the winning instance fires

#### State Threading

If multiple `on` handlers on the same condition instance fire in the same emit
(e.g., two handlers with different binding patterns both match), state is
threaded through them in clause order — the same pattern as periodic blocks
with multiple tags.

After all handlers for an instance complete, mutated state is written back via
`Effect::SetConditionState`.

### Interaction with Existing Systems

#### Suppress Clauses

Condition `suppress EventName(...)` clauses suppress **reactions**, not hooks
or condition event handlers. This is unchanged. Condition event handlers are
mandatory (like hooks) and cannot be suppressed via the `suppress` mechanism.

To prevent a condition event handler from firing, remove the condition.

#### Emit Depth

Condition event handlers participate in the existing emit depth limit
(`MAX_EMIT_DEPTH`). A handler that emits an event increments the depth counter.
This prevents infinite chains.

#### Off-Board Entities

Condition handlers only fire for entities returned by
`state.entities_in_play()`, consistent with hook dispatch.

#### Lifecycle Block Restrictions

Emit statements inside lifecycle blocks (`on_apply` / `on_remove`) already
fire hooks. They will also fire condition event handlers, subject to the
same `in_lifecycle_block` save/restore that hooks use.

### Worked Examples

**Example 1: FireShield — retaliation damage**

```
condition FireShield(caster_level: int) on bearer: Character
    stacking first
{
    on MeleeHit(target: bearer) {
        let attacker = trigger.attacker
        apply_damage(attacker, roll(1d6 + caster_level).total, "fire")
    }
}
```

Setup: Alice has `FireShield(caster_level: 5)`. Bob melees Alice.

```
emit MeleeHit(attacker: bob, target: alice)
```

1. Top-level hooks for `MeleeHit` fire (if any)
2. Condition handler discovery begins (post-hook state):
   a. Entity-typed payload values: `attacker` (bob), `target` (alice)
   b. Deduplicate: bob, alice (both unique)
3. Bob's conditions: snapshot, compute winners — no `on MeleeHit` handlers
4. Alice's conditions: snapshot → `[FireShield#1]`, winner = #1
5. FireShield's `on MeleeHit(target: bearer)` — evaluate binding: `bearer` =
   alice, event `target` = alice → match
6. Execute handler: bind bearer=alice, self=FireShield#1,
   trigger={attacker: bob, target: alice}, caster_level=5
7. `apply_damage(bob, roll(1d6+5).total, "fire")`

**Example 2: Stacking — only winner fires**

Setup: Alice has `FireShield#1(caster_level: 3)` and `FireShield#2(caster_level: 7)`.
Stacking is `first`, so #1 (oldest) wins.

```
emit MeleeHit(attacker: bob, target: alice)
```

1. Top-level hooks fire
2. Alice's conditions: snapshot → `[FireShield#1, FireShield#2]`
3. Winners = `{#1}` (stacking first → oldest)
4. FireShield#1 fires (caster_level=3), FireShield#2 skipped

**Example 3: Handler removes its own condition**

```
condition Thorns on bearer: Character stacking first {
    state { charges: int = 3 }

    on MeleeHit(target: bearer) {
        state.charges -= 1
        apply_damage(trigger.attacker, roll(1d4).total, "piercing")
        if state.charges <= 0 {
            remove_condition(bearer, "Thorns")
        }
    }
}
```

The handler completes fully (already-started handlers are not cancelled),
then on the next emit, the condition is gone and the handler no longer fires.

**Example 4: Cross-condition interaction**

```
condition Absorb on bearer: Character stacking first {
    on Damaged(target: bearer) {
        // Absorb fires for damage to bearer
        state.absorbed += trigger.amount
        if state.absorbed >= 50 {
            remove_condition(bearer, "Absorb")
        }
    }
}

condition Reflect on bearer: Character stacking first {
    on Damaged(target: bearer) {
        // Reflect fires for damage to bearer
        apply_damage(trigger.source, trigger.amount / 2, "force")
    }
}
```

Setup: Alice has both conditions. Snapshot: `[Absorb#1, Reflect#2]` (by
application order). Both are winners (different condition names, stacking is
per-name). Both handlers fire in application order.

If Absorb's handler removes Absorb, Reflect still fires (different condition).
If Absorb's handler had somehow removed Reflect, Reflect would be skipped
(snapshot entry for removed condition).

**Example 5: Periodic + event handler on same condition**

```
condition PoisonAura on bearer: Character stacking first {
    periodic #round_end_damage {
        // Passive: 1d4 poison damage per round to bearer
        bearer.hp -= roll(1d4).total
    }

    on MeleeHit(attacker: bearer) {
        // Reactive: poison on melee hit
        apply_condition(trigger.target, Poisoned, Duration.Rounds(3))
    }
}
```

The periodic block fires during `process_periodic_conditions(combatants,
"round_end_damage")`. The event handler fires during `emit MeleeHit(...)`.
Both share the same stacking winner computation and state threading, but fire
at different times through different dispatch paths.

**Example 6: Entity deduplication**

Setup: Alice has `SelfHarm` condition. Alice damages herself:

```
event SelfDamage { source: entity, target: entity }
emit SelfDamage(source: alice, target: alice)
```

Entity-typed payload values: `source` (alice), `target` (alice). After
deduplication: alice (once). Alice's condition handlers fire once, not twice.

## Pipeline Changes

### Shared Condition Traversal

The entity extraction → snapshot → stacking winners → existence check pipeline
is shared across suppress scanning, periodic processing, and condition event
handlers. Factor this into a reusable helper:

```rust
pub struct ConditionTraversal {
    /// Entity-typed values from payload, deduplicated, in scan order
    pub entities: Vec<(Name, EntityRef)>,
    /// Per-entity: snapshotted conditions with stacking winners computed
    pub snapshots: HashMap<EntityRef, ConditionSnapshot>,
}

pub struct ConditionSnapshot {
    pub conditions: Vec<ActiveCondition>,
    pub winners: HashSet<u64>,  // instance IDs that are stacking winners
}
```

Each consumer layers its mode-specific logic on top:

- **Suppress scanning:** checks `suppress` clauses on winners, returns bool
- **Periodic processing:** executes `periodic #tag` blocks on winners for a
  given tag
- **Condition event handlers:** matches `on` clauses on winners against the
  event, executes matching handler bodies

This reduces the chance of subtle ordering, stacking, or deduplication bugs
diverging across the three systems.

### AST (`ttrpg_ast`)

Add to `ConditionClause`:

```rust
OnEvent(OnEventClause),
```

```rust
pub struct OnEventClause {
    pub trigger: TriggerExpr,   // reuses existing TriggerExpr from hooks
    pub body: Block,
    pub span: Span,
}
```

This reuses `TriggerExpr` (event name + bindings) directly from the hook/
reaction AST, ensuring binding semantics stay unified.

### Parser (`ttrpg_parser`)

Add `parse_on_event_clause()` following the pattern of `parse_periodic_clause()`.
Triggered when the parser sees `on` followed by an identifier and `(` inside a
condition body.

```
on EventName(param: expr, ...) {
    <statements>
}
```

**Disambiguation:** Inside a condition body (after `{`), `on` followed by
`Ident` and `(` starts an event-handler clause. This is unambiguous:

- `on_apply` and `on_remove` are single underscore-joined tokens — the lexer
  produces them as `Ident("on_apply")` and `Ident("on_remove")`, not as `on`
  followed by `apply`.
- The condition header's `on bearer: Type` syntax only appears before the
  opening `{`, never inside the body.
- No other clause keyword inside condition bodies starts with `on`.

### Checker (`ttrpg_checker`)

Add `check_on_event_clause()`:

**Validation:**
- Event exists in the type environment
- Trigger bindings type-check (reuse `check_trigger_bindings()` from hook
  checking, or factor out shared logic)
- Binding expressions are side-effect-free (same `BlockKind::TriggerBinding`
  restriction as hooks)
- Body type-checks with full scope (bearer, self, state, params, trigger)
- Condition receiver and parameter names do not shadow `trigger`

**Scope binding:**
```rust
self.scope.push(BlockKind::OnEventBlock);  // new block kind
// Bind receiver (bearer)
self.scope.bind(c.receiver_name, VarBinding { ty: recv_ty, ... });
// Bind condition parameters
for param in &c.params {
    self.scope.bind(param.name, VarBinding { ty: param_ty, ... });
}
// Bind `self` as ActiveCondition
self.scope.bind("self", VarBinding { ty: Ty::ActiveCondition, ... });
// Bind state fields if present
if !state_ty_fields.is_empty() {
    self.scope.bind("state", VarBinding { ty: Ty::ConditionState(...), ... });
}
// Bind `trigger` as event payload struct
self.scope.bind("trigger", VarBinding { ty: event_payload_ty, ... });
self.check_block(&clause.body);
self.scope.pop();
```

**Trigger index registration:** Each condition `on` clause registers in a
new `condition_trigger_index` under the event name. This index is separate
from the hook/reaction trigger index.

### Trigger Index (`ttrpg_checker`)

Add a new index alongside the existing `trigger_index`:

```rust
pub condition_trigger_index: HashMap<Name, Vec<(Name, usize)>>,
// event_name → [(condition_name, clause_index)]
```

Populated during condition checking when `OnEvent` clauses are encountered.
Used by `find_matching_condition_handlers()` at runtime for efficient lookup.

This avoids polluting the function namespace with synthetic entries and keeps
the condition handler lookup path separate from hook/reaction lookup.

### Interpreter (`ttrpg_interp`)

#### Event Dispatch Extension (`event.rs`)

Add `find_matching_condition_handlers()`, built on the shared condition
traversal helper:

```rust
pub struct ConditionHandlerInfo {
    pub condition_name: Name,
    pub instance_id: u64,
    pub bearer: EntityRef,
    pub clause_index: usize,    // which OnEvent clause in the declaration
}

pub struct ConditionHandlerResult {
    pub handlers: Vec<ConditionHandlerInfo>,
}
```

This function:

1. Uses the shared traversal to collect entity-typed values, deduplicate,
   snapshot conditions, and compute stacking winners
2. For each winning instance, checks `OnEvent` clauses for trigger match
3. Returns matched handlers in entity order → application order → clause order

#### Emit Extension (`eval/emit.rs`)

Extend `eval_emit()` to dispatch condition handlers after hooks:

```rust
// Existing: execute top-level hooks
for hook_info in hook_result.hooks {
    action::execute_hook(env, ...)?;
}

// New: discover and execute condition event handlers (against post-hook state)
let cond_result = event::find_matching_condition_handlers(
    env.interp, env.state, event_name, &payload, &candidates,
)?;
for handler_info in cond_result.handlers {
    execute_condition_event_handler(env, &handler_info, payload.clone(), span)?;
}
```

#### Handler Execution

`execute_condition_event_handler()` follows the periodic block execution
pattern:

1. Look up condition declaration
2. Verify condition still exists on bearer (snapshot safety)
3. Push scope
4. Bind: `bearer`, `self` (ActiveCondition), condition params, `state`, `trigger`
5. Execute block body
6. Read back mutated state
7. Pop scope
8. Write back state via `Effect::SetConditionState`

No `ActionStarted`/`ActionCompleted` effects — condition handlers are not
actions. They are implicit effects of the condition's existence, like modifier
application.

## Migration Opportunities

Once implemented, existing patterns can be simplified:

### Example 1: Simple guard elimination

**Before:**
```
condition Concentrating on bearer: Character stacking first { }

hook OnConcentrationDamage on caster: Character with Spellcasting (
    trigger: Damaged(target: caster)
) {
    if has_condition(caster, Concentrating) {
        // concentration check
    }
}
```

**After:**
```
condition Concentrating on bearer: Character with Spellcasting as sc
    stacking first
{
    on Damaged(target: bearer) {
        // concentration check — only fires while Concentrating is active
        // no has_condition guard needed
    }
}
```

### Example 2: Stateful retaliation with charges

**Before:**
```
condition Thorns on bearer: Character stacking first {
    state { charges: int = 3 }
}

hook ThornsRetaliation on target: Character (
    trigger: MeleeHit(target: target)
) {
    if has_condition(target, Thorns) {
        // Must find the condition to read/write state — no direct access
        apply_damage(trigger.attacker, roll(1d4).total, "piercing")
        // Cannot decrement charges — state is inaccessible from hook
    }
}
```

**After:**
```
condition Thorns on bearer: Character stacking first {
    state { charges: int = 3 }

    on MeleeHit(target: bearer) {
        state.charges -= 1
        apply_damage(trigger.attacker, roll(1d4).total, "piercing")
        if state.charges <= 0 {
            remove_condition(bearer, "Thorns")
        }
    }
}
```

State access and self-removal are now natural — no workarounds needed.

### Example 3: Cross-bearer aura with explicit ordering

**Before:**
```
condition ProtectiveAura on bearer: Character stacking first { }

hook AuraDamageReduce on ward: Character (
    trigger: Damaged(target: ward)
) {
    // Must find which character has ProtectiveAura and is guarding this ward
    // Complex, error-prone, no stacking awareness
}
```

**After:**
```
condition ProtectiveAura(ward: entity) on bearer: Character stacking first {
    on Damaged(target: ward) {
        // Fires only while aura is active
        // trigger.amount has the damage, ward is the condition param
        // Stacking winner filtering applies automatically
    }
}
```

Execution sequence for `emit Damaged(source: orc, target: alice)`:
1. Top-level hooks for `Damaged` fire
2. Entity scan: `source` (orc), `target` (alice) — deduplicated
3. Orc's conditions: no `on Damaged` handlers
4. Alice's conditions: if Alice has `ProtectiveAura`, its handler fires;
   if Bob has `ProtectiveAura(ward: alice)`, Bob is not in the entity scan
   (he's neither source nor target), so his handler does **not** fire

Note: the cross-bearer case shows that condition event handlers only fire
when the bearer or a bound entity appears in the event payload's entity-typed
values. This is by design — it prevents scanning all entities in play.

Migration is optional and incremental — existing top-level hooks continue to
work.

## Test Matrix

| Scenario | Setup | Key behavior |
|----------|-------|--------------|
| Basic fire | Condition with `on` handler, emit matching event | Handler fires, trigger payload accessible |
| No match | Emit event that doesn't match any condition handler | No handler fires |
| Stacking first | Two instances, stacking first | Only oldest fires |
| Stacking best by | Two instances, stacking best by | Only winner fires |
| Stacking all | Two instances, stacking all | Both fire separately |
| Self-removal | Handler removes its own condition | Handler completes, condition gone on next emit |
| Cross-removal | Handler A removes condition B on same bearer | B's handler skipped (snapshot safety) |
| Same-bearer apply | Handler applies condition to same bearer | New condition does not fire in this emit |
| Cross-bearer | Handler applies condition to different bearer | New condition may fire if that bearer not yet processed |
| State mutation | Handler modifies state fields | State persisted via SetConditionState |
| State threading | Two handlers on same instance both match | State threaded in clause order |
| Hooks first | Top-level hook + condition handler for same event | Hook fires before condition handler |
| Post-hook state | Hook applies condition, condition has `on` handler for same event | Condition handler fires (discovered post-hook) |
| Emit depth | Handler emits event that triggers another handler | Depth limit prevents infinite chain |
| Off-board | Bearer is off-board | Handler does not fire |
| Condition params | Handler uses condition param in logic | Param correctly bound from instance |
| Trigger bindings | Handler uses condition param in binding expr | Binding evaluated with condition scope |
| With periodic | Condition has both periodic and on-event | Both work independently |
| Lifecycle block emit | on_apply emits event that triggers condition handler | Handler fires (lifecycle save/restore works) |
| Entity dedup | Same entity in multiple payload slots | Handler fires once, not once per slot |
| Reserved name | Condition param named `trigger` with `on` handler | Checker emits diagnostic |
| Multiple same-event | Two `on` handlers for same event, both match | Both fire in clause order |

## Decided

- **Clause keyword:** `on` — natural reading, unambiguous inside condition body
- **Semantics:** Hook-like (mandatory, not suppressible) — condition handlers
  represent inherent effects of having the condition
- **Dispatch model:** Execute hooks first, then discover and dispatch condition
  handlers against post-hook state
- **Handler ordering:** Entity order (param declaration order, then field
  declaration order, deduplicated) → condition application order → clause
  order within each condition
- **Entity deduplication:** Entities appearing in multiple payload slots are
  processed once, at the position of their first occurrence
- **Stacking:** Only stacking winners fire, same computation as periodic/modifiers
- **Snapshot:** Per-entity snapshot before dispatching handlers for that entity,
  same safety as periodic
- **State access:** Full mutable state access, threaded through handlers
- **Trigger index:** Separate `condition_trigger_index` (not mixed into hook index)
- **No ActionStarted/Completed:** Handlers are not actions — no lifecycle effects
- **Multiple handlers:** Multiple `on` handlers for the same event are allowed;
  all matching handlers fire in clause order
- **Reserved names:** `trigger` is reserved in conditions with `on` handlers
- **Shared traversal:** Entity extraction, snapshotting, and stacking winner
  computation are factored into a reusable helper shared with suppress and
  periodic processing

## Future Work

- **Condition reactions:** `react EventName(...) cost { ... } { ... }` syntax
  for optional, player-chosen responses scoped to a condition's lifetime.
  Deferred until a concrete use case appears.
- **Handler priority:** If ordering between condition handlers on different
  bearers matters beyond entity order, a priority annotation could be added.
  Not needed for initial implementation.
- **Suppress condition handlers:** A `suppress_handler` mechanism could allow
  one condition to block another condition's event handlers. This would be
  analogous to `suppress_modify` but for event handlers. Deferred.

## Open Questions

- **Should condition event handlers emit ActionStarted/ActionCompleted?**
  The current design says no (they're implicit effects, not player-visible
  actions). But if the host needs to intercept or veto them, action lifecycle
  effects would be needed. This could be added later without breaking changes.
- **Trigger binding scope: should `self` be available in bindings?** Hook
  trigger bindings are side-effect-free expressions. Allowing `self` (the
  ActiveCondition) in binding expressions would enable patterns like
  `on Damaged(target: bearer, source: self.source)`. This requires binding
  `self` before evaluating trigger expressions, which is feasible since the
  condition instance is known at match time.
