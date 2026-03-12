# Design: transfer_conditions Builtin

**Status:** Implemented

---

## Problem

The polymorph pattern (suspend original, spawn form entity, link via condition)
works mechanically — HP syncs, suspension/restoration, despawn all function
correctly. But conditions on the original entity don't carry over to the form.

When a Blessed wizard polymorphs into a troll, the Blessed condition stays on
the suspended original. The troll form fights without the blessing. On revert,
conditions applied to the form (e.g., someone casts Curse on the troll) are
lost when the form is despawned.

Some conditions should transfer (mental/magical effects tied to identity) and
some should not (physical traits, equipment bonuses). The DSL's existing
condition tag system (`tags: #curse, #mental`) provides the natural
classification mechanism.

## Goals

- Move conditions between entities based on tag membership
- Allow transfer in lifecycle blocks (on_remove needs it for revert)
- Preserve condition identity: params, duration, source, tags all carry over
- Keep the API minimal — one builtin covers polymorph setup and revert

## Non-Goals

- Automatic polymorph condition management (ruleset authors choose what to tag)
- Stacking validation during transfer (transferred conditions are placed as-is)
- Firing on_apply/on_remove hooks during transfer (avoids reentrancy)
- Firing host gates during transfer (keeps transfer atomic; see Edge Cases)
- Replacing apply_condition/remove_condition for normal use cases

## Design

### Builtin Signature

```
transfer_conditions(from: entity, to: entity, tag: string) -> unit
```

- Moves all active conditions on `from` that have `tag` in their tag set to `to`
- The `tag` parameter is a **string literal** (e.g., `"transferable"`). The
  checker performs special-case validation: it resolves the string value against
  declared tags and reports undeclared tags as errors, similar to how other
  builtins validate specific argument forms. This matches the existing precedent
  set by `process_periodic_conditions`, which also takes a string for tag
  matching.
- If `from` and `to` refer to the same entity, the call is a no-op
- If either `from` or `to` does not exist, the call is a no-op (see Adapter
  preconditions below)
- Updates each condition's `bearer` to the target entity
- Preserves: `id`, `name`, `params`, `duration`, `applied_at`, `source`, `tags`,
  `invocation`, `gained_at`
- Does NOT fire on_apply on the target or on_remove on the source
- Does NOT fire host gates (ConditionApplyGate/ConditionRemovalGate)
- Returns unit (consistent with apply_condition/remove_condition)

**Future work:** If the language gains tag literals as a first-class expression
type (`#transferable` as a value), this signature should be updated to use
`Ty::Tag` instead of `Ty::String` for stronger compile-time guarantees.

**Future work:** Tags could declare a `transfer_safe` property
(`tag transferable: transfer_safe`), enabling the checker to mechanically
enforce the Transferable Condition Checklist. A condition tagged with a
`transfer_safe` tag would be verified at compile time:

- `on bearer: entity` (not a specific type)
- `stacking all` (no conflicts on destination)
- No mutation builtins (`suspend`, `spawn`, `despawn`) in lifecycle blocks
- `modify` blocks only target derives with `target: entity` parameters

`transfer_conditions` would then restrict its tag argument to
`transfer_safe` tags, rejecting non-safe tags at compile time. This is
purely additive — the current string-based API and convention checklist
work without it. Transitive analysis of function calls in lifecycle blocks
is a known limitation; a first pass checking direct builtin calls covers
the practical cases.

### Lifecycle Block Access

Unlike `apply_condition()`/`remove_condition()`, `transfer_conditions()` is
**allowed in lifecycle blocks** (on_apply/on_remove). The reentrancy concern
that motivates the lifecycle restriction for apply/remove does not apply here
because transfer does not fire lifecycle hooks or host gates.

This is critical for the polymorph revert path:

```ttrpg
condition Polymorphed(original: Character, suspension_key: int) on bearer: Monster
    stacking first
{
    on_remove {
        // Transfer mental conditions back to original before despawn
        transfer_conditions(bearer, original, "transferable")

        original.hp = bearer.hp
        remove_suspension_source(original, source_id: suspension_key)
        despawn(bearer)
    }
}
```

**Self-transfer safeguard:** When `transfer_conditions` executes inside an
`on_remove` block, the condition instance whose `on_remove` is currently
executing is **excluded from transfer**. Without this, the removing condition
could be moved to the destination mid-removal, causing the subsequent
`RemoveCondition` effect to target the wrong entity.

The interpreter maintains a **stack** of active lifecycle condition IDs
(`lifecycle_condition_stack: Vec<u64>`), pushed before entering a lifecycle
block and popped on exit. `transfer_conditions` excludes the **top-of-stack**
entry. This correctly handles nested lifecycle execution (e.g., an on_remove
that emits an effect triggering another on_remove): each nesting level tracks
its own active condition, and only the innermost is excluded.

This stack is a new field added alongside the existing `in_lifecycle_block: u32`
counter. The counter continues to gate apply/remove; the stack provides
instance-level identity for transfer exclusion.

### Mutation Context

`transfer_conditions()` requires a mutation context (same as apply/remove). It
is rejected in derive, mechanic, table, and prompt blocks.

### Tag Convention

Ruleset authors tag conditions that should follow the creature's identity:

```ttrpg
tag transferable

condition Blessed on bearer: entity {
    tags: #transferable
    // ...
}

condition Cursed on bearer: entity {
    tags: #transferable, #curse
    // ...
}

// Physical traits do NOT get the tag
condition Regeneration(hp_per_round: int) on bearer: entity {
    // No #transferable — stays with the body
}
```

#### Transferable Condition Checklist

Before tagging a condition as transferable, verify:

- [ ] **Bearer type is `entity`** — not a specific type like `Character` or
  `Monster`. Ensures type compatibility with any transfer target.
- [ ] **No bearer-scoped side effects in lifecycle hooks** — no `suspend()`,
  `spawn()`, or other operations that create external state keyed to the
  bearer entity. Transfer skips on_remove/on_apply, so this state won't be
  cleaned up or re-established.
- [ ] **No bearer-keyed host integrations** — no host-side state (custom
  tracking, UI bindings, external system registrations) tied to the original
  bearer identity.
- [ ] **Modify targets are compatible** — modify blocks should target derives
  with `target: entity` parameters, not type-specific ones like
  `character_movement(character: Character)` that won't match after transfer
  to a different entity type.
- [ ] **Stacking policy is safe** — use `stacking all` or ensure the condition
  can't conflict with itself on the destination. Transfer bypasses stacking
  evaluation.

### Usage Pattern

```ttrpg
function polymorph_other(target: Character, form: Monster, key: int, dur: Duration) {
    // Move mental/magical conditions to the form
    transfer_conditions(target, form, "transferable")

    // Suspend original
    suspend_with_source(target, source_id: key,
        Presence.OffBoard, freeze_turns: true, freeze_durations: true)

    // Set form HP from original and link
    form.hp = target.hp
    form.max_hp = target.max_hp
    apply_condition(form, Polymorphed(original: target, suspension_key: key), dur)
}
```

On revert (in Polymorphed's on_remove), `transfer_conditions(bearer, original,
"transferable")` moves them back.

## Implementation

### Effect

New variant in `Effect` enum:

```rust
TransferConditions {
    from: EntityRef,
    to: EntityRef,
    tag: Name,
    /// Condition instance to exclude (e.g., the currently-removing condition).
    /// None when called outside a lifecycle block.
    exclude_instance: Option<u64>,
}
```

New `EffectKind::TransferConditions` discriminant. Added to `MUTATION_KINDS`.

### Builtin (interpreter)

In `builtins.rs`, add `builtin_transfer_conditions`:

- Signature: `(entity, entity, string) -> unit`
- No lifecycle block restriction (no `in_lifecycle_block` check)
- Does check `allows_mutation` context
- Reads `env.lifecycle_condition_stack.last()` to populate `exclude_instance`
- Emits `Effect::TransferConditions { from, to, tag, exclude_instance }`

### Adapter

In `apply_mutation`, handle `Effect::TransferConditions`:

**Preconditions** (checked before any mutation):

1. If `from == to`, return early (no-op)
2. Verify `from` exists via `state.read_conditions(&from)` — if `None`, emit
   a runtime warning and return (no-op)
3. Verify `to` exists via `state.read_conditions(&to)` — if `None`, emit a
   runtime warning and return (no-op)

Both entity checks happen before any condition is removed. This prevents the
data-loss scenario where conditions are removed from `from` but `add_condition`
silently drops them because `to` doesn't exist. Full transaction semantics are
not needed because once preconditions pass, each individual remove+add is safe
(entities cannot be despawned mid-effect-application).

**Transfer logic:**

`apply_mutation` receives the `TypeEnv` conditions map as an additional
parameter (only used by `TransferConditions`; other arms ignore it).

1. `state.read_conditions(&from)` — snapshot current conditions
2. Filter to those where `tag` is in `cond.tags`
3. Exclude `exclude_instance` if set
4. For each match, check bearer type compatibility:
   - Look up `type_env.conditions[&cond.name].receiver_type`
   - If `Ty::Entity(name)`, compare against `state.entity_type_name(&to)`
   - If incompatible, skip with runtime warning; condition stays on source
5. For each compatible match:
   - `state.remove_condition_by_id(&from, cond.id)`
   - `state.add_condition(&to, cond)` with `bearer` updated to `to`

Identity preservation relies on the existing `add_condition` contract:
transferred conditions have non-zero `id` fields, and `add_condition`
preserves IDs when `id > 0` (see `reference_state.rs:345-361`). The counter
is bumped to stay above externally-assigned IDs. No API changes needed.

### Lifecycle Condition Stack

New field in the interpreter environment:

```rust
/// Stack of condition instance IDs for active lifecycle blocks.
/// Pushed before entering on_apply/on_remove, popped on exit.
/// Used by transfer_conditions to exclude the currently-removing condition.
pub lifecycle_condition_stack: Vec<u64>,
```

In `pipeline.rs`, around lifecycle block execution:

```rust
// Before executing lifecycle block:
env.lifecycle_condition_stack.push(condition_instance_id);
env.in_lifecycle_block += 1;

// After executing lifecycle block:
env.in_lifecycle_block -= 1;
env.lifecycle_condition_stack.pop();
```

### Type Checker

In `checker/builtins.rs`, register:

```rust
builtin(
    "transfer_conditions",
    vec![
        param("from", Ty::AnyEntity),
        param("to", Ty::AnyEntity),
        param("tag", Ty::String),
    ],
    Ty::Unit,
),
```

In `check_builtins.rs`:

- Add `"transfer_conditions"` to the mutation-context check (same as `despawn`,
  `suspend_with_source`). Do NOT add it to the `allows_condition_manipulation()`
  gate.
- Add special-case validation for the `tag` argument: if the argument is a
  string literal, resolve it against declared tags and report undeclared tags
  as errors. If the argument is a non-literal expression, skip validation
  (same approach used for other builtins with known-value arguments).

## Edge Cases

### Same-entity transfer

`transfer_conditions(x, x, "tag")` is detected as a no-op before any mutations
and returns immediately. This avoids unnecessary remove/add churn that could
perturb insertion order with no semantic effect.

### Nonexistent entities

If either `from` or `to` does not exist (despawned, never created, etc.), the
entire transfer is skipped with a runtime warning. No conditions are removed
from `from`. This prevents the data-loss scenario where `remove_condition_by_id`
succeeds but the subsequent `add_condition` silently drops the condition because
`to` doesn't exist (`add_condition` returns without error for missing entities).

### Stacking conflicts

If the target already has a condition with the same name and a restrictive
stacking policy (e.g., `stacking first`), the transferred condition may
conflict. Since we bypass on_apply, stacking is not re-evaluated — the
condition is added as-is. This matches the "identity preservation" semantics:
the condition was already active, we're just moving which entity it lives on.

Ruleset authors should ensure transferable conditions use `stacking all` or
that conflicts can't arise in practice (see the Transferable Condition
Checklist above).

### Condition ordering

Conditions are stored in insertion order (`Vec<ActiveCondition>`), but modifier
precedence is determined by `gained_at` comparisons, not Vec position. After
transfer, a condition's Vec position on the destination may not reflect its
temporal ordering relative to conditions already present. This is acceptable
because:

- Modifier application uses `gained_at` for precedence, not Vec index
- `gained_at` is preserved through transfer, so precedence is correct
- Code that iterates conditions should not assume Vec order equals temporal order

If a future change introduces Vec-order-dependent semantics, `add_condition`
would need to insert by `gained_at` rather than appending. That is outside
the scope of this design.

### Suspension records and bearer-linked external state

Conditions whose lifecycle hooks or host integrations create external state
keyed to the bearer entity MUST NOT be tagged as transferable. Since transfer
skips on_remove/on_apply, this external state won't be cleaned up on the
source or re-established on the destination.

Examples of bearer-linked external state:
- Suspension records via `suspend()` in on_apply (keyed by condition instance
  ID on the bearer)
- Spawned entities keyed to the bearer
- Host-side tracking or UI state bound to the bearer identity

If a condition is transferred from entity A to entity B and later removed from
B, cleanup effects (like `RemoveSuspensionSource`) target B — but the
external state lives on A, leaving it stranded.

In practice this is natural: Petrified (suspends the bearer), Paralyzed
(suspends the bearer), etc. are physical states that shouldn't follow a
polymorph. Mental/magical conditions like Blessed, Cursed, Charmed don't
create bearer-linked external state. The Transferable Condition Checklist
provides concrete criteria for making this determination.

**Future work:** If a use case arises for transferring conditions with
bearer-linked state, the transfer implementation would need to relocate
associated records (suspension sources, spawned entity keys, etc.) from the
source to the target entity.

### Host gates

`transfer_conditions` intentionally bypasses `ConditionApplyGate` and
`ConditionRemovalGate`. This is consistent with the decision to skip
on_apply/on_remove: transfer is an atomic relocation of existing state, not a
new application or removal. Firing gates would allow hosts to veto individual
condition transfers, which could leave the polymorph in a half-transferred
state.

Hosts that need visibility into transfers can observe the
`TransferConditions` effect directly. If finer-grained host notification is
needed (e.g., logging each moved condition), a `ConditionTransferNotification`
effect can be added as future work without changing the no-veto semantics.

### Bearer type compatibility

The adapter checks bearer type compatibility at transfer time. For each
matching condition, it looks up `receiver_type` from `TypeEnv.conditions` and
compares against `state.entity_type_name(&to)`:

- `Ty::AnyEntity` (`on bearer: entity`) — always compatible, transferred
- `Ty::Entity(name)` — transferred only if the target entity's type matches
- Incompatible conditions are **skipped with a runtime warning**, not
  transferred. No conditions are lost — they remain on the source entity.

This prevents silent failures where a `on bearer: Character` condition gets
transferred to a Monster, producing non-functional modify blocks and runtime
errors on `bearer.field` access.

**Implementation:** `apply_mutation` for `TransferConditions` receives
access to the `TypeEnv` conditions map (passed as an additional parameter).
The check mirrors the existing `value_matches_ty` pattern at
`value.rs:529-535`: `AnyEntity` always matches, `Entity(name)` requires an
exact type name match, unknown entity type accepts (best-effort).

**Convention:** Transferable conditions SHOULD still declare
`on bearer: entity` (the top entity type) for maximum compatibility. The
runtime check is a safety net, not a replacement for good practice. The
Transferable Condition Checklist above codifies this.

### Modify clauses

Conditions with `modify` blocks bind to derive/mechanic parameters. After
transfer, the condition's modify blocks will match against derives that involve
the NEW bearer. This works if the derive parameter accepts the target's entity
type (e.g., `target: entity`). Conditions that modify type-specific derives
(e.g., `character_movement(character: Character)`) won't match if transferred
to a Monster. This is acceptable — physical stat modifications shouldn't
transfer anyway, and the bearer type convention above prevents the mismatch.

### Despawned form

The polymorph on_remove calls `transfer_conditions` BEFORE `despawn(bearer)`.
Order matters: once the form is despawned, its conditions are gone.

## Testing

1. Basic transfer: apply tagged condition, transfer, verify moved
2. Non-matching tags: conditions without the tag stay on source
3. Multiple conditions: mix of tagged and untagged, verify correct split
4. Round-trip: transfer to form, transfer back, verify preserved
5. Lifecycle block: transfer inside on_remove (the polymorph revert case)
6. Params preserved: condition with parameters survives transfer
7. Empty transfer: no conditions match tag — no error, no-op
8. Self-exclusion: condition executing on_remove is not transferred
9. Tag validation: checker rejects undeclared tag string literals
10. Host gate bypass: verify no gate effects emitted during transfer
11. Same-entity no-op: `transfer_conditions(x, x, "tag")` is a no-op, no ordering change
12. Nonexistent source: `from` doesn't exist — no-op, no error
13. Nonexistent destination: `to` doesn't exist — no-op, no conditions lost from source
14. Ordering preservation: `gained_at` values unchanged after transfer
15. Revoke after transfer: `revoke()` finds transferred condition by preserved `invocation`
16. Bearer type skip: `on bearer: Character` condition skipped when transferring to Monster, stays on source
17. Bearer type entity: `on bearer: entity` condition transfers to any entity type
