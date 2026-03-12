# Design: Periodic Condition Blocks

**Status:** Implemented
**Last updated:** 2026-03-10

---

## Problem

Conditions that need per-round effects (bleeding, zone occupant damage) currently
require separate standalone functions that duplicate knowledge about what the
condition does:

- `Bleeding` is an empty condition; all HP-loss logic lives in
  `process_bleeding()` in `osric_combat.ttrpg`
- `InsideBladeBarrier` is an empty condition; all damage logic lives in
  `process_blade_barrier_damage()` in `osric_zone_spells.ttrpg`

This splits the condition's behavior across two locations. Adding a new periodic
effect requires writing both a condition declaration and a processing function,
then wiring the function into the combat loop. The condition itself carries no
information about what it does periodically.

## Goals

- Co-locate periodic effect logic with the condition that causes it
- Provide a generic processing mechanism so the combat loop doesn't need
  spell-specific or condition-specific function calls
- Preserve explicit ordering control in the combat loop via tag-based filtering
- Keep the design simple — small tag vocabulary, no priority numbers

## Non-Goals

- Automatic tick scheduling (the combat loop remains responsible for when to
  call processing)
- Replacing `expire_conditions()` — duration expiry is a separate mechanism
- Replacing non-condition periodic effects like `process_temp_healing()` (which
  operates on entity fields, not conditions)
- First-class tag values — v1 uses string-based tag filtering (see Future Work)

## Design

### Syntax

A new `periodic` clause inside condition blocks, with exactly one tag.

The tag uses bare `#tag` syntax (not `[#tag]`). Square brackets are reserved
for modify selectors, which select *what to modify*. Here the tag is metadata
on the periodic block itself — it categorizes when the block should fire.

```
condition Bleeding on bearer: entity
    stacking first
{
    periodic #round_end_damage {
        if bearer is Character {
            bearer.hp = bearer.hp - 1
            if bearer.hp <= -10 {
                bearer.hp = -10
                remove_condition(bearer, "Bleeding")
                remove_condition(bearer, "Unconscious")
                apply_condition(bearer, Dead, Duration.Indefinite)
                emit CharacterDead(target: bearer)
            } else if bearer.hp <= -6 {
                if !has_condition(bearer, "Scarred") {
                    apply_condition(bearer, Scarred, Duration.Indefinite)
                }
            }
        }
    }
}
```

```
condition InsideBladeBarrier on bearer: entity
    stacking all
{
    periodic #round_end_damage {
        if let EffectSource.Spell(zone_name, cl) = self.source {
            let damage = roll(8d8).total
            bearer.TakeDamage(bearer, damage, DamageType.Slashing)
            emit SpellDamaged(caster: bearer, target: bearer,
                spell_name: zone_name, amount: damage)
        }
    }
}
```

### Tag Declarations

Periodic tags use the existing tag declaration system. Tags must be declared
with `tag` at the system level before use:

```
tag round_end_damage
tag round_end_healing
```

The checker validates periodic tag references against the tag namespace, the
same way it validates tags on functions, conditions, and modify clauses.

### Tag Filtering

The built-in function `process_periodic_conditions` takes a combatant list and a
tag name (as a string) to filter on:

```
process_periodic_conditions(combatants, "round_end_damage")
process_periodic_conditions(combatants, "round_end_healing")
expire_conditions(combatants)
```

Only periodic blocks whose tag matches the requested tag name are executed.
This gives the combat loop explicit control over ordering without requiring
condition-specific function names.

**Runtime tag validation:** `process_periodic_conditions` raises a runtime error
if the tag string does not match any declared `tag` in the program. This catches
typos at the call site (e.g., `"round_end_damge"`) immediately rather than
silently executing nothing. The checker cannot validate the string literal at
compile time in v1, so runtime validation is the safety net.

A condition may have multiple periodic blocks with different tags if it needs
to participate in multiple phases:

```
condition PoisonedBlade on bearer: entity stacking first {
    periodic #round_end_damage {
        // ongoing poison damage
    }
    periodic #round_end_healing {
        // reduce poison duration or partial recovery
    }
}
```

A single condition declaration (excluding ancestors) may not have two periodic
blocks with the same tag. The checker reports a duplicate-tag error.

### Scope Inside the Block

The periodic block body has access to:

- `bearer` — the entity carrying the condition
- `self` — the full `ActiveCondition` instance being processed, providing
  access to `self.source`, `self.id`, `self.duration`, `self.applied_at`,
  `self.name`, and `self.tags`
- Condition parameters from one effective inherited parameter map. Ancestors are
  materialized first and descendants later, so if both a parent and child
  declare the same parameter name, the child's binding shadows the parent's
  binding in periodic execution.

**Why `self` instead of just `source`:** The standalone functions being replaced
have full access to condition instance data via `conditions()` — for example,
`process_blade_barrier_damage` reads `cond.source` from the iterator. Binding
the full instance as `self` preserves this expressiveness. For `stacking all`
conditions, `self.id` is needed to remove or reason about a specific instance.

**Note on lifecycle blocks:** Lifecycle blocks (`on_apply` / `on_remove`) bind
only `bearer` and the same effective inherited condition-parameter map — they do
not bind `self`. Periodic blocks are intentionally broader in scope because
they replace standalone functions that had full access to condition instance
data.

The body uses the same statement grammar as function bodies — `let`, `if`,
`if let`, field assignment, function calls, `emit`.

**Unlike lifecycle blocks**, periodic blocks are not restricted from calling
`apply_condition()` or `remove_condition()`. They execute in the combat loop
context (like the standalone functions they replace), not during condition
application. The existing `process_bleeding()` calls both freely.

### Execution Semantics

When `process_periodic_conditions(combatants, tag)` is called:

1. For each combatant in order:
2. **Snapshot** the combatant's active conditions and compute stacking winners
3. For each condition in the snapshot (in application order):
4. If the condition is a stacking winner and its declaration (including
   ancestors) has a `periodic` block tagged with `tag`:
5. Execute the block with `bearer` bound to the combatant, `self` bound to
   the active condition instance, and the effective inherited condition
   parameter map bound from the instance

#### Snapshot Semantics

The condition list for each combatant is snapshotted at the start of that
combatant's iteration. This provides same-bearer mutation safety:

- **Removed conditions are not revisited.** If a periodic block removes another
  condition on the same bearer (or removes itself), remaining entries in the
  snapshot that refer to now-removed conditions are skipped.
- **Same-bearer applies do not tick.** Conditions applied to the current bearer
  during the pass (e.g., `Dead` applied by the `Bleeding` block) do not execute
  their periodic blocks until the next `process_periodic_conditions` call.
- **Already-started blocks complete.** Removing a condition does not cancel a
  periodic block that has already begun executing.

**Cross-bearer mutations are order-dependent.** The snapshot is taken
per-combatant, not globally. A periodic block on combatant A that applies a
condition to combatant B (where B has not yet been processed) will cause that
new condition to appear in B's snapshot and potentially tick in the same pass.
Conversely, if B was already processed, the new condition will not tick until
the next call. This matches the behavior of the standalone functions being
replaced (e.g., `process_bleeding` iterates combatants in order and mutations
are visible to later iterations).

#### Stacking Winner Execution

Periodic blocks execute only for stacking winners, as computed by
`compute_stacking_winners()`:

- **`stacking all`**: Every instance is a winner. Each instance's periodic
  block executes separately with its own `self`. This is correct for cases
  like overlapping Blade Barriers — each zone deals its own damage.
- **`stacking first`**: The oldest instance wins. Its periodic block executes
  once. This is correct for Bleeding.
- **`stacking best by`**: The instance with the best parameter value wins
  (ties broken by oldest). Only the winner's periodic block executes.

Suppressed (non-winning) instances do not execute periodic blocks, consistent
with how they are excluded from modifier collection.

#### Inheritance

Periodic blocks participate in condition inheritance using the same ancestor
traversal as lifecycle blocks (`collect_ancestor_order()`, DFS post-order).
Parent periodic blocks execute before child periodic blocks.

If a parent condition declares `periodic #round_end_damage` and a child
condition also declares `periodic #round_end_damage`, both execute (parent
first). If only the parent declares it, the child inherits the behavior.

#### Worked Examples

**Example 1: Cross-bearer mutation (order-dependent)**

Setup: Combatants processed in order `[Alice, Bob]`. Alice has condition
`Contagion` with a periodic block that applies `Diseased` to all adjacent
entities (including Bob). Bob has no conditions initially.

```
process_periodic_conditions([Alice, Bob], "round_end_damage")
```

1. Snapshot Alice's conditions: `[Contagion]`
2. Execute Contagion's periodic block → applies `Diseased` to Bob
3. Snapshot Bob's conditions: `[Diseased]` ← includes the just-applied condition
4. If `Diseased` has `periodic #round_end_damage`, it executes for Bob in this pass

If the combatant order were `[Bob, Alice]`, Bob's snapshot would be empty and
`Diseased` would not tick until the next call.

**Example 2: Self-removal under `stacking all`**

Setup: A combatant has two `InsideBladeBarrier` instances (IDs 5 and 8) from
overlapping zones. Instance 5's periodic block kills the bearer, triggering
condition cleanup that removes both instances.

```
process_periodic_conditions([bearer], "round_end_damage")
```

1. Snapshot: `[InsideBladeBarrier#5, InsideBladeBarrier#8]`, both are winners
2. Execute #5's periodic block → bearer takes damage, dies, conditions removed
3. Check #8 against live conditions → #8 no longer exists → skip

Instance #5's block completes fully (already-started blocks are not cancelled).
Instance #8 is skipped because it was removed.

**Example 3: Inherited parent+child periodic blocks**

Setup: `condition BaseDot` has `periodic #round_end_damage { /* 1 damage */ }`.
`condition BurningDot extends BaseDot` also has `periodic #round_end_damage { /* fire VFX */ }`.
A combatant has `BurningDot`.

```
process_periodic_conditions([bearer], "round_end_damage")
```

1. `collect_ancestor_order("BurningDot")` → `[BaseDot, BurningDot]`
2. Execute `BaseDot`'s periodic block (1 damage)
3. Execute `BurningDot`'s periodic block (fire VFX)

Both blocks execute, parent first.

### Combat Loop After Migration

In `osric_initiative.ttrpg`, `resolve_round` becomes:

```
// End-of-round bookkeeping
process_periodic_conditions(combatants, "round_end_damage")
process_temp_healing(combatants)          // not condition-based
expire_conditions(combatants)
emit RoundEnd(round: round)
```

`process_bleeding()` and `process_blade_barrier_damage()` are removed — their
logic moves into the `Bleeding` and `InsideBladeBarrier` condition declarations.

`process_temp_healing()` remains a standalone function because temp damage
recovery operates on an entity field, not a condition.

## Pipeline Changes

### AST (`ttrpg_ast`)

Add to `ConditionClause`:

```rust
Periodic(PeriodicClause),
```

```rust
pub struct PeriodicClause {
    pub tag: Name,
    pub body: Block,
    pub span: Span,
}
```

### Parser (`ttrpg_parser`)

Add `parse_periodic_clause()` following the pattern of `parse_lifecycle_block()`.
Triggered when the parser sees `periodic` inside a condition body.

```
periodic #tag {
    <statements>
}
```

The `#` is consumed as syntax; the tag name is stored as a `Name`.

### Checker (`ttrpg_checker`)

Add `check_periodic_clause()` to type-check the body. Scope binding:

- `bearer` — bound to the condition's receiver type
- Condition parameters — bound from the condition's param list
- `self` — bound as `ActiveCondition` type (the full condition instance)

Validation:

- **Tag existence:** Validate that the periodic tag is declared in the tag
  namespace (`env.tags.contains(tag_name)`), using the same check as modify
  selector tags.
- **No duplicate tags:** Within a single condition declaration (excluding
  ancestors), report an error if two periodic blocks use the same tag.
- **Body type-checking:** Same rules as function bodies.

### Interpreter (`ttrpg_interp`)

Add built-in function `process_periodic_conditions(combatants, tag)`:

1. **Validate tag:** Check that `tag` matches a declared tag name; raise a
   runtime error if not found
2. For each combatant, snapshot active conditions and compute stacking winners
3. For each winning condition instance in the snapshot:
   a. Collect the ancestor chain via `collect_ancestor_order()`
   b. For each ancestor (parent-first), check for a `periodic` clause matching
      the requested tag
   c. If found, execute the block body with `bearer`, `self` (the active
      condition instance), and the effective inherited condition parameter map
      bound from the instance
   d. Skip snapshot entries whose condition has been removed since the snapshot
4. Conditions applied to the current bearer during execution are not processed
   in this pass (cross-bearer applies may be processed; see Snapshot Semantics)

The execution mechanism follows `execute_lifecycle_blocks()` in `pipeline.rs`,
extended to bind `self` and to use snapshot-based iteration.

**Refactoring opportunity:** The stacking-winner + ancestor-chain traversal
pattern is shared with modifier collection, suppression checks, and lifecycle
execution. Consider factoring out a shared helper that iterates winning active
condition instances plus ancestor clauses, so that modifiers, periodic blocks,
and lifecycle blocks all build on a common traversal path.

### Builtin Registration

Register `process_periodic_conditions` as a built-in with signature
`(list<entity>, string) -> void`. The string argument is matched against
periodic block tag names.

## Migration Plan

1. Add `tag round_end_damage` declaration to `osric_conditions.ttrpg`
2. Implement the `periodic` clause (AST, parser, checker)
3. Implement `process_periodic_conditions` builtin (interpreter)
4. Move `process_bleeding()` logic into `Bleeding` condition's periodic block
5. Update `osric/tests/osric_initiative.ttrpg-cli` to exercise bleeding via
   `process_periodic_conditions` instead of the removed `process_bleeding()`
6. Move `process_blade_barrier_damage()` logic into `InsideBladeBarrier`
   condition's periodic block
7. Update `osric/tests/osric_zone_spells.ttrpg-cli` to exercise zone damage via
   `process_periodic_conditions` instead of the removed
   `process_blade_barrier_damage()`
8. Update `resolve_round` to call `process_periodic_conditions` instead of
   the removed functions
9. Verify test matrix (see below) — ensure coverage is preserved, not just
   that tests pass

### Test Matrix

The following scenarios must pass after migration, anchored in existing OSRIC
integration tests:

| Scenario | Condition | Key behavior |
|----------|-----------|-------------|
| Bleeding death | `Bleeding` (stacking first) | HP decrements by 1/round; at -10, removes Bleeding + Unconscious, applies Dead, emits CharacterDead |
| Scar threshold | `Bleeding` | At -6 HP, applies Scarred if not already present |
| Overlapping zones | `InsideBladeBarrier` (stacking all) | Each instance deals 8d8 separately; two overlapping barriers = two damage rolls |
| No same-bearer tick | Any periodic condition | Condition applied to the same bearer during a `process_periodic_conditions` pass does not execute its periodic block in that same pass |
| Cross-bearer ordering | Any periodic condition | Condition applied to a later combatant by an earlier combatant's periodic block is visible in the later combatant's snapshot |
| Removal during pass | `Bleeding` removing itself | Removing a condition mid-pass skips remaining snapshot entries for that condition but does not cancel the currently executing block |
| Monsters don't bleed | `Bleeding` | `if bearer is Character` guard prevents monster bleeding (monsters die at 0 HP) |
| Unknown tag error | N/A | `process_periodic_conditions(combatants, "typo")` raises a runtime error |

## Decided

- **Tag syntax on periodic blocks**: Bare `#tag` (not `[#tag]`). Square brackets
  are reserved for modify selectors. Periodic tags are metadata on the block
  itself, not selectors.
- **Tag representation at call site**: String matching for v1. The builtin takes
  a string argument: `process_periodic_conditions(combatants, "round_end_damage")`.
  Unknown tag strings produce a runtime error.
- **Tag validation**: Periodic tags use the existing `tag` declaration system and
  are validated by the checker at declaration sites. Call-site strings are
  validated at runtime.
- **Snapshot semantics**: Condition list snapshotted per combatant; same-bearer
  mutations during the pass do not cause new conditions to tick. Cross-bearer
  mutations are order-dependent (see Snapshot Semantics).
- **Inheritance**: Periodic blocks inherit via ancestor chain, same as lifecycle
  blocks.
- **Scope**: Periodic blocks bind `bearer`, the effective inherited condition
  parameter map, and `self` (the full `ActiveCondition` instance). Descendant
  parameter names shadow matching ancestor names. This is intentionally broader
  than lifecycle blocks.
- **Stacking**: Only stacking winners execute periodic blocks, using the same
  winner computation as modifier collection.
- **No duplicate tags**: A single condition declaration may not have two periodic
  blocks with the same tag.
- **Execution order**: Combatant iteration order, then condition application
  order within each combatant, then ancestor order (parent before child) within
  each condition's inheritance chain.

## Future Work

- **First-class tag literals**: If tag values become passable as first-class
  values (`#tag` syntax in expressions), the builtin signature could change to
  `(list<entity>, tag) -> void`. This would provide compile-time validation at
  the call site, replacing the current runtime check.
- **Multi-tag periodic blocks**: `periodic #tag1, #tag2 { ... }` syntax for
  blocks that should fire in multiple phases. Deferred until a concrete use
  case appears.

## Open Questions

- Should `process_periodic_conditions` be a true built-in, or could it be
  expressible as a DSL function that iterates conditions and pattern-matches
  on periodic blocks? (Likely needs to be a built-in since DSL functions
  cannot introspect condition declarations.)
