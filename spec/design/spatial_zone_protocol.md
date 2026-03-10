# Design: Host-Driven Spatial Zone Protocol

**Issue:** tdsl-lj6q.4
**Status:** Draft
**Last updated:** 2026-03-10

---

## Problem

The DSL can now model generic persistent zones and a standard event vocabulary,
but hosts still need a precise contract for when those events fire and in what
order. Without that contract, different hosts will produce subtly different
behavior for the same spell or hazard:

- a moving aura may or may not count as a target entering the zone
- a wall may deal damage on path contact in one host and only on final overlap
  in another
- zone expiry may or may not remove occupant conditions consistently

This design defines the host-side event protocol for persistent positioned
effects. The host remains authoritative for geometry and movement, while the DSL
receives stable semantic events such as `ZoneEntered` and `ZoneCrossed`.

## Goals

- Standardize when `ZoneEntered`, `ZoneExited`, `ZoneCrossed`, and
  `ZoneExpired` fire
- Define host responsibilities for membership recomputation
- Specify ordering semantics for movement, anchored-zone motion, and expiry
- Keep geometry and path math host-defined rather than forcing a shared spatial
  engine into the DSL
- Support the v1 patterns needed by occupant zones, barriers, and triggered
  zones

## Non-Goals

- Defining a universal geometry algorithm for circles, walls, or line
  intersection
- Defining a shared `ZoneShape` taxonomy across all rulesets
- Making the DSL compute spatial relationships directly
- Standardizing movement path discretization across all hosts
- Solving all spell-specific policy in this layer

## Assumptions

This protocol assumes the generic `Zone` entity and standard zone events exist.
The host is responsible for:

- storing or resolving entity positions
- storing or resolving zone positions
- determining zone membership from its spatial model
- determining whether a movement path contacts or crosses a barrier zone

The DSL is responsible for:

- applying and removing occupant conditions
- reacting to boundary events
- implementing spell- or ruleset-specific consequences

## Core Model

For protocol purposes, a zone has two relevant spatial states:

- a resolved center or footprint used for current membership checks
- a prior membership set over `(target, zone)` pairs

The host must maintain enough state to compare previous and new membership for
each active zone instance. Membership is always tracked per zone instance, not
per spell name or source name.

### Zone Behavior Fields

Each zone instance carries orthogonal fields that tell the host exactly which
event categories are relevant. These are the machine-readable contract that
connects DSL zone definitions to host event emission.

```
enum ContactMode {
    None,       // no path contact detection
    Crossed     // host performs path intersection; emits ZoneCrossed
}
```

The `Zone` entity gains three new fields:

```
entity Zone {
    ...
    contact_mode: ContactMode = ContactMode.None
    tracks_occupancy: bool = true
    trigger: bool = false
    ...
}
```

Host behavior by field combination:

- **`tracks_occupancy = true`**: The host tracks membership and emits
  `ZoneEntered` / `ZoneExited` on transitions.
- **`contact_mode = Crossed`**: The host performs path contact detection and
  emits `ZoneCrossed` when a target's movement path intersects the zone.
- **`trigger = true`**: The zone is one-shot. The host emits `ZoneEntered` for
  only the first qualifying entrant per step (lowest target entity ID). Ruleset
  code is expected to deactivate or expire the zone after triggering.

These fields are fully orthogonal. A zone can track occupancy and detect
crossings simultaneously, or do neither, or any combination.

> **Periodic zone effects use periodic condition blocks.** Periodic zone effects
> (e.g., Blade Barrier damage each round) are implemented as `periodic #tag`
> blocks on zone-tracking conditions (e.g., `InsideBladeBarrier`). The combat
> loop calls `process_periodic_conditions(combatants, "round_end_damage")` to
> execute all matching periodic blocks. See `spec/design/periodic_condition_blocks.md`
> for the full design. This replaces the earlier pattern of standalone processing
> functions like `process_blade_barrier_damage()`.

### Zone-Motion Crossing (Optional)

When a zone with `contact_mode = Crossed` changes position (e.g., an anchored
zone whose anchor moved), the zone boundary may sweep through stationary
targets. Hosts MAY detect this and emit `ZoneCrossed(target, zone)` for
affected targets.

This is optional because swept-area contact detection requires significantly
more geometric computation than point-in-region or line-segment intersection,
and the protocol does not prescribe zone geometry. Hosts that implement it must
still follow the deterministic ordering rules (crossings before membership
deltas, sorted by zone ID then target ID).

**Motivation**: The ring form of Wall of Fire (both arcane and druidic) moves
with its caster and deals damage when creatures pass through the flames. When
the caster walks past a stationary enemy, the ring sweeps through them. Without
zone-motion crossing, that enemy receives only membership events
(`ZoneEntered`/`ZoneExited`), not `ZoneCrossed`.

**DSL authoring guidance**: Spell authors should write handlers that work
correctly regardless of whether the host emits zone-motion `ZoneCrossed`. The
recommended pattern is:

- Handle `ZoneCrossed` for crossing damage (path contact from either target
  motion or zone motion)
- Handle `ZoneEntered` with a `zone_moved` guard to apply crossing damage as a
  fallback when the entry was caused by zone motion rather than target motion

This dual-handler approach ensures correct behavior on all conformant hosts
while giving capable hosts the opportunity to distinguish crossing from entry.

The `ZoneEntered` event gains an additional host-provided field:

- `zone_moved: bool` — `true` when the entry was caused by zone motion (the
  target was stationary and the zone moved onto it), `false` otherwise. Hosts
  MUST set this field accurately.

### Occupancy vs Contact

The protocol distinguishes two related but separate concepts:

- **occupancy**: whether a target is considered inside a zone after recompute
- **contact/crossing**: whether the target's movement path intersects a barrier
  or contact-sensitive zone during the step

This distinction is intentional. A target can cross a wall and end outside it,
or enter a volume without crossing a barrier boundary.

### Zone Lifecycle State Machine

A zone exists in one of three states:

| From state | To state | Transition | Emitted events |
|------------|----------|------------|----------------|
| *(new)* | Active | Zone created or activated | `ZoneEntered` for each current occupant |
| Active | Inactive | `active` set to `false` | `ZoneExited` for each current occupant |
| Inactive | Active | `active` set to `true` | `ZoneEntered` for each current occupant |
| Active | Expired | Terminal removal | `ZoneExited` for each current occupant, then `ZoneExpired` |
| Inactive | Expired | Terminal removal | `ZoneExpired` (no occupants to exit) |

Expired is terminal. An expired zone cannot transition to any other state.

## Step Boundaries and Snapshot Semantics

A **recompute step** is one atomic change that triggers zone interaction
recomputation. Examples of atomic changes:

- one target changes position
- one zone changes resolved position (including anchor-driven updates)
- one zone is created, activated, deactivated, or expired

When a game action moves multiple targets (e.g., a mass teleport), the host
decomposes it into sequential per-target recompute steps, each processed in
target entity ID order.

Within a single recompute step:

1. The host computes **all events from a pre-step snapshot** of membership
   state. No DSL side effects from event handlers alter the membership snapshot
   used for event computation within the same step.
2. Events are emitted in deterministic order (see Ordering Rules below).
3. The DSL processes each emitted event in order. Side effects from handlers
   (e.g., a trigger handler deactivating its zone) take effect for subsequent
   recompute steps, not the current one.

This snapshot rule ensures that event computation is deterministic regardless of
whether the host internally batches or streams events.

**Trigger short-circuit rule**: When `trigger = true`, the host computes
qualifying entrants from the pre-step snapshot but emits `ZoneEntered` for only
the first qualifying entrant (lowest target entity ID). This ensures one-shot
semantics are deterministic even when multiple targets enter simultaneously.

## Event Semantics

### `ZoneEntered(target, zone, zone_moved)`

Emit when:

- the target was outside the zone before recompute
- the target is inside the zone after recompute
- the zone has `tracks_occupancy = true` or `trigger = true`

The `zone_moved` field MUST be set by the host:

- `true` when the entry was caused by zone motion while the target was
  stationary (zone moved onto the target)
- `false` when the entry was caused by target motion, zone creation, or zone
  activation

This can happen because:

- the target moved (`zone_moved = false`)
- the zone moved (`zone_moved = true`)
- the zone was created or activated around the target (`zone_moved = false`)

For trigger zones, only the first qualifying entrant per step receives this
event (see Step Boundaries above).

### `ZoneExited(target, zone)`

Emit when:

- the target was inside the zone before recompute
- the target is outside the zone after recompute
- the zone has `tracks_occupancy = true`

This can happen because:

- the target moved
- the zone moved
- the zone is being deactivated
- the target is being removed from play

Note: terminal expiry also produces `ZoneExited` for current occupants before
`ZoneExpired` fires.

### `ZoneCrossed(target, zone)`

Emit when the host determines that the target's movement path intersected a
zone with `contact_mode = Crossed` during the step.

Notes:

- `ZoneCrossed` does not imply final occupancy
- `ZoneCrossed` is path-based, not delta-membership-based
- spontaneous overlap from zone creation or teleport placement is not a crossing
- the host only performs path contact detection for zones with
  `contact_mode = Crossed`
- **target-path crossing** is REQUIRED: hosts MUST detect path contact when a
  target moves through a zone with `contact_mode = Crossed`
- **zone-motion crossing** is OPTIONAL: when a zone with `contact_mode =
  Crossed` moves and its boundary sweeps through a stationary target, hosts
  MAY emit `ZoneCrossed`. Hosts that cannot perform swept-area geometry may
  omit it. See "Zone-Motion Crossing" above for guidance.

### `ZoneExpired(zone)`

Emit when the host permanently ends a zone because its duration expires or its
sustaining condition fails. `ZoneExpired` is a **terminal** lifecycle event: the
zone is permanently removed and cannot be reactivated.

`ZoneExpired` is not a substitute for membership cleanup; membership cleanup
must still be expressed through `ZoneExited` for current occupants as described
below.

**Deactivation vs expiry**: Setting `active = false` temporarily is
deactivation, not expiry. Deactivation emits `ZoneExited` for current occupants
but does not emit `ZoneExpired`. A deactivated zone may later be reactivated
(setting `active = true`), which triggers membership recompute and emits
`ZoneEntered` for any targets now inside it. Only terminal removal emits
`ZoneExpired`.

## Recompute Triggers

At minimum, hosts must recompute zone interactions when any of the following
occur:

- a target changes position
- a zone changes resolved position
- a zone becomes active (reactivation)
- a zone becomes inactive (deactivation)
- a zone is created
- a zone is expired or removed
- a target is removed from play

Anchored zones are not special in the event model. If their resolved position
changes because the anchor moved, hosts treat that as a zone movement recompute.

## Ordering Rules

The protocol is defined in terms of observable event order, not internal host
algorithms.

### Deterministic Ordering

When a recompute step produces events for multiple zones or multiple targets,
hosts must emit them in a deterministic order:

1. Sort events by zone entity ID (ascending).
2. Within the same zone, sort by target entity ID (ascending).
3. Within the same `(target, zone)` pair, emit `ZoneExited` before
   `ZoneEntered`.
4. Across all zones, emit all `ZoneCrossed` events before all membership-delta
   events (`ZoneExited`, `ZoneEntered`).

This ensures that DSL hooks observe a consistent, reproducible event sequence
regardless of host-internal data structure iteration order.

### Movement or Reposition Step

For a step that changes a target position, a zone position, or both:

1. Resolve new zone positions first.
   For anchored zones, update the zone's resolved position from the anchor
   before evaluating membership.
2. Detect path contact for zones with `contact_mode = Crossed`.
   Emit `ZoneCrossed` for each such zone whose boundary or contact region
   the target's movement path intersects.
   Optionally, if a zone with `contact_mode = Crossed` changed position in
   step 1 and the host supports zone-motion crossing, emit `ZoneCrossed` for
   stationary targets whose position the zone boundary swept through.
3. Compute final membership deltas from pre-step snapshot.
   Emit `ZoneExited` for zones whose membership changed from inside to outside.
   Emit `ZoneEntered` for zones whose membership changed from outside to inside.
   For trigger zones, emit `ZoneEntered` only for the first qualifying entrant.

Within steps 2 and 3, apply the deterministic ordering rules above.

This ordering ensures that:

- wall-style zones can react to path contact even when final occupancy is
  unchanged
- occupancy-based conditions are applied or removed from the final state

### Zone Creation or Activation

When a zone is created or activated (including reactivation from `active=false`):

1. Resolve the zone's initial position
2. Compute current occupants
3. Emit `ZoneEntered` for each occupant (ordered by target entity ID)
   - For trigger zones, emit only for the first occupant (lowest entity ID)

Zone creation does not emit `ZoneCrossed`.

### Zone Deactivation

When a zone is deactivated (setting `active = false` without terminal removal):

1. Identify all current occupants
2. Emit `ZoneExited` for each current occupant (ordered by target entity ID)
3. Mark the zone inactive so it no longer participates in membership
   processing

The zone retains its state and may be reactivated later.

### Zone Expiry (Terminal)

When a zone is permanently expired or removed:

1. Identify all current occupants
2. Emit `ZoneExited` for each current occupant (ordered by target entity ID)
3. Emit `ZoneExpired(zone)`
4. Remove the zone so it no longer participates in future membership
   processing

This ordering allows rulesets to reuse normal exit cleanup for occupant
conditions and then run any zone-level expiry logic afterward.

### Target Removal

When a target is removed from play (death, despawn, or host-side entity
removal):

1. Identify all active zones where the target has membership
2. Emit `ZoneExited(target, zone)` for each such zone (ordered by zone entity
   ID)
3. Clear membership state for the target across all zones

This ensures that occupant conditions applied by `ZoneEntered` handlers are
properly cleaned up via the normal `ZoneExited` path.

### Time Progression

For zone expiry processing during time progression:

1. Expire any zones whose lifetime ends at this step, using the expiry ordering
   above

## Required Invariants

Hosts implementing this protocol must preserve the following invariants:

- membership is tracked per `(target, zone)` pair
- `ZoneEntered` fires at most once per outside-to-inside transition
- `ZoneExited` fires at most once per inside-to-outside transition
- at most one `ZoneEntered` or `ZoneExited` per `(target, zone)` per step,
  based on the final membership delta
- `ZoneCrossed` does not by itself change membership
- `ZoneCrossed` is only emitted for zones with `contact_mode = Crossed`
- `ZoneExpired` is terminal; it does not replace occupant cleanup; if occupants
  existed, their `ZoneExited` events must fire first
- deactivation (`active=false`) is not terminal; deactivated zones may be
  reactivated
- once expired, a zone does not participate in future membership processing
- overlapping zones are independent; events are never merged by spell name,
  source, or shape
- event ordering is deterministic: sorted by zone entity ID, then target entity
  ID, with exits before enters
- trigger zones emit `ZoneEntered` for at most one target per step (the lowest
  entity ID among qualifying entrants)
- all events in a step are computed from a pre-step membership snapshot; DSL
  side effects do not alter event computation within the same step
- when a target is removed from play, `ZoneExited` is emitted for each zone
  where the target had membership
- `ZoneEntered` events MUST include an accurate `zone_moved` field
- zone-motion `ZoneCrossed` is OPTIONAL; hosts that emit it must follow the
  same ordering rules as target-path crossings

## Edge Cases

### Zone moves onto a stationary target

Treat this the same as any other outside-to-inside transition:

- emit `ZoneEntered(target, zone, zone_moved=true)`

### Zone moves away from a stationary target

Treat this the same as any other inside-to-outside transition:

- emit `ZoneExited(target, zone)`

### Anchored barrier zone moves through a stationary target

The host MUST emit membership events:

- if the target ends inside: `ZoneEntered(target, zone)` with `zone_moved=true`
- if the target ends outside after being inside: `ZoneExited(target, zone)`

The host MAY additionally emit `ZoneCrossed(target, zone)` if it can detect
that the zone boundary swept through the target during the position change (see
"Zone-Motion Crossing" above).

**Sweep-through with no membership change**: If the host does not support
zone-motion crossing and the target starts and ends outside the zone (the
barrier swept through without leaving the target inside), no events are emitted
at all. This is a known gap on basic hosts — the `zone_moved` fallback only
helps when the zone comes to rest on the target (producing `ZoneEntered`). For
thin barriers like Wall of Fire (ring form), the common case is that the ring
sweeps over the target and continues past, leaving the target outside. Only
hosts that implement zone-motion crossing can detect this case.

When the zone sweeps onto a target and the target ends inside, basic hosts emit
`ZoneEntered(zone_moved=true)`, and DSL spell authors should use the
`zone_moved` field to apply crossing damage as a fallback — see the
dual-handler pattern described in "Zone-Motion Crossing" above.

### Zone is created already overlapping a target

Emit `ZoneEntered` on creation or activation. Do not emit `ZoneCrossed`.

### Zone expires while a target is inside

Emit:

1. `ZoneExited(target, zone)` for each current occupant
2. `ZoneExpired(zone)`

### Zone is deactivated while a target is inside

Emit:

1. `ZoneExited(target, zone)` for each current occupant

Do not emit `ZoneExpired`. The zone may be reactivated later.

### Path crosses a wall but ends outside it

Emit `ZoneCrossed`. Do not emit `ZoneEntered` unless final membership is inside.

### Target teleports directly into a zone

Emit `ZoneEntered` if final membership is inside. Do not emit `ZoneCrossed`
unless the host's teleport model explicitly treats teleport as path contact,
which should be avoided in v1.

### Same step leaves and re-enters the same zone

In v1, emit at most one `ZoneEntered` or one `ZoneExited` per `(target, zone)`
per step, based on the final membership delta:

- if the target starts inside and ends inside: no event
- if the target starts outside and ends outside: no event (but `ZoneCrossed` may
  fire for zones with `contact_mode = Crossed` if the path intersected)
- if the target starts inside and ends outside: `ZoneExited`
- if the target starts outside and ends inside: `ZoneEntered`

Multi-transition path-order behavior is deferred to a future protocol revision.

### Target removed from play while inside zones

When a target is removed from play (via `despawn()`, death, or host-side entity
removal) while inside one or more active zones:

1. Emit `ZoneExited(target, zone)` for each zone where the target has
   membership (ordered by zone entity ID)
2. Clear all membership state for the target

This ensures occupant conditions are cleaned up through the normal exit path.
The host must emit these events before the target entity is fully removed.

### Two targets enter a trigger zone simultaneously

When a recompute step (e.g., zone creation overlapping two targets) would
qualify multiple targets for entry into a trigger zone:

- The host emits `ZoneEntered` for only the first qualifying entrant (lowest
  target entity ID)
- The remaining targets do not receive `ZoneEntered` for this zone in this step
- The trigger handler is expected to deactivate or expire the zone, preventing
  future entries

Example: targets T5 and T3 both overlap a newly created trigger zone. The host
emits `ZoneEntered(T3, zone)` only. T5 does not receive an event.

## Conformance Scenario Matrix

This table summarizes expected events for common scenarios. All columns refer to
a single recompute step.

| # | Scenario | Start in | End in | Target moved | Zone moved | Path contact | Zone removed | Expected events (in order) |
|---|----------|----------|--------|--------------|------------|--------------|--------------|----------------------------|
| 1 | Target walks into occupant zone | no | yes | yes | no | no | no | `ZoneEntered` |
| 2 | Target walks out of occupant zone | yes | no | yes | no | no | no | `ZoneExited` |
| 3 | Target walks through barrier wall | no | no | yes | no | yes | no | `ZoneCrossed` |
| 4 | Target walks into barrier zone and stays | no | yes | yes | no | yes | no | `ZoneCrossed`, `ZoneEntered` |
| 5 | Zone created overlapping target | no | yes | no | no | no | no | `ZoneEntered` |
| 6 | Anchored zone moves onto target | no | yes | no | yes | no | no | `ZoneEntered(zone_moved=true)` |
| 7 | Anchored zone moves away from target | yes | no | no | yes | no | no | `ZoneExited` |
| 8a | Anchored barrier sweeps through target (capable host) | no | no | no | yes | yes | no | `ZoneCrossed` |
| 8b | Anchored barrier sweeps through target (basic host) | no | no | no | yes | no | no | *(none)* |
| 9 | Zone expires with occupant | yes | n/a | no | no | no | yes | `ZoneExited`, `ZoneExpired` |
| 10 | Zone deactivated with occupant | yes | n/a | no | no | no | no | `ZoneExited` |
| 11 | Teleport into zone | no | yes | yes | no | no | no | `ZoneEntered` |
| 12 | Target enters zone A, exits zone B (same step) | B:yes, A:no | B:no, A:yes | yes | no | no | no | `ZoneExited(B)`, `ZoneEntered(A)` |
| 13 | Trigger zone fires | no | yes | yes | no | no | no | `ZoneEntered` *(then DSL deactivates)* |
| 14 | Target starts and ends inside, no change | yes | yes | yes | no | no | no | *(none)* |
| 15 | Path crosses barrier, ends outside | no | no | yes | no | yes | no | `ZoneCrossed` |
| 16 | Two targets enter trigger zone (creation) | both: no | both: yes | no | no | no | no | `ZoneEntered(lowest ID only)` |
| 17 | Target despawned while inside zone | yes | n/a | no | no | no | no | `ZoneExited` |

These scenarios should be implemented as machine-readable test fixtures in the
interpreter test suite to serve as a conformance acceptance suite for host
implementations.

## Worked Example: Multi-Zone Movement Step

Setup:

- Target T10 starts at position (2, 2)
- Zone Z1: occupant zone centered at (5, 5), radius 10ft. T10 is currently
  inside (prior membership: true)
- Zone Z2: barrier wall from (8, 0) to (8, 10), `contact_mode = Crossed`,
  `tracks_occupancy = false`
- Zone Z3: occupant zone centered at (12, 2), radius 5ft. T10 is currently
  outside (prior membership: false)

Action: T10 moves from (2, 2) to (12, 2), crossing Z2's wall and entering Z3's
area while leaving Z1's area.

Recompute step for T10's move:

1. **Resolve zone positions**: no anchored zones moved, nothing to update.

2. **Path contact detection** (zones with `contact_mode = Crossed`):
   - Z2: path from (2,2) to (12,2) intersects the wall → queue
     `ZoneCrossed(T10, Z2)`

3. **Membership deltas** (from pre-step snapshot):
   - Z1: was inside, now outside → queue `ZoneExited(T10, Z1)`
   - Z2: `tracks_occupancy = false`, skip membership
   - Z3: was outside, now inside → queue `ZoneEntered(T10, Z3)`

4. **Emit events in deterministic order**:
   - All crossings first: `ZoneCrossed(T10, Z2)`
   - Then membership deltas sorted by zone ID, exits before enters:
     `ZoneExited(T10, Z1)`, `ZoneEntered(T10, Z3)`

Final emitted sequence:

```
1. ZoneCrossed(T10, Z2)
2. ZoneExited(T10, Z1)
3. ZoneEntered(T10, Z3)
```

## Reference Pseudocode

These sketches show the minimum host state and required ordering. They are not
prescriptive about data structures.

### `recompute_after_move(target, from_pos, to_pos)`

```
// Snapshot membership state before computing events
membership_snapshot = copy(prior_membership)

zone_moved_set = {}
for zone in active_zones sorted by zone.id:
    if zone.moves_with_anchor and zone.anchor moved:
        update zone.resolved_position from anchor
        zone_moved_set.add(zone)

crossing_events = []
membership_events = []

for zone in active_zones sorted by zone.id:
    if zone.contact_mode == Crossed:
        // REQUIRED: target-path crossing
        if from_pos != to_pos and path_intersects(from_pos, to_pos, zone):
            crossing_events.append(ZoneCrossed(target, zone))
        // OPTIONAL: zone-motion crossing
        elif zone in zone_moved_set and host_supports_zone_motion_crossing:
            if swept_area_intersects(target.position, zone.old_pos, zone.new_pos):
                crossing_events.append(ZoneCrossed(target, zone))

    if not zone.tracks_occupancy and not zone.trigger:
        continue

    was_inside = membership_snapshot[target, zone]
    is_inside  = compute_membership(target, zone)
    zm = zone in zone_moved_set and from_pos == to_pos

    if was_inside and not is_inside:
        membership_events.append(ZoneExited(target, zone))
    elif not was_inside and is_inside:
        if zone.trigger:
            // Only first entrant; check if another already queued
            if no ZoneEntered for this zone already queued:
                membership_events.append(ZoneEntered(target, zone, zone_moved=zm))
        else:
            membership_events.append(ZoneEntered(target, zone, zone_moved=zm))

    prior_membership[target, zone] = is_inside

emit crossing_events   // all crossings before membership deltas
emit membership_events // exits before enters (guaranteed by sort + append order)
```

### `remove_target(target)`

```
for zone in active_zones sorted by zone.id:
    if prior_membership[target, zone]:
        emit ZoneExited(target, zone)
        prior_membership[target, zone] = false
```

### `progress_time(current_step)`

```
for zone in active_zones sorted by zone.id:
    if zone.lifetime_ends_at == current_step:
        for target in occupants(zone) sorted by target.id:
            emit ZoneExited(target, zone)
            prior_membership[target, zone] = false
        emit ZoneExpired(zone)
        remove zone from active_zones
```

## Guidance for Common Zone Patterns

### Occupant Zones

Examples: `Silence`, `Protection from Evil`

Field settings:

```
contact_mode = ContactMode.None
tracks_occupancy = true
trigger = false
```

Use `ZoneEntered` and `ZoneExited`. For periodic damage or healing effects,
use `periodic #tag` blocks on zone-tracking conditions, processed by
`process_periodic_conditions()` from the combat loop.

### Barrier Zones

Examples: `Wall of Fire`, `Blade Barrier`

Field settings:

```
contact_mode = ContactMode.Crossed
tracks_occupancy = true   // if the zone also has occupancy effects
trigger = false
```

Barrier effects use `ZoneCrossed` for path contact. Set `tracks_occupancy` to
`true` if the zone also applies conditions or effects to occupants (e.g., Wall
of Fire deals damage both on crossing and while standing in the flames). Set it
to `false` if only crossing matters. For periodic occupant damage, use
`periodic #tag` blocks on zone-tracking conditions (e.g., `InsideBladeBarrier`).

### Anchored Barrier Zones

Examples: `Wall of Fire` (ring form)

Field settings:

```
contact_mode = ContactMode.Crossed
tracks_occupancy = true
trigger = false
```

These zones move with their anchor (typically the caster) and deal damage both
on crossing and to occupants. Because zone-motion crossing is optional, spell
authors must handle both code paths:

```
on ZoneCrossed(target, zone) {
    // Path contact damage — works for both target motion and zone motion
    // (on hosts that support zone-motion crossing)
    apply_crossing_damage(target, zone)
}

on ZoneEntered(target, zone) where zone_moved {
    // Fallback — zone swept onto a stationary target on a host that does not
    // emit zone-motion ZoneCrossed. Apply crossing damage here.
    apply_crossing_damage(target, zone)
}

on ZoneEntered(target, zone) where not zone_moved {
    // Normal entry (target walked in). Crossing damage, if any, was already
    // handled by ZoneCrossed. Apply occupant conditions only.
    apply_occupant_effects(target, zone)
}
```

On hosts that emit zone-motion `ZoneCrossed`, both `ZoneCrossed` and
`ZoneEntered(zone_moved=true)` fire when the zone sweeps onto a target. The
spell handler must avoid double-applying damage. The simplest approach: the
`ZoneEntered where zone_moved` handler checks whether a `ZoneCrossed` was
already processed for the same `(target, zone)` in this step, and skips damage
if so.

### Trigger Zones

Examples: `Glyph of Warding`

Field settings:

```
contact_mode = ContactMode.None
tracks_occupancy = true
trigger = true
```

Use `ZoneEntered` (one-shot, first entrant only per step), then deactivate or
expire the zone as appropriate.

## Required DSL and Test Changes

This design adds new types and fields that must be implemented in the DSL before
the protocol can be adopted.

### New enum types

Add to `osric/osric_core.ttrpg`:

- `ContactMode { None, Crossed }`

### Zone entity field additions

Add to the `Zone` entity in `osric/osric_core.ttrpg`:

- `contact_mode: ContactMode = ContactMode.None`
- `tracks_occupancy: bool = true`
- `trigger: bool = false`

All new fields have defaults, so existing zone instantiations remain valid
without changes.

### Files requiring updates

- `osric/osric_core.ttrpg` — new enum and Zone fields
- `crates/ttrpg_interp/tests/osric_core_integration.rs` — update
  `osric_core_has_all_enums` (add ContactMode to the 30→31 enum count), update
  `zone_entity_fields` (add 3 new fields to the assertion)
- Any existing OSRIC spell modules that create Zone instances should continue to
  work without changes due to default values

## Host API Shape

This design does not require a specific Rust trait yet, but it assumes the host
has operations equivalent to:

- recompute zone interactions after a target move
- recompute zone interactions after a zone move
- recompute zone interactions when a target is removed from play
- progress time for zone expiry
- determine path contact for zones with `contact_mode = Crossed`

The existing movement event pattern in the DSL (`from_position` / `to_position`
fields on events like `entity_leaves_reach`) provides the natural input data for
zone recompute. Hosts should derive both path contact and final membership from
the same `(target, from_pos, to_pos)` tuple that drives other movement events.

The important contract is the emitted event sequence, not the concrete host API
surface.

## Open Questions

- Should the project eventually standardize a host helper for membership diffing
  in the reference CLI or interpreter support library?
- When a host can represent multiple crossings of the same zone in one step,
  should later iterations standardize path-order behavior more tightly?
- Should zone-motion crossing be promoted from OPTIONAL to REQUIRED in a future
  protocol version once reference geometry helpers exist?
- ~~When concrete spells require periodic zone effects, should the project add a
  host-driven `ZoneTick` event, or continue with explicit combat-loop functions?~~
  **Resolved:** Periodic condition blocks (`periodic #tag { ... }`) now handle this.
  See `spec/design/periodic_condition_blocks.md`.

## Recommendation

Adopt the protocol above for v1:

- host-owned geometry
- semantic event delivery to the DSL
- explicit membership-delta and path-contact events
- orthogonal zone behavior fields (`contact_mode`, `tracks_occupancy`,
  `trigger`) replacing a single policy enum
- deterministic event ordering by zone and target entity ID
- snapshot-based event computation within each recompute step
- trigger short-circuit for one-shot semantics
- deactivation/reactivation as distinct from terminal expiry
- expiry modeled as `ZoneExited*` followed by `ZoneExpired`
- at most one enter/exit per `(target, zone)` per step
- target removal emits `ZoneExited` for affected zones
- tiered conformance: target-path crossing REQUIRED, zone-motion crossing
  OPTIONAL (host-MAY)
- `zone_moved` field on `ZoneEntered` enables DSL fallback for hosts without
  zone-motion crossing

This preserves the current architecture, keeps the DSL out of geometry math, and
gives ruleset authors enough structure to implement occupant zones, barriers,
and triggered zones consistently. The tiered conformance model avoids forcing
swept-area geometry on all hosts while ensuring spells like Wall of Fire (ring
form) degrade gracefully — capable hosts emit `ZoneCrossed` on zone motion,
simpler hosts fall back to `ZoneEntered` with `zone_moved=true`, and DSL
handlers cover both paths.