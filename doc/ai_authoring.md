# TTRPG DSL — AI Authoring Guide

> Concise reference for AI agents generating DSL code.
> For full syntax, types, operators, and builtins see [`language_reference.md`](language_reference.md) and `spec/v0/`.
> Validate output with `ttrpg check <file>` or `ttrpg check -s` (snippet mode, auto-wraps in system block).

---

## Block Categories

| Block     | Dice | Mutate | Receiver       | Returns | Cost |
|-----------|------|--------|----------------|---------|------|
| derive    | -    | -      | -              | value   | -    |
| table     | -    | -      | -              | value   | -    |
| mechanic  | yes  | -      | -              | value   | -    |
| function  | yes  | yes    | -              | optional| -    |
| action    | yes  | yes    | `on` receiver  | optional| yes  |
| reaction  | yes  | yes    | `on` + trigger | unit    | yes  |
| hook      | yes  | yes    | `on` + trigger | unit    | -    |
| condition | -    | -      | `on bearer`    | -       | -    |
| prompt    | -    | -      | -              | value   | -    |
| move      | yes  | yes    | `on` receiver  | unit    | yes  |

**Decision tree:**

- Named constant value (no body needed)? → **const**
- Static lookup / mapping data? → **table**
- Pure computation, no dice? → **derive**
- Needs dice, no mutation? → **mechanic**
- Reusable logic with dice + mutation, no receiver? → **function**
- Needs dice + mutation, player-initiated? → **action**
- Needs dice + mutation, triggered, optional (has cost)? → **reaction**
- Needs dice + mutation, triggered, mandatory (no cost)? → **hook**
- PbtA-style 2d6+stat with strong/weak/miss outcomes? → **move**
- Declarative buff/debuff overlay (+ optional event reactions)? → **condition**
- Human decision point? → **prompt**

---

## Top 12 Mistakes

### 1. Dice in derive

```ttrpg-err
derive bad(score: int) -> int {
    roll(1d20 + score).total
}
```

```ttrpg
mechanic good(score: int) -> RollResult {
    roll(1d20 + score)
}
```

### 2. Mutation in mechanic

```ttrpg-err
entity Character { name: string, HP: resource(0..=max_HP), max_HP: int }
mechanic bad(target: Character, amount: int) -> int {
    target.HP -= amount
    amount
}
```

```ttrpg
entity Character { name: string, HP: resource(0..=max_HP), max_HP: int }
action ApplyDamage on actor: Character (target: Character, amount: int) {
    cost { action }
    resolve { target.HP -= amount }
}
```

### 3. Comparing DiceExpr without roll()

```ttrpg-err
derive bad(bonus: int) -> bool {
    let expr: DiceExpr = 1d20 + bonus
    expr >= 15
}
```

```ttrpg
mechanic good(bonus: int) -> bool {
    let result: RollResult = roll(1d20 + bonus)
    result >= 15
}
```

### 4. int / int expecting int (always produces float)

```ttrpg-err
derive bad(score: int) -> int {
    (score - 10) / 2
}
```

```ttrpg
derive good(score: int) -> int {
    floor((score - 10) / 2)
}
```

### 5. resource with exclusive range (must use ..=)

```ttrpg-err
entity Bad { HP: resource(0..100), max_HP: int }
```

```ttrpg
entity Good { HP: resource(0..=max_HP), max_HP: int }
```

### 6. emit with positional args (must be named)

```ttrpg-err
entity Character { name: string, HP: resource(0..=max_HP), max_HP: int, position: Position, AC: int }
event Damaged(target: Character, amount: int) {}
action Hit on attacker: Character (target: Character) {
    cost { action }
    resolve {
        target.HP -= 5
        emit Damaged(target, 5)
    }
}
```

```ttrpg
entity Character { name: string, HP: resource(0..=max_HP), max_HP: int, position: Position, AC: int }
event Damaged(target: Character, amount: int) {}
action Hit on attacker: Character (target: Character) {
    cost { action }
    resolve {
        target.HP -= 5
        emit Damaged(target: target, amount: 5)
    }
}
```

### 7. Mixing `,` and `|` in with constraints

```ttrpg-err
entity Creature { name: string }
group Flying { fly_speed: int }
group Swimming { swim_speed: int }
group Climbing { climb_speed: int }
derive bad(c: Creature with Flying, Swimming | Climbing) -> int { 0 }
```

Pick one: `with A, B` (AND) or `with A | B` (OR).

### 8. Condition modify trying to mutate entity state

```ttrpg-err
entity Character { name: string, HP: resource(0..=max_HP), max_HP: int }
condition Bad on bearer: Character {
    modify attack_roll(attacker: bearer) {
        bearer.HP -= 1
    }
}
```

Modify clauses are declarative — they can only override parameters (phase 1) or rewrite result fields (phase 2). No entity mutation.

### 9. Group field access without has guard (disjunctive with)

```ttrpg-err
entity Creature { name: string, optional Flying }
group Flying { fly_speed: int }
derive bad(c: Creature with Flying | Swimming) -> int {
    c.Flying.fly_speed
}
group Swimming { swim_speed: int }
```

```ttrpg
entity Creature { name: string, optional Flying, optional Swimming }
group Flying { fly_speed: int }
group Swimming { swim_speed: int }
derive good(c: Creature with Flying | Swimming) -> int {
    if c has Flying as f {
        c.f.fly_speed
    } else {
        0
    }
}
```

### 10. Mutating a restricted field from another system

```ttrpg-err
// core.ttrpg
system "Core" {
    entity Character { restricted HP: int }
}

// ext.ttrpg — imports Core
import "core.ttrpg"
use "Core"
system "Ext" {
    action Zap on target: Character () {
        resolve { target.HP -= 1 }    // ERROR: restricted field
    }
}
```

Restricted fields can only be mutated within the system that declares the field's type/group, or the system that declares the entity containing the group. Other systems can read them freely. Move the mutation into a permitted system, or remove the `restricted` modifier if cross-system mutation is intended.

### 11. Missing event declaration before emit

```ttrpg-err
entity Character { name: string, HP: resource(0..=max_HP), max_HP: int, position: Position, AC: int }
action Bad on actor: Character (target: Character) {
    cost { action }
    resolve {
        emit Zapped(target: target, amount: 5)
    }
}
```

```ttrpg
entity Character { name: string, HP: resource(0..=max_HP), max_HP: int, position: Position, AC: int }
event Zapped(target: Character, amount: int) {}
action Good on actor: Character (target: Character) {
    cost { action }
    resolve {
        emit Zapped(target: target, amount: 5)
    }
}
```

### 12. Entity construction in non-mutating context

```ttrpg-err
entity Monster { name: string }
derive bad() -> Monster {
    Monster { name: "Ogre" }
}
```

```ttrpg
entity Monster { name: string }
function good() -> Monster {
    Monster { name: "Ogre" }
}
```

Entity construction spawns mutable state, so it requires a mutating context: `function`, `action`, `reaction`, `hook`, or `with_budget`. Use `function` instead of `derive`/`mechanic`.

To apply conditions at creation time, use the `with [conditions]` clause:
```ttrpg-with-preamble
entity Monster { name: string, hit_dice: int, max_hp: int }
enum Duration { Indefinite, Rounds(count: int) }
condition Poisoned on target: Monster {}
condition Weakened(amount: int) on target: Monster {}

function create_cursed_rat() -> Monster {
    Monster { name: "Rat", hit_dice: 1, max_hp: 2 } with [Poisoned, Weakened(amount: 3)]
}
```

Each condition is applied as `Duration.Indefinite` in list order. Full lifecycle/veto behaviour is preserved. The `with` clause is only valid on entity construction — not on structs, enums, or existing entity references.

---

## Shared Preamble

Blocks fenced as ` ```ttrpg-with-preamble ` implicitly include these declarations.
When authoring, assume these types exist — do **not** redeclare them.
Self-contained blocks (` ```ttrpg `) still declare everything they need.

```ttrpg-preamble
enum Ability { STR, DEX, CON, INT, WIS, CHA }
enum RollMode { normal, advantage, disadvantage }
enum DamageType { slashing, piercing, bludgeoning, fire, cold }

struct TurnBudget {
    actions: int = 0
    bonus_actions: int = 0
    reactions: int = 0
    movement: int = 0
}

tag #concentration
tag #spellcasting_gate

enum GrapplingHold { light, firm, pinned }

group Spellcasting {
    spell_dc: int
    spell_slots: int = 0
}

entity Character {
    name: string
    level: int = 1
    HP: resource(0..=max_HP)
    max_HP: int
    speed: int = 30
    position: Position
    AC: int
    abilities: map<Ability, int>
    concentrating_on: option<Invocation>
    optional Spellcasting
}

derive initial_budget(actor: Character) -> TurnBudget {
    TurnBudget { actions: 1, bonus_actions: 1, reactions: 1, movement: actor.speed }
}

event Damaged(target: Character, attacker: Character, amount: int) {}
```

---

> **Declaration syntax, type system, expressions, operators, and builtins:** see [`language_reference.md`](language_reference.md).

---

## Common Game Patterns

### Ability Modifier (derive)

```ttrpg
derive modifier(score: int) -> int {
    floor((score - 10) / 2)
}

derive proficiency_bonus(level: int) -> int {
    floor((level - 1) / 4) + 2
}
```

### d20 Check with Advantage/Disadvantage (mechanic)

```ttrpg-with-preamble
mechanic d20_check(
    bonus: int,
    mode: RollMode = normal
) -> RollResult {
    let base: DiceExpr = match mode {
        normal       => 1d20,
        advantage    => 2d20kh1,
        disadvantage => 2d20kl1
    }
    roll(base + bonus)
}
```

### Attack Action with Damage Event (action + event + hook)

```ttrpg-with-preamble
action Attack on attacker: Character (target: Character) {
    cost { action }
    requires { distance(attacker.position, target.position) <= 5 }
    resolve {
        let atk: RollResult = roll(1d20 + 5)
        if atk >= target.AC {
            let dmg: RollResult = roll(1d8 + 3)
            target.HP -= dmg.total
            emit Damaged(target: target, attacker: attacker, amount: dmg.total)
        }
    }
}

hook DeathDrop on target: Character (trigger: Damaged(target: target)) {
    if target.HP <= 0 {
        // handle death/unconscious
    }
}
```

### Concentration Spell (invocation tracking)

```ttrpg-with-preamble
enum Duration {
    EndOfTurn,
    StartOfNextTurn,
    Rounds(count: int),
    Minutes(count: int),
    Indefinite
}

event ConcentrationStarted(caster: Character, inv: Invocation)

hook on_conc on caster: Character (trigger: ConcentrationStarted(caster: caster)) {
    revoke(caster.concentrating_on)
    caster.concentrating_on = some(trigger.inv)
}

action CastBless on caster: Character (targets: list<Character>) #concentration {
    cost { action }
    resolve {
        let inv = invocation()
        for target in targets {
            apply_condition(target, Blessed, Duration.Rounds(10))
        }
        emit ConcentrationStarted(caster: caster, inv: inv)
    }
}

condition Blessed on bearer: Character {
    modify d20_check(attacker: bearer) {
        bonus = bonus + 2
    }
}

mechanic d20_check(
    attacker: Character,
    bonus: int = 0
) -> RollResult {
    roll(1d20 + bonus)
}
```

### Condition with Modify (advantage/disadvantage)

```ttrpg-with-preamble
tag position
tag penalty

mechanic attack_roll(
    attacker: Character,
    target: Character,
    mode: RollMode = normal
) -> RollResult {
    let base: DiceExpr = match mode {
        normal       => 1d20,
        advantage    => 2d20kh1,
        disadvantage => 2d20kl1
    }
    roll(base)
}

condition Prone on bearer: Character {
    modify attack_roll(attacker: bearer) #position #penalty {
        mode = disadvantage
    }
    modify initial_budget(actor: bearer) #position {
        result.movement = floor(bearer.speed / 2)
    }
}
```

### Tags on Modify Clauses and Suppress-Modify

Tags annotate modify clauses for provenance tracking and targeted suppression.
Place `#tag` annotations after bindings, before the opening brace.
Tags must be declared with `tag` declarations.

```ttrpg-with-preamble
tag position
tag fear

derive attack_roll(attacker: Character, attack_mod: int = 0) -> int #position {
    attack_mod
}

condition Frightened(source: Character) on bearer: Character {
    modify attack_roll(attacker: bearer) #fear {
        attack_mod = attack_mod - 2
    }
}

condition FreedomOfMovement on bearer: Character {
    suppress [#position](attacker: bearer)    // suppress all #position modifiers
}
```

`suppress [selector](bindings)` suppresses modify clauses matching the selector.
Selector predicates: `#tag`, `returns Type`, `has param: Type`.
Bindings are optional — omitting them suppresses all matching modifiers regardless of entity.

Use the REPL `breakdown` command to inspect which modifiers were applied:
```
breakdown attack_roll(fighter, goblin)
```
```

### Cost Modification (CunningAction pattern)

```ttrpg-with-preamble
action Dash on actor: Character () {
    cost { action }
    resolve { turn.movement += actor.speed }
}

action Hide on actor: Character () {
    cost { action }
    resolve { }
}

condition CunningAction on bearer: Character {
    modify Dash.cost(actor: bearer) {
        cost = bonus_action
    }
    modify Hide.cost(actor: bearer) {
        cost = bonus_action
    }
}
```

### Condition with Lifecycle Hooks (on_apply / on_remove)

```ttrpg
entity Character {
    name: string
    HP: resource(0..=max_HP)
    max_HP: int
    poisoned_flag: bool = false
}

event StatusGained(target: Character, status: string) {}
event StatusLost(target: Character, status: string) {}
event Damaged(target: Character, amount: int) {}

enum RollMode { normal, advantage, disadvantage }

mechanic saving_throw(target: Character, mode: RollMode = normal) -> RollResult {
    let base: DiceExpr = match mode {
        normal       => 1d20,
        advantage    => 2d20kh1,
        disadvantage => 2d20kl1
    }
    roll(base)
}

condition Poisoned(potency: int) on bearer: Character {
    on_apply {
        let dmg: RollResult = roll(dice(potency, 6))
        bearer.HP -= dmg.total
        bearer.poisoned_flag = true
        emit StatusGained(target: bearer, status: "Poisoned")
        emit Damaged(target: bearer, amount: dmg.total)
    }

    on_remove {
        bearer.poisoned_flag = false
        emit StatusLost(target: bearer, status: "Poisoned")
    }

    modify saving_throw(target: bearer) {
        mode = disadvantage
    }
}
```

See [`language_reference.md`](language_reference.md) for lifecycle hook rules (permitted builtins, trigger semantics, scoping).

### Condition State Fields

State fields are per-instance mutable fields on the condition. They provide internal bookkeeping (counters, accumulators, cached values) without polluting the condition's public interface. Unlike params (immutable, externally matchable), state fields are mutable within the condition's blocks and invisible to the untyped `conditions()` overload, stacking, and `remove_condition()`. State can be read externally via the typed `conditions(entity, CondName)` overload — see the "Typed `conditions()` overload" section under Condition Application.

```ttrpg
entity Character {
    HP: resource(0..=max_HP)
    max_HP: int = 20
}

event RoundEndDamage(combatant: entity) {}
event Damaged(target: Character, amount: int)
event PoisonSummary(target: Character, total_damage: int, rounds: int)

condition Poisoned(potency: int) on bearer: Character
    stacking first
{
    state {
        ticks_elapsed: int = 0
        cumulative_damage: int = 0
    }

    on_apply {
        state.cumulative_damage = roll(dice(potency, 6)).total
        bearer.HP -= state.cumulative_damage
        emit Damaged(target: bearer, amount: state.cumulative_damage)
    }

    on RoundEndDamage(combatant: bearer) {
        state.ticks_elapsed += 1
        let tick_dmg = roll(1d4).total
        state.cumulative_damage += tick_dmg
        bearer.HP -= tick_dmg
    }

    on_remove {
        emit PoisonSummary(target: bearer, total_damage: state.cumulative_damage,
                           rounds: state.ticks_elapsed)
    }
}
```

**Key rules:**

- Declared in a `state { ... }` block inside the condition body, before executable blocks
- Each field: `name: Type = default_expr` — defaults are required
- Access via `state.field_name` prefix — **mutable** in on_apply, on_remove, on-event handlers; **read-only** in modify
- `state` is a reserved identifier inside conditions — cannot be used as a param or receiver name
- Allowed types: all value types including entity refs, enums, lists, structs. Disallowed: Condition, ActiveCondition, Module, FnRef
- Default expressions may reference condition parameters
- **Inheritance:** child sees parent state fields, can add its own, cannot redeclare parent field names. Sibling parents with the same field name is a checker error.
- **Persistence:** one mutable state map threaded through the full inherited dispatch chain. on_apply: final map travels with ApplyCondition effect. on-event/on_remove: written back via SetConditionState at dispatch exit. If condition removed mid-block, write-back is a no-op.

### Condition with Event Handlers

Event handlers co-locate event-reactive logic inside the condition. They replace the pattern of a separate `hook` + `has_condition()` guard.

```ttrpg-with-preamble
event MeleeHit(attacker: Character, target: Character) {}

condition FireShield(caster_level: int) on bearer: Character
    stacking first
{
    on MeleeHit(target: bearer) {
        trigger.attacker.HP -= roll(1d6 + caster_level).total
    }
}
```

Trigger bindings use the same syntax as hooks. The condition's receiver and params are in scope for binding expressions:

```ttrpg-with-preamble
// Only fires when the nemesis is the attacker
condition Vendetta(nemesis: Character) on bearer: Character
    stacking first
{
    on Damaged(target: bearer, attacker: nemesis) {
        bearer.HP += trigger.amount
    }
}
```

**Handler scope:** `bearer`, `self` (ActiveCondition), `trigger` (event payload), `state` fields, condition params.

**State + self-removal:**

```ttrpg-with-preamble
event MeleeHit(attacker: Character, target: Character) {}

condition Thorns on bearer: Character stacking first {
    state { charges: int = 3 }

    on MeleeHit(target: bearer) {
        state.charges -= 1
        trigger.attacker.HP -= roll(1d4).total
        if state.charges <= 0 {
            remove_condition(bearer, "Thorns")
        }
    }
}
```

**Key rules:**

- Handlers fire after all hooks for the event (post-hook state)
- Only stacking winners execute handlers
- Snapshot safety: removed conditions are skipped; newly applied conditions don't fire in the same emit
- `trigger` is a reserved name in conditions with `on` handlers
- Multiple `on` handlers per condition are allowed (same or different events)
- Not suppressible — to stop a handler, remove the condition

See [`language_reference.md`](language_reference.md) for full event handler rules (dispatch order, stacking, snapshot semantics, state threading).

### Condition Stacking Policies

When multiple instances of the same condition exist on one bearer, the `stacking` clause controls which instances contribute effects. Place it after the condition header, before `{`.

| Policy | Syntax | Meaning |
|--------|--------|---------|
| `all` | (default, implicit) | Every instance contributes all effects |
| `first` | `stacking first` | Oldest instance wins; all others suppressed |
| `best by highest` | `stacking best by highest(param) ties oldest` | Highest param value wins; ties broken by oldest |
| `best by lowest` | `stacking best by lowest(param) ties oldest` | Lowest param value wins; ties broken by oldest |

**Suppressed instances** remain in state (duration keeps ticking). When the winner expires, the next-best becomes the new winner on next evaluation.

The `stacking` clause belongs to the concrete condition — it is not copied by `include`.

For `best by`, the named parameter must be `int` and declared on that condition.

```ttrpg-with-preamble
mechanic attack_roll(
    attacker: Character,
    target: Character,
    attack_mod: int = 0
) -> RollResult {
    roll(1d20 + attack_mod)
}

derive can_cast(caster: Character) -> bool #spellcasting_gate {
    true
}

// Parameterless non-doubling: only one instance matters
condition Prone on bearer: Character
    stacking first
{
    modify attack_roll(target: bearer) {
        attack_mod = attack_mod + 4
    }
}

// Parameterised: strongest concealment wins
condition Concealed(level: int) on bearer: Character
    stacking best by highest(level) ties oldest
{
    modify attack_roll(target: bearer) {
        attack_mod = attack_mod - level
    }
}

// Multi-opponent: each instance tracks a different opponent (default all)
condition Grappling(opponent: Character, hold: GrapplingHold) on bearer: Character {
    modify [#spellcasting_gate](caster: bearer) {
        result = false
    }
}
```

**When to use each policy:**
- `first` — boolean status effects that shouldn't double (Prone, Stunned, Dead)
- `best by highest/lowest` — parameterised effects where only the strongest matters (Concealed, Cover)
- `all` (default) — effects that genuinely stack or track distinct sources (Grappling, Buff per source)

### Condition as First-Class Value

Condition names are values of type `Condition`. They can be stored in variables,
passed as function parameters, and used in `apply_condition()` / `remove_condition()`.
This enables shared helpers that abstract common spell patterns.

```ttrpg-with-preamble
enum Duration { EndOfTurn, Rounds(count: int), Indefinite }

condition Paralyzed on bearer: entity {
    on_apply {}
}

condition Sleeping on bearer: entity {
    on_apply {}
}

// Generic helper: save-negates-condition pattern
function resolve_save_negates_condition(
    caster: entity,
    targets: list<entity>,
    spell_name: string,
    cond: Condition,
    duration_rounds: int
) {
    for target in targets {
        apply_condition(target, cond, Duration.Rounds(duration_rounds))
    }
}

// Callers pass the condition by name
function resolve_hold_person(caster: entity, targets: list<entity>) {
    resolve_save_negates_condition(caster, targets, "Hold Person", Paralyzed, 10)
}

function resolve_sleep(caster: entity, targets: list<entity>) {
    resolve_save_negates_condition(caster, targets, "Sleep", Sleeping, 20)
}
```

**`Condition` vs `ActiveCondition`:**
- `Condition` = a condition blueprint (e.g. `Prone`, `Sleeping`, `Concealed(level: 3)`)
- `ActiveCondition` = a live instance on an entity, with `.name`, `.duration`, `.source`, `.id`, `.applied_at`, `.tags` fields; returned by `conditions(entity)`. Narrow with `is ActiveCondition<CondName>` to access condition params
- `has_condition(entity, Prone)` → `bool` — checks if entity has an active condition by name (bare condition identifier, not string). Prefer over `any([c.name == X for c in conditions(entity)])`.

**Typed `conditions()` overload:**

`conditions(entity, ConditionName)` returns `list<ActiveCondition<ConditionName>>` — a typed list filtered to only instances of the named condition. Each element exposes condition parameters as fields and state fields via `.state`:

```ttrpg-snippet
condition Grappling(opponent: entity, hold: GrapplingHold) on bearer: entity {
    state { current_hold: GrapplingHold = hold, controlling: bool = true }
}

/ Typed access to params and state:
let grapples = conditions(bearer, Grappling)
if len(grapples) > 0 {
    let g = first(grapples).unwrap()
    g.opponent          // param (immutable, from application time)
    g.hold              // param
    g.state.current_hold // state field (mutable within condition, read-only here)
    g.state.controlling  // state field
    g.id                // base ActiveCondition field still accessible
    g.name              // base ActiveCondition field
    remove_condition(bearer, g) // compatible with remove_condition
}
```

- Second argument must be a bare condition identifier (not a string)
- Returns empty list if no matching conditions exist
- State access is read-only from outside the condition — only the condition's own blocks can mutate state
- Typed results are compatible with `remove_condition()` (subtype of `ActiveCondition` and `Condition`)

**`is ActiveCondition<CondName>` narrowing:**

When iterating all conditions via `conditions(entity)`, use `is ActiveCondition<CondName>` to narrow and access params:

```ttrpg-snippet
for c in conditions(target) {
    if c is ActiveCondition<Grappling> {
        c.opponent           // typed as entity after narrowing
        c.state.current_hold // state access works too
    } else if c is ActiveCondition<Frightened> {
        c.source_entity      // Frightened-specific param
    }
}
```

- Before narrowing, only base fields (`.name`, `.duration`, `.source`, `.id`, `.applied_at`, `.tags`) are accessible — accessing param fields on un-narrowed `ActiveCondition` is a checker error
- After narrowing, params and `.state` are available with their declared types
- Use the 2-arg `conditions(entity, CondName)` overload when you only care about one condition type; use `is` narrowing when you need to branch on multiple condition types in a single loop

**`EffectSource` — condition provenance:**

`EffectSource` is a user-defined enum (like `Duration`) that tags conditions with their origin. The engine requires a plain `Unknown` variant. `apply_condition()` returns `option<int>` (`some(id)` on success, `none` if the host vetoes) and accepts an optional 4th argument for the source; when omitted, it defaults to `EffectSource.Unknown`.

```ttrpg-snippet
enum EffectSource {
    Unknown,
    Spell(name: string, caster_level: int),
    Item(name: string)
}

// Apply with source metadata:
apply_condition(target, Held, Duration.Rounds(10),
    EffectSource.Spell(name: "Hold Person", caster_level: 7))

// Query source on active conditions:
for c in conditions(target) {
    if let EffectSource.Spell(name, caster_level) = c.source {
        // use caster_level for dispel checks
    }
}
```

### Suspension (Imprisonment / Stasis Pattern)

The suspension system temporarily removes entities from play or freezes their progression. Models imprisonment, soul trapping, temporal stasis, and similar effects.

**Core concepts:**
- **SuspensionRecord**: source-keyed record with `presence` (Presence enum), `freeze_turns`, `freeze_durations`
- **Worst-case-wins**: off-board if ANY record says OffBoard, turns frozen if ANY says so
- **Auto-cleanup**: suspension keyed to a condition token is removed when the condition is removed
- **Presence**: built-in enum with `OnMap` and `OffBoard` variants

**Lifecycle-based suspension** (preferred — auto-cleans on condition removal):

```ttrpg
entity Character { name: string }

condition Imprisoned on bearer: entity
    stacking first
{
    on_apply {
        suspend(bearer, Presence.OffBoard, freeze_turns: true, freeze_durations: true)
    }
}
```

`suspend(entity, ...)` is only available in lifecycle blocks. It keys the suspension to `condition_token()` automatically. When the condition is removed (via `remove_condition()` or `revoke()`), the suspension record is cleaned up after the removal succeeds.

**Manual suspension** (for effects not tied to a single condition):

```ttrpg-snippet
// In an action or function:
suspend_with_source(target, source_id: 42,
    presence: Presence.OffBoard, freeze_turns: true, freeze_durations: true)

// Later, to restore:
remove_suspension_source(target, source_id: 42)
```

**Query builtins** (available anywhere):
- `is_suspended(target)` → true if any suspension records exist
- `is_off_board(target)` → true if any record sets OffBoard
- `are_turns_frozen(target)` → true if any record freezes turns
- `are_durations_frozen(target)` → true if any record freezes durations

**Duration freeze semantics:** when durations are unfrozen, each condition's `applied_at` is bumped forward to preserve remaining duration. Conditions applied mid-freeze get a proportionally smaller bump.

**Enumeration:** off-board entities are excluded from hook candidate scanning and modify evaluation but remain accessible for direct queries (e.g., checking conditions, revoking).

**Typical spell patterns:**
- **Imprisonment / Trap the Soul**: `suspend(bearer, Presence.OffBoard, freeze_turns: true, freeze_durations: true)` in on_apply
- **Temporal Stasis**: same as above — entity removed from all interaction
- **On-map freeze** (e.g., paralysis variant that also pauses durations): `suspend(bearer, Presence.OnMap, freeze_turns: true, freeze_durations: true)`
- **Astral Spell**: suspend body with OffBoard + spawn astral proxy (composes with entity construction and summoning patterns)

### Condition Transfer (Polymorph Pattern)

`transfer_conditions(from, to, "tag")` moves all active conditions on `from` that have `tag` in their tag set to `to`. Designed for polymorph/transformation where mental/magical conditions should follow the creature's identity between entities.

**Key properties:**
- Preserves condition identity: id, params, duration, source, tags, gained_at
- Does NOT fire on_apply/on_remove hooks or host gates — atomic relocation
- Allowed in lifecycle blocks (critical for the revert path in on_remove)
- Tag must be declared; checker validates string literals at compile time
- Same-entity calls are no-ops; nonexistent entities are no-ops
- Bearer type incompatible conditions are skipped (stays on source)
- Self-exclusion: in on_remove, the condition being removed is automatically excluded from transfer

**Tag convention:** Tag conditions that represent mental/magical effects with `#transferable` (or similar). Physical/equipment conditions are not tagged.

```ttrpg-with-preamble
entity Monster {
    name: string
    hp: resource(0..=max_hp)
    max_hp: int
    ac: int
}

tag transferable

condition Blessed on bearer: entity stacking all {
    tags: #transferable
}

condition Regeneration(hp_per_round: int) on bearer: entity stacking all {
    // No #transferable — physical trait stays with the body
}

condition Polymorphed(original: Character, suspension_key: int) on bearer: Monster
    stacking first
{
    on_remove {
        transfer_conditions(bearer, original, "transferable")
        original.HP = bearer.hp
        remove_suspension_source(original, source_id: suspension_key)
        despawn(bearer)
    }
}

function polymorph(target: Character, form_name: string, form_ac: int, key: int) -> Monster {
    suspend_with_source(target, source_id: key,
        presence: Presence.OffBoard, freeze_turns: true, freeze_durations: true)

    let form = Monster {
        name: form_name,
        hp: target.HP,
        max_hp: target.max_HP,
        ac: form_ac
    }
    transfer_conditions(target, form, "transferable")
    apply_condition(form, Polymorphed(original: target, suspension_key: key),
        Duration.Indefinite)
    form
}
```

**Transferable condition checklist** (verify before tagging as transferable):
- Bearer type is `entity` (not `Character` or `Monster`) — ensures cross-type compatibility
- No side effects in lifecycle hooks (`suspend()`, `spawn()`) — transfer skips hooks
- Modify blocks target derives with `target: entity` parameters
- Stacking policy is `stacking all` or cannot conflict on destination

### Resistance Check (guard match)

```ttrpg
enum DamageType { slashing, piercing, bludgeoning, fire, cold }

entity Character {
    name: string
    resistances: set<DamageType>
    immunities: set<DamageType>
    vulnerabilities: set<DamageType>
}

derive apply_resistances(
    target: Character,
    raw_damage: int,
    damage_type: DamageType
) -> int {
    match {
        damage_type in target.immunities      => 0,
        damage_type in target.resistances     => floor(raw_damage / 2),
        damage_type in target.vulnerabilities => raw_damage * 2,
        _ => raw_damage
    }
}
```


### Struct Spread (copy-and-modify)

```ttrpg
struct Weapon {
    name: string
    damage: DiceExpr
    bonus: int = 0
}

derive enchant_weapon(w: Weapon, extra_bonus: int) -> Weapon {
    Weapon { bonus: w.bonus + extra_bonus, ..w }
}
```

`..base` copies all unspecified fields from `base`. Explicit fields override the spread. Spread must come last: `Weapon { bonus: 5, ..old }`. Works with structs only (not entities).

---

## Validation Workflow

Check a file (transitive `import` dependencies are resolved automatically):

```bash
ttrpg check myfile.ttrpg
```

Check a snippet (auto-wrapped in `system "<check>" { ... }`):

```bash
echo 'derive foo() -> int { floor(10 / 3) }' | ttrpg check -s
```

Check multiple files together (imports are still followed from each):

```bash
ttrpg check core.ttrpg combat.ttrpg
```

---

## Query / Introspection

The `query` subcommand inspects type declarations and signatures without executing code.

### Topics

| Topic                 | Description                              |
|-----------------------|------------------------------------------|
| `types`               | All type declarations (entities, structs, enums, units) |
| `events`              | All event declarations                   |
| `actions`             | All action signatures                    |
| `conditions`          | All condition declarations               |
| `mechanics` (alias: `derives`) | All derives and mechanics         |
| `reactions`           | All reaction signatures                  |
| `hooks`               | All hook signatures                      |
| `entity <name>`       | Detailed entity schema (fields, groups)  |
| `all`                 | Full schema dump (all of the above)      |

### Usage

```bash
ttrpg query types myfile.ttrpg
ttrpg query actions core.ttrpg combat.ttrpg
ttrpg query entity Character combat.ttrpg
ttrpg query all *.ttrpg
```

Query a snippet:

```bash
ttrpg query types -s -c 'entity Foo { x: int }'
echo 'derive double(n: int) -> int { n * 2 }' | ttrpg query mechanics -s
```

### Flags

| Flag               | Description                                          |
|--------------------|------------------------------------------------------|
| `--system <name>`  | Filter output to declarations from a specific system |
| `--xref`           | Include cross-references (`query entity` only)       |
| `-s, --snippet`    | Auto-wrap source in system block                     |
| `-c <source>`      | Inline source instead of file paths                  |

### Cross-references (`--xref`)

When querying a specific entity, `--xref` appends all applicable conditions, actions, reactions, and hooks that reference that entity type:

```bash
ttrpg query entity Character combat.ttrpg --xref
```

```
entity Character {
  name: string
  HP: resource
  ...
}

// applicable conditions
condition Prone on bearer: Character
condition Stunned on bearer: Character

// actions
action Attack on attacker: Character(target: Character, weapon: Weapon)
action Dash on actor: Character

// reactions
reaction OpportunityAttack on reactor: Character (trigger: entity_leaves_reach)

// hooks
hook DeathDrop on target: Character (trigger: Damaged)
```
