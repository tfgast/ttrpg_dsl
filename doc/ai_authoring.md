# TTRPG DSL — AI Authoring Guide

> Concise reference for AI agents generating DSL code.
> For full details see [`language_reference.md`](language_reference.md) and `spec/v0/`.
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
- Declarative buff/debuff overlay? → **condition**
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

## Declaration Skeletons

### Enum

```ttrpg
enum DamageType { slashing, piercing, bludgeoning, fire, cold }
enum HitResult { hit(amount: int), miss }
enum Size ordered { small, medium, large }
```

### Struct

```ttrpg
struct Weapon {
    name: string
    damage: DiceExpr
    bonus: int = 0
}
```

### Entity

```ttrpg
group Spellcasting {
    spell_dc: int
    spell_slots: int = 0
}

group CombatStats {
    AC: int
}

entity Character {
    name: string
    level: int = 1
    HP: resource(0..=max_HP)
    max_HP: int
    speed: int = 30
    position: Position
    optional Spellcasting
    include CombatStats
}
```

### Group

```ttrpg
group Spellcasting {
    spell_dc: int
    spell_slots: int = 0
}

group CombatStats {
    AC: int
    abilities: map<Ability, int>
}

enum Ability { STR, DEX, CON, INT, WIS, CHA }
```

### Unit Type

```ttrpg
unit Feet suffix ft { value: int }
```

### Table

```ttrpg
// Single-key table (range patterns + wildcard fallback)
table str_melee_mod(score: int) -> int {
    1..=3   => -3,
    4..=5   => -2,
    6..=8   => -1,
    9..=12  =>  0,
    13..=15 =>  1,
    16..=17 =>  2,
    _       =>  3
}

// Types needed by multi-key examples
enum CombatAptitude { martial, semi_martial, non_martial }
enum SaveCategory { Fighter, Cleric, Thief }
struct SavingThrows { death: int, wand: int, paralysis: int, breath: int, spell: int }

// Multi-key table (bracket syntax)
table character_thac0(aptitude: CombatAptitude, level: int) -> int {
    [martial, 1..=3]       => 19,
    [martial, 4..=6]       => 17,
    [semi_martial, 1..=4]  => 19,
    [semi_martial, 5..=8]  => 17,
    [non_martial, 1..=5]   => 19,
    [non_martial, _]       => 14
}

// Returning struct values
table saving_throws(category: SaveCategory, level: int) -> SavingThrows {
    [Fighter, 1..=3] => SavingThrows { death: 12, wand: 13, paralysis: 14, breath: 15, spell: 16 },
    [Fighter, 4..=6] => SavingThrows { death: 10, wand: 11, paralysis: 12, breath: 13, spell: 14 }
}
```

**Key rules:**

- Pure scope (like derive) — no dice, no mutation, no receiver
- Keys can be: expressions (enum variants, literals), inclusive ranges (`1..=3`), or wildcard (`_`)
- Ranges only valid for `int` parameters
- Single-key: `key => value`; multi-key: `[key1, key2] => value`
- First-match semantics — entries evaluated in order
- Wildcard must be last (checker warns about unreachable entries after `_`)
- Called like any function: `str_melee_mod(14)`, `character_thac0(martial, 5)`

### Function

```ttrpg-with-preamble
action Attack on attacker: Character (target: Character) {
    cost { action }
    resolve {
        let atk: RollResult = roll(1d20 + 5)
        if atk >= 10 {
            target.HP -= roll(1d8).total
        }
    }
}

// Void function (no return type)
function resolve_attacks(attacker: Character, target: Character, count: int) {
    with_budget(attacker, { actions: count }) {
        for i in 0..count {
            attacker.Attack(target)
        }
    }
}

// Function with return value
function compute_heal(base: int, bonus: int) -> int {
    base * 2 + bonus
}
```

**Key rules:**

- Can roll dice, mutate entities, emit events, call actions/functions/derives/mechanics
- No receiver (`on`), no cost/requires clauses
- Cannot use `invocation()` directly (actions called by a function get their own)
- NOT subject to condition `modify` clauses (no modify pipeline)
- Return type optional — omit `->` for void functions
- Supports `return expr` for early exit (or bare `return` for void functions)
- **Function references:** functions can be stored as first-class values using `fn(T1, T2) -> R` types. Use the function name as a bare identifier to create a reference. Only `function` blocks without `with` constraints are eligible.
- `with_budget(entity, { field: value }) { body }` provisions a scoped turn budget:
  - Actions called inside the body deduct from the provisioned budget
  - `turn` keyword works inside action/reaction/hook resolve blocks (set by action dispatch)
  - Use `budget_of(entity)` to query an entity's budget from function scope (outside actions)
  - Entity arg pays costs; action receiver can differ (summoning pattern)
  - Nesting supported; cleanup always runs (error-safe)

### Derive

```ttrpg
derive modifier(score: int) -> int {
    floor((score - 10) / 2)
}
```

### Mechanic

```ttrpg-with-preamble
mechanic attack_roll(bonus: int, mode: RollMode) -> RollResult {
    let base: DiceExpr = match mode {
        normal       => 1d20,
        advantage    => 2d20kh1,
        disadvantage => 2d20kl1
    }
    roll(base + bonus)
}
```

### Action

```ttrpg-with-preamble
action Dash on actor: Character () {
    cost { action }
    resolve {
        turn.movement += actor.speed
    }
}
```

Actions may declare a return type with `-> Type` after the parameter list. The resolve block must then produce a value of that type. On veto or requires/cost failure, `none` is returned, so declare `option<T>`:

```ttrpg-with-preamble
action CheckAlive on actor: Character () -> option<bool> {
    resolve {
        some(actor.HP > 0)
    }
}
```

All overloads of the same action name must agree on return type.

### Reaction

```ttrpg-with-preamble
reaction ConcentrationSave on caster: Character (trigger: Damaged(target: caster)) {
    cost free
    resolve {
        let dc = max(10, floor(trigger.amount / 2))
        let save: RollResult = roll(1d20)
        if save.total < dc {
            // concentration broken
        }
    }
}
```

### Hook

```ttrpg-with-preamble
event turn_start(actor: Character) {}

hook Regenerate on creature: Character (trigger: turn_start(actor: creature)) {
    if creature.HP > 0 {
        creature.HP += 10
    }
}
```

### Condition

```ttrpg-with-preamble
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
    modify attack_roll(attacker: bearer) {
        mode = disadvantage
    }
    modify attack_roll(target: bearer) {
        mode = advantage
    }
}

```

**Condition tags** — static categorical properties declared inside the condition body with `tags:`:

```ttrpg
entity Character { hp: int }
tag curse
tag disease

condition Afflicted on bearer: Character { }
condition BestowCurse on bearer: Character {
    tags: #curse
}
condition MummyRot(severity: int) extends Afflicted on bearer: Character {
    tags: #curse, #disease
}
```

At runtime, tags are a `Set<string>` on `ActiveCondition.tags`: `"curse" in c.tags`.

Condition tags describe **what the condition is** (`#curse`, `#disease`, `#poison`). Use `EffectSource` for **how it was applied** (magical vs non-magical). Use modify-clause tags for **individual effect suppression** (`#penalty`, `#position`).

**Lifecycle hooks (on_apply / on_remove):**

- At most one `on_apply` and one `on_remove` per condition
- Hook-like capabilities: mutation, dice, emit, call derives/mechanics/functions
- **Forbidden:** `apply_condition()`, `remove_condition()`, `revoke(invocation)`, `invocation()`
- **Allowed:** `transfer_conditions()`, `suspend()`, `condition_token()`, `despawn()`, field mutations
- `on_apply` fires before activation — error prevents application
- `on_remove` fires before removal — error does NOT prevent removal
- `bearer` + condition params + `state` (mutable, if declared) in scope; `invocation()` unavailable
- Use `extends` (not `apply_condition` in on_apply) for conditions that imply other conditions

**Periodic blocks (`periodic #tag { ... }`):**

- Per-round effects co-located with the condition — replaces standalone processing functions
- Tag must be declared with `tag` at system level; no duplicate tags per condition
- Executed by `process_periodic_conditions(combatants, "tag_name")` from the combat loop
- **Scope:** `bearer` + condition params + `self` (full `ActiveCondition` instance) + `state` (mutable state fields, if declared)
- **Full function-body permissions:** mutations, dice, emit, `apply_condition()`, `remove_condition()`, action calls — NOT restricted like lifecycle blocks
- Only stacking winners execute; inherits via `extends` (parent before child)

### Event

```ttrpg
entity Character { name: string }
event Damaged(target: Character, attacker: Character) {
    amount: int
    damage_type: string
}
```

### Tag

```ttrpg
tag #concentration
tag #ranged
```

### Const

Named compile-time constants. Pure expressions only (no dice, no mutation).
Useful for magic numbers, struct literal boilerplate, and enum defaults.

```ttrpg
const MAX_LEVEL = 20
const BASE_THAC0: int = 20
const STATS = [10, 12, 14]
```

Consts can reference other consts and use arithmetic, struct literals, enum variants, and list/map literals. Assignment to a const is an error.

### Prompt

```ttrpg-with-preamble
prompt choose_target(chooser: Character, candidates: list<Character>) -> Character {
    hint: "Choose a target creature"
    suggest: candidates[0]
}
```

### Option

```ttrpg-with-preamble
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

option flanking extends "<snippet>" {
    description: "Flanking grants advantage on melee attacks"
    default: off
    when enabled {
        modify attack_roll(attacker: _) {
            mode = advantage
        }
    }
}
```

### Move (PbtA Sugar)

```ttrpg
entity Character { name: string, stats: map<string, int> }

move GoAggro on actor: Character (target: Character) {
    trigger: "threaten with force"
    roll: 2d6 + actor.stats["Hard"]
    on strong_hit {
        // 10+: full success
    }
    on weak_hit {
        // 7-9: partial success
    }
    on miss {
        // 6-: failure
    }
}
```

**Key rules:**

- Desugars to a mechanic (for the roll) + action (with outcome matching)
- Hardcoded PbtA thresholds: 10+ strong\_hit, 7–9 weak\_hit, 6- miss
- Must have exactly three outcomes: `strong_hit`, `weak_hit`, `miss`
- Action cost is always `{ action }`
- For custom thresholds, use mechanic + action directly instead

### System & Use

```ttrpg
// system "Core Rules" {
//     // all declarations go here
// }
//
// // Names without spaces can be bare identifiers:
// system CoreRules {
//     // all declarations go here
// }
//
// // In another file:
// use "Core Rules"
// use "Core Rules" as Core
// use CoreRules as Core
// // Then: Core.TypeName, Core.function(), Core.Enum.Variant
```

---

## Type System Quick Reference

### Primitives

| Type     | Notes                                        |
|----------|----------------------------------------------|
| `int`    | Signed integer                               |
| `bool`   | `true` / `false`                             |
| `string` | Double-quoted                                |
| `float`  | No literals — only from `/` operator         |

### Composites

| Type              | Notes                                    |
|-------------------|------------------------------------------|
| `list<T>`         | Ordered sequence; `[1, 2, 3]`            |
| `set<T>`          | Unordered unique; `[a, b].to_set()`      |
| `map<K, V>`       | Key-value; `{"a": 1}`                    |
| `option<T>`       | `some(x)` or `none`                      |
| `resource(m..=n)` | Bounded int, clamps on assign            |

### Dice Pipeline

```
DiceExpr  ──roll()──▶  RollResult  ──.total──▶  int
                                     .unmodified (sum of kept dice, no modifier)
                                     .dice       (all die outcomes)
                                     .kept       (after keep/drop filters)
                                     .modifier   (constant terms)
```

- `DiceExpr + DiceExpr` → combined pool
- `DiceExpr + int` → adds modifier
- `DiceExpr * int` → **TYPE ERROR** (use `multiply_dice(expr, factor)`)
- `RollResult >= int` → implicit `.total` coercion in comparisons
- `DiceExpr >= int` → **TYPE ERROR** (must `roll()` first)

### Arithmetic Rules

- `int / int` → **always float** — use `floor()` or `ceil()` to get int
- `int div int` → **int** (floor division) — e.g., `7 div 2` = `3`, `-7 div 2` = `-4`
- `float + int` → float (numeric promotion)
- Unit arithmetic: same-unit `+`/`-`, `int * unit`, `unit / unit → float`
- Unit floor division: `unit div int → unit`, `unit div unit → int`

### Special Types

| Type              | Notes                                         |
|-------------------|-----------------------------------------------|
| `entity`          | Polymorphic any-entity alias in type position  |
| `any`             | Dynamically typed — enter via `to_any(x)`, narrow via `is` |
| `Position`        | Opaque board location, use `distance(a, b)`    |
| `Direction`       | Opaque spatial orientation (host-provided)      |
| `Duration`        | `EndOfTurn`, `StartOfNextTurn`, `Rounds(n)`, `Minutes(n)`, `Indefinite` |
| `EffectSource`    | Condition provenance metadata — must have plain `Unknown` variant |
| `Invocation`      | Execution scope handle from `invocation()`     |
| `Condition`       | Condition identifier — pass to `apply_condition()`, store in variables |
| `ActiveCondition` | Runtime condition instance: `.name`, `.duration`, `.source`, `.id` |
| `Presence`        | Built-in enum: `OnMap`, `OffBoard` — entity board presence state |

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

**Key rules:**

- At most one `on_apply` and one `on_remove` per condition
- Hook-like capabilities: mutation, dice rolls, emit events, call derives/mechanics/functions
- **Forbidden inside lifecycle blocks:** `apply_condition()`, `remove_condition()`, `revoke(invocation)`, `invocation()` (prevents reentrancy). `revoke entity.Group` is allowed.
- `on_apply` fires **before** activation (modify/suppress not yet in effect). Error → condition never applied.
- `on_remove` fires **before** removal (modify/suppress still in effect). Error → condition still removed.
- `bearer` + condition parameters + `state` (if declared) in scope. `invocation()` not available.
- **Available in lifecycle blocks:** `suspend()`, `condition_token()`, `transfer_conditions()`, `despawn()` — see Suspension and Transfer patterns below.
- `transfer_conditions()` is safe in lifecycle blocks because it skips on_apply/on_remove hooks (no reentrancy risk).
- With `extends`, ancestor lifecycle blocks run first (DFS post-order). One mutable state map is threaded through the full chain — parent mutations visible to child blocks.
- **Design principle:** use `extends` for conditions that imply others, not `apply_condition()` in on_apply.

### Condition State Fields

State fields are per-instance mutable fields private to the condition. They provide internal bookkeeping (counters, accumulators, cached values) without polluting the condition's public interface. Unlike params (immutable, externally matchable), state fields are mutable and invisible to `conditions()`, stacking, and `remove_condition()`.

```ttrpg
entity Character {
    HP: resource(0..=max_HP)
    max_HP: int = 20
}

tag round_end_damage
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

    periodic #round_end_damage {
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
- Access via `state.field_name` prefix — **mutable** in on_apply, on_remove, periodic; **read-only** in modify
- `state` is a reserved identifier inside conditions — cannot be used as a param or receiver name
- Allowed types: all value types including entity refs, enums, lists, structs. Disallowed: Condition, ActiveCondition, Module, FnRef
- Default expressions may reference condition parameters
- **Inheritance:** child sees parent state fields, can add its own, cannot redeclare parent field names. Sibling parents with the same field name is a checker error.
- **Persistence:** one mutable state map threaded through the full inherited dispatch chain. on_apply: final map travels with ApplyCondition effect. periodic/on_remove: written back via SetConditionState at dispatch exit. If condition removed mid-block, write-back is a no-op.

### Condition with Periodic Blocks

Periodic blocks run during the combat loop via `process_periodic_conditions()`, not at condition apply/remove time. They replace standalone processing functions like `process_bleeding()`.

```ttrpg
tag round_end_damage

entity Creature { hp: int }

event Ticked(target: entity, amount: int)

condition Bleeding on bearer: Creature
    stacking first
{
    periodic #round_end_damage {
        bearer.hp = bearer.hp - 1
        emit Ticked(target: bearer, amount: 1)
        if bearer.hp <= 0 {
            remove_condition(bearer, "Bleeding")
        }
    }
}

condition OnFire on bearer: Creature
    stacking all
{
    periodic #round_end_damage {
        let damage = roll(1d6).total
        bearer.hp = bearer.hp - damage
        emit Ticked(target: bearer, amount: damage)
    }
}
```

**Key rules:**

- `periodic #tag { ... }` — tag must be declared with `tag` at system level
- Multiple periodic blocks allowed (different tags); duplicate tags per condition is a parser error
- **Scope:** `bearer` + condition params + `self` (the `ActiveCondition` instance: `.name`, `.duration`, `.source`, `.id`, `.applied_at`, `.tags`) + `state` (mutable state fields, if declared)
- **Full permissions:** unlike lifecycle blocks, periodic blocks CAN call `apply_condition()`, `remove_condition()`, and actions
- **Processing:** `process_periodic_conditions(combatants, "round_end_damage")` — iterates combatants, snapshots conditions, executes matching periodic blocks on stacking winners only
- **Snapshot semantics:** conditions removed mid-pass are skipped; conditions applied to the same bearer don't tick until the next call
- **Stacking:** `all` = every instance ticks separately (e.g., overlapping Blade Barriers), `first` = only oldest, `best by` = only winner
- **Inheritance:** parent periodic blocks execute before child (DFS post-order, same as lifecycle blocks)
- **Runtime tag validation:** `process_periodic_conditions(combatants, "typo")` raises a runtime error if the tag is undeclared

### Condition Stacking Policies

When multiple instances of the same condition exist on one bearer, the `stacking` clause controls which instances contribute effects. Place it after the condition header, before `{`.

| Policy | Syntax | Meaning |
|--------|--------|---------|
| `all` | (default, implicit) | Every instance contributes all effects |
| `first` | `stacking first` | Oldest instance wins; all others suppressed |
| `best by highest` | `stacking best by highest(param) ties oldest` | Highest param value wins; ties broken by oldest |
| `best by lowest` | `stacking best by lowest(param) ties oldest` | Lowest param value wins; ties broken by oldest |

**Suppressed instances** remain in state (duration keeps ticking). When the winner expires, the next-best becomes the new winner on next evaluation.

The `stacking` clause belongs to the concrete condition — it is NOT inherited via `extends`.

For `best by`, the named parameter must be `int` and declared on that condition (not inherited).

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
- `ActiveCondition` = a live instance on an entity, with `.name`, `.duration`, `.source`, `.id`, `.applied_at` fields; returned by `conditions(entity)`
- `has_condition(entity, "Prone")` → `bool` — checks if entity has an active condition by name. Prefer over `any([c.name == X for c in conditions(entity)])`.

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
    Presence.OffBoard, freeze_turns: true, freeze_durations: true)

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
        Presence.OffBoard, freeze_turns: true, freeze_durations: true)

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

### Entity Construction

Entities can be constructed inline using struct literal syntax. Only allowed in mutating contexts (function, action, reaction, hook, `with_budget`).

```ttrpg
entity Monster {
    name: string
    hit_dice: int
    max_hp: int
    ac: int = 10
    optional Spellcasting {
        spell_slots: int
        spell_dc: int = 10
    }
    include BasicStats
}

group BasicStats {
    str_score: int = 10
    dex_score: int = 10
}

// Basic construction — fields with defaults can be omitted
function create_ogre() -> Monster {
    Monster {
        name: "Ogre",
        hit_dice: 4,
        max_hp: 26,
        ac: 5,
    }
}

// With inline group initializer — activates an optional group
function create_wizard() -> Monster {
    Monster {
        name: "Goblin Wizard",
        hit_dice: 1,
        max_hp: 4,
        Spellcasting {
            spell_slots: 3,
            spell_dc: 12,
        },
    }
}

// Override include group defaults
function create_giant() -> Monster {
    Monster {
        name: "Hill Giant",
        hit_dice: 8,
        max_hp: 44,
        BasicStats {
            str_score: 19,
            dex_score: 8,
        },
    }
}
```

**Key rules:**

- Include groups auto-materialize with defaults if not provided
- Spread (`..base`) is not supported for entities
- Group initializers are not valid on struct or unit types
- Entity construction in derive, mechanic, table, condition, or prompt is a checker error

### Type Narrowing (is)

Use `expr is Type` to branch on type and access type-specific fields. The variable is narrowed within the then-block.

**Entity type narrowing:**

```ttrpg
entity Character {
    name: string
    level: int
}

entity Monster {
    name: string
    hit_dice: int
}

function get_power(target: entity) -> int {
    if target is Character {
        target.level
    } else if target is Monster {
        target.hit_dice
    } else {
        0
    }
}
```

**Any-type narrowing:**

Use `to_any(x)` to wrap any value into the `any` type, then `is` guards to narrow:

```ttrpg
struct Pos {
    x: int
    y: int
}

derive describe(val: any) -> string {
    if val is int {
        "a number"
    } else if val is Pos {
        "a position"          // val narrowed to Pos, field access works
    } else {
        "something else"
    }
}
```

Container types use concrete type parameters:

```ttrpg
derive sum_if_ints(val: any) -> int {
    if val is list<int> {
        sum(val)              // narrowed to list<int>
    } else {
        0
    }
}
```

Composes with `has` narrowing via `&&`:

```ttrpg-with-preamble
function spellcaster_dc(target: entity) -> int {
    if target is Character && target has Spellcasting {
        target.Spellcasting.spell_dc
    } else {
        0
    }
}
```

**Key rules:**

- Left operand must be `any` or entity type (specific or polymorphic `entity`)
- For entity: right operand must name a declared entity type
- For `any`: right operand can be any concrete type (primitives, structs, enums, containers like `list<int>`)
- `is any` and `is entity` are not valid targets — use concrete types
- Same precedence as `in` and `has`
- Narrowing applies only in the then-block (not the else-block)

---

## Module Structure Convention

Recommended declaration order within a `system` block:

1. Enums
2. Structs
3. Unit types
4. Tags
5. Groups
6. Entities
7. Events
8. Tables
9. Derives
10. Mechanics
11. Functions
12. Prompts
13. Actions
14. Reactions
15. Hooks
16. Conditions
17. Moves
18. Options

Multiple `system` blocks with the same name merge additively.
Symbol imports (`use`) are NOT transitive — each file must declare its own.

## Source Imports

Use the `import` directive to declare file-level source dependencies:

```
import "core.ttrpg"
import "combat.ttrpg"

use "Core"
system "Ext" {
    // can reference types from Core
}
```

- `import` loads source files (path must be a string); `use` exposes symbols from another system (name can be a string or identifier)
- Import paths are resolved relative to the importing file's directory
- Transitive imports are followed automatically — if `a.ttrpg` imports `b.ttrpg` and `b.ttrpg` imports `c.ttrpg`, loading `a.ttrpg` loads all three
- Duplicate imports are deduplicated by canonical path (diamond patterns are fine)
- Mutual imports between files are allowed (no cycle errors)

**Prefer `import` over glob patterns.** When each file declares its own imports, the dependency graph is explicit and the CLI only needs the entrypoint file(s) to discover the full set of sources.

`import` goes at the top of the file, before `use` declarations and `system` blocks.

## Package Manifests

Rule module directories (e.g., `ose/`, `osric/`) use a `ttrpg.toml` manifest to declare package identity and loadable targets:

```toml
manifest_version = 1

[package]
name = "ose"
default_target = "full"

[entries.core]
path = "ose_core.ttrpg"

[entries.combat]
path = "ose_combat.ttrpg"

[bundles.full]
entries = ["core", "class", "combat", "equipment", "magic", "spells"]
```

- **entry** = single root source file
- **bundle** = curated list of entries loaded together
- **target** = either an entry or bundle

Load by package name instead of glob patterns:

```
load ose            # loads default target (full bundle)
load ose:core       # loads single entry
load ose:chargen    # loads curated subset
```

When creating a new rule module directory, add a `ttrpg.toml` with at minimum a `[package]` table, one entry per source file, and a `full` bundle listing all entries.

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
