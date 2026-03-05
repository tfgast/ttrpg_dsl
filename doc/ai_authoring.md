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
| action    | yes  | yes    | `on` receiver  | unit    | yes  |
| reaction  | yes  | yes    | `on` + trigger | unit    | yes  |
| hook      | yes  | yes    | `on` + trigger | unit    | -    |
| condition | -    | -      | `on bearer`    | -       | -    |
| prompt    | -    | -      | -              | value   | -    |
| move      | yes  | yes    | `on` receiver  | unit    | yes  |

**Decision tree:**

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

## Top 11 Mistakes

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
use "Core"
system "Ext" {
    action Zap on target: Character () {
        resolve { target.HP -= 1 }    // ERROR: restricted field
    }
}
```

Restricted fields can only be mutated within the declaring system. Other systems can read them freely. Move the mutation into the declaring system, or remove the `restricted` modifier if cross-system mutation is intended.

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
- `with_budget(entity, { field: value }) { body }` provisions a scoped turn budget:
  - `turn` keyword becomes readable/writable inside the body
  - Actions called deduct from the provisioned budget
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

// Condition with lifecycle hooks (on_apply / on_remove)
// condition Poisoned(potency: int) on bearer: Character {
//     on_apply {
//         let dmg: RollResult = roll(dice(potency, 6))
//         bearer.HP -= dmg.total
//     }
//     on_remove {
//         bearer.poisoned_flag = false
//     }
//     modify saving_throw(target: bearer) {
//         mode = disadvantage
//     }
// }
```

**Lifecycle hooks (on_apply / on_remove):**

- At most one `on_apply` and one `on_remove` per condition
- Hook-like capabilities: mutation, dice, emit, call derives/mechanics/functions
- **Forbidden:** `apply_condition()`, `remove_condition()`, `revoke(invocation)`, `invocation()`
- `on_apply` fires before activation — error prevents application
- `on_remove` fires before removal — error does NOT prevent removal
- `bearer` + condition params in scope; `invocation()` unavailable
- Use `extends` (not `apply_condition` in on_apply) for conditions that imply other conditions

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
// // In another file:
// use "Core Rules"
// use "Core Rules" as Core
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
- `float + int` → float (numeric promotion)
- Unit arithmetic: same-unit `+`/`-`, `int * unit`, `unit / unit → float`

### Special Types

| Type              | Notes                                         |
|-------------------|-----------------------------------------------|
| `entity`          | Polymorphic any-entity alias in type position  |
| `Position`        | Opaque board location, use `distance(a, b)`    |
| `Duration`        | `end_of_turn`, `start_of_next_turn`, `rounds(n)`, `minutes(n)`, `indefinite` |
| `Invocation`      | Execution scope handle from `invocation()`     |
| `ActiveCondition` | Runtime condition instance: `.name`, `.duration`, `.id` |

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
    end_of_turn,
    start_of_next_turn,
    rounds(count: int),
    minutes(count: int),
    indefinite
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
            apply_condition(target, Blessed, Duration.rounds(10))
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
    modify initial_budget(actor: bearer) {
        result.movement = floor(bearer.speed / 2)
    }
}
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
- `bearer` + condition parameters in scope. `invocation()` not available.
- With `extends`, ancestor lifecycle blocks run first (DFS post-order).
- **Design principle:** use `extends` for conditions that imply others, not `apply_condition()` in on_apply.

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
Imports (`use`) are NOT transitive — each file must declare its own.

---

## Validation Workflow

Check a full file:

```bash
ttrpg check myfile.ttrpg
```

Check a snippet (auto-wrapped in `system "<check>" { ... }`):

```bash
echo 'derive foo() -> int { floor(10 / 3) }' | ttrpg check -s
```

Check multiple files together:

```bash
ttrpg check core.ttrpg combat.ttrpg spells.ttrpg
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
