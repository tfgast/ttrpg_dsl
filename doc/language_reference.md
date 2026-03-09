# TTRPG DSL — Quick Reference (v0)

## Types

### Primitives

| Type     | Description                                    |
|----------|------------------------------------------------|
| `int`    | Signed integer                                 |
| `bool`   | `true` or `false`                              |
| `string` | Double-quoted text                             |
| `float`  | No literals — produced only by `/` operator    |

### Composites

| Type             | Description                              |
|------------------|------------------------------------------|
| `list<T>`        | Ordered sequence                         |
| `set<T>`         | Unordered unique elements                |
| `map<K, V>`      | Key-value mapping                        |
| `option<T>`      | `T` or `none`                            |
| `resource(m..=n)`| Bounded int, assignments clamp to bounds |

### Dice Types

| Type         | Description                                  |
|--------------|----------------------------------------------|
| `DiceExpr`   | Unevaluated dice pool                        |
| `RollResult` | Result of `roll()` — fields: `expr`, `dice`, `kept`, `modifier`, `total`, `unmodified` |

### Special Types

| Type              | Description                                                 |
|-------------------|-------------------------------------------------------------|
| `entity`          | Polymorphic any-entity alias in type position               |
| `Position`        | Opaque game board location                                  |
| `Duration`        | `EndOfTurn`, `StartOfNextTurn`, `Rounds(n)`, `Minutes(n)`, `Indefinite` |
| `Invocation`      | Opaque execution scope handle                               |
| `ActiveCondition` | Runtime condition instance — fields: `name`, `duration`, `id` |
| `Condition`       | Condition identifier — store in variables, pass to functions |

---

## Declarations

### Enum

```
enum Ability { STR, DEX, CON, WIS, INT, CHA }
enum HitResult { hit(amount: int), miss }
enum Size ordered { small, medium, large }        // enables < > comparisons
```

### Struct

```
struct Weapon {
    name: string
    damage: DiceExpr
    range: Feet = 5ft
}
```

Construction: `Weapon { name: "Sword", damage: 1d8 }`
Spread: `Weapon { ...old, damage: 2d6 }`

### Entity

```
entity Character {
    name: string
    HP: resource(0..=max_HP)
    max_HP: int = 10
    optional Spellcasting
    include CombatStats                      // always present
}
```

#### Entity Construction

Entities can be constructed inline using struct literal syntax, but only in mutating contexts (function, action, reaction, hook, `with_budget`).

```
// Basic construction
function create_ogre() -> Monster {
    Monster { name: "Ogre", hit_dice: 4, max_hp: 26 }
}

// With inline group initializer (activates optional group)
function create_wizard() -> Monster {
    Monster {
        name: "Wizard", hit_dice: 1, max_hp: 4,
        Spellcasting { spell_slots: 3, spell_dc: 12 },
    }
}
```

- Include groups auto-materialize with defaults if not explicitly provided
- Spread (`..base`) not supported for entities
- Group initializers not valid on struct/unit types
- Construction in derive/mechanic/table/condition/prompt is a checker error

### Restricted Fields

Fields marked `restricted` can only be mutated within the declaring system or the system that declares the entity containing the field. Other systems can read but not assign (`=`, `+=`, `-=`).

```
entity Character {
    restricted HP: resource(0..=max_HP)    // only declaring system can modify
    max_HP: int
    name: string                           // any system can modify
}

group Spellcasting {
    restricted spell_slots: int = 0
    spell_dc: int
}
```

Applies to entity, struct, and group fields. `grant` is exempt (initializes, doesn't mutate). Skipped in single-file/REPL mode.

### Group

```
group Spellcasting {
    spell_dc: int
    spell_slots: int = 0
}
```

Attach to entities: `optional GroupName` or `optional GroupName { inline fields }`
Access: `entity.GroupName.field`

### Unit Type

```
unit Feet suffix ft { value: int }
```

Literal: `30ft`; struct form: `Feet { value: 30 }`
Same-unit arithmetic: `+`, `-`, `int * unit`, `unit / unit -> float`, `unit div int -> unit`, `unit div unit -> int`

### Event

```
event Damaged(target: Character, attacker: Character) {
    amount: int
    damage_type: DamageType
}
```

Parameters = matching context; body fields = payload.

### Tag

```
tag #concentration
```

Applied on declarations: `action CastBless ... #concentration { ... }`

### Const

Named compile-time constant. Pure expression (same restrictions as derive — no dice, no mutation).

```
const MAX_LEVEL = 20
const BASE_THAC0: int = 20
const STATS = [10, 12, 14]
```

- Optional type annotation: `const NAME: Type = expr`
- Value can be any pure expression: literals, arithmetic, struct literals, enum variants, list/map literals, references to other consts
- Assignment to a const is a compile error
- Consts share the function namespace (no const and derive with the same name)

### Table

Static lookup declaration with pattern-matching keys.

```
// Single-key with range patterns and wildcard
table ability_mod(score: int) -> int {
    1..=3   => -3,
    4..=5   => -2,
    6..=8   => -1,
    9..=12  =>  0,
    13..=15 =>  1,
    16..=17 =>  2,
    _       =>  3
}

// Multi-key (bracket syntax)
table save_dc(class: Class, level: int) -> int {
    [Fighter, 1..=3] => 14,
    [Fighter, 4..=6] => 12,
    [Thief,   1..=4]  => 15,
    [Thief,   _]      => 13
}
```

Syntax: `table name(params) -> ReturnType { entries }`

Key types:
- **Expression**: enum variant, int/string literal, any expression — `Fighter`, `0`, `"Sword"`
- **Range**: inclusive only — `1..=3` (int params only)
- **Wildcard**: `_` — matches anything, must be last entry

Entry syntax:
- Single-key: `key => value`
- Multi-key: `[key1, key2, ...] => value`

Semantics:
- Pure scope (same as derive) — no dice, no mutation, no receiver
- First-match: entries evaluated in order, first full match wins
- All keys in an entry must match (conjunction)
- Value expressions evaluated lazily (only on match)
- Called like a function: `ability_mod(14)`, `save_dc(Fighter, 5)`

Errors:
- Runtime: no matching entry → runtime error (unless wildcard covers all cases)
- Checker: range on non-int param, key/value type mismatch, entries after wildcard (warning)

---

## Block Categories

| Block     | Dice | Mutate | Receiver          | Returns | Cost |
|-----------|------|--------|-------------------|---------|------|
| derive    | -    | -      | -                 | value   | -    |
| table     | -    | -      | -                 | value   | -    |
| mechanic  | yes  | -      | -                 | value   | -    |
| function  | yes  | yes    | -                 | optional| -    |
| action    | yes  | yes    | `on` receiver     | optional| yes  |
| reaction  | yes  | yes    | `on` + trigger    | unit    | yes  |
| hook      | yes  | yes    | `on` + trigger    | unit    | -    |
| condition | -    | -      | `on bearer`       | -       | -    |
| prompt    | -    | -      | -                 | value   | -    |
| move      | yes  | yes    | `on` receiver     | unit    | yes  |

### Derive

```
derive modifier(score: int) -> int {
    floor((score - 10) / 2)
}
```

### Mechanic

```
mechanic attack_roll(bonus: int) -> RollResult #attack {
    roll(1d20 + bonus)
}
```

### Function

```
function resolve_attacks(attacker: Character, target: Character, count: int) {
    with_budget(attacker, { actions: count }) {
        for i in 0..count {
            attacker.Attack(target)
        }
    }
}

function compute_heal(base: int, bonus: int) -> int {
    base * 2 + bonus
}
```

Syntax: `function Name(params) -> ReturnType { body }` (return type optional, defaults to unit)

Capabilities: dice, mutation, emit, grant/revoke, call actions/functions/derives/mechanics.
Restrictions: no receiver (`on`), no cost/requires, no `invocation()`, not targeted by condition `modify`.

`with_budget(entity, { field: value }) { body }` — provisions a scoped turn budget:
- `turn` keyword readable/writable inside the body
- Actions called deduct from the provisioned budget
- Entity arg pays costs; action receiver can differ
- Nesting supported; cleanup always runs (error-safe)

### Move (PbtA Sugar)

```
move GoAggro on actor: Character (target: Character) {
    trigger: "threaten with force"
    roll: 2d6 + actor.stats["Hard"]
    on strong_hit { }
    on weak_hit { }
    on miss { }
}
```

Desugars to mechanic + action. Hardcoded PbtA thresholds: 10+ strong\_hit, 7–9 weak\_hit, 6- miss.
Must have exactly three outcomes. Action cost is always `{ action }`.

### Action

```
action Attack on attacker: Character (target: Character, weapon: Weapon) #attack {
    cost { action }
    requires { distance(attacker.position, target.position) <= weapon.range }
    resolve {
        let result = attack_roll(attacker.abilities[STR])
        if result >= target.AC {
            target.HP -= roll(weapon.damage).total
        }
    }
}
```

Actions may declare a return type with `-> Type`. The resolve block must produce that type. On veto or requires/cost failure, `none` is returned, so the declared type should typically be `option<T>`:

```
action ResistSpell on target: Character (category: option<SaveCategory>) -> option<bool> {
    resolve {
        if category.is_some() {
            let cat = category.unwrap()
            some(roll_saving_throw(character_best_saves(target), cat, 0))
        } else {
            some(false)  // no save — spell lands
        }
    }
}
```

All overloads of the same action must agree on return type. When no return type is declared, the action returns unit and the resolve block value is discarded.

Cost tokens: `action`, `bonus_action`, `reaction`, `movement`, `free_interactions`, `free` (plus plural forms and custom TurnBudget fields).

### Reaction

```
reaction Parry on defender: Character (trigger: Attacked(target: defender)) {
    cost { reaction }
    resolve {
        trigger.damage -= defender.proficiency
    }
}
```

### Hook

```
hook DeathDrop on target: Character (trigger: Damaged(target: target)) {
    if target.HP <= 0 {
        apply_condition(target, Unconscious, Duration.Indefinite)
    }
}
```

Always fires, no cost, not suppressible.

### Condition

```
condition Prone on bearer: Character {
    modify attack_roll(attacker: bearer) #position #penalty {
        mode = disadvantage                          // phase 1: pre-call
    }
    modify initial_budget(actor: bearer) #position {
        result.movement = floor(bearer.speed / 2)    // phase 2: post-call
    }
    suppress opportunity_attack(entity: bearer)
}

condition FreedomOfMovement on bearer: Character {
    suppress [#position](attacker: bearer)           // suppress all #position modifiers
}
```

Modify targets: name, `[#tag]`, `[returns Type]`, `[has param: Type?]`
Cost modify: `modify Dash.cost(actor: bearer) { cost = bonus_action }`
Modify tags: `modify attack_roll(attacker: bearer) #position #penalty { ... }`
Suppress-modify: `suppress [#position](attacker: bearer)` — suppress all modify clauses matching the selector

#### Lifecycle Hooks (on_apply / on_remove)

Conditions can include imperative blocks that execute when applied or removed.

```
condition Burning(damage: int) on bearer: Character {
    on_apply {
        emit StatusGained(target: bearer, status: "Burning")
        bearer.took_fire_damage = true
    }
    on_remove {
        emit StatusLost(target: bearer, status: "Burning")
    }
    modify fire_resistance(target: bearer) { ... }
}
```

At most one `on_apply` and one `on_remove` per condition.

**Capabilities:** mutation, dice, emit, call derives/mechanics/functions (hook-like semantics).

**Restrictions (checker-enforced):** `apply_condition()`, `remove_condition()`, `revoke(invocation)`, `invocation()` are forbidden. `revoke entity.Group` is allowed.

**Trigger points:**
- `on_apply`: fires before activation (modify/suppress not yet in effect). Error prevents application.
- `on_remove`: fires before removal (modify/suppress still in effect). Error does NOT prevent removal.

**Scoping:** `bearer` + condition parameters in scope. `invocation()` unavailable.

**Inheritance:** with `extends`, ancestor lifecycle blocks run first (DFS post-order).

#### Stacking Policies

Controls which instances contribute effects when multiple instances of the same condition exist on one bearer.

```
condition Prone on bearer: Character
    stacking first
{ ... }

condition Concealed(level: int) on bearer: Character
    stacking best by highest(level) ties oldest
{ ... }
```

| Policy | Meaning |
|--------|---------|
| `all` (default) | Every instance contributes |
| `first` | Oldest instance wins |
| `best by highest(param) ties oldest` | Highest param value wins |
| `best by lowest(param) ties oldest` | Lowest param value wins |

Suppressed instances remain in state (duration ticks). `best by` param must be `int`, declared on the condition. Not inherited via `extends`.

### Prompt

```
prompt choose_target(chooser: Character, options: list<Character>) -> Character {
    hint: "Choose a target for your attack"
}
```

### Option

```
option flanking extends "Core Rules" {
    description: "Flanking grants advantage on melee attacks"
    default: off
    when enabled {
        modify attack_roll(attacker: _) { mode = advantage }
    }
}
```

---

## Parameters & Constraints

```
param: Type
param: Type = default_value
actor: Character with Spellcasting as sc           // conjunctive — all required
target: Creature with Flying | Swimming            // disjunctive — at least one
```

- Conjunctive (`with A, B`): call-site must prove all, body accesses directly
- Disjunctive (`with A | B`): no narrowing, use `has` guards in body
- Mixing `,` and `|` is a parse error

---

## Expressions

### Literals

```
42                    // int
true  false           // bool
"hello"               // string
none                  // option<T>
1d20  4d6kh3  2d20kl1  4d6dh1    // dice
30ft                  // unit literal
[1, 2, 3]            // list
{"a": 1, "b": 2}    // map
```

### Operators (precedence low to high)

| Precedence | Operators                           |
|------------|-------------------------------------|
| 1          | `\|\|`                              |
| 2          | `&&`                                |
| 3          | `==` `!=` `>=` `<=` `>` `<`        |
| 4          | `in` `has` `is`                     |
| 5          | `+` `-`                             |
| 6          | `*` `/` `div` `%`                   |
| 7          | `!` `-` (unary)                     |
| 8          | `.` `[]` `()`                       |

### Arithmetic Rules

- `int / int` always produces `float` — use `floor()` or `ceil()` to convert back
- `int div int` produces `int` (floor division) — e.g., `7 div 2` = `3`
- `unit div int` produces same unit; `unit div unit` produces `int`
- `DiceExpr + DiceExpr` combines pools; `DiceExpr + int` adds modifier
- `RollResult` auto-coerces to `.total` in comparisons

### Control Flow

```
// If
if condition { body }
if condition { body } else { body }
if let Some(x) = opt { body }

// Match (pattern)
match result {
    hit(amount) => target.HP -= amount,
    miss => {},
}

// Match (guard)
match {
    total >= 20 => "critical",
    total >= dc => "success",
    _ => "failure",
}

// For
for target in targets { target.HP -= damage }
for i in 0..5 { ... }          // exclusive: 0,1,2,3,4
for i in 0..=5 { ... }         // inclusive: 0,1,2,3,4,5

// List comprehension
[x * 2 for x in numbers if x > 5]
```

### Has Expression

```
if entity has Spellcasting as sc {
    entity.sc.spell_slots -= 1
}
```

### Is Expression

Tests whether an entity is a specific entity type. Enables flow-sensitive type narrowing within the then-block.

```
if target is Character {
    target.level          // Character fields accessible here
} else if target is Monster {
    target.hit_dice       // Monster fields accessible here
}
```

Requirements:
- Left operand must be an entity type (specific or polymorphic `entity`)
- Right operand must name a declared entity type

Composes with `has` narrowing via `&&`:

```
if target is Character && target has Spellcasting {
    target.Spellcasting.spell_dc
}
```

### Block Values

Blocks are expressions — last expression statement is the value.
`let` and assignment as last statement make the block return `unit`.

---

## Statements

```
let name: Type = expr              // variable binding
let name = expr                    // type inferred

lvalue = expr                      // assignment
lvalue += expr                     // compound assignment
lvalue -= expr

grant entity.Group { field: val }  // activate optional group
revoke entity.Group                // deactivate optional group

emit EventName(param: value)       // fire event (named args only)
```

---

## Builtin Functions

### Math
`floor(f)` `ceil(f)` `max(a, b)` `min(a, b)` — also accept a single `list<int>`: `max(xs)` `min(xs)`

### Dice
`roll(expr)` `dice(count, sides)` `multiply_dice(expr, factor)` `max_value(expr)` `dice_count(expr)` `dice_sides(expr)` `dice_modifier(expr)`

### Collections
`len(xs)` `keys(m)` `values(m)` `first(xs)` `last(xs)` `append(xs, item)` `concat(a, b)` `reverse(xs)` `sum(xs)` `any(xs)` `all(xs)` `sort(xs)`

### List Methods
`.to_set()` `.contains(e)` `.remove_first(e)`

### Option
`some(x)` `.unwrap()` `.unwrap_or(default)` `.is_some()` `.is_none()`

### Set Methods
`.add(e)` `.remove(e)` `.union(s)` `.intersection(s)` `.difference(s)` `.to_list()` `.contains(e)` `+=` `-=`

### String Methods
`.len()` `.contains(s)` `.starts_with(s)` `.ends_with(s)`

### DiceExpr Methods
`.roll()` `.multiply(factor)`

### Entity & Conditions
`apply_condition(target, cond, duration)` `remove_condition(target, cond)` `conditions(entity)` `has_condition(entity, name)`

`has_condition(entity, "Prone")` returns `true` if the entity has an active condition with that name. Shorthand for `any([c.name == "Prone" for c in conditions(entity)])`.

Condition names are first-class values of type `Condition`. They can be stored in variables and passed as function parameters:
```
let c = Prone                           // Condition value
apply_condition(target, c, Duration.Indefinite)

function apply_cond(t: entity, c: Condition, dur: Duration) {
    apply_condition(t, c, dur)
}
apply_cond(target, Sleeping, Duration.Rounds(10))
```
`Condition` (blueprint) vs `ActiveCondition` (live instance with `.name`, `.duration`, `.id`).

### Enum
`ordinal(v)` `from_ordinal(E, i)` `try_from_ordinal(E, i)`

### Invocation
`invocation()` `revoke(inv)` — revokes all conditions tagged with that invocation

### Time
`game_time()` `advance_time(amount)` — advance\_time only callable from function scope (not during action/reaction/hook execution)

### Other
`distance(a, b)` `error(msg)` `turn` (mutable TurnBudget in resolve blocks and `with_budget` bodies)

---

## Modules & Imports

```
system "Core Rules" {
    // declarations...
}

use "Core Rules"
use "Core Rules" as Core

Core.TypeName
Core.Enum.Variant
Core.function()
```

Multiple `system` blocks with the same name merge additively.
Imports are NOT transitive.

---

## Lexer Rules

- Comments: `// line comment` (no block comments)
- NL suppressed: inside `()` `[]`; after `+ - * / || && == != >= <= in => -> = += -=`; after `{ , : | #`
- Reserved keywords: `let` `if` `else` `match` `true` `false` `none` `in` `for`
- Soft keywords (usable as identifiers): `system` `use` `group` `enum` `struct` `entity` `derive` `mechanic` `function` `action` `reaction` `hook` `condition` `prompt` `option` `event` `move` `cost` `tag` `table` `unit` `suffix` `requires` `resolve` `modify` `suppress` `trigger` `roll` `on` `returns` `when` `enabled` `hint` `suggest` `description` `default` `result` `with` `has` `is` `include` `as` `grant` `revoke` `emit` `free` `ordered` `extends` `restricted` `on_apply` `on_remove` `stacking` `best` `by` `highest` `lowest` `ties` `oldest`
- Dice literals take precedence over unit literals (`2d6` is dice, not unit)
