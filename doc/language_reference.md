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
| `Duration`        | `end_of_turn`, `start_of_next_turn`, `rounds(n)`, `minutes(n)`, `indefinite` |
| `Invocation`      | Opaque execution scope handle                               |
| `ActiveCondition` | Runtime condition instance — fields: `name`, `duration`, `id` |
| `Condition`       | Reference to a condition type                               |

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
Same-unit arithmetic: `+`, `-`, `int * unit`, `unit / unit -> float`

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

---

## Block Categories

| Block     | Dice | Mutate | Receiver          | Returns | Cost |
|-----------|------|--------|-------------------|---------|------|
| derive    | -    | -      | -                 | value   | -    |
| mechanic  | yes  | -      | -                 | value   | -    |
| action    | yes  | yes    | `on` receiver     | unit    | yes  |
| reaction  | yes  | yes    | `on` + trigger    | unit    | yes  |
| hook      | yes  | yes    | `on` + trigger    | unit    | -    |
| condition | -    | -      | `on bearer`       | -       | -    |
| prompt    | -    | -      | -                 | value   | -    |

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
        apply_condition(target, Unconscious, Duration.indefinite)
    }
}
```

Always fires, no cost, not suppressible.

### Condition

```
condition Prone on bearer: Character {
    modify attack_roll(attacker: bearer) {
        mode = disadvantage                          // phase 1: pre-call
    }
    modify initial_budget(actor: bearer) {
        result.movement = floor(bearer.speed / 2)    // phase 2: post-call
    }
    suppress opportunity_attack(entity: bearer)
}
```

Modify targets: name, `[#tag]`, `[returns Type]`, `[has param: Type?]`
Cost modify: `modify Dash.cost(actor: bearer) { cost = bonus_action }`

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
| 4          | `in` `has`                          |
| 5          | `+` `-`                             |
| 6          | `*` `/`                             |
| 7          | `!` `-` (unary)                     |
| 8          | `.` `[]` `()`                       |

### Arithmetic Rules

- `int / int` always produces `float` — use `floor()` or `ceil()` to convert back
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
`floor(f)` `ceil(f)` `max(a, b)` `min(a, b)`

### Dice
`roll(expr)` `dice(count, sides)` `multiply_dice(expr, factor)`

### Collections
`len(xs)` `keys(m)` `values(m)` `first(xs)` `last(xs)` `append(xs, item)` `concat(a, b)` `reverse(xs)` `sum(xs)` `any(xs)` `all(xs)` `sort(xs)`

### Option
`some(x)` `.unwrap()` `.unwrap_or(default)` `.is_some()` `.is_none()`

### Set Methods
`.add(e)` `.remove(e)` `.union(s)` `.intersection(s)` `.difference(s)` `.to_list()` `.contains(e)` `+=` `-=`

### String Methods
`.len()` `.contains(s)` `.starts_with(s)` `.ends_with(s)`

### DiceExpr Methods
`.roll()` `.multiply(factor)`

### Entity & Conditions
`apply_condition(target, cond, duration)` `remove_condition(target, cond)` `conditions(entity)`

### Enum
`ordinal(v)` `from_ordinal(E, i)` `try_from_ordinal(E, i)`

### Invocation
`invocation()` `revoke(inv)` — revokes all conditions tagged with that invocation

### Other
`distance(a, b)` `error(msg)` `turn` (mutable TurnBudget in resolve blocks)

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
- Soft keywords (usable as identifiers): `system` `use` `group` `enum` `struct` `entity` `derive` `mechanic` `action` `reaction` `hook` `condition` `prompt` `option` `event` `move` `cost` `tag` `table` `unit` `suffix` `requires` `resolve` `modify` `suppress` `trigger` `roll` `on` `returns` `when` `enabled` `hint` `suggest` `description` `default` `result` `with` `has` `include` `as` `grant` `revoke` `emit` `free` `ordered` `extends`
- Dice literals take precedence over unit literals (`2d6` is dice, not unit)
