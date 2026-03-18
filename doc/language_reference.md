# TTRPG DSL — Language Reference (v0)

> Complete syntax, types, operators, and builtins. For patterns, common mistakes, and worked examples see [`ai_authoring.md`](ai_authoring.md).

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
| `any`             | Dynamically typed — enter via `to_any(x)`, narrow via `is`  |
| `fn(T1, T2) -> R` | Function reference type — see [Function References](#function-references) |
| `Position`        | Opaque game board location                                  |
| `Direction`       | Opaque spatial orientation (host-provided)                   |
| `Duration`        | `EndOfTurn`, `StartOfNextTurn`, `Rounds(n)`, `Minutes(n)`, `Indefinite` |
| `EffectSource`    | Condition provenance — user-defined enum, must have plain `Unknown` variant |
| `Invocation`      | Opaque action/reaction/hook execution ID — tags conditions for batch `revoke()` |
| `ActiveCondition` | Runtime condition instance — fields: `name`, `duration`, `source`, `id`, `applied_at`, `tags`; narrow with `is ActiveCondition<CondName>` for param access |
| `Condition`       | Condition identifier — store in variables, pass to functions |
| `Presence`        | Built-in enum: `OnMap`, `OffBoard` — entity board presence state |

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
Spread: `Weapon { damage: 2d6, ..old }` — copies unspecified fields from `old`

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

An optional `with [conditions]` clause can follow entity construction to apply conditions at creation time with `Duration.Indefinite`:

```
function create_cursed_rat() -> Monster {
    Monster { name: "Rat", hit_dice: 1, max_hp: 2 } with [Poisoned, Cursed]
}

// Conditions with parameters work too
function create_weak_zombie() -> Monster {
    Monster { name: "Zombie", hit_dice: 2, max_hp: 8 } with [Weakened(amount: 3)]
}
```

Each condition is applied in list order via `apply_condition(entity, cond, Duration.Indefinite)` after the entity is spawned and groups are materialized. Full lifecycle/veto behaviour is preserved. The clause is only valid on entity construction — not on struct/unit types or existing entity references.

- Include groups auto-materialize with defaults if not explicitly provided
- Spread (`..base`) not supported for entities
- Group initializers not valid on struct/unit types
- Construction in derive/mechanic/table/condition/prompt is a checker error
- `with [...]` clause only valid on entity types (checker error on structs/enums)

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

## Block Types

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

#### Function References

Functions (only `function` blocks — not derives, mechanics, actions, or tables) can be referenced as first-class values by using the function name as a bare identifier in expression position:

```
function add(a: int, b: int) -> int { a + b }

let op: fn(int, int) -> int = add     // fn ref
op(10, 20)                            // call through ref → 30
```

Type syntax: `fn(ParamType1, ParamType2) -> ReturnType`. Omit `-> ReturnType` for unit-returning functions: `fn(int)`.

Restrictions:
- Only `function` blocks can be referenced (not derives, mechanics, actions, tables, or builtins)
- Functions with `with` constraints on any parameter cannot be referenced (the constraint cannot be enforced through indirect calls)
- Signature matching is exact (structural equality, not coercion-compatible)
- Named arguments are not supported when calling through a function reference — positional only

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

Always fires, no cost, not suppressible. During `emit`, hooks execute before condition event handlers (see [Event Handlers](#event-handlers-on)).

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

#### Condition Tags

Conditions can carry declaration-level tags — static categorical properties of the condition type. Tags are declared inside the condition body with `tags:`:

```
tag curse
tag disease

condition BestowCurse on bearer: Character {
    tags: #curse
}
condition MummyRot on bearer: Character {
    tags: #curse, #disease
}
```

At runtime, tags are exposed as a `Set<string>` on the `tags` field of `ActiveCondition`:

```
let c = conditions(target)[0]
if "curse" in c.tags { ... }
```

**Three kinds of tags/metadata on conditions:**

| What | Purpose | Example |
|------|---------|---------|
| Condition tags | Static identity of the condition type | `tags: #curse` in condition body |
| Modify-clause tags | Individual effect categorization / suppression | `modify foo(...) #penalty { ... }` |
| EffectSource | Per-application source metadata | `EffectSource.Spell(name: "Hold Person", ...)` |

Use condition tags for properties that are always true (`#curse`, `#disease`, `#poison`). Use `EffectSource` for source-dependent properties like magicalness.

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

**Clause copying:** use `include modify/suppress/suppress-modify CondName` to copy declarative clauses from another condition at compile time.

#### Suspension (Entity Presence and Freeze)

The suspension system temporarily removes entities from play or freezes their turn/duration progression. Models imprisonment, soul trapping, temporal stasis, and similar effects.

Suspension records are source-keyed (typically by condition token). Resolution uses **worst-case-wins**: off-board if ANY record says `OffBoard`, turns frozen if ANY says so, etc.

**In lifecycle blocks** (`on_apply`/`on_remove`):
```
condition Imprisoned on bearer: entity stacking first {
    on_apply {
        suspend(bearer, Presence.OffBoard, freeze_turns: true, freeze_durations: true)
    }
}
```
`suspend(entity, ...)` is only available in lifecycle blocks. It keys the suspension to `condition_token()` automatically. When the condition is removed, the suspension record is auto-cleaned.

**Outside lifecycle blocks** (actions, functions):
```
suspend_with_source(target, source_id: 42, presence: Presence.OffBoard,
    freeze_turns: true, freeze_durations: true)
// Later:
remove_suspension_source(target, source_id: 42)
```

**Duration freeze:** when unfrozen, each condition's `applied_at` is bumped forward to preserve remaining duration.

**Enumeration:** off-board entities are excluded from hook scanning and modify evaluation but still exist for direct queries.

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

Suppressed instances remain in state (duration ticks). `best by` param must be `int`, declared on the condition. Not copied by `include`.

`all` is the implicit default — omit the `stacking` clause entirely:

```
condition Grappling(opponent: Character) on bearer: Character {
    // stacking all (implicit) — each instance tracks a different opponent
}
```

#### Event Handlers (`on`)

Event handlers co-locate event-reactive logic with the condition that grants it. They fire automatically during `emit` dispatch for stacking winners, with lifetime scoped to the condition's active duration.

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

**Syntax:** `on EventName(param: expr, ...)` — trigger bindings use the same fill-the-gaps semantics as hooks and reactions. The condition's receiver and parameters are in scope for binding expressions.

**Scope:** The handler body has access to:

| Name | Type | Description |
|------|------|-------------|
| bearer (receiver) | entity | The entity carrying the condition |
| `self` | ActiveCondition | The condition instance (`.name`, `.id`, `.duration`, `.source`, `.tags`, `.applied_at`) |
| `trigger` | event payload struct | The event payload (same as hooks) |
| `state` | mutable struct | Condition state fields (if declared) |
| condition params | per-param types | Bound from the active condition's parameter map |

**Capabilities:** Full function-body semantics — mutations, dice, emit, `apply_condition()`, `remove_condition()`, action calls. Unlike lifecycle blocks, event handlers are NOT restricted from condition manipulation.

**Dispatch order:** When `emit EventName(...)` fires:
1. All matching top-level hooks execute (existing behavior, unchanged)
2. All matching condition event handlers execute (against post-hook state)

Hooks fire first because they represent system-level invariants. Condition handlers execute second, seeing any mutations hooks made.

**Handler matching:**
1. Collect entity-typed values from the event payload (params first, then fields)
2. Deduplicate by entity ID (first occurrence wins)
3. For each unique entity, snapshot conditions and compute stacking winners
4. For each winning instance, check `on` clauses for trigger match
5. Matched handlers fire in entity order → application order → clause order

**Stacking:** Only stacking winners execute event handlers (`all` = every instance, `first` = oldest, `best by` = winner). Same computation as modifier collection.

**Snapshot safety:**
- Removed conditions are skipped (not revisited)
- Conditions applied to the same bearer during handler dispatch do not fire in this emit pass
- Already-started handlers complete even if their condition is removed

**State threading:** If multiple `on` handlers on the same instance match (e.g., two handlers for the same event with different bindings), state is threaded through them in clause order. After all handlers complete, mutated state is written back via `SetConditionState`.

**Emit depth:** Handlers participate in the existing emit depth limit. A handler that emits an event increments the depth counter.

**Multiple handlers:** A condition may declare multiple `on` handlers for different events or for the same event:

```
condition Guardian on bearer: Character stacking first {
    on Damaged(target: bearer) {
        // self-damage reaction
    }
    on MeleeHit(target: bearer) {
        // melee-specific reaction
    }
}
```

**Reserved names:** `trigger` is reserved in conditions that declare `on` handlers — it cannot be used as a receiver name or parameter name. The checker emits a diagnostic if shadowed. (`self` and `state` are already reserved in all conditions.)

**Not suppressible:** Condition event handlers are mandatory (like hooks). They cannot be suppressed via `suppress` clauses. To prevent a handler from firing, remove the condition.

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
`extends` names another option or a system. When an option extends a parent, its `when enabled` modifiers are active only when both the parent and the child are enabled. The parent must exist; circular extends chains are rejected by the checker.

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

No set literal syntax exists — create sets from lists: `[1, 2, 3].to_set()`.

Map and struct literals both use `{ key: value }` syntax. The parser disambiguates by context: `{ key: value }` with no type name prefix is a **map literal**; `TypeName { field: value }` with a type name prefix is a **struct literal**.

#### Dice Filter Syntax

Dice literals support optional filters that keep or drop dice from the pool before summing:

| Filter | Meaning | Example | Result |
|--------|---------|---------|--------|
| `kh`*N* | **K**eep **H**ighest *N* dice | `4d6kh3` | Roll 4d6, keep the 3 highest |
| `kl`*N* | **K**eep **L**owest *N* dice | `2d20kl1` | Roll 2d20, keep the lowest 1 (disadvantage) |
| `dh`*N* | **D**rop **H**ighest *N* dice | `4d6dh1` | Roll 4d6, drop the highest 1 (same as `4d6kl3`) |
| `dl`*N* | **D**rop **L**owest *N* dice | `4d6dl1` | Roll 4d6, drop the lowest 1 (same as `4d6kh3`) |

Full syntax: `<count>d<sides>[kh|kl|dh|dl]<filter_count>`

- Filter count must be less than dice count
- `kh` and `dl` are equivalent when the counts sum to the total (e.g., `4d6kh3` = `4d6dl1`)
- Dice literals take precedence over unit literals (`2d6` is dice, not a unit)

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
if let some(x) = opt { body }

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

#### If-Let (Option Unwrapping)

`if let some(x) = expr` unwraps an `option<T>` value, binding the inner value if present:

```
function find_strongest(enemies: list<Character>) -> option<Character> {
    if len(enemies) == 0 { return none }
    some(sort_by_hp(enemies)[-1])
}

// Usage:
if let some(target) = find_strongest(enemies) {
    attacker.Attack(target)
}
```

The pattern name is `some(x)` (lowercase), matching the `some()` constructor function.

### Indexing

Lists support both positive and negative integer indexing:

```
let xs = [10, 20, 30]
xs[0]     // 10 (first element)
xs[2]     // 30 (third element)
xs[-1]    // 30 (last element)
xs[-2]    // 20 (second-to-last)
```

Negative indices count from the end: `xs[-1]` is equivalent to `xs[len(xs) - 1]`. Out-of-bounds indices (positive or negative) produce a runtime error.

Maps use the same syntax with key expressions: `m["key"]`, `m[enum_variant]`.

### Has Expression

```
if entity has Spellcasting as sc {
    entity.sc.spell_slots -= 1
}
```

### Is Expression

Tests whether a value is a specific type. Enables flow-sensitive type narrowing within the then-block. Works with both `entity`-typed and `any`-typed values.

**Entity narrowing:**

```
if target is Character {
    target.level          // Character fields accessible here
} else if target is Monster {
    target.hit_dice       // Monster fields accessible here
}
```

**Any-type narrowing:**

```
let x: any = to_any(42)
if x is int {
    x + 1              // narrowed to int, arithmetic works
}

let val: any = to_any(Pos { x: 10, y: 20 })
if val is Pos {
    val.x + val.y      // narrowed to Pos, field access works
}

// Containers with concrete type parameters
let xs: any = to_any([1, 2, 3])
if xs is list<int> {
    sum(xs)            // narrowed to list<int>
}
```

**ActiveCondition narrowing:**

```
for c in conditions(target) {
    if c is ActiveCondition<Frightened> {
        c.source_entity    // Frightened param accessible after narrowing
    }
}
```

Before narrowing, only base fields (`.name`, `.duration`, `.source`, `.id`, `.applied_at`, `.tags`) are accessible. Accessing condition param fields on un-narrowed `ActiveCondition` is a checker error — narrow first with `is ActiveCondition<CondName>`.

Requirements:
- Left operand must be `any`, entity-typed (specific or polymorphic `entity`), or `ActiveCondition`
- For `entity`-typed: right operand must name a declared entity type
- For `any`-typed: right operand can be any concrete type (primitives, structs, enums, containers)
- For `ActiveCondition`: right operand must be `ActiveCondition<CondName>`
- `is any` and `is entity` are not valid targets

Composes with `has` narrowing via `&&`:

```
if target is Character && target has Spellcasting {
    target.Spellcasting.spell_dc
}
```

### Function References

A bare function name in expression position resolves to a `Value::FnRef` — a first-class reference to that function. The value can be stored in variables, passed as arguments, stored in struct fields, and called.

```
function double(x: int) -> int { x * 2 }

let f: fn(int) -> int = double    // reference
f(5)                               // call → 10

// Stored in structs
struct Ops { apply: fn(int, int) -> int }
function add(a: int, b: int) -> int { a + b }
let ops = Ops { apply: add }
ops.apply(3, 4)                    // call through struct field → 7
```

Resolution order for bare identifiers: local bindings → consts → function refs → condition names → enum type names.

Only `function` blocks (no `with` constraints on any parameter) are eligible. The `fn(T1, T2) -> R` type uses exact structural signature matching.

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
// lvalue = ident (.field | [index])*
// Index expressions in lvalues must be side-effect-free
// (no dice, no function calls — only arithmetic, variables, pure builtins)

grant entity.Group { field: val }  // activate optional group
revoke entity.Group                // deactivate optional group

emit EventName(param: value)       // fire event (named args only)

with_budget(entity, { field: val }) { body }  // scoped turn budget (see Function section)
with_budgets(specs) { body }                  // provision budgets for multiple entities
with_cost_payer(entity) { body }              // override which entity pays action costs
```

### Return

`return` and `return expr` exit the enclosing block early:

```
function find_first_positive(xs: list<int>) -> int {
    for x in xs {
        if x > 0 { return x }
    }
    -1
}
```

- Allowed in: `function`, `action` (resolve), `reaction`, `hook`, lifecycle blocks (`on_apply`, `on_remove`, `on_event`)
- Not allowed in: `derive`, `mechanic`, `table`, `condition` (modify/suppress), `prompt`
- `return` without a value returns unit — only valid when the block expects no return value
- Implicit return: the last expression in a block is its value (no `return` needed)
- `let` or assignment as the last statement makes the block return unit

---

## Builtin Functions

### Math
`floor(f)` `ceil(f)` `max(a, b)` `min(a, b)` — also accept a single `list<int>`: `max(xs)` `min(xs)`

### Dice
`roll(expr)` `dice(count, sides)` `multiply_dice(expr, factor)` `max_value(expr)` `dice_count(expr)` `dice_sides(expr)` `dice_modifier(expr)`

### Collections
`len(xs)` `keys(m)` `values(m)` `first(xs)` `last(xs)` `append(xs, item)` `concat(a, b)` `reverse(xs)` `sum(xs)` `any(xs)` `all(xs)` `sort(xs)` `take(xs, n)`

### List Methods
`.len()` `.first()` `.last()` `.append(e)` `.concat(other)` `.reverse()` `.sum()` `.any()` `.all()` `.sort()` `.take(n)` `.to_set()` `.contains(e)` `.remove_first(e)`

### Option
`some(x)` `.unwrap()` `.unwrap_or(default)` `.is_some()` `.is_none()`

### Any Type

`to_any(x)` — wraps any value into `any`. Use `is` guards to narrow back to a concrete type:

```
let val: any = to_any(42)
if val is int {
    val + 1           // narrowed to int, arithmetic works
}

// Useful for heterogeneous collections
let items: list<any> = [to_any(1), to_any("hello"), to_any(true)]
for item in items {
    if item is int { /* handle int */ }
    else if item is string { /* handle string */ }
}
```

### Set Methods
`.add(e)` `.remove(e)` `.union(s)` `.intersection(s)` `.difference(s)` `.to_list()` `.contains(e)` `+=` `-=`

### String Methods
`.len()` `.contains(s)` `.starts_with(s)` `.ends_with(s)`

### DiceExpr Methods
`.roll()` `.multiply(factor)`

### Entity & Conditions
`apply_condition(target, cond, duration [, source])` `remove_condition(target, cond)` `conditions(entity)` `has_condition(entity, cond)` `transfer_conditions(from, to, tag)`

`apply_condition(...)` returns `option<int>`: `some(id)` when the condition is applied, `none` if the host vetoes it. The optional 4th argument is an `EffectSource` value (defaults to `EffectSource.Unknown`). Access the stored source on active conditions via `.source`. **Syntactic sugar:** `EntityType { ... } with [Cond1, Cond2]` desugars to `apply_condition(entity, cond, Duration.Indefinite)` for each condition (see Entity Construction above).

`has_condition(entity, Prone)` returns `true` if the entity has an active condition with that name (bare condition identifier, not string). Shorthand for `any([c.name == "Prone" for c in conditions(entity)])`.

`transfer_conditions(from, to, "tag")` moves all active conditions on `from` that have `tag` in their tag set to `to`. Preserves condition identity (id, params, duration, source, tags). Does NOT fire lifecycle hooks or host gates — it's an atomic relocation. Allowed in lifecycle blocks (unlike apply/remove). Tag must be a declared tag name; the checker validates string literals. Same-entity calls are no-ops. Conditions with incompatible bearer types are skipped.

Condition names are first-class values of type `Condition`. They can be stored in variables and passed as function parameters:
```
let c = Prone                           // Condition value
let applied = apply_condition(target, c, Duration.Indefinite)

function apply_cond(t: entity, c: Condition, dur: Duration) {
    apply_condition(t, c, dur)
}
apply_cond(target, Sleeping, Duration.Rounds(10))
```
`Condition` (blueprint) vs `ActiveCondition` (live instance with `.name`, `.duration`, `.source`, `.id`, `.applied_at`, `.tags`). Use `is ActiveCondition<CondName>` to narrow and access condition params, or `conditions(entity, CondName)` for the typed overload.

### Enum

`ordinal(v)` — returns the 0-based index of an enum variant.

`from_ordinal(EnumType, i)` — constructs a variant by index. Only works with fieldless variants. Errors if out of range.

`try_from_ordinal(EnumType, i)` — like `from_ordinal` but returns `option<Variant>` instead of erroring:

```
enum Size ordered { small, medium, large }

ordinal(Size.medium)              // 1
from_ordinal(Size, 0)             // Size.small
try_from_ordinal(Size, 99)        // none
```

### Invocation
`invocation()` `revoke(inv)` — revokes all conditions tagged with that invocation

`invocation()` creates an opaque scope handle that tags all conditions applied within the same action execution. `revoke(inv)` removes all conditions tagged with that invocation — used for concentration-style "end all effects from this casting" patterns:

```
action CastBless on caster: Character (targets: list<Character>) #concentration {
    cost { action }
    resolve {
        let inv = invocation()
        for target in targets {
            apply_condition(target, Blessed, Duration.Rounds(10))
        }
        caster.concentrating_on = some(inv)
    }
}

// Later, to end concentration:
function break_concentration(caster: Character) {
    if let some(inv) = caster.concentrating_on {
        revoke(inv)                // removes all Blessed conditions from this casting
        caster.concentrating_on = none
    }
}
```

### Suspension
`suspend(target, presence, freeze_turns, freeze_durations)` — lifecycle-only, keys to current condition token
`suspend_with_source(target, source_id, presence, freeze_turns, freeze_durations)` — explicit source key
`remove_suspension_source(target, source_id)` — removes suspension records by source
`condition_token()` — lifecycle-only, returns pre-allocated condition instance ID

Typical use: pass the token as a source key for suspension so it auto-cleans when the condition is removed:

```
condition Imprisoned on bearer: entity stacking first {
    on_apply {
        let token = condition_token()
        suspend_with_source(bearer, source_id: token,
            presence: Presence.OffBoard, freeze_turns: true, freeze_durations: true)
    }
    on_remove {
        remove_suspension_source(bearer, source_id: condition_token())
    }
}
```
`is_suspended(target)` `is_off_board(target)` `are_turns_frozen(target)` `are_durations_frozen(target)` — queries

### Time
`game_time() -> int` — returns the current game time counter (integer, starts at 0). Pure read, callable anywhere.

`advance_time(amount: int)` — increments the game time counter by `amount` (must be positive). Only callable from `function` scope — not during action/reaction/hook execution. Emits an `AdvanceTime` effect.

```
function long_rest(party: list<entity>) {
    advance_time(480)   // 8 hours in minutes
    for member in party {
        member.HP = member.max_HP
    }
}

derive hours_elapsed() -> int {
    game_time() div 60
}
```

### Other
`distance(a, b)` `error(msg)` `turn` (mutable TurnBudget in resolve blocks and `with_budget` bodies) `budget_of(entity)` `despawn(entity)`

`error(msg)` aborts evaluation with a custom message. Use for unreachable branches or precondition violations:

```
derive safe_divide(a: int, b: int) -> int {
    if b == 0 { error("division by zero") }
    floor(a / b)
}
```

### Budget & Cost Management

`budget_of(entity)` — returns the entity's current `TurnBudget` struct. Only valid inside a `with_budget` or `with_budgets` scope. Errors if no budget is provisioned.

`with_budgets(specs)` — like `with_budget` but provisions budgets for multiple entities at once. Takes a `list<BudgetSpec>` expression. Each spec pairs an entity with a budget map. Budgets are restored on scope exit (error-safe).

`with_cost_payer(entity) { body }` — overrides which entity pays action costs within the body. By default, the `with_budget` entity pays. Use this when the cost-payer differs from the action performer (e.g., a wizard commanding a summoned creature):

```
function command_minion(wizard: Character, skeleton: Character, target: Character) {
    with_budget(skeleton, { action: 1 }) {
        with_cost_payer(wizard) {
            skeleton.MeleeAttack(target)    // skeleton acts, wizard pays
        }
    }
}
```

`despawn(entity)` — removes an entity from the game state, including all associated conditions and turn budgets. Only valid in mutating contexts (function, action, reaction, hook). Emits a `RemoveEntity` effect.

---

## Modules & Imports

```
system "Core Rules" {
    // declarations...
}

// System names can also be bare identifiers (no spaces):
system CoreRules {
    // declarations...
}

use "Core Rules"
use "Core Rules" as Core
use CoreRules as Core

Core.TypeName
Core.Enum.Variant
Core.function()
```

Multiple `system` blocks with the same name merge additively.
Imports are NOT transitive.

### Import

```
import "relative/path.ttrpg"
```

File-level source loading directive. Tells the resolver to load another file as a transitive dependency. The resolver follows `import` edges to build the complete file graph from an entrypoint.

- Path is relative to the importing file
- Circular imports are allowed (all files load simultaneously)
- `import` loads source; `use` controls symbol visibility between systems
- Transitive `import` dependencies are resolved automatically by `ttrpg check`

### Package Manifest (`ttrpg.toml`)

A `ttrpg.toml` file at a package root declares package identity, named entries, and curated bundles:

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

[bundles.chargen]
entries = ["core", "class", "chargen", "equipment"]
```

| Concept          | Meaning                                            |
|------------------|----------------------------------------------------|
| **entry**        | A single root source file                          |
| **bundle**       | A curated composition of multiple entries           |
| **target**       | Either an entry or a bundle (the unit of loading)  |
| `default_target` | What bare `load <pkg>` resolves to                 |

CLI loading:
```
load ose          # load default target (full bundle)
load ose:core     # load single entry
load ose:chargen  # load named bundle
```

---

## Lexer Rules

- Comments: `// line comment` (no block comments)
- NL suppressed: inside `()` `[]`; after `+ - * / || && == != >= <= in => -> = += -=`; after `{ , : | #`
- Reserved keywords: `let` `if` `else` `match` `true` `false` `none` `in` `for`
- Soft keywords (usable as identifiers): `system` `use` `group` `enum` `struct` `entity` `derive` `mechanic` `function` `action` `reaction` `hook` `condition` `prompt` `option` `event` `move` `cost` `tag` `table` `unit` `suffix` `fn` `requires` `resolve` `modify` `suppress` `trigger` `roll` `on` `returns` `when` `enabled` `hint` `suggest` `description` `default` `result` `with` `has` `is` `include` `as` `grant` `revoke` `emit` `free` `ordered` `extends` `restricted` `on_apply` `on_remove` `stacking` `best` `by` `highest` `lowest` `ties` `oldest`
- Dice literals take precedence over unit literals (`2d6` is dice, not unit)
