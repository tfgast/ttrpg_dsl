# Writing .ttrpg-cli Test Scripts

Test scripts are an alternative to Rust integration tests for validating
`.ttrpg` rule modules. They use the same REPL commands available in
interactive mode, executed sequentially from a file.

**When to use scripts vs Rust tests:**

| Use scripts for | Keep in Rust for |
|-----------------|------------------|
| Derive/table value checks | AST structure inspection (enum counts, field counts) |
| Mechanic evaluation with dice | Custom EffectHandler logic |
| Action execution + entity state | Interpreter/checker API surface tests |
| Error case validation | Tests needing programmatic loops |

## Running tests

```bash
just test-scripts                        # Run all .ttrpg-cli scripts (quiet)
ttrpg run path/to/test.ttrpg-cli        # Run a single script (verbose)
ttrpg --quiet run path/to/test.ttrpg-cli # Run a single script (quiet)
```

The `--quiet` flag suppresses effect log output (`[RollDice]`,
`[MutateField]`, `[ActionStarted]`, etc.) while still showing errors
and assertion failures. `just test-scripts` uses `--quiet` by default.

Scripts exit 0 on success, 1 if any assertion fails. Failed assertions
print the file, line number, and values.

## File layout

Place test scripts alongside the rule modules they test:

```
osric/tests/osric_combat.ttrpg-cli
osric/tests/osric_saves.ttrpg-cli
ose/tests/ose_combat.ttrpg-cli
```

`just test-scripts` discovers `osric/tests/*.ttrpg-cli` and
`ose/tests/*.ttrpg-cli` automatically.

## Script structure

Every script starts by loading the source files, then runs assertions:

```
// Description of what this script tests
load osric/*.ttrpg

// ── Section heading ─────────────────────────
assert_eq some_derive(1), expected_value
```

Comments use `//`. Blank lines are ignored.

## Core commands

### Asserting values

```
// Assert an expression evaluates to true
assert 2 + 3 == 5

// Assert two expressions are equal
assert_eq fighter_group_bthb(5), 4

// Assert two expressions are not equal
assert_ne result, TurnOutcome.Impossible
assert_ne fighter.HP, 0

// Assert an expression is a specific enum variant (ignoring fields)
assert_match result, TurnResult.Turned
assert_match school, SpellSchool.Evocation

// Assert a command fails
assert_err call missile_range_penalty(Feet { value: 50 }, Feet { value: 0 })

// Assert list membership with `in`
assert "Shield" in equipment_package(Fighter)
assert MeleeWeapon.Club in class_allowed_melee(Cleric)

// Assert non-membership (wrap in parens for == false)
assert (MeleeWeapon.SwordLong in class_allowed_melee(Cleric)) == false
```

`assert_eq` evaluates both sides as DSL expressions. `assert_match`
checks only the variant name — useful when an enum variant carries
fields you don't care about (e.g., `TurnResult.Turned { number_affected }`).
Function calls (derives, mechanics) can be called directly as expressions:

```
assert_eq bthb(Fighter, 5), 4
assert_eq damage_roll(1d8), 5
```

### Controlling dice

Queue deterministic rolls before any expression or command that rolls dice:

```
// Queue a single roll
rolls 15
assert_eq attack_roll_aac(4, 15), AttackOutcome.Hit

// Queue multiple rolls (consumed left to right)
rolls 15 6
do MeleeAttack(attacker, target)

// Clear the queue (use between unrelated test sections)
rolls clear
```

Always `rolls clear` before a new section if a previous test might have
leftover unconsumed rolls.

### Spawning entities

```
spawn Character fighter {
    name: "Fighter",
    classes: [ClassLevel { class: Fighter, level: 5 }],
    abilities: { STR: 12, INT: 12, WIS: 12, DEX: 12, CON: 12, CHA: 12 },
    HitPoints { max_hp: 30, hp: 30 },
    EquipmentSlots { wielded_main: some(Melee(SwordLong)) }
}
```

The handle (`fighter`) is how you refer to this entity in later commands.
Spawn blocks support:
- Base fields: `name: "Fighter"`
- Struct literals: `ClassLevel { class: Fighter, level: 5 }`
- Included groups: `HitPoints { max_hp: 30, hp: 30 }`
- Optional groups: `EquipmentSlots { ... }` (omit to leave unset)
- Optional groups with fields: `ExceptionalStrength { percentile: 76 }`
- Option values: `some(Melee(SwordLong))`, `none`

Note: spawn lines can be long. This is fine -- each command is one line.

### Modifying entities

```
set fighter.hp = 20
set fighter.hp -= 5
set fighter.hp += 3
```

### Executing actions

```
do MeleeAttack(attacker, target)
do MissileAttack(archer, target, Feet { value: 60 })
```

The first argument is the actor handle, remaining arguments are action
parameters. After execution, assert on entity state:

```
rolls 15 6
do MeleeAttack(attacker, target)
assert_eq target.hp, 4
```

### Calling functions directly

Use `call` as a command (for `assert_err`) or call directly in expressions:

```
// In assert_eq, just call the function as an expression
assert_eq bthb(Fighter, 5), 4

// For assert_err, use the call command
assert_err call missile_range_penalty(Feet { value: 50 }, Feet { value: 0 })
```

### Inspecting state (debugging)

These print to stdout and are useful while writing tests:

```
inspect fighter           // Show all fields
inspect fighter.hp        // Show one field
state                     // Show all entities
entity Character          // Show entity type schema
actions                   // List all actions
mechanics                 // List all derives/mechanics
```

## Value syntax

### Integers and booleans
```
42, -3, true, false
```

### Strings
```
"hello world"
```

### Dice expressions
```
1d8, 2d6 + 1, 1d4 - 1
```

### Enum variants

Bare variant names work when unambiguous. When a variant name appears in
multiple enums, the REPL resolves it using the parameter's type hint:

```
assert_eq bthb(Fighter, 5), 4        // Fighter resolved via parameter type
assert_eq bthb(Class.Cleric, 7), 4   // qualified form also works
```

### Enum variants with fields

Both call-style and struct-body syntax work:

```
Melee(SwordLong)                              // positional arg
WieldedItem.Melee(SwordLong)                  // qualified, positional
WieldedItem.Melee { weapon: SwordLong }       // qualified, struct body (named fields)
some(WieldedItem.Melee { weapon: SwordLong }) // nested in option
```

### Struct literals

```
Feet { value: 70 }
ClassLevel { class: Fighter, level: 5 }
Armor { armour_type: PlateMail }
```

### Option values

```
some(Melee(SwordLong))    // option with a value
none                       // empty option
```

### Lists and maps

```
[ClassLevel { class: Fighter, level: 5 }]             // list
{ STR: 12, INT: 12, WIS: 12, DEX: 12, CON: 12, CHA: 12 }  // map
```

### Field access on results

Chain `.field` to access struct or enum variant fields from function results:

```
assert_eq resolve_melee_attack(atk, tgt, SwordLong).outcome, AttackOutcome.Hit
assert_eq encounter_sequence().surprise, SurpriseState.NoSurprise

// Enum variant fields work the same way
rolls 3 4
let result = resolve_turn_undead(cleric, 1, false)
assert_eq result.number_affected, 7
```

### Index access and length

Use `[n]` to index into lists (zero-based) and `.len()` for length:

```
assert_eq [10, 20, 30][0], 10
assert_eq [10, 20, 30][2], 30
assert_eq [10, 20, 30][-1], 30       // negative indexing from end
assert_eq [1, 2, 3].len(), 3
assert_eq equipment_package(Fighter).len(), 8
```

### Comparison operators

All standard comparison operators work in expressions:

```
assert 5 > 3
assert 3 < 5
assert 5 >= 5
assert 3 <= 5
assert 5 != 3

// Useful for monotonicity spot-checks without needing loops
assert thief_skill_base(ClimbWalls, 15) >= thief_skill_base(ClimbWalls, 1)
```

### Binding results with `let`

Use `let` to capture a result and assert on multiple fields without
re-evaluating (which would re-roll dice):

```
rolls 15 6
let result = resolve_melee_attack(atk, tgt, SwordLong)
assert_eq result.outcome, AttackOutcome.Hit
assert_eq result.damage, 6

// For enum results where you only care about the variant, not the fields:
rolls 8
let turn = resolve_turn_undead(cleric, 1, false)
assert_match turn, TurnResult.Turned
assert turn.number_affected > 0
```

`let` also works with action calls, using either function-call or
method-call syntax:

```
let result = Attack(fighter, goblin)
assert result == hit(9)

let hp = fighter.Heal()
assert hp == 15
```

Variables persist for the rest of the script and can be used in any
expression context (`eval`, `assert`, `assert_eq`, `assert_ne`, `assert_match`).

## Known limitations

### What still needs Rust tests

- **AST structure verification** -- checking that a system block contains
  specific enums, structs, or tables by name and field count. The REPL has
  `types`/`actions`/`mechanics` commands but they're display-only, not
  assertable.

- **Custom effect handlers** -- tests that intercept specific effects to
  verify event payloads (e.g., confirming a `Damaged` event was emitted
  with the right fields).

- **Interpreter API tests** -- anything testing the Rust API surface
  (`StateAdapter`, `StateProvider`, etc.) rather than the DSL rules.

## Tips

- Use `entity <Name>` to see the full schema before writing spawn blocks.
- Use `inspect <handle>` to debug unexpected assertion failures.
- Group related assertions under `// ── Section ───` comment headers.
- Use `rolls clear` between test sections to avoid stale roll queues.
- One script per rule module (e.g., `osric_combat.ttrpg-cli` for
  `osric_combat.ttrpg`).
- See `osric/tests/osric_combat.ttrpg-cli` as a reference implementation.
