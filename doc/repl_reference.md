# TTRPG DSL — REPL Quick Reference

## Invocation

```
ttrpg                           # interactive REPL
ttrpg --vi                      # REPL with vi keybindings
ttrpg run <script.ttrpg-cli>    # execute script file
ttrpg -c "<commands>"           # execute inline commands
ttrpg check <files...>          # type-check files (no execution)
ttrpg check -s "<snippet>"      # check snippet (auto-wrapped in system block)
ttrpg query <topic> <files...>  # introspect type declarations (no execution)
ttrpg query <topic> -s -c <src> # query inline snippet
cat commands.txt | ttrpg        # pipe mode (no line editing)
```

---

## Commands

### Loading Programs

| Command            | Description                                    |
|--------------------|------------------------------------------------|
| `load <path...>`   | Load source files (glob patterns OK)           |
| `reload`           | Reload last loaded files                       |
| `errors`           | Show diagnostics from last load                |

```
load spec/v0/04_full_example.ttrpg
load *.ttrpg
reload
errors
```

### Expression Evaluation

| Command           | Description                                    |
|-------------------|------------------------------------------------|
| `eval <expr>`     | Evaluate a DSL expression                      |

```
eval 2 + 3
eval floor((16 - 10) / 2)
eval [1, 2, 3]
eval fighter.HP
```

Spawned entity handles are bound as variables in expressions.

### Entity Management

| Command                                        | Description                        |
|------------------------------------------------|------------------------------------|
| `spawn <Type> <handle> [{ field: val, ... }]`  | Create entity instance             |
| `set <handle>.<field> [= \| += \| -=] <val>`  | Modify entity field                |
| `destroy <handle>`                              | Remove entity                      |
| `inspect <handle>[.field]`                      | View entity/field state            |

```
spawn Character fighter { name: "Ava", HP: 30, AC: 18 }
spawn Character caster { name: "Zed", Spellcasting { spell_dc: 15, spell_slots: 3 } }
set fighter.HP -= 10
set fighter.AC = 20
inspect fighter
inspect fighter.HP
destroy goblin
```

Resource fields auto-clamp to bounds on `set`.

### Actions & Functions

| Command                       | Description                              |
|-------------------------------|------------------------------------------|
| `do <expr>`                   | Evaluate expression for side effects     |
| `call <func>(args)`           | Call a derive or mechanic                |
| `let <name> = <expr>`         | Bind result to a variable                |

`do` evaluates any expression and prints the result. It supports both
function-call and method-call syntax for actions:

```
do Attack(fighter, goblin)
do fighter.Attack(goblin)
do CastBless(caster, [fighter, rogue])
call modifier(16)
call attack_roll(5)
```

`let` captures the result for use in later assertions:

```
let result = Attack(fighter, goblin)
assert result == hit(9)
let hp = fighter.Heal()
```

### Optional Groups

| Command                                    | Description                      |
|--------------------------------------------|----------------------------------|
| `grant <handle>.<Group> [{ fields }]`      | Grant optional group             |
| `revoke <handle>.<Group>`                   | Revoke optional group            |

```
grant hero.Spellcasting { spell_slots: 5, spell_dc: 14 }
revoke hero.Spellcasting
```

Cannot grant/revoke required (`include`) groups.

### Introspection

| Command              | Description                                                |
|----------------------|------------------------------------------------------------|
| `state`              | Show all entities and their current values                  |
| `types`              | List all defined types (entities, structs, enums, units)    |
| `entity <name>`      | Show detailed entity type declaration (fields, groups)      |
| `actions`            | List all actions with signatures                            |
| `mechanics`          | List all derives and mechanics (alias: `derives`)           |
| `conditions`         | List all active conditions across entities                  |
| `condition_decls`    | List all condition declarations                             |
| `events`             | List all event declarations                                 |
| `reactions`          | List all reaction declarations                              |
| `hooks`              | List all hook declarations                                  |

```
types
entity Character
actions
mechanics
conditions
condition_decls
events
reactions
hooks
```

### Options

| Command              | Description                          |
|----------------------|--------------------------------------|
| `enable <name>`      | Enable a declared option             |
| `disable <name>`     | Disable a declared option            |
| `options`            | List all options with current state  |

```
enable flanking
disable flanking
options
```

Options with `default: on` are auto-enabled on load.

### Testing & Assertions

| Command                                      | Description                                   |
|----------------------------------------------|-----------------------------------------------|
| `assert <expr>`                              | Verify expression is true                     |
| `assert_eq <a>, <b>`                         | Verify two expressions are equal              |
| `assert_ne <a>, <b>`                         | Verify two expressions are not equal          |
| `assert_match <expr>, <Enum>.<Variant>`      | Verify expression matches enum variant        |
| `assert_err <command>`                        | Verify a command produces an error            |
| `assert_condition <handle>, <Condition>`      | Verify entity has a condition                 |
| `assert_no_condition <handle>, <Condition>`   | Verify entity does not have a condition       |

```
assert fighter.HP > 0
assert_eq call modifier(16), 3
assert_ne fighter.HP, 0
assert_match result, TurnOutcome.Turned
assert_err destroy nonexistent
assert_condition fighter, Prone
assert_no_condition fighter, Stunned
```

### Dice Control

| Command              | Description                                   |
|----------------------|-----------------------------------------------|
| `seed <value>`       | Set RNG seed for deterministic rolls          |
| `rolls <v1 v2 ...>`  | Queue predetermined roll results              |
| `rolls clear`        | Clear the roll queue                          |

```
seed 42
rolls 18 5 12
rolls clear
```

Queued rolls are consumed in order; RNG resumes after queue empties.

---

## Query Subcommand (CLI)

The `query` subcommand inspects type declarations and signatures from source files without executing code.

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

```
ttrpg query types myfile.ttrpg
ttrpg query actions core.ttrpg combat.ttrpg
ttrpg query entity Character combat.ttrpg
ttrpg query all *.ttrpg
```

### Flags

| Flag               | Description                                          |
|--------------------|------------------------------------------------------|
| `--system <name>`  | Filter output to declarations from a specific system |
| `--xref`           | Include cross-references (`entity` topic only)       |
| `-s, --snippet`    | Auto-wrap source in system block                     |
| `-c <source>`      | Inline source instead of file paths                  |

Cross-references (`--xref`) appends applicable conditions, actions, reactions, and hooks for the queried entity:

```
ttrpg query entity Character combat.ttrpg --xref
```

---

## REPL Features

- **Tab completion**: commands, handles, types, actions, fields, builtins, methods
- **History**: persistent in `~/.local/share/ttrpg/history.txt`; Up/Down arrows, Ctrl+R search
- **Comments**: lines starting with `//` are ignored; trailing `//` comments stripped
- **Exit**: Ctrl+D; Ctrl+C clears current line
