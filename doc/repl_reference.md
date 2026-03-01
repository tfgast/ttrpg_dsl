# TTRPG DSL — REPL Quick Reference

## Invocation

```
ttrpg                           # interactive REPL
ttrpg --vi                      # REPL with vi keybindings
ttrpg run <script.ttrpg-cli>    # execute script file
ttrpg -c "<commands>"           # execute inline commands
ttrpg check <files...>          # type-check files (no execution)
ttrpg check -s "<snippet>"      # check snippet (auto-wrapped in system block)
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
| `do <Action>(<actor>, args)`  | Execute an action                        |
| `call <func>(args)`           | Call a derive or mechanic                |

```
do Attack(fighter, goblin)
do CastBless(caster, [fighter, rogue])
call modifier(16)
call attack_roll(5)
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

| Command       | Description                                         |
|---------------|-----------------------------------------------------|
| `state`       | Show all entities and their current values           |
| `types`       | List all defined types (entities, structs, enums)    |
| `actions`     | List all actions with signatures                     |
| `mechanics`   | List all derives and mechanics with signatures       |
| `conditions`  | List all active conditions across entities           |

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

| Command                     | Description                                   |
|-----------------------------|-----------------------------------------------|
| `assert <expr>`             | Verify expression is true                     |
| `assert_eq <a>, <b>`        | Verify two expressions are equal              |
| `assert_err <command>`       | Verify a command produces an error            |

```
assert fighter.HP > 0
assert_eq call modifier(16), 3
assert_err destroy nonexistent
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

## REPL Features

- **Tab completion**: commands, handles, types, actions, fields, builtins, methods
- **History**: persistent in `~/.local/share/ttrpg/history.txt`; Up/Down arrows, Ctrl+R search
- **Comments**: lines starting with `//` are ignored; trailing `//` comments stripped
- **Exit**: Ctrl+D; Ctrl+C clears current line
