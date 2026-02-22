# TTRPG DSL CLI — Design Document

## Purpose

A minimal CLI tool for **language exploration during v0/v1 design**. Primary use cases:

1. Load a `.ttrpg` file, set up game state, and interactively call actions/mechanics/derives to see what happens.
2. Run scripted command sequences for automated testing and regression checking.
3. Quickly answer "what does this mechanic actually do?" while iterating on the language spec.

This is an internal developer tool, not an end-user product. We optimize for scriptability and fast iteration over polish. Breaking changes are expected and welcome.

---

## Design Goals

1. **Scriptable.** Every operation available in the REPL is also available via stdin/file input. Automated tests can feed commands in and assert on output.

2. **Deterministic when needed.** Seeded RNG mode so that scripted test runs produce identical results.

3. **Transparent.** Every effect the interpreter produces is visible. The user always sees what the engine is doing and why.

4. **Minimal.** Ship the smallest useful thing. No readline, no color, no tab completion in v0. These can come later without architectural changes.

5. **Throwaway-friendly.** The CLI exists to stress-test the language. We expect to rewrite or discard parts of it as the DSL evolves.

---

## Architecture

### Crate layout

New workspace member: `crates/ttrpg_cli`

The crate has both a library target (`lib.rs`) and a binary target (`main.rs`). The library exposes the `Runner` type so Rust tests can drive the CLI command language programmatically. The binary is a thin wrapper that reads from stdin/files and feeds lines to the runner.

```
crates/ttrpg_cli/
├── Cargo.toml
└── src/
    ├── lib.rs           # Re-exports runner, commands, etc.
    ├── main.rs          # Argument parsing, mode dispatch, I/O loop
    ├── repl.rs          # Interactive REPL loop
    ├── commands.rs      # Command parsing and dispatch
    ├── runner.rs        # Shared execution engine (used by REPL, script mode, and Rust tests)
    ├── state.rs         # GameState setup helpers, entity builder
    └── effects.rs       # EffectHandler implementation, output formatting
```

Dependencies:
- `ttrpg_ast`, `ttrpg_lexer`, `ttrpg_parser`, `ttrpg_checker`, `ttrpg_interp` (workspace)
- `rand` (dice rolling)
- No other external dependencies in v0

### Execution modes

**Interactive REPL** (default): `ttrpg`
```
$ ttrpg
ttrpg> load spec/v0/04_full_example.ttrpg
Loaded system "D&D 5e Combat": 4 entities, 8 mechanics, 4 actions, 1 reaction, 3 conditions
ttrpg>
```

**Script mode**: `ttrpg run script.ttrpg-test`
```
$ ttrpg run scenario.ttrpg-test
```
Reads commands from a file, executes sequentially, exits with 0 on success or non-zero on error. Same command language as the REPL.

**Pipe mode** (implicit): when stdin is not a TTY, behaves like script mode reading from stdin. This lets tests do:
```
echo 'load foo.ttrpg\neval modifier(16)' | ttrpg
```

### Why not just `cargo test`?

Integration tests in `ttrpg_interp` already verify correctness at the Rust API level. The CLI serves a different purpose: it lets us test the *language* at the *language* level. A CLI script like:

```
load dnd5e.ttrpg
spawn Character fighter { AC: 16, HP: 30, max_HP: 30, ... }
spawn Character goblin { AC: 13, HP: 7, max_HP: 7, ... }
do Attack(fighter, goblin, longsword)
assert goblin.HP < 7 || goblin.HP == 7  // miss is possible
```

...is closer to how a DSL author thinks about their system than Rust test code that constructs `Value::Struct` by hand.

---

## Command Language

Commands are line-oriented. Blank lines are ignored. `//` begins a comment that extends to end-of-line — it can appear at the start of a line (whole-line comment) or after a command (inline comment). The comment is stripped before the command is parsed.

### Parsing strategy

Each line is split into a **keyword** (the first whitespace-delimited token) and a **tail** (the rest of the line). The keyword determines which command runs; the tail is parsed by that command's own logic. Commands that accept DSL expressions (`eval`, `assert`, `call`, etc.) delegate tail parsing to the DSL parser itself — they don't try to re-tokenize commas or braces.

For `assert_eq`, the two expressions are separated by the **first top-level comma** (one not nested inside parentheses, brackets, or braces). This avoids ambiguity with commas inside function arguments or collection literals.

For `assert_err`, the tail is parsed as a full command (keyword + tail) and executed in an error-catching context.

### Pipeline commands

```
load <path>                     # Parse, lower, check, build interpreter
reload                          # Re-run pipeline on the last loaded file
errors                          # Show parse/check diagnostics from last load
```

`load` runs the full pipeline and reports errors. If there are check errors, the interpreter is not built — but the `errors` command shows all parse and check diagnostics from the last load attempt, and `types` still works (it reads from the partial type environment built during checking). Commands that require a working interpreter (`do`, `call`, `eval`, `what_triggers`, `react`) will error with "no interpreter loaded." `reload` is shorthand for re-loading the same path (useful during file editing).

### State setup

```
spawn <EntityType> <handle> { field: value, ... }
set <handle>.<field> = <value>
destroy <handle>
```

The `<handle>` is a bare identifier (no quotes) used to reference the entity in subsequent commands — it's a CLI-local name, not the entity's in-game `name` field. The `spawn` command creates a `GameState` entity and assigns field values. Field values use DSL expression syntax (so `HP: 30`, `abilities: { STR: 16, DEX: 14 }`, etc.)

```
ttrpg> spawn Character fighter { name: "Aragorn", AC: 16, HP: 30, max_HP: 30, speed: 30 }
Spawned fighter (Character)
ttrpg> set fighter.AC = 18
fighter.AC = 18
```

### Execution

```
eval <expr>                     # Evaluate a DSL expression
call <fn>(<args>)               # Call a derive or mechanic by name
do <Action>(actor, args...)     # Execute an action
react <Reaction>(reactor) with { field: value, ... }  # Execute a reaction
what_triggers <event> at <entity>, <entity>, ... with { field: value, ... }  # Query event
```

`eval` is for quick expression testing (dice math, arithmetic, function calls). `call` invokes a named derive/mechanic. `do` runs the full action pipeline (cost, requires, resolve). Entity arguments use the names from `spawn`.

`react` executes a reaction directly. The `with { ... }` clause provides the event payload as a struct literal — its fields must match the event's declared shape.

`what_triggers` is a **query**, not an execution. It calls the interpreter's `what_triggers` (which is pure — no side effects, no dice, no state changes) and prints which reactions are triggerable and which are suppressed by conditions. It does not execute those reactions. To actually run a triggered reaction, use `react` on the ones reported as triggerable. The entity list after `at` specifies the candidate reactors. Candidates are checked in the order listed, making output deterministic.

```
ttrpg> eval 2d6 + 3
DiceExpr(2d6 + 3)
ttrpg> eval roll(2d6 + 3)
RollResult { rolls: [4, 2], total: 9 }
ttrpg> call modifier(16)
3
ttrpg> do Attack(fighter, goblin, longsword)
[ActionStarted] Attack by fighter
[RequiresCheck] passed
[DeductCost] fighter: action
[RollDice] 1d20 + 5 → RollResult { rolls: [14], total: 19 }
[RollDice] 1d8 + 3 → RollResult { rolls: [6], total: 9 }
[MutateField] goblin.HP: 7 → -2 (clamped to 0)
[ActionCompleted] Attack by fighter
=> hit(9)
```

### Inspection

```
inspect <entity>                # Show all fields
inspect <entity>.<field>        # Show one field
types                           # List all declared types
actions                         # List all actions with signatures
mechanics                       # List all mechanics/derives
conditions                      # List active conditions on all entities
state                           # Dump full game state
```

### Conditions and turn management

```
apply <Condition> to <entity> [duration]    # Manually apply a condition
remove <Condition> from <entity>            # Manually remove a condition
budget <entity>                             # Show turn budget
```

These are convenience commands for setting up game state. During normal action execution, conditions are applied/removed through the effect pipeline automatically.

### Assertions (for scripting)

```
assert <expr>                   # Fail with error if expr is falsy
assert_eq <expr> , <expr>       # Fail if not equal (comma-separated)
assert_err <command>            # Expect the command to produce any error
```

`assert_err` expects the embedded command to fail with *any* error — parse errors, check errors, runtime errors, or unknown-command errors. This allows testing the full pipeline: `assert_err load bad_syntax.ttrpg` verifies that a malformed file fails to load; `assert_err do Attack(nobody, nothing)` verifies a runtime failure.

Assertion failures in script mode cause a non-zero exit code and print the failing line with context. This is the primary mechanism for automated language-level tests.

### Configuration

```
seed <u64>                      # Set RNG seed for deterministic rolls
rolls <n> <n> <n> ...           # Queue specific die results (appends to queue)
rolls clear                     # Empty the roll queue
trace [on|off]                  # Toggle verbose effect logging (default: on)
quiet [on|off]                  # Suppress all output except errors and assert failures
```

`seed` sets a deterministic RNG — every `RollDice` effect uses this seeded RNG instead of system randomness.

`rolls` goes further: it queues exact individual die results that are consumed in order (one value per physical die). Each value must be in the range `1..=sides` for the die being rolled; out-of-range values are a runtime error. When the queue is non-empty, queued values are used instead of the RNG. When the queue is exhausted, subsequent rolls fall back to the current RNG (seeded or random). This means `rolls` and `seed` compose: queue known values for the rolls you care about, and let the RNG handle the rest. Calling `rolls` again appends to the existing queue; `rolls clear` empties it.

```
// Test: critical hit with known rolls
load dnd5e.ttrpg
spawn Character a { ... }
spawn Character b { ... }
rolls 20 6 6                    // attack d20=20 (crit!), damage 2d8=6,6
do Attack(a, b, greatsword)
assert_eq b.HP, 26              // 38 - 12 = 26
```

### Effect handling modes

```
mode auto                       # All effects auto-handled (default)
mode prompt                     # Pause on ResolvePrompt effects for user input
mode gm                         # Pause on ResolvePrompt AND gate effects (ActionStarted, RequiresCheck, DeductCost)
```

In `auto` mode (the default, and what scripts use), the REPL handles everything automatically: dice are rolled via RNG, costs are acknowledged, and `ResolvePrompt` effects return the `suggest` value if one exists or produce a runtime error if there is no suggestion (prompts with no `suggest` clause are inherently interactive and cannot be auto-resolved).

In `prompt` mode, `ResolvePrompt` effects pause for user input instead of using the suggest value. All other effects are still auto-handled.

In `gm` mode, `ResolvePrompt` effects pause for user input (same as prompt mode), and additionally gate effects (`ActionStarted`, `RequiresCheck`, `DeductCost`) pause for confirmation — the user can acknowledge, veto, or override. This simulates a GM reviewing each step.

---

## Output Format

### Human-readable (default)

Effect log lines are prefixed with the effect kind in brackets. Values are printed in DSL-compatible syntax where possible.

```
[RollDice] 1d20 + 5 → 19
[MutateField] goblin.HP: 7 → 0 (clamped)
=> hit(9)
```

### Machine-readable (future)

A `--format json` flag could emit one JSON object per line (JSONL). Not in v0, but the internal representation should make this straightforward to add later. The `runner` module produces structured `OutputEvent` values that the display layer formats — so swapping formatters is a localized change.

---

## Effect Handler Implementation

The CLI's `EffectHandler` is the core of the tool. It acts as a fully automated host.

The CLI does **not** use `StateAdapter`. Instead, the `EffectHandler` implementation wraps a `GameState` directly (which implements `WritableState`) and handles all effects itself. This gives the CLI full visibility into every effect — including mutations — because it sees them before applying them to state. This is a Layer 1 integration by choice: maximum transparency at the cost of more handler code, which is the right tradeoff for a debugging/exploration tool.

### Mutation arithmetic

Mutation effects (`MutateField`, `MutateTurnField`) carry an `AssignOp` (`=`, `+=`, `-=`), not a pre-computed final value. The CLI handler must compute the final value itself: read the current value, apply the operator, clamp to bounds if present. This is the same logic that `StateAdapter` performs internally via `compute_field_value` and `compute_turn_field_value` in `adapter.rs`. To avoid duplicating this arithmetic, `ttrpg_interp` should expose these as public utility functions that the CLI (and any other Layer 1 host) can use.

### Effect-by-effect behavior

#### Value effects (interpreter needs a value back)

```
RollDice { expr }         → Roll using seeded RNG (or pop from `rolls` queue).
                            Print the roll. Return Rolled(result).

ResolvePrompt { suggest } → In auto mode: return suggest value if present.
                            If no suggest value, runtime error (prompt requires interaction).
                            In prompt/gm mode: print hint, read user input, return PromptResult.
```

#### Mutation effects (CLI reads old value, computes new, writes to GameState)

```
MutateField { entity, path, op, value, bounds }
                          → Read old value at path. Compute final value via op + bounds clamping.
                            Write to GameState. Print old → new. Return Acknowledged.

ApplyCondition { target, condition, duration }
                          → Call GameState::add_condition.
                            Print "[Condition] Prone applied to goblin". Return Acknowledged.

RemoveCondition { target, condition }
                          → Call GameState::remove_condition.
                            Print "[Condition] Prone removed from goblin". Return Acknowledged.

MutateTurnField { actor, field, op, value }
                          → Read old turn budget value. Compute final value via op.
                            Write to GameState. Print old → new. Return Acknowledged.
```

#### Decision effects (CLI must apply state changes itself)

```
DeductCost { actor, token, budget_field }
                          → In auto mode: decrement budget_field on actor's turn budget by 1.
                            Print "[Cost] fighter: action". Return Acknowledged.
                          → In gm mode: print cost, read user choice.
                            Acknowledged → decrement. Vetoed → skip. Override(Str) → decrement
                            the replacement field instead (interpreter validates the replacement).
```

#### Gate effects (host can alter control flow)

```
ActionStarted { name, kind, actor, params }
                          → In auto mode: Return Acknowledged.
                          → In gm mode: print action summary, read user choice.
                            Valid responses: Acknowledged (proceed), Vetoed (abort action).

RequiresCheck { action, passed, reason }
                          → In auto mode: Return Acknowledged (interpreter uses original pass/fail).
                          → In gm mode: print pass/fail, read user choice.
                            Valid responses: Acknowledged (keep result), Override(Bool) (force pass/fail).
```

#### Informational effects (fire-and-forget)

```
ActionCompleted { name, actor }
                          → Print "[ActionCompleted] Attack by fighter". Return Acknowledged.

ModifyApplied { source, target_fn, phase, changes }
                          → Print modifier source and field changes. Return Acknowledged.
```

---

## Testing Integration

### As a test harness

The primary testing workflow is `.ttrpg-test` script files:

```bash
# In a shell test runner or CI
ttrpg run tests/combat_basics.ttrpg-test
ttrpg run tests/condition_modifiers.ttrpg-test
ttrpg run tests/pbta_moves.ttrpg-test
```

Each script loads a system file, sets up state, runs operations, and asserts on results. Exit code 0 = pass, non-zero = fail with diagnostic output.

### As a Rust integration

The `runner` module is a library-quality component that can also be used from Rust tests directly:

```rust
use ttrpg_cli::runner::Runner;

#[test]
fn test_attack_reduces_hp() {
    let mut runner = Runner::new();
    runner.exec("load tests/fixtures/dnd5e.ttrpg").unwrap();
    runner.exec("spawn Character a { HP: 30, max_HP: 30, AC: 10 }").unwrap();
    runner.exec("spawn Character b { HP: 20, max_HP: 20, AC: 10 }").unwrap();
    runner.exec("seed 1").unwrap();
    runner.exec("do Attack(a, b, sword)").unwrap();

    let hp = runner.eval("b.HP").unwrap();
    assert!(hp < Value::Int(20));
}
```

This is secondary to the script-based approach but useful for cases that need Rust-level assertions.

---

## Implementation Plan

### Phase 1: Skeleton

- Create `crates/ttrpg_cli` with `lib.rs` and `main.rs` (both targets from the start)
- Argument parsing: `ttrpg` (REPL), `ttrpg run <file>` (script)
- Basic REPL loop: read line from stdin, print it back
- `load` command: run full pipeline, report errors
- `eval` command: parse and evaluate a single expression (requires a minimal state/handler)

### Phase 2: State and Execution

- `spawn` / `set` / `destroy` commands using `GameState`
- `EffectHandler` implementation with seeded RNG
- `do` command for action execution
- `call` command for derives/mechanics
- Effect log output

### Phase 3: Inspection and Scripting

- `inspect` / `state` / `types` / `actions` / `mechanics` / `conditions` commands
- `assert` / `assert_eq` / `assert_err` commands
- `seed` / `rolls` commands
- Script mode (`ttrpg run`)
- Pipe detection (non-TTY stdin)

### Phase 4: Polish (only if needed)

- `reload` command
- `apply` / `remove` / `budget` convenience commands
- `trace` / `quiet` / `mode` commands
- Better error formatting
- Readline support (rustyline)

---

## Non-goals for v0

- Color/syntax highlighting
- Tab completion
- Command history persistence
- JSON output format
- Session save/load
- LSP integration
- Performance optimization
- Stable command syntax (we'll break it freely)
