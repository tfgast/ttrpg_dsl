# TTRPG DSL — Claude Code Instructions

## Before Writing .ttrpg Files

Read `doc/ai_authoring.md` first. It covers block categories, type system, common mistakes, and patterns. Use OSRIC modules (`osric/`) as reference implementations.

## Project Structure

Rust workspace with crates: `ttrpg_ast`, `ttrpg_lexer`, `ttrpg_parser`, `ttrpg_checker`, `ttrpg_interp`, `ttrpg_cli`, `ttrpg_ose_data`.

Pipeline: lex → parse → lower_moves → check → interpret.

| Directory | Contents |
|-----------|----------|
| `crates/` | Rust source for each pipeline stage |
| `ose/` | OSE (Old-School Essentials) rule modules |
| `osric/` | OSRIC (1e AD&D) rule modules |
| `spec/v0/` | Language specification (5 parts) |
| `doc/` | ai_authoring.md, language_reference.md |
| `examples/` | Example .ttrpg files |

## Build & Validate

Use `just` (task runner):

```bash
just test      # Run test suite (cargo test --workspace)
just clippy    # Lint
just fmt       # Format
just all       # Full CI check: fmt + clippy + test
just check     # Type-check without codegen
```

Validate .ttrpg files:

```bash
ttrpg check myfile.ttrpg              # Check a file
ttrpg check core.ttrpg combat.ttrpg   # Check multiple files together
ttrpg check -s                         # Snippet mode (auto-wraps in system block)
```

Always run `ttrpg check` on .ttrpg files before considering work done. Always run `just test` after Rust changes.

## Writing Tests

Read `@doc/test_scripts.md` before writing or modifying `.ttrpg-cli` test scripts. It covers all available commands (assertions, dice control, spawning, etc.) and value syntax.

**Choose the right test approach:**

- **`.ttrpg-cli` scripts** — for testing DSL rule logic: derive/table values, mechanic evaluation, action execution, entity state changes, error cases. Place in `{ruleset}/tests/`. Run with `just test-scripts`.
- **Rust integration tests** — for testing Rust internals: AST structure, custom effect handlers, interpreter API surface, tests needing programmatic loops. Place in `crates/ttrpg_interp/tests/`.

Prefer scripts over Rust tests when either would work — they're faster to write and closer to the DSL.

## Coding Conventions

- Follow existing patterns in the crate you're modifying
