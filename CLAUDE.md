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

## Coding Conventions

- Follow existing patterns in the crate you're modifying
- Integration tests for .ttrpg rule modules go in `crates/ttrpg_interp/tests/`
- Test file naming: `{ruleset}_{topic}_integration.rs`
