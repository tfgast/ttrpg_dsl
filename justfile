# TTRPG DSL task runner
# https://github.com/casey/just

# List available recipes
default:
    @just --list

# Format all code
fmt:
    cargo fmt --all

# Check formatting without modifying files
fmt-check:
    cargo fmt --all -- --check

# Run clippy lints
clippy:
    cargo clippy --workspace --all-targets

# Run the test suite
test:
    cargo test --workspace

# Type-check without codegen
check:
    cargo check --workspace --all-targets

# Full CI-equivalent check: format, clippy, test
all: fmt-check clippy test

# Run clippy and auto-fix what it can
fix:
    cargo clippy --workspace --all-targets --fix --allow-dirty

# Build in release mode
build:
    cargo build --release

# Run the CLI (pass args after --)
run *ARGS:
    cargo run --release -- {{ARGS}}
