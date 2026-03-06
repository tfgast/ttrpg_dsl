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

# Full CI-equivalent check: format, clippy, test, scripts
all: fmt-check clippy test test-scripts

# Run clippy and auto-fix what it can
fix:
    cargo clippy --workspace --all-targets --fix --allow-dirty

# Build in release mode
build:
    cargo build --release

# Run criterion benchmarks
bench *ARGS:
    cargo bench -p ttrpg_interp {{ARGS}}

# Run the CLI (pass args after --)
run *ARGS:
    cargo run --release -- {{ARGS}}

# Run .ttrpg-cli integration test scripts
test-scripts:
    #!/usr/bin/env bash
    set -euo pipefail
    failed=0
    for script in osric/tests/*.ttrpg-cli ose/tests/*.ttrpg-cli tests/*.ttrpg-cli; do
        [ -f "$script" ] || continue
        echo "── $script ──"
        if cargo run --quiet --bin ttrpg -- --quiet run "$script"; then
            echo "  PASS"
        else
            echo "  FAIL"
            failed=1
        fi
    done
    exit $failed

# ── Fuzzing ──────────────────────────────────────────────────────
# Use malloc_limit_mb instead of rss_limit_mb to avoid false-positive
# OOM reports from ASAN shadow memory overhead.
fuzz_malloc_limit := "2048"

# Seed fuzz corpus from existing .ttrpg files
fuzz-seed:
    #!/usr/bin/env bash
    set -euo pipefail
    targets=(fuzz_lexer fuzz_parser fuzz_checker fuzz_full_pipeline)
    for target in "${targets[@]}"; do
        dir="fuzz/corpus/${target}"
        mkdir -p "$dir"
        cp -n fuzz/seed_corpus/*.ttrpg "$dir/" 2>/dev/null || true
        for f in prototypes/*.ttrpg spec/v0/*.ttrpg ose/*.ttrpg examples/*.ttrpg; do
            [ -f "$f" ] && cp -n "$f" "$dir/" 2>/dev/null || true
        done
    done
    echo "Seeded corpus for ${#targets[@]} targets"

# Run a fuzz target (default: fuzz_parser, 5 minutes)
# Usage: just fuzz [target] [duration]
fuzz target="fuzz_parser" duration="300":
    just fuzz-seed
    cargo +nightly fuzz run {{target}} -- \
        -rss_limit_mb=0 -malloc_limit_mb={{fuzz_malloc_limit}} \
        -max_total_time={{duration}}

# List available fuzz targets
fuzz-list:
    cargo +nightly fuzz list

# Reproduce a crash from an artifact file
# Usage: just fuzz-repro fuzz_parser fuzz/artifacts/fuzz_parser/crash-abc123
fuzz-repro target artifact:
    cargo +nightly fuzz run {{target}} {{artifact}} -- \
        -rss_limit_mb=0 -malloc_limit_mb={{fuzz_malloc_limit}}

# Run all fuzz targets briefly (smoke test, 30s each)
fuzz-smoke:
    #!/usr/bin/env bash
    set -euo pipefail
    just fuzz-seed
    targets=(fuzz_lexer fuzz_parser fuzz_checker fuzz_full_pipeline fuzz_checker_ast fuzz_interp_ast)
    for target in "${targets[@]}"; do
        echo "── Fuzzing $target for 30s ──"
        cargo +nightly fuzz run "$target" -- \
            -rss_limit_mb=0 -malloc_limit_mb={{fuzz_malloc_limit}} \
            -max_total_time=30
    done

# Generate coverage report for a fuzz target
fuzz-coverage target="fuzz_parser":
    cargo +nightly fuzz coverage {{target}}
    @echo "Coverage data in fuzz/coverage/{{target}}"
