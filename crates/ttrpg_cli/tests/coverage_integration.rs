//! Integration tests for DSL-level code coverage.
//!
//! Tests verify that the coverage system correctly tracks line hits,
//! branch coverage, function entry, report generation, reset, and
//! combined coverage across multiple scenarios.

use std::sync::atomic::{AtomicU64, Ordering};
use ttrpg_cli::runner::Runner;
use ttrpg_interp::coverage::BranchKind;

// ── Helpers ──────────────────────────────────────────────────

static COUNTER: AtomicU64 = AtomicU64::new(0);

fn write_temp(name: &str, source: &str) -> std::path::PathBuf {
    let id = COUNTER.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join("ttrpg_cli_cov_test");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{name}_{id}.ttrpg"));
    std::fs::write(&path, source).unwrap();
    path
}

/// Small system with a derive, a function with branching, and an action.
const SIMPLE_SYSTEM: &str = r#"
system "Test" {
    entity Character {
        HP: int
        STR: int
        AC: int
    }

    derive modifier(score: int) -> int {
        floor((score - 10) / 2)
    }

    derive classify(value: int) -> string {
        if value >= 15 {
            "high"
        } else if value >= 10 {
            "medium"
        } else {
            "low"
        }
    }

    derive pick(value: int) -> string {
        match value {
            1 => "one",
            2 => "two",
            _ => "other",
        }
    }

    function heal(target: Character, amount: int) {
        target.HP += amount
    }

    action Attack on actor: Character (target: Character) {
        resolve {
            let damage = modifier(actor.STR)
            target.HP -= damage
        }
    }
}
"#;

fn load_simple_system() -> Runner {
    let path = write_temp("simple", SIMPLE_SYSTEM);
    let mut runner = Runner::new();
    runner.enable_coverage();
    runner.exec(&format!("load {}", path.display())).unwrap();
    runner.take_output();
    std::fs::remove_file(&path).ok();
    runner
}

fn exec(runner: &mut Runner, cmd: &str) -> Vec<String> {
    runner.exec(cmd).unwrap();
    runner.take_output()
}

// ═══════════════════════════════════════════════════════════════
//  Line hit tracking
// ═══════════════════════════════════════════════════════════════

#[test]
fn coverage_tracks_derive_call() {
    let mut r = load_simple_system();
    exec(&mut r, "seed 1");

    exec(&mut r, "call modifier(14)");

    let output = exec(&mut r, "coverage");
    let report = output.join("\n");

    // The derive body line should be HIT
    assert!(report.contains("HIT"), "expected HIT in report:\n{report}");

    // The summary should show some lines covered
    assert!(
        report.contains("lines covered"),
        "expected summary in report:\n{report}"
    );
}

#[test]
fn coverage_uncalled_functions_are_miss() {
    let mut r = load_simple_system();
    exec(&mut r, "seed 1");

    // Call only modifier, not classify or pick or heal
    exec(&mut r, "call modifier(10)");

    let output = exec(&mut r, "coverage");
    let report = output.join("\n");

    // modifier should be HIT, classify and heal should be MISS
    assert!(report.contains("HIT"), "should have some HIT lines");
    assert!(report.contains("MISS"), "should have some MISS lines");

    // Uncovered details should list uncalled functions
    assert!(
        report.contains("classify") && report.contains("never called"),
        "classify should be reported as uncalled:\n{report}"
    );
    assert!(
        report.contains("heal") && report.contains("never called"),
        "heal should be reported as uncalled:\n{report}"
    );
}

// ═══════════════════════════════════════════════════════════════
//  Branch tracking
// ═══════════════════════════════════════════════════════════════

#[test]
fn coverage_tracks_if_then_branch() {
    let mut r = load_simple_system();
    exec(&mut r, "seed 1");

    // classify(18) should take the "high" (then) branch
    exec(&mut r, "call classify(18)");

    let cov = r.coverage_data().unwrap().borrow();
    let has_if_then = cov
        .hit_branches
        .iter()
        .any(|bp| matches!(bp.kind, BranchKind::IfThen));
    assert!(has_if_then, "should record IfThen branch");
}

#[test]
fn coverage_tracks_if_else_branch() {
    let mut r = load_simple_system();
    exec(&mut r, "seed 1");

    // classify(5) should take the else->else branch ("low")
    exec(&mut r, "call classify(5)");

    let cov = r.coverage_data().unwrap().borrow();
    let has_if_else = cov
        .hit_branches
        .iter()
        .any(|bp| matches!(bp.kind, BranchKind::IfElse));
    assert!(has_if_else, "should record IfElse branch");
}

#[test]
fn coverage_tracks_match_arms() {
    let mut r = load_simple_system();
    exec(&mut r, "seed 1");

    // pick(1) should hit MatchArm(0)
    exec(&mut r, "call pick(1)");

    let cov = r.coverage_data().unwrap().borrow();
    let has_match_arm = cov
        .hit_branches
        .iter()
        .any(|bp| matches!(bp.kind, BranchKind::MatchArm(0)));
    assert!(has_match_arm, "should record MatchArm(0) for value 1");
}

#[test]
fn coverage_tracks_match_wildcard() {
    let mut r = load_simple_system();
    exec(&mut r, "seed 1");

    // pick(99) should hit the wildcard arm (MatchArm(2))
    exec(&mut r, "call pick(99)");

    let cov = r.coverage_data().unwrap().borrow();
    let has_wildcard = cov
        .hit_branches
        .iter()
        .any(|bp| matches!(bp.kind, BranchKind::MatchArm(2)));
    assert!(has_wildcard, "should record MatchArm(2) for wildcard");
}

// ═══════════════════════════════════════════════════════════════
//  Function entry tracking
// ═══════════════════════════════════════════════════════════════

#[test]
fn coverage_tracks_function_entry() {
    let mut r = load_simple_system();
    exec(&mut r, "seed 1");

    exec(&mut r, "call modifier(14)");
    exec(&mut r, "call classify(10)");

    let cov = r.coverage_data().unwrap().borrow();
    assert!(
        cov.hit_functions.contains("modifier"),
        "modifier should be recorded"
    );
    assert!(
        cov.hit_functions.contains("classify"),
        "classify should be recorded"
    );
    assert!(
        !cov.hit_functions.contains("heal"),
        "heal should NOT be recorded (not called)"
    );
}

#[test]
fn coverage_tracks_action_entry() {
    let mut r = load_simple_system();
    exec(&mut r, "seed 1");
    exec(
        &mut r,
        "spawn Character fighter { HP: 30, STR: 16, AC: 14 }",
    );

    exec(&mut r, "spawn Character target { HP: 20, STR: 10, AC: 12 }");
    exec(&mut r, "do Attack(fighter, target)");

    let cov = r.coverage_data().unwrap().borrow();
    assert!(
        cov.hit_functions.contains("Attack"),
        "Attack action should be recorded: {:?}",
        cov.hit_functions
    );
}

// ═══════════════════════════════════════════════════════════════
//  Coverage reset
// ═══════════════════════════════════════════════════════════════

#[test]
fn coverage_reset_clears_data() {
    let mut r = load_simple_system();
    exec(&mut r, "seed 1");

    exec(&mut r, "call modifier(14)");
    {
        let cov = r.coverage_data().unwrap().borrow();
        assert!(!cov.hit_spans.is_empty(), "should have hits before reset");
        assert!(
            !cov.hit_functions.is_empty(),
            "should have function entries before reset"
        );
    }

    exec(&mut r, "coverage reset");

    let cov = r.coverage_data().unwrap().borrow();
    assert!(cov.hit_spans.is_empty(), "spans should be cleared");
    assert!(cov.hit_branches.is_empty(), "branches should be cleared");
    assert!(cov.hit_functions.is_empty(), "functions should be cleared");
}

// ═══════════════════════════════════════════════════════════════
//  Report format
// ═══════════════════════════════════════════════════════════════

#[test]
fn coverage_report_contains_expected_sections() {
    let mut r = load_simple_system();
    exec(&mut r, "seed 1");
    exec(&mut r, "call modifier(14)");

    let output = exec(&mut r, "coverage");
    let report = output.join("\n");

    // File header
    assert!(
        report.contains("=== Coverage:"),
        "should have file header:\n{report}"
    );

    // Line annotations
    assert!(
        report.contains("HIT") || report.contains("MISS"),
        "should have line annotations:\n{report}"
    );

    // Summary line
    assert!(
        report.contains("Summary:") && report.contains("lines covered"),
        "should have summary:\n{report}"
    );

    // Should include line numbers
    assert!(
        report.contains("|"),
        "should have line number separators:\n{report}"
    );
}

#[test]
fn coverage_report_without_enable_gives_error() {
    let mut r = Runner::new();
    let result = r.exec("coverage");
    assert!(result.is_err(), "should error when coverage not enabled");
    let err = result.unwrap_err();
    assert!(
        err.to_string().contains("not enabled"),
        "error should mention not enabled: {err}"
    );
}

#[test]
fn coverage_report_without_loaded_file_gives_error() {
    let mut r = Runner::new();
    r.enable_coverage();
    let result = r.exec("coverage");
    assert!(result.is_err(), "should error when no file loaded");
    let err = result.unwrap_err();
    assert!(
        err.to_string().contains("no source files"),
        "error should mention no source files: {err}"
    );
}

// ═══════════════════════════════════════════════════════════════
//  Combined coverage across scenarios
// ═══════════════════════════════════════════════════════════════

#[test]
fn combined_coverage_accumulates_across_calls() {
    let mut r = load_simple_system();
    exec(&mut r, "seed 1");

    // Scenario 1: call modifier
    exec(&mut r, "call modifier(14)");

    // Scenario 2: call classify with different branches
    exec(&mut r, "call classify(18)"); // high branch
    exec(&mut r, "call classify(12)"); // medium branch
    exec(&mut r, "call classify(5)"); // low branch

    // Scenario 3: call pick with different arms
    exec(&mut r, "call pick(1)");
    exec(&mut r, "call pick(2)");
    exec(&mut r, "call pick(99)");

    // All three functions should be covered
    let cov = r.coverage_data().unwrap().borrow();
    assert!(cov.hit_functions.contains("modifier"));
    assert!(cov.hit_functions.contains("classify"));
    assert!(cov.hit_functions.contains("pick"));

    // Should have multiple branch kinds
    let branch_kinds: Vec<_> = cov.hit_branches.iter().map(|bp| &bp.kind).collect();
    let has_then = branch_kinds.iter().any(|k| matches!(k, BranchKind::IfThen));
    let has_else = branch_kinds.iter().any(|k| matches!(k, BranchKind::IfElse));
    let has_match = branch_kinds
        .iter()
        .any(|k| matches!(k, BranchKind::MatchArm(_)));
    assert!(has_then, "should have IfThen branches");
    assert!(has_else, "should have IfElse branches");
    assert!(has_match, "should have MatchArm branches");

    // Report should show good coverage
    drop(cov);
    let report = exec(&mut r, "coverage").join("\n");

    // Only heal and Attack should remain uncalled
    assert!(
        !report.contains("modifier -- never called"),
        "modifier was called"
    );
    assert!(
        !report.contains("classify -- never called"),
        "classify was called"
    );
}

#[test]
fn merge_combines_separate_coverage_data() {
    // Test CoverageData::merge() directly
    let mut r1 = load_simple_system();
    exec(&mut r1, "seed 1");
    exec(&mut r1, "call modifier(14)");

    let mut r2 = load_simple_system();
    exec(&mut r2, "seed 1");
    exec(&mut r2, "call classify(18)");
    exec(&mut r2, "call pick(2)");

    // Merge r2's data into r1's
    let cov1 = r1.coverage_data().unwrap();
    let cov2 = r2.coverage_data().unwrap();
    cov1.borrow_mut().merge(&cov2.borrow());

    let combined = cov1.borrow();
    assert!(
        combined.hit_functions.contains("modifier"),
        "should have modifier from r1"
    );
    assert!(
        combined.hit_functions.contains("classify"),
        "should have classify from r2"
    );
    assert!(
        combined.hit_functions.contains("pick"),
        "should have pick from r2"
    );
}

// ═══════════════════════════════════════════════════════════════
//  Coverage with mutations (function calls that modify state)
// ═══════════════════════════════════════════════════════════════

#[test]
fn coverage_tracks_function_with_mutation() {
    let mut r = load_simple_system();
    exec(&mut r, "seed 1");
    exec(&mut r, "spawn Character hero { HP: 20, STR: 14, AC: 12 }");

    exec(&mut r, "call heal(hero, 5)");

    let cov = r.coverage_data().unwrap().borrow();
    assert!(
        cov.hit_functions.contains("heal"),
        "heal function should be recorded"
    );
    assert!(
        !cov.hit_spans.is_empty(),
        "should have span hits from heal body"
    );
}

// ═══════════════════════════════════════════════════════════════
//  Coverage percentage accuracy
// ═══════════════════════════════════════════════════════════════

#[test]
fn coverage_percentage_increases_with_more_calls() {
    let mut r = load_simple_system();
    exec(&mut r, "seed 1");

    // Baseline: call one derive
    exec(&mut r, "call modifier(10)");
    let report1 = exec(&mut r, "coverage").join("\n");

    // Extract percentage from first report
    let pct1 = extract_line_coverage_pct(&report1);

    // Reset and exercise more code
    exec(&mut r, "coverage reset");
    exec(&mut r, "call modifier(14)");
    exec(&mut r, "call classify(18)");
    exec(&mut r, "call classify(5)");
    exec(&mut r, "call pick(1)");
    exec(&mut r, "call pick(99)");

    let report2 = exec(&mut r, "coverage").join("\n");
    let pct2 = extract_line_coverage_pct(&report2);

    assert!(
        pct2 > pct1,
        "more calls should increase coverage: {pct1:.1}% vs {pct2:.1}%"
    );
}

/// Extract the line coverage percentage from a coverage report summary line.
fn extract_line_coverage_pct(report: &str) -> f64 {
    // Look for "Summary: X/Y lines covered (Z%)"
    for line in report.lines() {
        if let Some(start) = line.find("lines covered (") {
            let rest = &line[start + "lines covered (".len()..];
            if let Some(end) = rest.find('%') {
                if let Ok(pct) = rest[..end].parse::<f64>() {
                    return pct;
                }
            }
        }
    }
    0.0
}
