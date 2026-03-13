//! OSRIC combined DSL coverage test.
//!
//! Runs every `.ttrpg-cli` test script in `osric/tests/` through a single
//! Runner instance with coverage enabled. Each script gets a fresh `load`
//! (resetting game state/handles) while coverage data accumulates across all
//! scripts. The combined report is written to `target/osric_coverage_report.txt`.

use ttrpg_cli::runner::Runner;

/// Workspace root, derived from `CARGO_MANIFEST_DIR` at compile time.
fn workspace_root() -> std::path::PathBuf {
    // CARGO_MANIFEST_DIR for ttrpg_cli is crates/ttrpg_cli
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent() // crates/
        .unwrap()
        .parent() // workspace root
        .unwrap()
        .to_path_buf()
}

#[test]
fn osric_combined_coverage() {
    let root = workspace_root();

    // Set working directory so `load osric/*.ttrpg` resolves correctly.
    std::env::set_current_dir(&root).expect("failed to chdir to workspace root");

    // 1. Create runner with coverage enabled
    let mut runner = Runner::new();
    runner.enable_coverage();
    runner.set_quiet(true);

    // 2. Discover all .ttrpg-cli test scripts
    let tests_dir = root.join("osric/tests");
    let mut scripts: Vec<_> = std::fs::read_dir(&tests_dir)
        .expect("failed to read osric/tests/")
        .filter_map(|entry| {
            let entry = entry.ok()?;
            let path = entry.path();
            if path.extension().and_then(|e| e.to_str()) == Some("ttrpg-cli") {
                Some(path)
            } else {
                None
            }
        })
        .collect();
    scripts.sort();

    let mut errors = Vec::new();

    // 3. Run each script — the `load` command in each script resets game
    //    state while coverage accumulates across all scripts.
    for script_path in &scripts {
        let script_name = script_path.file_name().unwrap().to_string_lossy();
        let content = std::fs::read_to_string(script_path)
            .unwrap_or_else(|e| panic!("cannot read {script_name}: {e}"));

        // Clear leftover rolls/variables from previous scripts (load resets
        // game state and handles but not the roll queue).
        let _ = runner.exec("rolls clear");
        runner.take_output();

        for (lineno, line) in content.lines().enumerate() {
            if let Err(e) = runner.exec(line) {
                errors.push(format!("{script_name}:{}: {e}", lineno + 1));
            }
            runner.take_output(); // discard per-line output
        }
    }

    assert!(
        errors.is_empty(),
        "{} error(s) running CLI test scripts:\n{}",
        errors.len(),
        errors.join("\n")
    );

    // 4. Generate and write coverage report
    runner
        .exec("coverage")
        .expect("failed to generate coverage report");
    let output = runner.take_output();
    let report = output.join("\n");

    let out_path = root.join("target/osric_coverage_report.txt");
    std::fs::write(&out_path, &report).expect("failed to write coverage report");

    // Print summary to stdout (visible with --nocapture)
    let lines: Vec<&str> = report.lines().collect();
    let summary_start = lines
        .iter()
        .rposition(|l| l.starts_with("══"))
        .unwrap_or(lines.len().saturating_sub(20));
    for line in &lines[summary_start..] {
        println!("{line}");
    }

    println!("\nFull report: {}", out_path.display());
    println!("Scripts executed: {}", scripts.len());
}
