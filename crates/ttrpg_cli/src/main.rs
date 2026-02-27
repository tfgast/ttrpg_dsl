use std::io::{self, BufRead, IsTerminal};
use std::path::PathBuf;
use std::process;

use ttrpg_ast::diagnostic::{MultiSourceMap, Severity};
use ttrpg_cli::runner::Runner;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();

    // Check for --vi flag
    let vi_mode = args.iter().any(|a| a == "--vi");
    let args: Vec<&str> = args
        .iter()
        .filter(|a| *a != "--vi")
        .map(|s| s.as_str())
        .collect();

    match args.first().copied() {
        Some("run") => {
            if args.len() != 2 {
                eprintln!("usage: ttrpg run <script.ttrpg-cli>");
                process::exit(1);
            }
            run_script(args[1]);
        }
        Some("check") => {
            if args.len() < 2 {
                eprintln!("usage: ttrpg check <files...>");
                process::exit(1);
            }
            run_check(&args[1..]);
        }
        Some(other) => {
            eprintln!("unknown subcommand: {}", other);
            eprintln!("usage: ttrpg [--vi] [run <script> | check <files...>]");
            process::exit(1);
        }
        None => {
            let stdin = io::stdin();
            if stdin.is_terminal() {
                ttrpg_cli::repl::run_repl(vi_mode);
            } else {
                run_pipe();
            }
        }
    }
}

/// Pipe mode: read raw lines from stdin, no reedline.
fn run_pipe() {
    let stdin = io::stdin();
    let mut runner = Runner::new();
    let mut had_error = false;

    for line in stdin.lock().lines() {
        let line = match line {
            Ok(l) => l,
            Err(e) => {
                eprintln!("read error: {}", e);
                process::exit(1);
            }
        };

        let result = runner.exec(&line);

        for out in runner.take_output() {
            println!("{}", out);
        }

        if let Err(e) = result {
            eprintln!("error: {}", e);
            had_error = true;
        }
    }

    if had_error {
        process::exit(1);
    }
}

fn run_check(file_args: &[&str]) {
    // Resolve globs and collect paths
    let mut paths: Vec<PathBuf> = Vec::new();
    for arg in file_args {
        if arg.contains('*') || arg.contains('?') || arg.contains('[') {
            match glob::glob(arg) {
                Ok(entries) => {
                    let mut found = false;
                    for entry in entries {
                        match entry {
                            Ok(path) => {
                                paths.push(path);
                                found = true;
                            }
                            Err(e) => {
                                eprintln!("glob error for '{}': {}", arg, e);
                                process::exit(1);
                            }
                        }
                    }
                    if !found {
                        eprintln!("no files matched pattern '{}'", arg);
                        process::exit(1);
                    }
                }
                Err(e) => {
                    eprintln!("invalid glob pattern '{}': {}", arg, e);
                    process::exit(1);
                }
            }
        } else {
            paths.push(PathBuf::from(arg));
        }
    }

    // Read all files
    let mut sources: Vec<(String, String)> = Vec::new();
    for path in &paths {
        match std::fs::read_to_string(path) {
            Ok(content) => sources.push((path.to_string_lossy().into_owned(), content)),
            Err(e) => {
                eprintln!("cannot read '{}': {}", path.display(), e);
                process::exit(1);
            }
        }
    }

    // Parse and check
    let result = ttrpg_parser::parse_multi(&sources);
    let mut all_diags = result.diagnostics;

    let check_result = ttrpg_checker::check_with_modules(&result.program, &result.module_map);
    all_diags.extend(check_result.diagnostics);

    // Render diagnostics
    let source_map = MultiSourceMap::new(sources);
    let mut error_count = 0;
    let mut warning_count = 0;

    for diag in &all_diags {
        match diag.severity {
            Severity::Error => error_count += 1,
            Severity::Warning => warning_count += 1,
        }
        eprintln!("{}", source_map.render(diag));
    }

    // Summary
    if error_count > 0 {
        eprintln!(
            "{} error{}, {} warning{}",
            error_count,
            if error_count == 1 { "" } else { "s" },
            warning_count,
            if warning_count == 1 { "" } else { "s" },
        );
        process::exit(1);
    } else if warning_count > 0 {
        eprintln!(
            "{} warning{}",
            warning_count,
            if warning_count == 1 { "" } else { "s" },
        );
    }
}

fn run_script(path: &str) {
    let content = match std::fs::read_to_string(path) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("cannot read '{}': {}", path, e);
            process::exit(1);
        }
    };

    let mut runner = Runner::new();
    let mut had_error = false;

    for (lineno, line) in content.lines().enumerate() {
        let result = runner.exec(line);

        for out in runner.take_output() {
            println!("{}", out);
        }

        if let Err(e) = result {
            eprintln!("{}:{}: error: {}", path, lineno + 1, e);
            had_error = true;
        }
    }

    if had_error {
        process::exit(1);
    }
}
