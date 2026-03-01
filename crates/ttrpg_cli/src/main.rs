use std::io::{self, BufRead, IsTerminal};
use std::path::PathBuf;
use std::process;

use ttrpg_ast::diagnostic::{MultiSourceMap, Severity};
use ttrpg_cli::runner::Runner;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();

    // Check for --help / -h flag
    if args.iter().any(|a| a == "--help" || a == "-h") {
        print_usage();
        return;
    }

    // Check for --vi flag
    let vi_mode = args.iter().any(|a| a == "--vi");
    let args: Vec<&str> = args
        .iter()
        .filter(|a| *a != "--vi")
        .map(|s| s.as_str())
        .collect();

    match args.first().copied() {
        Some("-c") => {
            if args.len() != 2 {
                eprintln!("usage: ttrpg -c <commands>");
                process::exit(1);
            }
            run_commands(args[1]);
        }
        Some("run") => {
            if args.get(1).copied() == Some("-c") {
                if args.len() != 3 {
                    eprintln!("usage: ttrpg run -c <commands>");
                    process::exit(1);
                }
                run_commands(args[2]);
            } else {
                if args.len() != 2 {
                    eprintln!("usage: ttrpg run <script.ttrpg-cli>");
                    process::exit(1);
                }
                run_script(args[1]);
            }
        }
        Some("check") => {
            // Strip -s / --snippet flag
            let check_args: Vec<&str> = args[1..]
                .iter()
                .filter(|a| **a != "-s" && **a != "--snippet")
                .copied()
                .collect();
            let snippet = check_args.len() < args.len() - 1;

            if check_args.first().copied() == Some("-c") {
                if check_args.len() != 2 {
                    eprintln!("usage: ttrpg check [-s] -c <source>");
                    process::exit(1);
                }
                if check_args[1] == "-" {
                    check_stdin(snippet);
                } else {
                    check_source(check_args[1], snippet);
                }
            } else if check_args.is_empty() {
                if io::stdin().is_terminal() {
                    eprintln!("usage: ttrpg check [-s] <files...>");
                    process::exit(1);
                }
                check_stdin(snippet);
            } else {
                check_files(&check_args, snippet);
            }
        }
        Some(other) => {
            eprintln!("unknown subcommand: {}", other);
            eprintln!("usage: ttrpg [--vi] [-c <commands> | run <script> | check <files...>]");
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

/// Execute CLI commands from a string.
fn run_commands(commands: &str) {
    exec_commands("-c", commands);
}

/// Execute CLI commands from a script file.
fn run_script(path: &str) {
    let content = match std::fs::read_to_string(path) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("cannot read '{}': {}", path, e);
            process::exit(1);
        }
    };
    exec_commands(path, &content);
}

/// Shared implementation for running CLI commands from a labeled source.
fn exec_commands(label: &str, content: &str) {
    let mut runner = Runner::new();
    let mut had_error = false;

    for (lineno, line) in content.lines().enumerate() {
        let result = runner.exec(line);

        for out in runner.take_output() {
            println!("{}", out);
        }

        if let Err(e) = result {
            eprintln!("{}:{}: error: {}", label, lineno + 1, e);
            had_error = true;
        }
    }

    if had_error {
        process::exit(1);
    }
}

/// Check DSL source read from stdin.
fn check_stdin(snippet: bool) {
    let source = io::read_to_string(io::stdin()).unwrap_or_else(|e| {
        eprintln!("read error: {}", e);
        process::exit(1);
    });
    let sources = vec![("<stdin>".to_string(), source)];
    check_sources(sources, snippet);
}

/// Check DSL source passed as a string.
fn check_source(source: &str, snippet: bool) {
    let sources = vec![("<string>".to_string(), source.to_string())];
    check_sources(sources, snippet);
}

/// Check DSL source files by path (with glob support).
fn check_files(file_args: &[&str], snippet: bool) {
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

    check_sources(sources, snippet);
}

/// Print CLI usage and exit.
fn print_usage() {
    println!(
        "\
ttrpg — TTRPG DSL interpreter

USAGE:
  ttrpg [--vi]                       Start interactive REPL
  ttrpg -c <commands>                Execute commands inline
  ttrpg run <script.ttrpg-cli>       Execute a script file
  ttrpg run -c <commands>            Execute commands inline (alt form)
  ttrpg check <files...>             Type-check source files
  ttrpg check -s <files...>          Type-check snippets (auto-wrapped in system block)
  ttrpg check [-s] -c <source>       Type-check source string
  echo <commands> | ttrpg            Pipe mode (no line editing)

FLAGS:
  --vi                               Use vi keybindings in REPL
  -h, --help                         Show this help

REPL:
  Type 'help' inside the REPL for a list of commands."
    );
}

/// Shared implementation for checking DSL sources.
///
/// When `snippet` is true, each source is auto-wrapped in
/// `system "<check>" { ... }` before parsing, and diagnostic spans are
/// adjusted so line/column numbers stay relative to the original input.
fn check_sources(sources: Vec<(String, String)>, snippet: bool) {
    let snippet_prefix = "system \"<check>\" {\n";
    let snippet_suffix = "\n}\n";
    let prefix_len = snippet_prefix.len();

    // Parse and check — wrap sources if in snippet mode
    let all_diags = if snippet {
        let wrapped: Vec<(String, String)> = sources
            .iter()
            .map(|(name, src)| {
                (
                    name.clone(),
                    format!("{}{}{}", snippet_prefix, src, snippet_suffix),
                )
            })
            .collect();
        let result = ttrpg_parser::parse_multi(&wrapped);
        let mut diags = result.diagnostics;
        let cr = ttrpg_checker::check_with_modules(&result.program, &result.module_map);
        diags.extend(cr.diagnostics);

        // Adjust spans back to original source offsets
        for diag in &mut diags {
            if !diag.span.is_dummy() {
                diag.span.start = diag.span.start.saturating_sub(prefix_len);
                diag.span.end = diag.span.end.saturating_sub(prefix_len);
            }
        }
        diags
    } else {
        let result = ttrpg_parser::parse_multi(&sources);
        let mut diags = result.diagnostics;
        let cr = ttrpg_checker::check_with_modules(&result.program, &result.module_map);
        diags.extend(cr.diagnostics);
        diags
    };

    // Render diagnostics against the original (unwrapped) sources
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
