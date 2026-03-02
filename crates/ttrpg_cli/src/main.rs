use std::io::{self, BufRead, IsTerminal};
use std::path::PathBuf;
use std::process;

use ttrpg_ast::diagnostic::{MultiSourceMap, Severity};
use ttrpg_checker::env::TypeEnv;
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
            // Strip -s / --snippet and --format json flags
            let mut snippet = false;
            let mut json = false;
            let mut check_args: Vec<&str> = Vec::new();
            let mut rest = &args[1..];
            while let Some((&first, tail)) = rest.split_first() {
                match first {
                    "-s" | "--snippet" => {
                        snippet = true;
                        rest = tail;
                    }
                    "--format" => {
                        match tail.first() {
                            Some(&"json") => json = true,
                            Some(other) => {
                                eprintln!("unknown format: {other}");
                                process::exit(1);
                            }
                            None => {
                                eprintln!("--format requires an argument");
                                process::exit(1);
                            }
                        }
                        rest = &tail[1..];
                    }
                    _ if first.starts_with("--format=") => {
                        let val = &first["--format=".len()..];
                        if val == "json" {
                            json = true;
                        } else {
                            eprintln!("unknown format: {val}");
                            process::exit(1);
                        }
                        rest = tail;
                    }
                    _ => {
                        check_args.push(first);
                        rest = tail;
                    }
                }
            }

            if check_args.first().copied() == Some("-c") {
                if check_args.len() != 2 {
                    eprintln!("usage: ttrpg check [-s] [--format json] -c <source>");
                    process::exit(1);
                }
                if check_args[1] == "-" {
                    check_stdin(snippet, json);
                } else {
                    check_source(check_args[1], snippet, json);
                }
            } else if check_args.is_empty() {
                if io::stdin().is_terminal() {
                    eprintln!("usage: ttrpg check [-s] [--format json] <files...>");
                    process::exit(1);
                }
                check_stdin(snippet, json);
            } else {
                check_files(&check_args, snippet, json);
            }
        }
        Some("query") => {
            run_query(&args[1..]);
        }
        Some(other) => {
            eprintln!("unknown subcommand: {other}");
            eprintln!(
                "usage: ttrpg [--vi] [-c <commands> | run <script> | check <files...> | query <topic> <files...>]"
            );
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
                eprintln!("read error: {e}");
                process::exit(1);
            }
        };

        let result = runner.exec(&line);

        for out in runner.take_output() {
            println!("{out}");
        }

        if let Err(e) = result {
            if e.is_rendered() {
                eprintln!("{e}");
            } else {
                eprintln!("error: {e}");
            }
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
            eprintln!("cannot read '{path}': {e}");
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
            println!("{out}");
        }

        if let Err(e) = result {
            if e.is_rendered() {
                eprintln!("{e}");
            } else {
                eprintln!("{}:{}: error: {}", label, lineno + 1, e);
            }
            had_error = true;
        }
    }

    if had_error {
        process::exit(1);
    }
}

/// Check DSL source read from stdin.
fn check_stdin(snippet: bool, json: bool) {
    let source = io::read_to_string(io::stdin()).unwrap_or_else(|e| {
        eprintln!("read error: {e}");
        process::exit(1);
    });
    let sources = vec![("<stdin>".to_string(), source)];
    check_sources(sources, snippet, json);
}

/// Check DSL source passed as a string.
fn check_source(source: &str, snippet: bool, json: bool) {
    let sources = vec![("<string>".to_string(), source.to_string())];
    check_sources(sources, snippet, json);
}

/// Check DSL source files by path (with glob support).
fn check_files(file_args: &[&str], snippet: bool, json: bool) {
    let sources = resolve_and_read_files(file_args);
    check_sources(sources, snippet, json);
}

/// Resolve glob patterns and read file contents.
fn resolve_and_read_files(file_args: &[&str]) -> Vec<(String, String)> {
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
                                eprintln!("glob error for '{arg}': {e}");
                                process::exit(1);
                            }
                        }
                    }
                    if !found {
                        eprintln!("no files matched pattern '{arg}'");
                        process::exit(1);
                    }
                }
                Err(e) => {
                    eprintln!("invalid glob pattern '{arg}': {e}");
                    process::exit(1);
                }
            }
        } else {
            paths.push(PathBuf::from(arg));
        }
    }

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
    sources
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
  ttrpg check --format json <files>  JSON diagnostic output (one object per line)
  ttrpg query <topic> <files...>     Introspect loaded type declarations
  ttrpg query <topic> -s -c <src>    Query inline snippet
  echo <commands> | ttrpg            Pipe mode (no line editing)

QUERY TOPICS:
  types, events, actions, conditions, mechanics, reactions, hooks, entity <name>, all

FLAGS:
  --vi                               Use vi keybindings in REPL
  --format json                      Output as JSON (check, query)
  --system <name>                    Filter query output by system name
  -s, --snippet                      Auto-wrap source in system block (check, query)
  -h, --help                         Show this help

REPL:
  Type 'help' inside the REPL for a list of commands."
    );
}

/// Parse query flags and dispatch to query_sources.
fn run_query(args: &[&str]) {
    let mut json = false;
    let mut snippet = false;
    let mut system_filter: Option<String> = None;
    let mut query_args: Vec<&str> = Vec::new();
    let mut rest = args;

    while let Some((&first, tail)) = rest.split_first() {
        match first {
            "-s" | "--snippet" => {
                snippet = true;
                rest = tail;
            }
            "--format" => {
                match tail.first() {
                    Some(&"json") => json = true,
                    Some(other) => {
                        eprintln!("unknown format: {other}");
                        process::exit(1);
                    }
                    None => {
                        eprintln!("--format requires an argument");
                        process::exit(1);
                    }
                }
                rest = &tail[1..];
            }
            _ if first.starts_with("--format=") => {
                let val = &first["--format=".len()..];
                if val == "json" {
                    json = true;
                } else {
                    eprintln!("unknown format: {val}");
                    process::exit(1);
                }
                rest = tail;
            }
            "--system" => {
                match tail.first() {
                    Some(name) => system_filter = Some(name.to_string()),
                    None => {
                        eprintln!("--system requires an argument");
                        process::exit(1);
                    }
                }
                rest = &tail[1..];
            }
            _ if first.starts_with("--system=") => {
                system_filter = Some(first["--system=".len()..].to_string());
                rest = tail;
            }
            _ => {
                query_args.push(first);
                rest = tail;
            }
        }
    }

    let topic = match query_args.first().copied() {
        Some(t) => t,
        None => {
            eprintln!("usage: ttrpg query <topic> [options] <files...>");
            eprintln!(
                "topics: types, events, actions, conditions, mechanics, reactions, hooks, entity <name>, all"
            );
            process::exit(1);
        }
    };

    // Validate topic and extract topic-specific args
    let (entity_name, file_args) = match topic {
        "types" | "events" | "actions" | "conditions" | "mechanics" | "reactions" | "hooks"
        | "all" => (None, &query_args[1..]),
        "entity" => {
            let name = match query_args.get(1).copied() {
                Some(n) => n,
                None => {
                    eprintln!("usage: ttrpg query entity <name> <files...>");
                    process::exit(1);
                }
            };
            (Some(name), &query_args[2..])
        }
        other => {
            eprintln!("unknown query topic: {other}");
            eprintln!(
                "topics: types, events, actions, conditions, mechanics, reactions, hooks, entity <name>, all"
            );
            process::exit(1);
        }
    };

    // Load sources
    let sources = if file_args.first().copied() == Some("-c") {
        if file_args.len() != 2 {
            eprintln!("usage: ttrpg query <topic> [options] -c <source>");
            process::exit(1);
        }
        if file_args[1] == "-" {
            let source = io::read_to_string(io::stdin()).unwrap_or_else(|e| {
                eprintln!("read error: {e}");
                process::exit(1);
            });
            vec![("<stdin>".to_string(), source)]
        } else {
            vec![("<string>".to_string(), file_args[1].to_string())]
        }
    } else if file_args.is_empty() {
        if io::stdin().is_terminal() {
            eprintln!("usage: ttrpg query <topic> [options] <files...>");
            process::exit(1);
        }
        let source = io::read_to_string(io::stdin()).unwrap_or_else(|e| {
            eprintln!("read error: {e}");
            process::exit(1);
        });
        vec![("<stdin>".to_string(), source)]
    } else {
        resolve_and_read_files(file_args)
    };

    query_sources(
        sources,
        snippet,
        topic,
        entity_name,
        system_filter.as_deref(),
        json,
    );
}

/// Parse, check, and dispatch to the appropriate query topic handler.
fn query_sources(
    sources: Vec<(String, String)>,
    snippet: bool,
    topic: &str,
    entity_name: Option<&str>,
    _system_filter: Option<&str>,
    _json: bool,
) {
    let snippet_prefix = "system \"<check>\" {\n";
    let snippet_suffix = "\n}\n";

    // Parse and check
    let (env, all_diags) = if snippet {
        let wrapped: Vec<(String, String)> = sources
            .iter()
            .map(|(name, src)| (name.clone(), format!("{snippet_prefix}{src}{snippet_suffix}")))
            .collect();
        let result = ttrpg_parser::parse_multi(&wrapped);
        let mut diags = result.diagnostics;
        let cr = ttrpg_checker::check_with_modules(&result.program, &result.module_map);
        diags.extend(cr.diagnostics);
        (cr.env, diags)
    } else {
        let result = ttrpg_parser::parse_multi(&sources);
        let mut diags = result.diagnostics;
        let cr = ttrpg_checker::check_with_modules(&result.program, &result.module_map);
        diags.extend(cr.diagnostics);
        (cr.env, diags)
    };

    // Report errors to stderr and abort
    let source_map = MultiSourceMap::new(sources);
    let has_errors = all_diags.iter().any(|d| d.severity == Severity::Error);
    if has_errors {
        for diag in &all_diags {
            eprintln!("{}", source_map.render(diag));
        }
        process::exit(1);
    }

    // Dispatch to topic handler
    match topic {
        "types" => query_types(&env),
        "events" => query_events(&env),
        "actions" => query_actions(&env),
        "conditions" => query_conditions(&env),
        "mechanics" => query_mechanics(&env),
        "reactions" => query_reactions(&env),
        "hooks" => query_hooks(&env),
        "entity" => query_entity(&env, entity_name.unwrap()),
        "all" => query_all(&env),
        _ => unreachable!(),
    }
}

// -- Topic stubs (each implemented by a follow-up bead) --

fn query_types(env: &TypeEnv) {
    let lines = ttrpg_cli::format::format_types(env);
    if lines.is_empty() {
        println!("no types");
    } else {
        for line in lines {
            println!("{line}");
        }
    }
}

fn query_events(_env: &TypeEnv) {
    eprintln!("query events: not yet implemented");
    process::exit(1);
}

fn query_actions(_env: &TypeEnv) {
    eprintln!("query actions: not yet implemented");
    process::exit(1);
}

fn query_conditions(_env: &TypeEnv) {
    eprintln!("query conditions: not yet implemented");
    process::exit(1);
}

fn query_mechanics(_env: &TypeEnv) {
    eprintln!("query mechanics: not yet implemented");
    process::exit(1);
}

fn query_reactions(_env: &TypeEnv) {
    eprintln!("query reactions: not yet implemented");
    process::exit(1);
}

fn query_hooks(_env: &TypeEnv) {
    eprintln!("query hooks: not yet implemented");
    process::exit(1);
}

fn query_entity(_env: &TypeEnv, _name: &str) {
    eprintln!("query entity: not yet implemented");
    process::exit(1);
}

fn query_all(_env: &TypeEnv) {
    eprintln!("query all: not yet implemented");
    process::exit(1);
}

/// Shared implementation for checking DSL sources.
///
/// When `snippet` is true, each source is auto-wrapped in
/// `system "<check>" { ... }` before parsing, and diagnostic spans are
/// adjusted so line/column numbers stay relative to the original input.
fn check_sources(sources: Vec<(String, String)>, snippet: bool, json: bool) {
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
                    format!("{snippet_prefix}{src}{snippet_suffix}"),
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
                diag.span.start = diag.span.start.saturating_sub(prefix_len as u32);
                diag.span.end = diag.span.end.saturating_sub(prefix_len as u32);
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
        if json {
            println!("{}", source_map.render_json(diag));
        } else {
            eprintln!("{}", source_map.render(diag));
        }
    }

    // Summary (human-readable only)
    if !json {
        if error_count > 0 {
            eprintln!(
                "{} error{}, {} warning{}",
                error_count,
                if error_count == 1 { "" } else { "s" },
                warning_count,
                if warning_count == 1 { "" } else { "s" },
            );
        } else if warning_count > 0 {
            eprintln!(
                "{} warning{}",
                warning_count,
                if warning_count == 1 { "" } else { "s" },
            );
        }
    }

    if error_count > 0 {
        process::exit(1);
    }
}
