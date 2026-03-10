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

    // Check for global flags
    let vi_mode = args.iter().any(|a| a == "--vi");
    let coverage_mode = args.iter().any(|a| a == "--coverage");
    let quiet_mode = args.iter().any(|a| a == "--quiet");
    let non_interactive = args.iter().any(|a| a == "--non-interactive");
    let args: Vec<&str> = args
        .iter()
        .filter(|a| {
            *a != "--vi" && *a != "--coverage" && *a != "--quiet" && *a != "--non-interactive"
        })
        .map(|s| s.as_str())
        .collect();

    match args.first().copied() {
        Some("-c") => {
            if args.len() != 2 {
                eprintln!("usage: ttrpg -c <commands>");
                process::exit(1);
            }
            run_commands(args[1], coverage_mode, quiet_mode);
        }
        Some("run") => {
            if args.get(1).copied() == Some("-c") {
                if args.len() != 3 {
                    eprintln!("usage: ttrpg run -c <commands>");
                    process::exit(1);
                }
                run_commands(args[2], coverage_mode, quiet_mode);
            } else {
                if args.len() != 2 {
                    eprintln!("usage: ttrpg run <script.ttrpg-cli>");
                    process::exit(1);
                }
                run_script(args[1], coverage_mode, quiet_mode);
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
                let interactive = !non_interactive;
                ttrpg_cli::repl::run_repl(vi_mode, coverage_mode, interactive);
            } else {
                run_pipe(coverage_mode, quiet_mode);
            }
        }
    }
}

/// Pipe mode: read raw lines from stdin, no reedline.
fn run_pipe(coverage: bool, quiet: bool) {
    let stdin = io::stdin();
    let mut runner = Runner::new();
    if coverage {
        runner.enable_coverage();
    }
    runner.set_quiet(quiet);
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

    if runner.in_heredoc() {
        eprintln!("error: unclosed source heredoc at end of input");
        had_error = true;
    }
    if runner.in_continuation() {
        eprintln!("error: unclosed continuation at end of input");
        had_error = true;
    }

    if had_error {
        process::exit(1);
    }
}

/// Execute CLI commands from a string.
fn run_commands(commands: &str, coverage: bool, quiet: bool) {
    exec_commands("-c", commands, coverage, quiet);
}

/// Execute CLI commands from a script file.
fn run_script(path: &str, coverage: bool, quiet: bool) {
    let content = match std::fs::read_to_string(path) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("cannot read '{path}': {e}");
            process::exit(1);
        }
    };
    exec_commands(path, &content, coverage, quiet);
}

/// Shared implementation for running CLI commands from a labeled source.
fn exec_commands(label: &str, content: &str, coverage: bool, quiet: bool) {
    let mut runner = Runner::new();
    if coverage {
        runner.enable_coverage();
    }
    runner.set_quiet(quiet);
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

    if runner.in_heredoc() {
        eprintln!("{label}: error: unclosed source heredoc at end of input");
        had_error = true;
    }
    if runner.in_continuation() {
        eprintln!("{label}: error: unclosed continuation at end of input");
        had_error = true;
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

/// Check DSL source files by path (with glob support and import resolution).
fn check_files(file_args: &[&str], snippet: bool, json: bool) {
    let (sources, resolve_diags) = resolve_and_read_files(file_args);
    check_sources_with_resolve_diags(sources, resolve_diags, snippet, json);
}

/// Resolve glob patterns, follow `import` directives transitively, and read file contents.
fn resolve_and_read_files(
    file_args: &[&str],
) -> (Vec<(String, String)>, Vec<ttrpg_parser::Diagnostic>) {
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

    // Use the source resolver to follow `import` directives transitively.
    match ttrpg_cli::source_resolve::resolve_sources(&paths) {
        Ok(resolved) => (resolved.sources, resolved.diagnostics),
        Err(e) => {
            eprintln!("{e}");
            process::exit(1);
        }
    }
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
  types, events, actions, conditions, mechanics (alias: derives), reactions, hooks, entity <name>, all

FLAGS:
  --vi                               Use vi keybindings in REPL
  --non-interactive                   Disable interactive prompts in REPL
  --quiet                            Suppress effect log output (run, pipe)
  --format json                      Output as JSON (check, query)
  --system <name>                    Filter query output by system name
  --xref                             Include cross-references (query entity)
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
    let mut xref = false;
    let mut system_filter: Option<String> = None;
    let mut query_args: Vec<&str> = Vec::new();
    let mut rest = args;

    while let Some((&first, tail)) = rest.split_first() {
        match first {
            "-s" | "--snippet" => {
                snippet = true;
                rest = tail;
            }
            "--xref" => {
                xref = true;
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
                "topics: types, events, actions, conditions, mechanics (alias: derives), reactions, hooks, entity <name>, all"
            );
            process::exit(1);
        }
    };

    // Validate topic and extract topic-specific args
    let (entity_name, file_args) = match topic {
        "types" | "events" | "actions" | "conditions" | "mechanics" | "derives" | "reactions"
        | "hooks" | "all" => (None, &query_args[1..]),
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
                "topics: types, events, actions, conditions, mechanics (alias: derives), reactions, hooks, entity <name>, all"
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
        resolve_and_read_files(file_args).0
    };

    query_sources(
        sources,
        snippet,
        topic,
        entity_name,
        system_filter.as_deref(),
        json,
        xref,
    );
}

/// Parse, check, and dispatch to the appropriate query topic handler.
fn query_sources(
    sources: Vec<(String, String)>,
    snippet: bool,
    topic: &str,
    entity_name: Option<&str>,
    system_filter: Option<&str>,
    _json: bool,
    xref: bool,
) {
    let snippet_prefix = "system \"<check>\" {\n";
    let snippet_suffix = "\n}\n";

    // Parse and check
    let (env, all_diags) = if snippet {
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
        "types" => query_types(&env, system_filter),
        "events" => query_events(&env, system_filter),
        "actions" => query_actions(&env, system_filter),
        "conditions" => query_conditions(&env, system_filter),
        "mechanics" | "derives" => query_mechanics(&env, system_filter),
        "reactions" => query_reactions(&env, system_filter),
        "hooks" => query_hooks(&env, system_filter),
        "entity" => query_entity(&env, entity_name.unwrap(), xref),
        "all" => query_all(&env, system_filter),
        _ => unreachable!(),
    }
}

// -- Topic stubs (each implemented by a follow-up bead) --

fn print_query(lines: Vec<String>, empty_msg: &str) {
    if lines.is_empty() {
        println!("{empty_msg}");
    } else {
        for line in lines {
            println!("{line}");
        }
    }
}

fn query_types(env: &TypeEnv, system: Option<&str>) {
    print_query(
        ttrpg_cli::format::format_types_filtered(env, system),
        "no types",
    );
}

fn query_events(env: &TypeEnv, system: Option<&str>) {
    print_query(
        ttrpg_cli::format::format_events_filtered(env, system),
        "no events",
    );
}

fn query_actions(env: &TypeEnv, system: Option<&str>) {
    print_query(
        ttrpg_cli::format::format_actions_filtered(env, system),
        "no actions",
    );
}

fn query_conditions(env: &TypeEnv, system: Option<&str>) {
    print_query(
        ttrpg_cli::format::format_condition_decls_filtered(env, system),
        "no conditions",
    );
}

fn query_mechanics(env: &TypeEnv, system: Option<&str>) {
    print_query(
        ttrpg_cli::format::format_mechanics_filtered(env, system),
        "no mechanics",
    );
}

fn query_reactions(env: &TypeEnv, system: Option<&str>) {
    print_query(
        ttrpg_cli::format::format_reactions_filtered(env, system),
        "no reactions",
    );
}

fn query_hooks(env: &TypeEnv, system: Option<&str>) {
    print_query(
        ttrpg_cli::format::format_hooks_filtered(env, system),
        "no hooks",
    );
}

fn query_entity(env: &TypeEnv, name: &str, xref: bool) {
    match ttrpg_cli::format::format_entity(env, name, xref) {
        Ok(lines) => {
            for line in lines {
                println!("{line}");
            }
        }
        Err(msg) => {
            eprintln!("{msg}");
            process::exit(1);
        }
    }
}

fn query_all(env: &TypeEnv, system: Option<&str>) {
    use ttrpg_cli::format;
    let sections: &[(&str, Vec<String>)] = &[
        ("Types", format::format_types_filtered(env, system)),
        ("Events", format::format_events_filtered(env, system)),
        ("Actions", format::format_actions_filtered(env, system)),
        (
            "Conditions",
            format::format_condition_decls_filtered(env, system),
        ),
        ("Mechanics", format::format_mechanics_filtered(env, system)),
        ("Reactions", format::format_reactions_filtered(env, system)),
        ("Hooks", format::format_hooks_filtered(env, system)),
    ];

    let mut first = true;
    for (heading, lines) in sections {
        if lines.is_empty() {
            continue;
        }
        if !first {
            println!();
        }
        first = false;
        println!("// {heading}");
        for line in lines {
            println!("{line}");
        }
    }

    if first {
        println!("no declarations");
    }
}

/// Shared implementation for checking DSL sources.
///
/// When `snippet` is true, each source is auto-wrapped in
/// `system "<check>" { ... }` before parsing, and diagnostic spans are
/// adjusted so line/column numbers stay relative to the original input.
fn check_sources(sources: Vec<(String, String)>, snippet: bool, json: bool) {
    check_sources_with_resolve_diags(sources, Vec::new(), snippet, json);
}

/// Like `check_sources`, but prepends diagnostics from the source resolver.
fn check_sources_with_resolve_diags(
    sources: Vec<(String, String)>,
    resolve_diags: Vec<ttrpg_parser::Diagnostic>,
    snippet: bool,
    json: bool,
) {
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
        let mut diags = resolve_diags;
        diags.extend(result.diagnostics);
        let cr = ttrpg_checker::check_with_modules(&result.program, &result.module_map);
        diags.extend(cr.diagnostics);

        // Adjust spans and enhance snippet-specific diagnostics
        for diag in &mut diags {
            if !diag.span.is_dummy() {
                diag.span.start = diag.span.start.saturating_sub(prefix_len as u32);
                diag.span.end = diag.span.end.saturating_sub(prefix_len as u32);
            }
            if diag.message == "system blocks cannot be nested" {
                diag.help = Some(
                    "snippet mode (-s) already wraps your source in a system block; \
                     write declarations directly without a system wrapper"
                        .into(),
                );
            }
        }
        diags
    } else {
        let result = ttrpg_parser::parse_multi(&sources);
        let mut diags = resolve_diags;
        diags.extend(result.diagnostics);
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
