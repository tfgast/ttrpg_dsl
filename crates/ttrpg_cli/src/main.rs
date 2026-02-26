use std::io::{self, BufRead, IsTerminal};
use std::process;

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
        Some(other) => {
            eprintln!("unknown subcommand: {}", other);
            eprintln!("usage: ttrpg [--vi] [run <script>]");
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
