use std::io::{self, BufRead, IsTerminal, Write};
use std::process;

use ttrpg_cli::runner::Runner;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();

    match args.first().map(|s| s.as_str()) {
        Some("run") => {
            if args.len() < 2 {
                eprintln!("usage: ttrpg run <script.ttrpg-cli>");
                process::exit(1);
            }
            run_script(&args[1]);
        }
        Some(other) => {
            eprintln!("unknown subcommand: {}", other);
            eprintln!("usage: ttrpg [run <script>]");
            process::exit(1);
        }
        None => {
            run_repl();
        }
    }
}

fn run_repl() {
    let stdin = io::stdin();
    let is_tty = stdin.is_terminal();
    let mut runner = Runner::new();

    if is_tty {
        print!("ttrpg> ");
        io::stdout().flush().ok();
    }

    for line in stdin.lock().lines() {
        let line = match line {
            Ok(l) => l,
            Err(e) => {
                eprintln!("read error: {}", e);
                break;
            }
        };

        match runner.exec(&line) {
            Ok(()) => {}
            Err(e) => {
                if is_tty {
                    eprintln!("error: {}", e);
                } else {
                    eprintln!("error: {}", e);
                    process::exit(1);
                }
            }
        }

        for line in runner.take_output() {
            println!("{}", line);
        }

        if is_tty {
            print!("ttrpg> ");
            io::stdout().flush().ok();
        }
    }

    if is_tty {
        println!();
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

    for (lineno, line) in content.lines().enumerate() {
        match runner.exec(line) {
            Ok(()) => {}
            Err(e) => {
                eprintln!("{}:{}: error: {}", path, lineno + 1, e);
                process::exit(1);
            }
        }

        for out in runner.take_output() {
            println!("{}", out);
        }
    }
}
