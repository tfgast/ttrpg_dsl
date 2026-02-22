use std::path::PathBuf;

use ttrpg_ast::ast::Program;
use ttrpg_ast::diagnostic::{Diagnostic, Severity};
use ttrpg_checker::env::TypeEnv;
use ttrpg_interp::Interpreter;
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::Value;

use crate::commands::{self, Command};
use crate::effects::MinimalHandler;
use crate::format::format_value;

/// Errors produced by Runner operations.
#[derive(Debug)]
pub enum CliError {
    /// A user-facing message (not a bug).
    Message(String),
}

impl std::fmt::Display for CliError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CliError::Message(msg) => write!(f, "{}", msg),
        }
    }
}

/// The core CLI runner. Owns program state and dispatches commands.
pub struct Runner {
    program: Box<Program>,
    type_env: Box<TypeEnv>,
    game_state: GameState,
    last_path: Option<PathBuf>,
    diagnostics: Vec<Diagnostic>,
    output: Vec<String>,
}

impl Runner {
    /// Create a new runner with empty program state.
    pub fn new() -> Self {
        Runner {
            program: Box::new(Program { items: Vec::new() }),
            type_env: Box::new(TypeEnv::new()),
            game_state: GameState::new(),
            last_path: None,
            diagnostics: Vec::new(),
            output: Vec::new(),
        }
    }

    /// Execute a single line of input. Output is collected internally.
    pub fn exec(&mut self, line: &str) -> Result<(), CliError> {
        let cmd = match commands::parse_command(line) {
            Some(cmd) => cmd,
            None => return Ok(()), // blank or comment-only line
        };

        match cmd {
            Command::Load(path) => self.cmd_load(&path),
            Command::Eval(expr_str) => self.cmd_eval(&expr_str),
            Command::Reload => self.cmd_reload(),
            Command::Errors => self.cmd_errors(),
            Command::Unknown(kw) => Err(CliError::Message(format!("unknown command: {}", kw))),
        }
    }

    /// Drain and return collected output lines.
    pub fn take_output(&mut self) -> Vec<String> {
        std::mem::take(&mut self.output)
    }

    /// Evaluate an expression and return the value directly (for testing).
    pub fn eval(&mut self, expr: &str) -> Result<Value, CliError> {
        let (parsed, diags) = ttrpg_parser::parse_expr(expr);
        if !diags.is_empty() {
            let msgs: Vec<_> = diags.iter().map(|d| d.message.as_str()).collect();
            return Err(CliError::Message(format!("parse error: {}", msgs.join("; "))));
        }
        let parsed = parsed.ok_or_else(|| CliError::Message("failed to parse expression".into()))?;

        let interp = Interpreter::new(&self.program, &self.type_env)
            .map_err(|e| CliError::Message(format!("interpreter error: {}", e)))?;
        let mut handler = MinimalHandler;
        interp
            .evaluate_expr(&self.game_state, &mut handler, &parsed)
            .map_err(|e| CliError::Message(format!("runtime error: {}", e)))
    }

    // ── Command handlers ────────────────────────────────────────

    fn cmd_load(&mut self, path: &str) -> Result<(), CliError> {
        let source = match std::fs::read_to_string(path) {
            Ok(s) => s,
            Err(e) => {
                // Clear stale state so a previous successful load doesn't linger.
                self.program = Box::new(Program { items: Vec::new() });
                self.type_env = Box::new(TypeEnv::new());
                self.game_state = GameState::new();
                self.diagnostics = Vec::new();
                self.last_path = Some(PathBuf::from(path));
                return Err(CliError::Message(format!(
                    "cannot read '{}': {}",
                    path, e
                )));
            }
        };

        let (program, parse_diags) = ttrpg_parser::parse(&source);

        let mut lower_diags = Vec::new();
        let program = ttrpg_parser::lower_moves(program, &mut lower_diags);

        let check_result = ttrpg_checker::check(&program);

        // Merge all diagnostics
        let mut all_diags = Vec::new();
        all_diags.extend(parse_diags);
        all_diags.extend(lower_diags);
        all_diags.extend(check_result.diagnostics);

        let errors: Vec<_> = all_diags
            .iter()
            .filter(|d| d.severity == Severity::Error)
            .collect();

        if errors.is_empty() {
            self.program = Box::new(program);
            self.type_env = Box::new(check_result.env);
            self.game_state = GameState::new();
            self.diagnostics = all_diags;
            self.last_path = Some(PathBuf::from(path));
            self.output.push(format!("loaded {}", path));
            Ok(())
        } else {
            let error_count = errors.len();
            // Clear stale program state so eval cannot use a previous successful load.
            self.program = Box::new(Program { items: Vec::new() });
            self.type_env = Box::new(TypeEnv::new());
            self.game_state = GameState::new();
            self.diagnostics = all_diags;
            self.last_path = Some(PathBuf::from(path));
            self.output
                .push("use 'errors' to see diagnostics".into());
            Err(CliError::Message(format!(
                "failed to load '{}': {} error{}",
                path,
                error_count,
                if error_count == 1 { "" } else { "s" }
            )))
        }
    }

    fn cmd_eval(&mut self, expr_str: &str) -> Result<(), CliError> {
        let val = self.eval(expr_str)?;
        self.output.push(format_value(&val));
        Ok(())
    }

    fn cmd_reload(&mut self) -> Result<(), CliError> {
        match &self.last_path {
            Some(path) => {
                let path = path.to_string_lossy().to_string();
                self.cmd_load(&path)
            }
            None => Err(CliError::Message("no file loaded yet".into())),
        }
    }

    fn cmd_errors(&mut self) -> Result<(), CliError> {
        if self.diagnostics.is_empty() {
            self.output.push("no diagnostics".into());
        } else {
            for diag in &self.diagnostics {
                let severity = match diag.severity {
                    Severity::Error => "error",
                    Severity::Warning => "warning",
                };
                self.output
                    .push(format!("[{}] {}", severity, diag.message));
            }
        }
        Ok(())
    }
}

impl Default for Runner {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn eval_arithmetic() {
        let mut runner = Runner::new();
        let val = runner.eval("2 + 3").unwrap();
        assert_eq!(val, Value::Int(5));
    }

    #[test]
    fn eval_string_literal() {
        let mut runner = Runner::new();
        let val = runner.eval("\"hello\"").unwrap();
        assert_eq!(val, Value::Str("hello".into()));
    }

    #[test]
    fn eval_boolean() {
        let mut runner = Runner::new();
        assert_eq!(runner.eval("true").unwrap(), Value::Bool(true));
        assert_eq!(runner.eval("false").unwrap(), Value::Bool(false));
    }

    #[test]
    fn eval_none_literal() {
        let mut runner = Runner::new();
        assert_eq!(runner.eval("none").unwrap(), Value::None);
    }

    #[test]
    fn eval_comparison() {
        let mut runner = Runner::new();
        assert_eq!(runner.eval("3 > 2").unwrap(), Value::Bool(true));
        assert_eq!(runner.eval("1 == 2").unwrap(), Value::Bool(false));
    }

    #[test]
    fn eval_complex_arithmetic() {
        let mut runner = Runner::new();
        assert_eq!(runner.eval("(10 + 5) * 2").unwrap(), Value::Int(30));
    }

    #[test]
    fn eval_parse_error() {
        let mut runner = Runner::new();
        let err = runner.eval("2 +").unwrap_err();
        assert!(
            err.to_string().contains("parse error"),
            "got: {}",
            err
        );
    }

    #[test]
    fn exec_eval_collects_output() {
        let mut runner = Runner::new();
        runner.exec("eval 2 + 3").unwrap();
        let output = runner.take_output();
        assert_eq!(output, vec!["5"]);
    }

    #[test]
    fn exec_blank_line() {
        let mut runner = Runner::new();
        runner.exec("").unwrap();
        runner.exec("   ").unwrap();
        runner.exec("// comment").unwrap();
        assert!(runner.take_output().is_empty());
    }

    #[test]
    fn exec_unknown_command() {
        let mut runner = Runner::new();
        let err = runner.exec("foobar").unwrap_err();
        assert!(err.to_string().contains("unknown command"));
    }

    #[test]
    fn exec_reload_without_load() {
        let mut runner = Runner::new();
        let err = runner.exec("reload").unwrap_err();
        assert!(err.to_string().contains("no file loaded"));
    }

    #[test]
    fn exec_errors_empty() {
        let mut runner = Runner::new();
        runner.exec("errors").unwrap();
        let output = runner.take_output();
        assert_eq!(output, vec!["no diagnostics"]);
    }

    #[test]
    fn exec_load_nonexistent_file() {
        let mut runner = Runner::new();
        let err = runner.exec("load /nonexistent/path.ttrpg").unwrap_err();
        assert!(err.to_string().contains("cannot read"));
    }

    #[test]
    fn exec_load_and_eval() {
        // Create a temp file with a simple system
        let dir = std::env::temp_dir().join("ttrpg_cli_test");
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("test_load.ttrpg");
        std::fs::write(
            &path,
            r#"
system "test" {
    derive add(a: int, b: int) -> int { a + b }
}
"#,
        )
        .unwrap();

        let mut runner = Runner::new();
        runner
            .exec(&format!("load {}", path.display()))
            .unwrap();
        let output = runner.take_output();
        assert_eq!(output.len(), 1);
        assert!(output[0].starts_with("loaded"));

        // Eval a basic expression (derives aren't callable via eval, but arithmetic works)
        runner.exec("eval 10 * 3").unwrap();
        let output = runner.take_output();
        assert_eq!(output, vec!["30"]);

        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn exec_load_with_errors_then_errors_command() {
        let dir = std::env::temp_dir().join("ttrpg_cli_test");
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("test_errors.ttrpg");
        std::fs::write(
            &path,
            r#"
system "test" {
    derive bad() -> int { undefined_var }
}
"#,
        )
        .unwrap();

        let mut runner = Runner::new();
        let err = runner
            .exec(&format!("load {}", path.display()))
            .unwrap_err();
        assert!(err.to_string().contains("error"));
        // Output hint should still be available
        let output = runner.take_output();
        assert!(output.iter().any(|l| l.contains("errors")));

        runner.exec("errors").unwrap();
        let output = runner.take_output();
        assert!(!output.is_empty());
        assert!(output.iter().any(|l| l.contains("[error]")));

        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn exec_reload() {
        let dir = std::env::temp_dir().join("ttrpg_cli_test");
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("test_reload.ttrpg");
        std::fs::write(
            &path,
            r#"
system "test" {
    derive add(a: int, b: int) -> int { a + b }
}
"#,
        )
        .unwrap();

        let mut runner = Runner::new();
        runner
            .exec(&format!("load {}", path.display()))
            .unwrap();
        runner.take_output();

        runner.exec("reload").unwrap();
        let output = runner.take_output();
        assert!(output[0].starts_with("loaded"));

        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn eval_list_literal() {
        let mut runner = Runner::new();
        let val = runner.eval("[1, 2, 3]").unwrap();
        assert_eq!(
            val,
            Value::List(vec![Value::Int(1), Value::Int(2), Value::Int(3)])
        );
    }

    #[test]
    fn failed_load_clears_stale_state() {
        let dir = std::env::temp_dir().join("ttrpg_cli_test");
        std::fs::create_dir_all(&dir).unwrap();

        // First, load a good file
        let good = dir.join("good_stale.ttrpg");
        std::fs::write(
            &good,
            r#"
system "test" {
    derive add(a: int, b: int) -> int { a + b }
}
"#,
        )
        .unwrap();

        let mut runner = Runner::new();
        runner
            .exec(&format!("load {}", good.display()))
            .unwrap();
        runner.take_output();

        // Eval should work
        runner.exec("eval 1 + 2").unwrap();
        assert_eq!(runner.take_output(), vec!["3"]);

        // Now load a bad file
        let bad = dir.join("bad_stale.ttrpg");
        std::fs::write(
            &bad,
            r#"
system "test" {
    derive bad() -> int { undefined_var }
}
"#,
        )
        .unwrap();

        let err = runner
            .exec(&format!("load {}", bad.display()))
            .unwrap_err();
        assert!(err.to_string().contains("failed to load"));
        runner.take_output();

        // Arithmetic still works (no program needed for basic eval)
        runner.exec("eval 1 + 2").unwrap();
        runner.take_output();

        // Reload should re-attempt the bad file, not the good one
        let err = runner.exec("reload").unwrap_err();
        assert!(
            err.to_string().contains("failed to load"),
            "reload should target the bad file, got: {}",
            err
        );
        runner.take_output();

        std::fs::remove_file(&good).ok();
        std::fs::remove_file(&bad).ok();
    }

    #[test]
    fn io_failure_clears_stale_state() {
        let dir = std::env::temp_dir().join("ttrpg_cli_test");
        std::fs::create_dir_all(&dir).unwrap();

        // Load a good file first
        let good = dir.join("good_io.ttrpg");
        std::fs::write(
            &good,
            r#"
system "test" {
    derive add(a: int, b: int) -> int { a + b }
}
"#,
        )
        .unwrap();

        let mut runner = Runner::new();
        runner
            .exec(&format!("load {}", good.display()))
            .unwrap();
        runner.take_output();

        // Now try to load a nonexistent file (I/O failure)
        let err = runner
            .exec("load /nonexistent/path.ttrpg")
            .unwrap_err();
        assert!(err.to_string().contains("cannot read"));
        runner.take_output();

        // Diagnostics should be cleared (I/O failure has no parse diagnostics)
        runner.exec("errors").unwrap();
        let output = runner.take_output();
        assert_eq!(output, vec!["no diagnostics"]);

        // Reload should target the nonexistent file, not the good one
        let err = runner.exec("reload").unwrap_err();
        assert!(
            err.to_string().contains("cannot read"),
            "reload should target the failed path, got: {}",
            err
        );
        runner.take_output();

        std::fs::remove_file(&good).ok();
    }

    #[test]
    fn failed_load_returns_err() {
        let dir = std::env::temp_dir().join("ttrpg_cli_test");
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("test_load_err.ttrpg");
        std::fs::write(
            &path,
            r#"
system "test" {
    derive bad() -> int { undefined_var }
}
"#,
        )
        .unwrap();

        let mut runner = Runner::new();
        let result = runner.exec(&format!("load {}", path.display()));
        assert!(result.is_err(), "load with errors should return Err");
        let err = result.unwrap_err();
        assert!(
            err.to_string().contains("failed to load"),
            "got: {}",
            err
        );

        std::fs::remove_file(&path).ok();
    }
}
