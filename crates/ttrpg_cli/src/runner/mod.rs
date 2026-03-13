use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::path::PathBuf;
use std::rc::Rc;

use rand::SeedableRng;
use rand::rngs::StdRng;

use ttrpg_ast::Name;
use ttrpg_ast::ast::{AssignOp, DeclKind, FieldDef, Program, TopLevel, TypeExpr};
use ttrpg_ast::diagnostic::{Diagnostic, MultiSourceMap, Severity};
use ttrpg_ast::module::ModuleMap;
use ttrpg_checker::env::{DeclInfo, FnKind, TypeEnv};
use ttrpg_interp::Interpreter;
use ttrpg_interp::coverage::{self, CoverageData};
use ttrpg_interp::effect::FieldPathSegment;
use ttrpg_interp::handle_registry::HandleRegistry;
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::{EntityRef, StateProvider, WritableState};
use ttrpg_interp::value::Value;

use crate::commands::{self, Command};
use crate::effects::CliHandler;
use crate::format::{UnitSuffixes, format_value};

use ttrpg_interp::reference_state::{RefCellState, TrackedInterpreter};

mod assert;
mod config;
mod groups;
mod help;
mod host;
mod inspect;
mod load;
mod mutation;
mod parse;
mod util;

#[cfg(test)]
mod tests;

use ttrpg_interp::RuntimeError;

use util::*;

/// Errors produced by Runner operations.
#[derive(Debug)]
pub enum CliError {
    /// A user-facing message (not a bug).
    Message(String),
    /// A pre-rendered diagnostic with source spans (already includes "error:" prefix).
    Rendered(String),
}

impl CliError {
    /// Returns `true` if this error is already formatted with source spans.
    pub fn is_rendered(&self) -> bool {
        matches!(self, CliError::Rendered(_))
    }
}

impl std::fmt::Display for CliError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CliError::Message(msg) | CliError::Rendered(msg) => write!(f, "{msg}"),
        }
    }
}

/// Convert a `RuntimeError` into a `CliError`, rendering the source span
/// through the `MultiSourceMap` when available.
pub(super) fn render_runtime_error(
    e: &RuntimeError,
    source_map: &Option<MultiSourceMap>,
) -> CliError {
    if let (Some(span), Some(sm)) = (e.span, source_map.as_ref())
        && !span.is_dummy()
    {
        let diag = Diagnostic::error(&e.message, span);
        return CliError::Rendered(sm.render(&diag));
    }
    CliError::Message(format!("runtime error: {}", e.message))
}

/// State for accumulating a multi-line `source <<DELIM ... DELIM` block.
struct HeredocState {
    delimiter: String,
    lines: Vec<String>,
    snippet: bool,
}

/// What kind of loop we're accumulating.
enum LoopKind {
    /// `repeat N { ... }` — run body N times, no variable.
    Repeat { count: usize },
    /// `for VAR in START..END { ... }` or `for VAR in START..=END { ... }`
    For {
        var: String,
        start: i64,
        end: i64,
        inclusive: bool,
    },
    /// `for VAR in EXPR { ... }` — iterate over a list or set.
    ForEach { var: String, items: Vec<Value> },
}

/// State for accumulating a multi-line loop block.
struct LoopState {
    kind: LoopKind,
    lines: Vec<String>,
    brace_depth: i32,
}

/// State for accumulating a multi-line command via backslash continuation
/// or auto-continuation (unclosed delimiters).
struct ContinuationState {
    lines: Vec<String>,
}

/// The core CLI runner. Owns program state and dispatches commands.
pub struct Runner {
    program: Box<Program>,
    type_env: Box<TypeEnv>,
    module_map: ModuleMap,
    game_state: RefCell<GameState>,
    last_paths: Vec<PathBuf>,
    diagnostics: Vec<Diagnostic>,
    source_map: Option<MultiSourceMap>,
    output: Vec<String>,
    handles: HandleRegistry,
    variables: HashMap<String, Value>,
    rng: StdRng,
    roll_queue: VecDeque<i64>,
    prompt_queue: VecDeque<Value>,
    unit_suffixes: UnitSuffixes,
    coverage: Option<Rc<RefCell<CoverageData>>>,
    quiet: bool,
    interactive: bool,
    heredoc: Option<HeredocState>,
    continuation: Option<ContinuationState>,
    loop_state: Option<LoopState>,
    /// Prior zone membership: `(target_id, zone_id) -> is_inside`.
    /// Tracked across `zone_sync` calls for membership diffing.
    zone_membership: HashSet<(u64, u64)>,
}

impl Runner {
    /// Create a new runner with empty program state.
    pub fn new() -> Self {
        Runner {
            program: Box::new(Program::default()),
            type_env: Box::new(TypeEnv::new()),
            module_map: ModuleMap::default(),
            game_state: RefCell::new(GameState::new()),
            last_paths: Vec::new(),
            diagnostics: Vec::new(),
            source_map: None,
            output: Vec::new(),
            handles: HandleRegistry::new(),
            variables: HashMap::new(),
            rng: StdRng::from_os_rng(),
            roll_queue: VecDeque::new(),
            prompt_queue: VecDeque::new(),
            unit_suffixes: UnitSuffixes::new(),
            coverage: None,
            quiet: false,
            interactive: false,
            heredoc: None,
            continuation: None,
            loop_state: None,
            zone_membership: HashSet::new(),
        }
    }

    /// Returns all handle names (for tab completion).
    pub fn handle_names(&self) -> Vec<String> {
        self.handles.names().map(|s| s.to_string()).collect()
    }

    /// Returns all entity type names (for tab completion).
    pub fn entity_type_names(&self) -> Vec<String> {
        self.type_env
            .types
            .iter()
            .filter(|(_, info)| matches!(info, DeclInfo::Entity(_)))
            .map(|(name, _)| name.to_string())
            .collect()
    }

    /// Returns all action names (for tab completion).
    pub fn action_names(&self) -> Vec<String> {
        self.type_env
            .functions
            .values()
            .filter(|fi| matches!(fi.kind, FnKind::Action))
            .map(|fi| fi.name.to_string())
            .collect()
    }

    /// Returns all derive names (for tab completion).
    pub fn derive_names(&self) -> Vec<String> {
        self.type_env
            .functions
            .values()
            .filter(|fi| matches!(fi.kind, FnKind::Derive))
            .map(|fi| fi.name.to_string())
            .collect()
    }

    /// Returns all mechanic names (for tab completion).
    pub fn mechanic_names(&self) -> Vec<String> {
        self.type_env
            .functions
            .values()
            .filter(|fi| matches!(fi.kind, FnKind::Mechanic))
            .map(|fi| fi.name.to_string())
            .collect()
    }

    /// Returns all function block names (for tab completion).
    pub fn function_names(&self) -> Vec<String> {
        self.type_env
            .functions
            .values()
            .filter(|fi| matches!(fi.kind, FnKind::Function))
            .map(|fi| fi.name.to_string())
            .collect()
    }

    /// Returns all declared option names (for tab completion).
    pub fn option_names(&self) -> Vec<String> {
        self.type_env
            .options
            .iter()
            .map(|n| n.to_string())
            .collect()
    }

    /// Returns field names for a given entity type (for tab completion).
    pub fn field_names(&self, entity_type: &str) -> Vec<String> {
        self.type_env
            .lookup_fields(entity_type)
            .map(|fields| fields.iter().map(|f| f.name.to_string()).collect())
            .unwrap_or_default()
    }

    /// Returns the entity type name for a given handle (for tab completion).
    pub fn handle_type(&self, handle: &str) -> Option<String> {
        let entity = match self.variables.get(handle)? {
            Value::Entity(e) => *e,
            _ => return None,
        };
        let gs = self.game_state.borrow();
        gs.entity_type_name(&entity).map(|s| s.to_string())
    }

    /// Returns optional group names for a given entity type (for tab completion).
    pub fn group_names(&self, entity_type: &str) -> Vec<String> {
        match self.type_env.types.get(entity_type) {
            Some(DeclInfo::Entity(info)) => info
                .optional_groups
                .iter()
                .map(|g| g.name.to_string())
                .collect(),
            _ => Vec::new(),
        }
    }

    /// Returns field names within an optional group (for tab completion).
    pub fn group_field_names(&self, entity_type: &str, group_name: &str) -> Vec<String> {
        self.type_env
            .lookup_optional_group(entity_type, group_name)
            .map(|g| g.fields.iter().map(|f| f.name.to_string()).collect())
            .unwrap_or_default()
    }

    /// Returns true if a program has been loaded.
    pub fn is_loaded(&self) -> bool {
        !self.program.items.is_empty()
    }

    /// Returns `true` when the runner is inside a `source <<DELIM` block
    /// and waiting for the closing delimiter.
    pub fn in_heredoc(&self) -> bool {
        self.heredoc.is_some()
    }

    /// Returns `true` when the runner is accumulating a multi-line command
    /// (backslash continuation or unclosed delimiters).
    pub fn in_continuation(&self) -> bool {
        self.continuation.is_some()
    }

    /// Returns `true` when the runner is accumulating a loop block body.
    pub fn in_loop(&self) -> bool {
        self.loop_state.is_some()
    }

    /// Cancel any in-progress continuation (e.g. on Ctrl-C).
    pub fn cancel_continuation(&mut self) {
        self.continuation = None;
        self.heredoc = None;
        self.loop_state = None;
    }

    /// Execute a single line of input. Output is collected internally.
    pub fn exec(&mut self, line: &str) -> Result<(), CliError> {
        // If we're inside a heredoc block, accumulate or close.
        if let Some(ref mut state) = self.heredoc {
            if line.trim() == state.delimiter {
                let source = std::mem::take(&mut state.lines).join("\n");
                let snippet = state.snippet;
                self.heredoc = None;
                return self.cmd_source(&source, snippet);
            }
            state.lines.push(line.to_string());
            return Ok(());
        }

        // If we're inside a loop block, accumulate or close.
        if let Some(ref mut state) = self.loop_state {
            let trimmed = line.trim();
            // Track brace depth (string-aware)
            let delta = brace_delta(trimmed);
            state.brace_depth += delta;
            if state.brace_depth <= 0 {
                // Closing brace reached — execute the loop
                let state = self.loop_state.take().unwrap();
                return self.exec_loop(state);
            }
            state.lines.push(line.to_string());
            return Ok(());
        }

        // Handle line continuation (backslash or unclosed delimiters).
        if let Some(ref mut state) = self.continuation {
            state.lines.push(line.to_string());
            let joined = state.lines.join(" ");
            let trimmed = joined.trim();

            // Check for explicit backslash continuation
            if let Some(stripped) = trimmed.strip_suffix('\\') {
                // Still continuing — update the stored line without the backslash
                state.lines = vec![stripped.to_string()];
                return Ok(());
            }

            // Check if delimiters are now balanced
            if delimiters_balanced(trimmed) {
                self.continuation = None;
                return self.exec_continued(&joined);
            }
            return Ok(());
        }

        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with("//") {
            return Ok(());
        }

        // Check for `source [-s] <<DELIM`
        if (trimmed.starts_with("source ") || trimmed == "source")
            && let Some(heredoc) = Self::parse_source_heredoc(trimmed)
        {
            self.heredoc = Some(heredoc);
            return Ok(());
        }

        // Check for loop start before continuation — `repeat N {` and
        // `for VAR in RANGE {` have an intentionally unbalanced `{`.
        if (trimmed.starts_with("repeat ") || trimmed.starts_with("for "))
            && let Some(cmd) = commands::parse_command(trimmed) {
                match cmd {
                    commands::Command::Repeat(tail) => return self.cmd_repeat(&tail),
                    commands::Command::For(tail) => return self.cmd_for(&tail),
                    _ => {}
                }
            }

        // Check for explicit backslash continuation
        if let Some(stripped) = trimmed.strip_suffix('\\') {
            self.continuation = Some(ContinuationState {
                lines: vec![stripped.to_string()],
            });
            return Ok(());
        }

        // Check for unclosed delimiters (auto-continuation)
        if !delimiters_balanced(trimmed) {
            self.continuation = Some(ContinuationState {
                lines: vec![line.to_string()],
            });
            return Ok(());
        }

        self.exec_inner(line)
    }

    /// Execute a command that was assembled from continuation lines.
    fn exec_continued(&mut self, line: &str) -> Result<(), CliError> {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with("//") {
            return Ok(());
        }

        // Check for `source [-s] <<DELIM`
        if (trimmed.starts_with("source ") || trimmed == "source")
            && let Some(heredoc) = Self::parse_source_heredoc(trimmed)
        {
            self.heredoc = Some(heredoc);
            return Ok(());
        }

        self.exec_inner(line)
    }

    /// Try to parse `source [-s] <<DELIM` from a trimmed line.
    fn parse_source_heredoc(trimmed: &str) -> Option<HeredocState> {
        let rest = trimmed.strip_prefix("source")?.trim_start();
        let (snippet, rest) = if let Some(after_s) = rest.strip_prefix("-s") {
            (true, after_s.trim_start())
        } else {
            (false, rest)
        };
        let delim = rest.strip_prefix("<<")?.trim_start();
        if delim.is_empty() {
            return None;
        }
        Some(HeredocState {
            delimiter: delim.to_string(),
            lines: Vec::new(),
            snippet,
        })
    }

    /// Parse and begin a `repeat N {` loop.
    fn cmd_repeat(&mut self, tail: &str) -> Result<(), CliError> {
        // Expect "N {" — the opening brace must be on this line
        let tail = tail.trim();
        let (count_str, rest) = split_first_token(tail);
        let count: usize = count_str.parse().map_err(|_| {
            CliError::Message(format!("repeat: expected integer count, got '{count_str}'"))
        })?;
        let rest = rest.trim();
        if rest != "{" {
            return Err(CliError::Message(
                "repeat: expected '{' after count (e.g. `repeat 5 {`)".into(),
            ));
        }
        self.loop_state = Some(LoopState {
            kind: LoopKind::Repeat { count },
            lines: Vec::new(),
            brace_depth: 1,
        });
        Ok(())
    }

    /// Parse and begin a `for VAR in START..END {` loop.
    fn cmd_for(&mut self, tail: &str) -> Result<(), CliError> {
        // Expect "VAR in START..END {" or "VAR in START..=END {"
        let tail = tail.trim();

        // Parse: VAR in RANGE {
        let (var, rest) = split_first_token(tail);
        if !is_valid_handle(var) {
            return Err(CliError::Message(format!(
                "for: expected variable name, got '{var}'"
            )));
        }
        let rest = rest.trim();
        let rest = rest
            .strip_prefix("in ")
            .or_else(|| rest.strip_prefix("in\t"))
            .ok_or_else(|| CliError::Message("for: expected 'in' after variable name".into()))?
            .trim();

        // Find the opening brace
        let brace_pos = rest.rfind('{').ok_or_else(|| {
            CliError::Message("for: expected '{' (e.g. `for i in 0..10 {`)".into())
        })?;
        let range_str = rest[..brace_pos].trim();
        let after_brace = rest[brace_pos + 1..].trim();
        if !after_brace.is_empty() {
            return Err(CliError::Message(
                "for: '{' must be the last token on the line".into(),
            ));
        }

        // Try to parse as range: START..=END or START..END
        let loop_kind = if let Some((left, right)) = range_str.split_once("..=") {
            if let (Ok(s), Ok(e)) = (left.trim().parse::<i64>(), right.trim().parse::<i64>()) {
                LoopKind::For {
                    var: var.to_string(),
                    start: s,
                    end: e,
                    inclusive: true,
                }
            } else {
                // Not a valid integer range — try as expression
                self.for_each_kind(var, range_str)?
            }
        } else if let Some((left, right)) = range_str.split_once("..") {
            if let (Ok(s), Ok(e)) = (left.trim().parse::<i64>(), right.trim().parse::<i64>()) {
                LoopKind::For {
                    var: var.to_string(),
                    start: s,
                    end: e,
                    inclusive: false,
                }
            } else {
                // Not a valid integer range — try as expression
                self.for_each_kind(var, range_str)?
            }
        } else {
            // No '..' found — evaluate as expression (list/set iteration)
            self.for_each_kind(var, range_str)?
        };

        self.loop_state = Some(LoopState {
            kind: loop_kind,
            lines: Vec::new(),
            brace_depth: 1,
        });
        Ok(())
    }

    /// Evaluate an expression and build a `ForEach` loop kind from it.
    fn for_each_kind(&mut self, var: &str, expr_str: &str) -> Result<LoopKind, CliError> {
        let value = self.eval(expr_str)?;
        let items = match value {
            Value::List(items) => items,
            Value::Set(items) => items.into_iter().collect(),
            other => {
                return Err(CliError::Message(format!(
                    "for: expected list or set, got {}",
                    format_value(&other, &self.unit_suffixes)
                )));
            }
        };
        Ok(LoopKind::ForEach {
            var: var.to_string(),
            items,
        })
    }

    /// Execute a completed loop block.
    fn exec_loop(&mut self, state: LoopState) -> Result<(), CliError> {
        match state.kind {
            LoopKind::Repeat { count } => {
                for _ in 0..count {
                    for line in &state.lines {
                        self.exec(line)?;
                    }
                }
            }
            LoopKind::For {
                ref var,
                start,
                end,
                inclusive,
            } => {
                let range_end = if inclusive { end + 1 } else { end };
                for i in start..range_end {
                    self.variables.insert(var.clone(), Value::Int(i));
                    for line in &state.lines {
                        self.exec(line)?;
                    }
                }
                self.variables.remove(var);
            }
            LoopKind::ForEach { ref var, ref items } => {
                for item in items {
                    self.variables.insert(var.clone(), item.clone());
                    for line in &state.lines {
                        self.exec(line)?;
                    }
                }
                self.variables.remove(var);
            }
        }
        Ok(())
    }

    /// Inner dispatch — called by `exec` and also by `cmd_assert_err`.
    fn exec_inner(&mut self, line: &str) -> Result<(), CliError> {
        let cmd = match commands::parse_command(line) {
            Some(cmd) => cmd,
            None => return Ok(()), // blank or comment-only line
        };

        match cmd {
            Command::Load(path) => self.cmd_load(&path),
            Command::Eval(expr_str) => self.cmd_eval(&expr_str),
            Command::Reload => self.cmd_reload(),
            Command::Errors => self.cmd_errors(),
            Command::Spawn(tail) => self.cmd_spawn(&tail),
            Command::Set(tail) => self.cmd_set(&tail),
            Command::Destroy(handle) => self.cmd_destroy(&handle),
            Command::Do(tail) => self.cmd_do(&tail),
            Command::Call(tail) => self.cmd_call(&tail),
            Command::Grant(tail) => self.cmd_grant(&tail),
            Command::Revoke(tail) => self.cmd_revoke(&tail),
            // Variables
            Command::Let(tail) => self.cmd_let(&tail),
            // Inspection
            Command::Inspect(tail) => self.cmd_inspect(&tail),
            Command::State => self.cmd_state(),
            Command::Types => self.cmd_types(),
            Command::Entity(name) => self.cmd_entity(&name),
            Command::Actions => self.cmd_actions(),
            Command::Mechanics => self.cmd_mechanics(),
            Command::Functions => self.cmd_functions(),
            Command::Conditions => self.cmd_conditions(),
            Command::Reactions => self.cmd_reactions(),
            Command::Hooks => self.cmd_hooks(),
            Command::Events => self.cmd_events(),
            Command::ConditionDecls => self.cmd_condition_decls(),
            // Options
            Command::Enable(name) => self.cmd_enable(&name),
            Command::Disable(name) => self.cmd_disable(&name),
            Command::Options => self.cmd_options(),
            // Assertions
            Command::Assert(expr_str) => self.cmd_assert(&expr_str),
            Command::AssertEq(tail) => self.cmd_assert_eq(&tail),
            Command::AssertNe(tail) => self.cmd_assert_ne(&tail),
            Command::AssertMatch(tail) => self.cmd_assert_match(&tail),
            Command::AssertErr(tail) => self.cmd_assert_err(&tail),
            Command::AssertCondition(tail) => self.cmd_assert_condition(&tail),
            Command::AssertNoCondition(tail) => self.cmd_assert_no_condition(&tail),
            // Provenance
            Command::Breakdown(tail) => self.cmd_breakdown(&tail),
            // Host simulation
            Command::Emit(tail) => self.cmd_emit(&tail),
            Command::Place(tail) => self.cmd_place(&tail),
            Command::Pos(tail) => self.cmd_pos(&tail),
            Command::ZoneSync => self.cmd_zone_sync(),
            // Coverage
            Command::Coverage => self.cmd_coverage(),
            Command::CoverageReset => self.cmd_coverage_reset(),
            // Configuration
            Command::Seed(tail) => self.cmd_seed(&tail),
            Command::Rolls(tail) => self.cmd_rolls(&tail),
            Command::Prompts(tail) => self.cmd_prompts(&tail),
            // Help
            Command::Help(topic) => self.cmd_help(topic.as_deref()),
            // Loops
            Command::Repeat(tail) => self.cmd_repeat(&tail),
            Command::For(tail) => self.cmd_for(&tail),
            Command::Unknown(kw) => {
                if help::is_known_command(&kw) {
                    self.help_command(&kw)
                } else {
                    Err(CliError::Message(format!("unknown command: {kw}")))
                }
            }
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
            return Err(CliError::Message(format!(
                "parse error: {}",
                msgs.join("; ")
            )));
        }
        let parsed =
            parsed.ok_or_else(|| CliError::Message("failed to parse expression".into()))?;

        let cov_rc = self.coverage_rc();
        let mut interp = TrackedInterpreter::new(&self.program, &self.type_env, &self.game_state)
            .map_err(|e| render_runtime_error(&e, &self.source_map))?;
        if let Some(cov) = cov_rc {
            interp.interp.set_coverage(cov);
        }

        let state = RefCellState(&self.game_state);
        let mut handler = CliHandler::new(
            &self.game_state,
            self.handles.by_entity(),
            &mut self.rng,
            &mut self.roll_queue,
            &mut self.prompt_queue,
            &self.unit_suffixes,
        )
        .quiet(self.quiet)
        .interactive(self.interactive);
        let bindings: rustc_hash::FxHashMap<Name, Value> = self
            .variables
            .iter()
            .map(|(name, val)| (Name::from(name.as_str()), val.clone()))
            .collect();
        let result = interp
            .evaluate_expr_with_bindings(&state, &mut handler, &parsed, bindings)
            .map_err(|e| {
                // Emit any effect log lines even on error
                for line in handler.log.drain(..) {
                    self.output.push(line);
                }
                render_runtime_error(&e, &self.source_map)
            })?;

        // Emit any effect log lines
        for line in handler.log.drain(..) {
            self.output.push(line);
        }

        Ok(result)
    }

    /// Resolve a handle name to an EntityRef.
    fn resolve_handle(&self, name: &str) -> Result<EntityRef, CliError> {
        match self.variables.get(name) {
            Some(Value::Entity(entity)) => Ok(*entity),
            Some(_) => Err(CliError::Message(format!(
                "'{name}' is not an entity"
            ))),
            None => Err(CliError::Message(format!("unknown handle: {name}"))),
        }
    }

    /// Enable quiet mode: suppress effect handler log output.
    /// Only errors and assertion failures are shown.
    pub fn set_quiet(&mut self, quiet: bool) {
        self.quiet = quiet;
    }

    /// Set interactive mode. When `true`, prompts without a queued
    /// response block for user input via stdin. When `false` (the
    /// default), the handler auto-resolves using `suggest` or `UseDefault`.
    pub fn set_interactive(&mut self, interactive: bool) {
        self.interactive = interactive;
    }

    /// Returns whether the runner is in interactive mode.
    pub fn is_interactive(&self) -> bool {
        self.interactive
    }

    /// Enable coverage tracking. Creates the shared `Rc` that will be
    /// attached to every interpreter instance created via `make_interpreter`.
    pub fn enable_coverage(&mut self) {
        self.coverage = Some(Rc::new(RefCell::new(CoverageData::new())));
    }

    /// Returns a clone of the coverage `Rc` (if coverage is enabled).
    /// Cheap to clone since it's just an `Rc` bump.
    pub(super) fn coverage_rc(&self) -> Option<Rc<RefCell<CoverageData>>> {
        self.coverage.clone()
    }

    /// Returns a reference to the shared coverage data (if coverage is enabled).
    pub fn coverage_data(&self) -> Option<&Rc<RefCell<CoverageData>>> {
        self.coverage.as_ref()
    }

    /// `coverage` command — render a coverage report.
    fn cmd_coverage(&mut self) -> Result<(), CliError> {
        let cov = match &self.coverage {
            Some(cov) => cov,
            None => {
                return Err(CliError::Message(
                    "coverage not enabled (start with --coverage flag)".into(),
                ));
            }
        };

        let sm = match &self.source_map {
            Some(sm) => sm,
            None => {
                return Err(CliError::Message(
                    "no source files loaded — load a file first".into(),
                ));
            }
        };

        let mut sources = Vec::new();
        for i in 0..sm.file_count() {
            if let Some((filename, source, line_starts)) = sm.file_info(i) {
                sources.push(coverage::CoverageSource {
                    filename: filename.to_string(),
                    source: source.to_string(),
                    file_id: i as u32,
                    line_starts: line_starts.to_vec(),
                });
            }
        }

        let data = cov.borrow();
        let report = coverage::render_coverage_report(&data, &sources, &self.program);
        self.output.push(report);
        Ok(())
    }

    /// `coverage reset` command — clear coverage data.
    fn cmd_coverage_reset(&mut self) -> Result<(), CliError> {
        match &self.coverage {
            Some(cov) => {
                cov.borrow_mut().reset();
                self.output.push("coverage data reset".to_string());
                Ok(())
            }
            None => Err(CliError::Message(
                "coverage not enabled (start with --coverage flag)".into(),
            )),
        }
    }
}

impl Default for Runner {
    fn default() -> Self {
        Self::new()
    }
}
