use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap, VecDeque};
use std::path::PathBuf;

use rand::SeedableRng;
use rand::rngs::StdRng;

use ttrpg_ast::Name;
use ttrpg_ast::ast::{DeclKind, OptionalGroup, Program, TopLevel};
use ttrpg_ast::diagnostic::{Diagnostic, MultiSourceMap, Severity};
use ttrpg_ast::module::ModuleMap;
use ttrpg_checker::env::{DeclInfo, FnKind, TypeEnv};
use ttrpg_interp::Interpreter;
use ttrpg_interp::effect::FieldPathSegment;
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::{EntityRef, StateProvider, WritableState};
use ttrpg_interp::value::Value;

use crate::commands::{self, Command};
use crate::effects::{CliHandler, RefCellState};
use crate::format::format_value;

mod assert;
mod config;
mod groups;
mod inspect;
mod load;
mod mutation;
mod parse;
mod util;

#[cfg(test)]
mod tests;

use util::*;

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
    module_map: ModuleMap,
    game_state: RefCell<GameState>,
    last_paths: Vec<PathBuf>,
    diagnostics: Vec<Diagnostic>,
    source_map: Option<MultiSourceMap>,
    output: Vec<String>,
    handles: HashMap<String, EntityRef>,
    reverse_handles: HashMap<EntityRef, String>,
    rng: StdRng,
    roll_queue: VecDeque<i64>,
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
            handles: HashMap::new(),
            reverse_handles: HashMap::new(),
            rng: StdRng::from_os_rng(),
            roll_queue: VecDeque::new(),
        }
    }

    /// Returns all handle names (for tab completion).
    pub fn handle_names(&self) -> Vec<String> {
        self.handles.keys().cloned().collect()
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

    /// Returns field names for a given entity type (for tab completion).
    pub fn field_names(&self, entity_type: &str) -> Vec<String> {
        self.type_env
            .lookup_fields(entity_type)
            .map(|fields| fields.iter().map(|f| f.name.to_string()).collect())
            .unwrap_or_default()
    }

    /// Returns the entity type name for a given handle (for tab completion).
    pub fn handle_type(&self, handle: &str) -> Option<String> {
        let entity = self.handles.get(handle)?;
        let gs = self.game_state.borrow();
        gs.entity_type_name(entity).map(|s| s.to_string())
    }

    /// Returns optional group names for a given entity type (for tab completion).
    pub fn group_names(&self, entity_type: &str) -> Vec<String> {
        match self.type_env.types.get(entity_type) {
            Some(DeclInfo::Entity(info)) => {
                info.optional_groups.iter().map(|g| g.name.to_string()).collect()
            }
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

    /// Execute a single line of input. Output is collected internally.
    pub fn exec(&mut self, line: &str) -> Result<(), CliError> {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with("//") {
            return Ok(());
        }
        self.exec_inner(line)
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
            // Inspection
            Command::Inspect(tail) => self.cmd_inspect(&tail),
            Command::State => self.cmd_state(),
            Command::Types => self.cmd_types(),
            Command::Actions => self.cmd_actions(),
            Command::Mechanics => self.cmd_mechanics(),
            Command::Conditions => self.cmd_conditions(),
            // Assertions
            Command::Assert(expr_str) => self.cmd_assert(&expr_str),
            Command::AssertEq(tail) => self.cmd_assert_eq(&tail),
            Command::AssertErr(tail) => self.cmd_assert_err(&tail),
            // Configuration
            Command::Seed(tail) => self.cmd_seed(&tail),
            Command::Rolls(tail) => self.cmd_rolls(&tail),
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
            return Err(CliError::Message(format!(
                "parse error: {}",
                msgs.join("; ")
            )));
        }
        let parsed =
            parsed.ok_or_else(|| CliError::Message("failed to parse expression".into()))?;

        let interp = Interpreter::new(&self.program, &self.type_env)
            .map_err(|e| CliError::Message(format!("interpreter error: {}", e)))?;

        let state = RefCellState(&self.game_state);
        let mut handler = CliHandler::new(&self.game_state, &self.reverse_handles, &mut self.rng, &mut self.roll_queue);
        let bindings: HashMap<Name, Value> = self
            .handles
            .iter()
            .map(|(name, entity)| (Name::from(name.as_str()), Value::Entity(*entity)))
            .collect();
        let result = interp
            .evaluate_expr_with_bindings(&state, &mut handler, &parsed, bindings)
            .map_err(|e| {
                // Emit any effect log lines even on error
                for line in handler.log.drain(..) {
                    self.output.push(line);
                }
                CliError::Message(format!("runtime error: {}", e))
            })?;

        // Emit any effect log lines
        for line in handler.log.drain(..) {
            self.output.push(line);
        }

        Ok(result)
    }

    /// Resolve a handle name to an EntityRef.
    fn resolve_handle(&self, name: &str) -> Result<EntityRef, CliError> {
        self.handles
            .get(name)
            .copied()
            .ok_or_else(|| CliError::Message(format!("unknown handle: {}", name)))
    }
}

impl Default for Runner {
    fn default() -> Self {
        Self::new()
    }
}
