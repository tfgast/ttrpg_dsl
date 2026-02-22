use std::cell::RefCell;
use std::collections::HashMap;
use std::path::PathBuf;

use rand::SeedableRng;
use rand::rngs::StdRng;
use ttrpg_ast::ast::Program;
use ttrpg_ast::diagnostic::{Diagnostic, Severity};
use ttrpg_checker::env::TypeEnv;
use ttrpg_checker::ty::Ty;
use ttrpg_interp::Interpreter;
use ttrpg_interp::effect::FieldPathSegment;
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::{EntityRef, WritableState};
use ttrpg_interp::value::Value;

use crate::commands::{self, Command};
use crate::effects::{CliHandler, MinimalHandler, RefCellState};
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
    game_state: RefCell<GameState>,
    last_path: Option<PathBuf>,
    diagnostics: Vec<Diagnostic>,
    output: Vec<String>,
    handles: HashMap<String, EntityRef>,
    reverse_handles: HashMap<EntityRef, String>,
    rng: StdRng,
}

impl Runner {
    /// Create a new runner with empty program state.
    pub fn new() -> Self {
        Runner {
            program: Box::new(Program { items: Vec::new() }),
            type_env: Box::new(TypeEnv::new()),
            game_state: RefCell::new(GameState::new()),
            last_path: None,
            diagnostics: Vec::new(),
            output: Vec::new(),
            handles: HashMap::new(),
            reverse_handles: HashMap::new(),
            rng: StdRng::from_os_rng(),
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
            Command::Spawn(tail) => self.cmd_spawn(&tail),
            Command::Set(tail) => self.cmd_set(&tail),
            Command::Destroy(handle) => self.cmd_destroy(&handle),
            Command::Do(tail) => self.cmd_do(&tail),
            Command::Call(tail) => self.cmd_call(&tail),
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
        let mut handler = CliHandler::new(&self.game_state, &self.reverse_handles, &mut self.rng);
        let result = interp
            .evaluate_expr(&state, &mut handler, &parsed)
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

    // ── Command handlers ────────────────────────────────────────

    fn cmd_load(&mut self, path: &str) -> Result<(), CliError> {
        let source = match std::fs::read_to_string(path) {
            Ok(s) => s,
            Err(e) => {
                // Clear stale state so a previous successful load doesn't linger.
                self.program = Box::new(Program { items: Vec::new() });
                self.type_env = Box::new(TypeEnv::new());
                self.game_state = RefCell::new(GameState::new());
                self.diagnostics = Vec::new();
                self.last_path = Some(PathBuf::from(path));
                self.handles.clear();
                self.reverse_handles.clear();
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
            self.game_state = RefCell::new(GameState::new());
            self.diagnostics = all_diags;
            self.last_path = Some(PathBuf::from(path));
            self.handles.clear();
            self.reverse_handles.clear();
            self.output.push(format!("loaded {}", path));
            Ok(())
        } else {
            let error_count = errors.len();
            // Clear stale program state so eval cannot use a previous successful load.
            self.program = Box::new(Program { items: Vec::new() });
            self.type_env = Box::new(TypeEnv::new());
            self.game_state = RefCell::new(GameState::new());
            self.diagnostics = all_diags;
            self.last_path = Some(PathBuf::from(path));
            self.handles.clear();
            self.reverse_handles.clear();
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

    /// `spawn <EntityType> <handle> { field: value, ... }`
    fn cmd_spawn(&mut self, tail: &str) -> Result<(), CliError> {
        // Extract entity type and handle
        let tail = tail.trim();

        // Split into: type, handle, optional { ... }
        let (entity_type, rest) = split_first_token(tail);
        if entity_type.is_empty() {
            return Err(CliError::Message(
                "usage: spawn <EntityType> <handle> [{ field: value, ... }]".into(),
            ));
        }
        let rest = rest.trim();
        let (handle, rest) = split_first_token(rest);
        if handle.is_empty() {
            return Err(CliError::Message(
                "usage: spawn <EntityType> <handle> [{ field: value, ... }]".into(),
            ));
        }

        if !is_valid_handle(handle) {
            return Err(CliError::Message(format!(
                "invalid handle '{}': must be a bare identifier",
                handle
            )));
        }

        if self.handles.contains_key(handle) {
            return Err(CliError::Message(format!(
                "handle '{}' already exists",
                handle
            )));
        }

        // Validate entity type against loaded declarations
        match self.type_env.types.get(entity_type) {
            Some(ttrpg_checker::env::DeclInfo::Entity(_)) => {} // valid
            Some(_) => {
                return Err(CliError::Message(format!(
                    "'{}' is not an entity type",
                    entity_type
                )));
            }
            None => {
                return Err(CliError::Message(format!(
                    "unknown entity type '{}'",
                    entity_type
                )));
            }
        }

        // Parse optional field block
        let rest = rest.trim();
        let fields = if rest.starts_with('{') {
            // Find matching closing brace
            let block = rest
                .strip_prefix('{')
                .and_then(|s| s.strip_suffix('}'))
                .ok_or_else(|| CliError::Message("unmatched '{' in spawn".into()))?;
            self.parse_field_block(block)?
        } else if rest.is_empty() {
            HashMap::new()
        } else {
            return Err(CliError::Message(format!(
                "unexpected text after handle: {}",
                rest
            )));
        };

        // Validate field names and types against entity schema
        if let Some(schema_fields) = self.type_env.lookup_fields(entity_type) {
            for (field_name, field_val) in &fields {
                match schema_fields.iter().find(|f| f.name == *field_name) {
                    None => {
                        return Err(CliError::Message(format!(
                            "unknown field '{}' on entity type '{}'",
                            field_name, entity_type
                        )));
                    }
                    Some(fi) => {
                        if !value_matches_ty(field_val, &fi.ty) {
                            return Err(CliError::Message(format!(
                                "type mismatch for field '{}': expected {}, got {}",
                                field_name,
                                fi.ty.display(),
                                value_type_display(field_val)
                            )));
                        }
                    }
                }
            }
        }

        let entity = self.game_state.borrow_mut().add_entity(entity_type, fields);
        self.handles.insert(handle.to_string(), entity);
        self.reverse_handles.insert(entity, handle.to_string());
        self.output.push(format!(
            "spawned {} {} ({})",
            entity_type,
            handle,
            entity.0
        ));
        Ok(())
    }

    /// `set <handle>.<field> = <value>`
    fn cmd_set(&mut self, tail: &str) -> Result<(), CliError> {
        let tail = tail.trim();

        // Split on '='
        let eq_pos = tail
            .find('=')
            .ok_or_else(|| CliError::Message("usage: set <handle>.<field> = <value>".into()))?;
        let lhs = tail[..eq_pos].trim();
        let rhs = tail[eq_pos + 1..].trim();

        if rhs.is_empty() {
            return Err(CliError::Message("missing value after '='".into()));
        }

        // Split lhs on first '.'
        let dot_pos = lhs
            .find('.')
            .ok_or_else(|| CliError::Message("usage: set <handle>.<field> = <value>".into()))?;
        let handle = &lhs[..dot_pos];
        let field = &lhs[dot_pos + 1..];

        if handle.is_empty() || field.is_empty() {
            return Err(CliError::Message("usage: set <handle>.<field> = <value>".into()));
        }

        let entity = self.resolve_handle(handle)?;

        // Validate field name against entity schema (borrow scoped before eval)
        let expected_ty = {
            let gs = self.game_state.borrow();
            if let Some(type_name) = gs.entity_type_name(&entity) {
                if let Some(schema_fields) = self.type_env.lookup_fields(type_name) {
                    match schema_fields.iter().find(|f| f.name == field) {
                        Some(fi) => Some(fi.ty.clone()),
                        None => {
                            return Err(CliError::Message(format!(
                                "unknown field '{}' on entity type '{}'",
                                field, type_name
                            )));
                        }
                    }
                } else {
                    None
                }
            } else {
                None
            }
        };

        // Parse and evaluate the RHS expression (try handle resolution first)
        let val = if let Some(&ent) = self.handles.get(rhs) {
            Value::Entity(ent)
        } else {
            self.eval(rhs)?
        };

        // Validate type compatibility
        if let Some(ref ty) = expected_ty {
            if !value_matches_ty(&val, ty) {
                return Err(CliError::Message(format!(
                    "type mismatch for field '{}': expected {}, got {}",
                    field,
                    ty.display(),
                    value_type_display(&val)
                )));
            }
        }

        // Write directly to GameState
        self.game_state.borrow_mut().write_field(
            &entity,
            &[FieldPathSegment::Field(field.to_string())],
            val.clone(),
        );
        self.output.push(format!(
            "{}.{} = {}",
            handle,
            field,
            format_value(&val)
        ));
        Ok(())
    }

    /// `destroy <handle>`
    fn cmd_destroy(&mut self, tail: &str) -> Result<(), CliError> {
        let handle = tail.trim();
        if handle.is_empty() {
            return Err(CliError::Message("usage: destroy <handle>".into()));
        }

        let entity = self.resolve_handle(handle)?;
        let removed = self.game_state.borrow_mut().remove_entity(&entity);
        if !removed {
            return Err(CliError::Message(format!(
                "entity for handle '{}' not found in state",
                handle
            )));
        }
        self.handles.remove(handle);
        self.reverse_handles.remove(&entity);
        self.output.push(format!("destroyed {}", handle));
        Ok(())
    }

    /// `do <Action>(actor, args...)`
    fn cmd_do(&mut self, tail: &str) -> Result<(), CliError> {
        let tail = tail.trim();

        // Parse: Name(arg1, arg2, ...)
        let paren_pos = tail
            .find('(')
            .ok_or_else(|| CliError::Message("usage: do <Action>(actor, args...)".into()))?;
        let action_name = tail[..paren_pos].trim();
        if action_name.is_empty() {
            return Err(CliError::Message("missing action name".into()));
        }

        let args_str = tail[paren_pos + 1..]
            .strip_suffix(')')
            .ok_or_else(|| CliError::Message("unmatched '(' in do".into()))?;

        let arg_strs = split_top_level_commas(args_str);
        if arg_strs.is_empty() || arg_strs[0].trim().is_empty() {
            return Err(CliError::Message(
                "do requires at least an actor argument".into(),
            ));
        }

        // Validate no empty args (e.g. "do Act(fighter,,target)")
        for (i, arg_str) in arg_strs.iter().enumerate() {
            if i > 0 && arg_str.trim().is_empty() {
                return Err(CliError::Message("empty argument in do".into()));
            }
        }

        // Check that the action exists before evaluating args (avoid side effects)
        {
            let interp = Interpreter::new(&self.program, &self.type_env)
                .map_err(|e| CliError::Message(format!("interpreter error: {}", e)))?;
            if !interp.has_action(action_name) {
                return Err(CliError::Message(format!(
                    "undefined action '{}'",
                    action_name
                )));
            }
        }

        // First arg is the actor handle
        let actor_str = arg_strs[0].trim();
        let actor = self.resolve_handle(actor_str)?;

        // Remaining args: try handle resolution first, then parse as expression
        let mut args = Vec::new();
        for arg_str in &arg_strs[1..] {
            let arg_str = arg_str.trim();
            if let Some(&entity) = self.handles.get(arg_str) {
                args.push(Value::Entity(entity));
            } else {
                let val = self.eval(arg_str)?;
                args.push(val);
            }
        }

        let interp = Interpreter::new(&self.program, &self.type_env)
            .map_err(|e| CliError::Message(format!("interpreter error: {}", e)))?;
        let state = RefCellState(&self.game_state);
        let mut handler =
            CliHandler::new(&self.game_state, &self.reverse_handles, &mut self.rng);

        let result = interp
            .execute_action(&state, &mut handler, action_name, actor, args)
            .map_err(|e| {
                // Emit effect log even on error
                for line in handler.log.drain(..) {
                    self.output.push(line);
                }
                CliError::Message(format!("runtime error: {}", e))
            })?;

        // Emit effect log
        for line in handler.log.drain(..) {
            self.output.push(line);
        }

        self.output.push(format!("=> {}", format_value(&result)));
        Ok(())
    }

    /// `call <fn>(args...)`
    fn cmd_call(&mut self, tail: &str) -> Result<(), CliError> {
        let tail = tail.trim();

        // Parse: Name(arg1, arg2, ...)
        let paren_pos = tail
            .find('(')
            .ok_or_else(|| CliError::Message("usage: call <fn>(args...)".into()))?;
        let fn_name = tail[..paren_pos].trim();
        if fn_name.is_empty() {
            return Err(CliError::Message("missing function name".into()));
        }

        let args_str = tail[paren_pos + 1..]
            .strip_suffix(')')
            .ok_or_else(|| CliError::Message("unmatched '(' in call".into()))?;

        let arg_strs = split_top_level_commas(args_str);

        // Reject empty positional arguments (e.g. "call f(1,,2)")
        // Only skip the single-empty-string case from `call f()`
        let has_args = !(arg_strs.len() == 1 && arg_strs[0].trim().is_empty());
        if has_args {
            for arg_str in &arg_strs {
                if arg_str.trim().is_empty() {
                    return Err(CliError::Message("empty argument in call".into()));
                }
            }
        }

        // Check that the derive or mechanic exists before evaluating args
        let is_derive;
        let is_mechanic;
        {
            let interp = Interpreter::new(&self.program, &self.type_env)
                .map_err(|e| CliError::Message(format!("interpreter error: {}", e)))?;
            is_derive = interp.has_derive(fn_name);
            is_mechanic = interp.has_mechanic(fn_name);
        }
        if !is_derive && !is_mechanic {
            return Err(CliError::Message(format!(
                "undefined function '{}' (no derive or mechanic with that name)",
                fn_name
            )));
        }

        // Evaluate arguments: try handle resolution first, then parse as expression
        let mut args = Vec::new();
        if has_args {
            for arg_str in &arg_strs {
                let arg_str = arg_str.trim();
                if let Some(&entity) = self.handles.get(arg_str) {
                    args.push(Value::Entity(entity));
                } else {
                    let val = self.eval(arg_str)?;
                    args.push(val);
                }
            }
        }

        let interp = Interpreter::new(&self.program, &self.type_env)
            .map_err(|e| CliError::Message(format!("interpreter error: {}", e)))?;
        let state = RefCellState(&self.game_state);
        let mut handler =
            CliHandler::new(&self.game_state, &self.reverse_handles, &mut self.rng);

        // Dispatch to derive or mechanic based on structured check
        let result = if is_derive {
            interp
                .evaluate_derive(&state, &mut handler, fn_name, args)
                .map_err(|e| {
                    for line in handler.log.drain(..) {
                        self.output.push(line);
                    }
                    CliError::Message(format!("runtime error: {}", e))
                })?
        } else {
            interp
                .evaluate_mechanic(&state, &mut handler, fn_name, args)
                .map_err(|e| {
                    for line in handler.log.drain(..) {
                        self.output.push(line);
                    }
                    CliError::Message(format!("runtime error: {}", e))
                })?
        };

        // Emit effect log
        for line in handler.log.drain(..) {
            self.output.push(line);
        }

        self.output.push(format!("=> {}", format_value(&result)));
        Ok(())
    }

    // ── Parsing helpers ──────────────────────────────────────────

    /// Parse a field block like `key: expr, key: expr` into a HashMap.
    fn parse_field_block(&mut self, block: &str) -> Result<HashMap<String, Value>, CliError> {
        let mut fields = HashMap::new();
        let entries = split_top_level_commas(block);
        for entry in entries {
            let entry = entry.trim();
            if entry.is_empty() {
                continue;
            }
            let colon_pos = entry
                .find(':')
                .ok_or_else(|| CliError::Message(format!("expected 'key: value' in field block, got: {}", entry)))?;
            let key = entry[..colon_pos].trim();
            let val_str = entry[colon_pos + 1..].trim();
            if key.is_empty() || val_str.is_empty() {
                return Err(CliError::Message(format!(
                    "invalid field entry: {}",
                    entry
                )));
            }

            // Try handle resolution first, then fall back to expression eval
            let val = if let Some(&ent) = self.handles.get(val_str) {
                Value::Entity(ent)
            } else {
                let (parsed, diags) = ttrpg_parser::parse_expr(val_str);
                if !diags.is_empty() {
                    let msgs: Vec<_> = diags.iter().map(|d| d.message.as_str()).collect();
                    return Err(CliError::Message(format!(
                        "parse error in field '{}': {}",
                        key,
                        msgs.join("; ")
                    )));
                }
                let parsed = parsed.ok_or_else(|| {
                    CliError::Message(format!("failed to parse value for field '{}'", key))
                })?;

                let interp = Interpreter::new(&self.program, &self.type_env)
                    .map_err(|e| CliError::Message(format!("interpreter error: {}", e)))?;
                let mut handler = MinimalHandler;
                interp
                    .evaluate_expr(&*self.game_state.borrow(), &mut handler, &parsed)
                    .map_err(|e| {
                        CliError::Message(format!("error evaluating field '{}': {}", key, e))
                    })?
            };
            fields.insert(key.to_string(), val);
        }
        Ok(fields)
    }
}

/// Split a trimmed line into the first whitespace-delimited token and the rest.
fn split_first_token(s: &str) -> (&str, &str) {
    match s.find(char::is_whitespace) {
        Some(pos) => (&s[..pos], &s[pos + 1..]),
        None => (s, ""),
    }
}

/// Split on commas, respecting `()`, `[]`, `{}`, and `""` nesting.
fn split_top_level_commas(s: &str) -> Vec<&str> {
    let mut result = Vec::new();
    let mut depth = 0i32;
    let mut in_string = false;
    let mut start = 0;
    let bytes = s.as_bytes();
    let mut i = 0;

    while i < bytes.len() {
        if in_string {
            if bytes[i] == b'\\' {
                i += 2;
                continue;
            }
            if bytes[i] == b'"' {
                in_string = false;
            }
        } else {
            match bytes[i] {
                b'"' => in_string = true,
                b'(' | b'[' | b'{' => depth += 1,
                b')' | b']' | b'}' => depth -= 1,
                b',' if depth == 0 => {
                    result.push(&s[start..i]);
                    start = i + 1;
                }
                _ => {}
            }
        }
        i += 1;
    }
    result.push(&s[start..]);
    result
}

/// Check that a handle name is a bare identifier: `[a-zA-Z_][a-zA-Z0-9_]*`.
fn is_valid_handle(s: &str) -> bool {
    let mut chars = s.chars();
    match chars.next() {
        Some(c) if c.is_ascii_alphabetic() || c == '_' => {}
        _ => return false,
    }
    chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// Shallow check: does the runtime value match the declared type at the
/// top-level variant? Does not recurse into container element types.
fn value_matches_ty(val: &Value, ty: &Ty) -> bool {
    match (val, ty) {
        (Value::Int(_), Ty::Int | Ty::Resource) => true,
        (Value::Float(_), Ty::Float) => true,
        (Value::Bool(_), Ty::Bool) => true,
        (Value::Str(_), Ty::String) => true,
        (Value::None, Ty::Option(_)) => true,
        (Value::Option(_), Ty::Option(_)) => true,
        (Value::Entity(_), Ty::Entity(_) | Ty::AnyEntity) => true,
        (Value::List(_), Ty::List(_)) => true,
        (Value::Set(_), Ty::Set(_)) => true,
        (Value::Map(_), Ty::Map(_, _)) => true,
        (Value::Struct { name, .. }, Ty::Struct(n)) => name == n,
        (Value::Struct { .. }, Ty::RollResult | Ty::TurnBudget) => true,
        (Value::EnumVariant { enum_name, .. }, Ty::Enum(n)) => enum_name == n,
        (Value::DiceExpr(_), Ty::DiceExpr) => true,
        (Value::RollResult(_), Ty::RollResult) => true,
        (Value::Position(_), Ty::Position) => true,
        (Value::Duration(_), Ty::Duration) => true,
        (Value::Condition(_), Ty::Condition) => true,
        _ => false,
    }
}

/// Human-readable type name for a runtime value (used in error messages).
fn value_type_display(val: &Value) -> String {
    match val {
        Value::Int(_) => "int".into(),
        Value::Float(_) => "float".into(),
        Value::Bool(_) => "bool".into(),
        Value::Str(_) => "string".into(),
        Value::None => "none".into(),
        Value::Option(_) => "option".into(),
        Value::Entity(_) => "entity".into(),
        Value::List(_) => "list".into(),
        Value::Set(_) => "set".into(),
        Value::Map(_) => "map".into(),
        Value::Struct { name, .. } => name.clone(),
        Value::EnumVariant { enum_name, .. } => enum_name.clone(),
        Value::DiceExpr(_) => "DiceExpr".into(),
        Value::RollResult(_) => "RollResult".into(),
        Value::Position(_) => "Position".into(),
        Value::Duration(_) => "Duration".into(),
        Value::Condition(_) => "Condition".into(),
        Value::EnumNamespace(name) => format!("{}(namespace)", name),
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

    // ── Helpers ─────────────────────────────────────────────────

    use std::sync::atomic::{AtomicU64, Ordering};

    /// Load a program that declares `entity Character { HP: int  AC: int }`.
    fn load_character_program(runner: &mut Runner) {
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        let id = COUNTER.fetch_add(1, Ordering::Relaxed);
        let dir = std::env::temp_dir().join("ttrpg_cli_test");
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join(format!("test_character_{}.ttrpg", id));
        std::fs::write(
            &path,
            r#"
system "test" {
    entity Character {
        HP: int
        AC: int
    }
    derive id(x: int) -> int { x }
}
"#,
        )
        .unwrap();
        runner.exec(&format!("load {}", path.display())).unwrap();
        runner.take_output();
        std::fs::remove_file(&path).ok();
    }

    // ── Spawn/Set/Destroy tests ─────────────────────────────────

    #[test]
    fn spawn_and_eval_handle() {
        let mut runner = Runner::new();
        load_character_program(&mut runner);
        runner.exec("spawn Character fighter { HP: 30, AC: 15 }").unwrap();
        let output = runner.take_output();
        assert!(output[0].contains("spawned Character fighter"));

        // Eval the handle — should show Entity(...)
        runner.exec("eval fighter").unwrap_err();
        // Handle is not an eval-visible variable, that's expected for Phase 2
        // The handle registry is used by do/call/set/destroy, not eval
    }

    #[test]
    fn spawn_duplicate_handle_rejected() {
        let mut runner = Runner::new();
        load_character_program(&mut runner);
        runner.exec("spawn Character fighter {}").unwrap();
        runner.take_output();
        let err = runner.exec("spawn Character fighter {}").unwrap_err();
        assert!(err.to_string().contains("already exists"));
    }

    #[test]
    fn spawn_no_fields() {
        let mut runner = Runner::new();
        load_character_program(&mut runner);
        runner.exec("spawn Character fighter").unwrap();
        let output = runner.take_output();
        assert!(output[0].contains("spawned Character fighter"));
    }

    #[test]
    fn spawn_unknown_entity_type() {
        let mut runner = Runner::new();
        load_character_program(&mut runner);
        let err = runner.exec("spawn Goblin g").unwrap_err();
        assert!(err.to_string().contains("unknown entity type 'Goblin'"));
    }

    #[test]
    fn set_field() {
        let mut runner = Runner::new();
        load_character_program(&mut runner);
        runner.exec("spawn Character fighter { AC: 15 }").unwrap();
        runner.take_output();

        runner.exec("set fighter.AC = 18").unwrap();
        let output = runner.take_output();
        assert!(output.iter().any(|l| l.contains("fighter.AC = 18")));
    }

    #[test]
    fn set_unknown_handle() {
        let mut runner = Runner::new();
        let err = runner.exec("set ghost.HP = 10").unwrap_err();
        assert!(err.to_string().contains("unknown handle"));
    }

    #[test]
    fn destroy_entity() {
        let mut runner = Runner::new();
        load_character_program(&mut runner);
        runner.exec("spawn Character goblin { HP: 7 }").unwrap();
        runner.take_output();

        runner.exec("destroy goblin").unwrap();
        let output = runner.take_output();
        assert_eq!(output, vec!["destroyed goblin"]);

        // Handle should no longer exist
        let err = runner.exec("set goblin.HP = 10").unwrap_err();
        assert!(err.to_string().contains("unknown handle"));
    }

    #[test]
    fn destroy_unknown_handle() {
        let mut runner = Runner::new();
        let err = runner.exec("destroy ghost").unwrap_err();
        assert!(err.to_string().contains("unknown handle"));
    }

    // ── Call tests ──────────────────────────────────────────────

    #[test]
    fn call_derive() {
        let dir = std::env::temp_dir().join("ttrpg_cli_test");
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("test_call_derive.ttrpg");
        std::fs::write(
            &path,
            r#"
system "test" {
    derive double(x: int) -> int { x * 2 }
}
"#,
        )
        .unwrap();

        let mut runner = Runner::new();
        runner.exec(&format!("load {}", path.display())).unwrap();
        runner.take_output();

        runner.exec("call double(16)").unwrap();
        let output = runner.take_output();
        assert!(output.iter().any(|l| l.contains("=> 32")));

        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn call_mechanic_fallback() {
        let dir = std::env::temp_dir().join("ttrpg_cli_test");
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("test_call_mechanic.ttrpg");
        std::fs::write(
            &path,
            r#"
system "test" {
    mechanic add(a: int, b: int) -> int { a + b }
}
"#,
        )
        .unwrap();

        let mut runner = Runner::new();
        runner.exec(&format!("load {}", path.display())).unwrap();
        runner.take_output();

        runner.exec("call add(10, 20)").unwrap();
        let output = runner.take_output();
        assert!(output.iter().any(|l| l.contains("=> 30")));

        std::fs::remove_file(&path).ok();
    }

    // ── Issue regression tests ────────────────────────────────────

    #[test]
    fn call_empty_arg_rejected() {
        let dir = std::env::temp_dir().join("ttrpg_cli_test");
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("test_empty_arg.ttrpg");
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
        runner.exec(&format!("load {}", path.display())).unwrap();
        runner.take_output();

        let err = runner.exec("call add(1,,2)").unwrap_err();
        assert!(
            err.to_string().contains("empty argument"),
            "got: {}",
            err
        );

        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn call_undefined_function_rejected() {
        let dir = std::env::temp_dir().join("ttrpg_cli_test");
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("test_undef_fn.ttrpg");
        std::fs::write(
            &path,
            r#"
system "test" {
    derive id(x: int) -> int { x }
}
"#,
        )
        .unwrap();

        let mut runner = Runner::new();
        runner.exec(&format!("load {}", path.display())).unwrap();
        runner.take_output();

        let err = runner.exec("call nonexistent(42)").unwrap_err();
        assert!(
            err.to_string().contains("undefined function"),
            "got: {}",
            err
        );

        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn do_undefined_action_rejected() {
        let dir = std::env::temp_dir().join("ttrpg_cli_test");
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("test_undef_action.ttrpg");
        std::fs::write(
            &path,
            r#"
system "test" {
    entity Character { HP: int }
    derive id(x: int) -> int { x }
}
"#,
        )
        .unwrap();

        let mut runner = Runner::new();
        runner.exec(&format!("load {}", path.display())).unwrap();
        runner.take_output();

        runner.exec("spawn Character fighter { HP: 10 }").unwrap();
        runner.take_output();

        let err = runner.exec("do NoSuchAction(fighter)").unwrap_err();
        assert!(
            err.to_string().contains("undefined action"),
            "got: {}",
            err
        );

        std::fs::remove_file(&path).ok();
    }

    // ── Split helpers tests ──────────────────────────────────────

    #[test]
    fn split_top_level_commas_basic() {
        let parts = split_top_level_commas("a, b, c");
        assert_eq!(parts, vec!["a", " b", " c"]);
    }

    #[test]
    fn split_top_level_commas_nested() {
        let parts = split_top_level_commas("f(a, b), c");
        assert_eq!(parts, vec!["f(a, b)", " c"]);
    }

    #[test]
    fn split_top_level_commas_string() {
        let parts = split_top_level_commas(r#""a, b", c"#);
        assert_eq!(parts, vec![r#""a, b""#, " c"]);
    }

    #[test]
    fn split_top_level_commas_empty() {
        let parts = split_top_level_commas("");
        assert_eq!(parts, vec![""]);
    }

    // ── Load clears handles ──────────────────────────────────────

    #[test]
    fn load_clears_handles() {
        let dir = std::env::temp_dir().join("ttrpg_cli_test");
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("test_load_clears.ttrpg");
        std::fs::write(
            &path,
            r#"
system "test" {
    entity Character { HP: int }
    derive id(x: int) -> int { x }
}
"#,
        )
        .unwrap();

        let mut runner = Runner::new();
        runner.exec(&format!("load {}", path.display())).unwrap();
        runner.take_output();

        runner.exec("spawn Character fighter { HP: 30 }").unwrap();
        runner.take_output();

        // Reload clears handles
        runner.exec("reload").unwrap();
        runner.take_output();

        // Handle should no longer exist
        let err = runner.exec("set fighter.HP = 10").unwrap_err();
        assert!(err.to_string().contains("unknown handle"));

        std::fs::remove_file(&path).ok();
    }

    // ── Handle validation tests (Issue 3) ────────────────────────

    #[test]
    fn spawn_dotted_handle_rejected() {
        let mut runner = Runner::new();
        load_character_program(&mut runner);
        let err = runner.exec("spawn Character foo.bar").unwrap_err();
        assert!(
            err.to_string().contains("invalid handle"),
            "got: {}",
            err
        );
    }

    #[test]
    fn spawn_numeric_handle_rejected() {
        let mut runner = Runner::new();
        load_character_program(&mut runner);
        let err = runner.exec("spawn Character 123abc").unwrap_err();
        assert!(
            err.to_string().contains("invalid handle"),
            "got: {}",
            err
        );
    }

    #[test]
    fn spawn_underscore_handle_ok() {
        let mut runner = Runner::new();
        load_character_program(&mut runner);
        runner.exec("spawn Character _fighter").unwrap();
        let output = runner.take_output();
        assert!(output[0].contains("spawned Character _fighter"));
    }

    // ── Handle resolution in RHS tests (Issue 1) ────────────────

    /// Load a program with entity-typed fields for handle resolution tests.
    fn load_party_program(runner: &mut Runner) {
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        let id = COUNTER.fetch_add(1, Ordering::Relaxed);
        let dir = std::env::temp_dir().join("ttrpg_cli_test");
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join(format!("test_party_{}.ttrpg", id));
        std::fs::write(
            &path,
            r#"
system "test" {
    entity Character {
        HP: int
        AC: int
        ally: Character
    }
    derive id(x: int) -> int { x }
}
"#,
        )
        .unwrap();
        runner.exec(&format!("load {}", path.display())).unwrap();
        runner.take_output();
        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn spawn_field_handle_resolution() {
        let mut runner = Runner::new();
        load_party_program(&mut runner);

        runner.exec("spawn Character alice { HP: 30, AC: 15 }").unwrap();
        runner.take_output();

        // Spawn bob with ally: alice (handle resolves to entity value)
        runner.exec("spawn Character bob { HP: 25, ally: alice }").unwrap();
        let output = runner.take_output();
        assert!(output[0].contains("spawned Character bob"));
    }

    #[test]
    fn set_handle_rhs_resolves() {
        let mut runner = Runner::new();
        load_party_program(&mut runner);

        runner.exec("spawn Character alice { HP: 30 }").unwrap();
        runner.take_output();
        runner.exec("spawn Character bob { HP: 25 }").unwrap();
        runner.take_output();

        // Set bob.ally = alice (handle resolves to entity value)
        runner.exec("set bob.ally = alice").unwrap();
        let output = runner.take_output();
        assert!(output[0].contains("bob.ally ="));
    }

    // ── Schema validation tests (Issue 2) ────────────────────────

    #[test]
    fn spawn_unknown_field_rejected() {
        let mut runner = Runner::new();
        load_character_program(&mut runner);
        let err = runner
            .exec("spawn Character fighter { HP: 30, STR: 16 }")
            .unwrap_err();
        assert!(
            err.to_string().contains("unknown field 'STR'"),
            "got: {}",
            err
        );
    }

    #[test]
    fn set_unknown_field_rejected() {
        let mut runner = Runner::new();
        load_character_program(&mut runner);
        runner.exec("spawn Character fighter { HP: 30 }").unwrap();
        runner.take_output();

        let err = runner.exec("set fighter.STR = 16").unwrap_err();
        assert!(
            err.to_string().contains("unknown field 'STR'"),
            "got: {}",
            err
        );
    }

    #[test]
    fn spawn_type_mismatch_rejected() {
        let mut runner = Runner::new();
        load_character_program(&mut runner);
        let err = runner
            .exec(r#"spawn Character fighter { HP: "thirty" }"#)
            .unwrap_err();
        assert!(
            err.to_string().contains("type mismatch"),
            "got: {}",
            err
        );
    }

    #[test]
    fn set_type_mismatch_rejected() {
        let mut runner = Runner::new();
        load_character_program(&mut runner);
        runner.exec("spawn Character fighter { HP: 30 }").unwrap();
        runner.take_output();

        let err = runner.exec(r#"set fighter.HP = "thirty""#).unwrap_err();
        assert!(
            err.to_string().contains("type mismatch"),
            "got: {}",
            err
        );
    }
}
