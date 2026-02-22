pub mod value;
pub mod effect;
pub mod state;
pub mod eval;
pub mod call;
pub mod builtins;
pub mod action;
pub mod pipeline;
pub mod event;

use std::collections::HashMap;

use ttrpg_ast::Span;
use ttrpg_ast::ast::{
    ActionDecl, ConditionDecl, DeclKind, EventDecl, FnDecl, OptionDecl, Program, PromptDecl,
    ReactionDecl, TopLevel,
};
use ttrpg_checker::env::TypeEnv;

use crate::effect::EffectHandler;
use crate::state::{EntityRef, StateProvider};
use crate::value::Value;

// ── RuntimeError ───────────────────────────────────────────────

/// A runtime error produced by the interpreter.
///
/// Since the interpreter trusts that programs have passed type-checking,
/// runtime errors indicate either host state sync issues (e.g., missing
/// entity fields), protocol errors (invalid effect responses), arithmetic
/// errors (division by zero, overflow), or internal bugs.
#[derive(Debug, Clone)]
pub struct RuntimeError {
    pub message: String,
    pub span: Option<Span>,
}

impl RuntimeError {
    pub fn new(message: impl Into<String>) -> Self {
        RuntimeError {
            message: message.into(),
            span: None,
        }
    }

    pub fn with_span(message: impl Into<String>, span: Span) -> Self {
        RuntimeError {
            message: message.into(),
            span: Some(span),
        }
    }
}

impl std::fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)?;
        if let Some(span) = self.span {
            write!(f, " (at {}..{})", span.start, span.end)?;
        }
        Ok(())
    }
}

impl std::error::Error for RuntimeError {}

// ── DeclIndex ──────────────────────────────────────────────────

/// O(1) lookup index for declarations, built once at `Interpreter::new`.
///
/// Borrows from `Program` with the same lifetime, so no cloning is needed.
pub(crate) struct DeclIndex<'p> {
    pub actions: HashMap<&'p str, &'p ActionDecl>,
    pub derives: HashMap<&'p str, &'p FnDecl>,
    pub mechanics: HashMap<&'p str, &'p FnDecl>,
    pub reactions: HashMap<&'p str, &'p ReactionDecl>,
    pub conditions: HashMap<&'p str, &'p ConditionDecl>,
    pub events: HashMap<&'p str, &'p EventDecl>,
    pub prompts: HashMap<&'p str, &'p PromptDecl>,
    pub options: HashMap<&'p str, &'p OptionDecl>,
    pub option_order: Vec<&'p str>,
}

impl<'p> DeclIndex<'p> {
    fn build(program: &'p Program) -> Self {
        let mut index = DeclIndex {
            actions: HashMap::new(),
            derives: HashMap::new(),
            mechanics: HashMap::new(),
            reactions: HashMap::new(),
            conditions: HashMap::new(),
            events: HashMap::new(),
            prompts: HashMap::new(),
            options: HashMap::new(),
            option_order: Vec::new(),
        };

        for item in &program.items {
            if let TopLevel::System(system) = &item.node {
                for decl in &system.decls {
                    match &decl.node {
                        DeclKind::Action(a) => {
                            index.actions.insert(&a.name, a);
                        }
                        DeclKind::Derive(f) => {
                            index.derives.insert(&f.name, f);
                        }
                        DeclKind::Mechanic(f) => {
                            index.mechanics.insert(&f.name, f);
                        }
                        DeclKind::Reaction(r) => {
                            index.reactions.insert(&r.name, r);
                        }
                        DeclKind::Condition(c) => {
                            index.conditions.insert(&c.name, c);
                        }
                        DeclKind::Event(e) => {
                            index.events.insert(&e.name, e);
                        }
                        DeclKind::Prompt(p) => {
                            index.prompts.insert(&p.name, p);
                        }
                        DeclKind::Option(o) => {
                            index.options.insert(&o.name, o);
                            index.option_order.push(&o.name);
                        }
                        // Structs, enums, entities are accessed via TypeEnv, not DeclIndex.
                        // Move nodes should not exist after lowering.
                        _ => {}
                    }
                }
            }
        }

        index
    }
}

// ── Interpreter ────────────────────────────────────────────────

/// The main interpreter. Holds a reference to the checked program and
/// provides methods for executing actions, evaluating derives, etc.
pub struct Interpreter<'p> {
    pub(crate) program: &'p Program,
    pub(crate) type_env: &'p TypeEnv,
    pub(crate) index: DeclIndex<'p>,
}

impl<'p> Interpreter<'p> {
    /// Construct a new interpreter from a checked program.
    ///
    /// Fails if any `DeclKind::Move` nodes remain — this catches callers
    /// who forgot to run `lower_moves` before checking.
    pub fn new(program: &'p Program, type_env: &'p TypeEnv) -> Result<Self, RuntimeError> {
        // Belt-and-suspenders check: reject surviving Move nodes.
        for item in &program.items {
            if let TopLevel::System(system) = &item.node {
                for decl in &system.decls {
                    if matches!(&decl.node, DeclKind::Move(_)) {
                        return Err(RuntimeError::with_span(
                            "move declarations must be lowered before interpretation \
                             (call lower_moves before check)",
                            decl.span,
                        ));
                    }
                }
            }
        }

        let index = DeclIndex::build(program);

        Ok(Interpreter {
            program,
            type_env,
            index,
        })
    }
}

// ── Env (execution environment) ────────────────────────────────

/// Mutable execution environment, created fresh for each public API call.
pub(crate) struct Env<'a, 'p> {
    pub state: &'a dyn StateProvider,
    pub handler: &'a mut dyn EffectHandler,
    pub interp: &'a Interpreter<'p>,
    pub scopes: Vec<Scope>,
    pub turn_actor: Option<EntityRef>,
}

impl<'a, 'p> Env<'a, 'p> {
    pub fn new(
        state: &'a dyn StateProvider,
        handler: &'a mut dyn EffectHandler,
        interp: &'a Interpreter<'p>,
    ) -> Self {
        Env {
            state,
            handler,
            interp,
            scopes: vec![Scope::new()],
            turn_actor: None,
        }
    }

    /// Push a new scope onto the scope stack.
    pub fn push_scope(&mut self) {
        self.scopes.push(Scope::new());
    }

    /// Pop the current scope from the scope stack.
    pub fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    /// Bind a variable in the current (innermost) scope.
    pub fn bind(&mut self, name: String, value: Value) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.bindings.insert(name, value);
        }
    }

    /// Look up a variable by name, searching from innermost to outermost scope.
    pub fn lookup(&self, name: &str) -> Option<&Value> {
        for scope in self.scopes.iter().rev() {
            if let Some(val) = scope.bindings.get(name) {
                return Some(val);
            }
        }
        None
    }

    /// Get a mutable reference to a variable by name, searching from innermost to outermost.
    pub fn lookup_mut(&mut self, name: &str) -> Option<&mut Value> {
        for scope in self.scopes.iter_mut().rev() {
            if let Some(val) = scope.bindings.get_mut(name) {
                return Some(val);
            }
        }
        None
    }
}

/// A single lexical scope containing variable bindings.
pub(crate) struct Scope {
    pub bindings: HashMap<String, Value>,
}

impl Scope {
    pub fn new() -> Self {
        Scope {
            bindings: HashMap::new(),
        }
    }
}
