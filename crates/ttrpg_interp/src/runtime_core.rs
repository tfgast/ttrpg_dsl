//! Shared runtime state across executions.
//!
//! `RuntimeCore` holds immutable program data plus mutable caches and ID counters.
//! A single instance is shared (via `Rc`) across sequential `Execution` instances
//! on the same thread.

// Fields and methods defined here are used by Execution in later phases.
#![allow(dead_code)]

use std::cell::{Cell, RefCell};
use std::rc::Rc;
use std::sync::Arc;

use rustc_hash::FxHashMap;
use ttrpg_ast::Name;
use ttrpg_ast::ast::Program;
use ttrpg_checker::env::TypeEnv;

use crate::coverage::CoverageData;
use crate::value::Value;

/// Shared across executions. Immutable program data + mutable caches.
/// Single-threaded: not Send/Sync. One RuntimeCore per host thread.
pub struct RuntimeCore {
    pub(crate) program: Arc<Program>,
    pub(crate) type_env: Arc<TypeEnv>,
    pub(crate) consts: RefCell<FxHashMap<Name, Value>>,
    pub(crate) coverage: Option<RefCell<CoverageData>>,
    next_invocation_id: Cell<u64>,
    next_condition_id: Cell<u64>,
}

impl RuntimeCore {
    /// Primary constructor. Caller provides counter start values.
    pub fn new(
        program: Arc<Program>,
        type_env: Arc<TypeEnv>,
        invocation_start: u64,
        condition_start: u64,
    ) -> Rc<Self> {
        Rc::new(RuntimeCore {
            program,
            type_env,
            consts: RefCell::new(FxHashMap::default()),
            coverage: None,
            next_invocation_id: Cell::new(invocation_start),
            next_condition_id: Cell::new(condition_start),
        })
    }

    /// Convenience constructor that reads counter values from a `GameState`.
    pub fn from_game_state(
        program: Arc<Program>,
        type_env: Arc<TypeEnv>,
        state: &crate::reference_state::GameState,
    ) -> Rc<Self> {
        Self::new(
            program,
            type_env,
            state.next_invocation_id(),
            state.next_condition_id(),
        )
    }

    /// Enable coverage tracking.
    pub fn with_coverage(self: &Rc<Self>) -> Rc<Self> {
        // Since Rc is already created, we need a new one with coverage enabled.
        // This is a construction-time concern — call before creating Executions.
        Rc::new(RuntimeCore {
            program: Arc::clone(&self.program),
            type_env: Arc::clone(&self.type_env),
            consts: RefCell::new(FxHashMap::default()),
            coverage: Some(RefCell::new(CoverageData::default())),
            next_invocation_id: Cell::new(self.next_invocation_id.get()),
            next_condition_id: Cell::new(self.next_condition_id.get()),
        })
    }

    /// Allocate the next invocation ID.
    pub(crate) fn alloc_invocation_id(&self) -> u64 {
        let id = self.next_invocation_id.get();
        self.next_invocation_id.set(id.wrapping_add(1));
        id
    }

    /// Allocate the next condition ID.
    pub(crate) fn alloc_condition_id(&self) -> u64 {
        let id = self.next_condition_id.get();
        self.next_condition_id.set(id.wrapping_add(1));
        id
    }

    /// Current ID counter values. Call after completion to persist.
    pub fn counters(&self) -> (u64, u64) {
        (self.next_invocation_id.get(), self.next_condition_id.get())
    }

    /// Sync ID counters from a bridge interpreter back to this core.
    pub(crate) fn sync_counters(&self, invocation: u64, condition: u64) {
        self.next_invocation_id.set(invocation);
        self.next_condition_id.set(condition);
    }
}
