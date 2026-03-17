//! Shared runtime state across executions.
//!
//! `RuntimeCore` holds immutable program data plus mutable caches and ID counters.
//! A single instance is shared (via `Rc`) across sequential `Execution` instances
//! on the same thread.

use std::cell::{Cell, RefCell};
use std::rc::Rc;
use std::sync::Arc;

use rustc_hash::FxHashMap;
use ttrpg_ast::Name;
use ttrpg_ast::ast::Program;
use ttrpg_checker::env::TypeEnv;

use ttrpg_ast::span::Span;

use crate::RuntimeError;
use crate::coverage::CoverageData;
use crate::expr_eval::ExprWork;
use crate::value::Value;

/// Shared across executions. Immutable program data + mutable caches.
/// Single-threaded: not Send/Sync. One RuntimeCore per host thread.
pub struct RuntimeCore {
    pub(crate) program: Arc<Program>,
    pub(crate) type_env: Arc<TypeEnv>,
    pub(crate) consts: RefCell<FxHashMap<Name, Value>>,
    /// Cache of compiled expression work sequences, keyed by source span.
    /// Avoids redundant `compile_expr()` calls for the same expression
    /// across repeated function/derive/mechanic invocations.
    pub(crate) compiled_exprs: RefCell<FxHashMap<Span, Vec<ExprWork>>>,
    pub(crate) coverage: Option<Rc<RefCell<CoverageData>>>,
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
            compiled_exprs: RefCell::new(FxHashMap::default()),
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

    /// Enable coverage tracking with a fresh `CoverageData`.
    pub fn with_coverage(self: &Rc<Self>) -> Rc<Self> {
        self.with_shared_coverage(Rc::new(RefCell::new(CoverageData::default())))
    }

    /// Enable coverage tracking with an existing shared `CoverageData`.
    ///
    /// Use this when the caller already owns a `CoverageData` (e.g. the CLI
    /// runner) so that coverage hits flow into the same data the caller reads.
    pub fn with_shared_coverage(self: &Rc<Self>, cov: Rc<RefCell<CoverageData>>) -> Rc<Self> {
        Rc::new(RuntimeCore {
            program: Arc::clone(&self.program),
            type_env: Arc::clone(&self.type_env),
            consts: RefCell::new(FxHashMap::default()),
            compiled_exprs: RefCell::new(FxHashMap::default()),
            coverage: Some(cov),
            next_invocation_id: Cell::new(self.next_invocation_id.get()),
            next_condition_id: Cell::new(self.next_condition_id.get()),
        })
    }

    /// Allocate the next invocation ID.
    pub(crate) fn alloc_invocation_id(&self) -> Result<u64, RuntimeError> {
        let id = self.next_invocation_id.get();
        self.next_invocation_id.set(
            id.checked_add(1).ok_or_else(|| {
                RuntimeError::new("invocation ID counter overflow (u64 exhausted)")
            })?,
        );
        Ok(id)
    }

    /// Allocate the next condition ID.
    pub(crate) fn alloc_condition_id(&self) -> Result<u64, RuntimeError> {
        let id = self.next_condition_id.get();
        self.next_condition_id.set(
            id.checked_add(1).ok_or_else(|| {
                RuntimeError::new("condition ID counter overflow (u64 exhausted)")
            })?,
        );
        Ok(id)
    }

    /// Current ID counter values. Call after completion to persist.
    pub fn counters(&self) -> (u64, u64) {
        (self.next_invocation_id.get(), self.next_condition_id.get())
    }

    /// Compile an expression, returning cached work if available.
    ///
    /// On the first call for a given span, delegates to `compile_expr()` and
    /// stores the result. Subsequent calls for the same span clone the cached
    /// work sequence instead of recompiling.
    pub(crate) fn compile_expr_cached(
        &self,
        expr: &ttrpg_ast::span::Spanned<ttrpg_ast::ast::ExprKind>,
    ) -> Option<Vec<ExprWork>> {
        let span = expr.span;
        // Skip cache for dummy/synthetic spans — multiple unrelated
        // expressions can share Span::dummy(), causing collisions.
        if span == Span::dummy() {
            return crate::expr_eval::compile_expr(expr, &self.type_env, &self.program);
        }
        if let Some(cached) = self.compiled_exprs.borrow().get(&span) {
            return Some(cached.clone());
        }
        let work = crate::expr_eval::compile_expr(expr, &self.type_env, &self.program)?;
        self.compiled_exprs.borrow_mut().insert(span, work.clone());
        Some(work)
    }
}
