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

use crate::RuntimeError;
use crate::coverage::CoverageData;
use crate::value::Value;

/// Category of bridge fallback call, for instrumentation.
#[derive(Debug, Clone, Copy)]
pub enum BridgeCategory {
    /// eval_expr, eval_stmt, eval_block, eval_assign_with_rhs
    Eval,
    /// dispatch_table_with_values, evaluate_fn_with_values, evaluate_function_with_values
    Dispatch,
    /// execute_pipeline, collect_cost_modifiers, apply_single_cost_modifier
    Pipeline,
    /// Thin wrappers that only call emit() (budget, condition, revoke effects)
    EffectEmission,
    /// TryEvalHandler probing (checking whether an expression yields)
    Probe,
}

const BRIDGE_CATEGORY_COUNT: usize = 5;

/// Counts of bridge fallback calls by category.
#[derive(Debug)]
pub struct BridgeStats {
    counts: [Cell<u64>; BRIDGE_CATEGORY_COUNT],
}

impl Default for BridgeStats {
    fn default() -> Self {
        BridgeStats {
            counts: [
                Cell::new(0),
                Cell::new(0),
                Cell::new(0),
                Cell::new(0),
                Cell::new(0),
            ],
        }
    }
}

impl BridgeStats {
    /// Increment the counter for the given category.
    pub fn increment(&self, category: BridgeCategory) {
        let idx = category as usize;
        self.counts[idx].set(self.counts[idx].get() + 1);
    }

    /// Get the count for a given category.
    pub fn count(&self, category: BridgeCategory) -> u64 {
        self.counts[category as usize].get()
    }

    /// Total bridge calls across all categories.
    pub fn total(&self) -> u64 {
        self.counts.iter().map(|c| c.get()).sum()
    }

    /// Panics if any Eval, Dispatch, or Pipeline bridges were used.
    /// Call in tests that expect fully native step-based execution.
    pub fn assert_no_eval_bridges(&self) {
        let eval = self.count(BridgeCategory::Eval);
        let dispatch = self.count(BridgeCategory::Dispatch);
        let pipeline = self.count(BridgeCategory::Pipeline);
        assert!(
            eval + dispatch + pipeline == 0,
            "expected no eval/dispatch/pipeline bridges, got: eval={eval}, dispatch={dispatch}, pipeline={pipeline}"
        );
    }

    /// Panics if any EffectEmission bridges were used.
    /// All effect emissions now go through `StateAdapter::emit_effect()`.
    pub fn assert_no_effect_emission_bridges(&self) {
        let count = self.count(BridgeCategory::EffectEmission);
        assert!(
            count == 0,
            "expected no effect emission bridges, got: {count}"
        );
    }

    /// Panics if any Dispatch bridges were used.
    /// All dispatch operations (derive/mechanic/function/table) now use
    /// native child frames (DeriveEval/FunctionEval) instead of bridging.
    pub fn assert_no_dispatch_bridges(&self) {
        let count = self.count(BridgeCategory::Dispatch);
        assert!(count == 0, "expected no dispatch bridges, got: {count}");
    }

    /// Format counts as a single-line summary string.
    pub fn summary(&self) -> String {
        format!(
            "bridge_stats: eval={}, dispatch={}, pipeline={}, effect_emission={}, probe={}, total={}",
            self.count(BridgeCategory::Eval),
            self.count(BridgeCategory::Dispatch),
            self.count(BridgeCategory::Pipeline),
            self.count(BridgeCategory::EffectEmission),
            self.count(BridgeCategory::Probe),
            self.total(),
        )
    }
}

/// Shared across executions. Immutable program data + mutable caches.
/// Single-threaded: not Send/Sync. One RuntimeCore per host thread.
pub struct RuntimeCore {
    pub(crate) program: Arc<Program>,
    pub(crate) type_env: Arc<TypeEnv>,
    pub(crate) consts: RefCell<FxHashMap<Name, Value>>,
    pub(crate) coverage: Option<Rc<RefCell<CoverageData>>>,
    bridge_stats: BridgeStats,
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
            bridge_stats: BridgeStats::default(),
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
            coverage: Some(cov),
            bridge_stats: BridgeStats::default(),
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

    /// Sync ID counters from a bridge interpreter back to this core.
    pub(crate) fn sync_counters(&self, invocation: u64, condition: u64) {
        self.next_invocation_id.set(invocation);
        self.next_condition_id.set(condition);
    }

    /// Bridge call statistics accumulated during step-based execution.
    pub fn bridge_stats(&self) -> &BridgeStats {
        &self.bridge_stats
    }
}
