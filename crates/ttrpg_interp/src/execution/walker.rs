use super::*;

/// Which modifier pipeline the walker is serving.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ModifyWalkerMode {
    Cost,
    Phase1,
    Phase2,
}

/// What the walker is waiting for after pushing an ExprEval child.
#[derive(Debug, Clone)]
enum ModifyWalkerAwait {
    /// Not waiting — ready to process next stmt.
    Ready,
    /// Waiting for ExprEval result for a Let binding value.
    LetExpr(Name),
    /// Waiting for ExprEval result for an If condition.
    IfCondition,
    /// Waiting for ExprEval result for a ParamOverride value.
    ParamOverride(Name),
    /// Waiting for ExprEval result for a ResultOverride field value.
    ResultOverride(Name),
    /// Waiting for ExprEval result for `result = expr` (phase2 ParamOverride).
    ResultParamOverride,
}

/// Actions produced by the walker for the parent frame to execute.
pub(crate) enum WalkerStep {
    /// Push this ExprEval frame as a child. Return `Advance::Push(frame)`.
    PushExpr(Frame),
    /// Let binding evaluated — parent should `env.bind(name, value)`.
    Bind(Name, Value),
    /// Cost override (pure data) — parent applies to CostClause.
    CostOverride {
        tokens: Vec<Spanned<Name>>,
        free: bool,
    },
    /// ParamOverride evaluated — parent updates params vec + env.bind.
    ParamOverride(Name, Value),
    /// ResultOverride field evaluated — parent updates result fields + env.bind.
    ResultOverride(Name, Value),
    /// `result = expr` evaluated — parent replaces result + env.bind.
    ResultParamOverride(Value),
    /// If condition evaluated — entering chosen body. The walker has already
    /// pushed the parent stmts to its stack and set up the body. Parent
    /// should `env.push_scope()`.
    EnterBody,
    /// Current If body is done. Parent should `env.pop_scope()`, do
    /// mode-specific rebinding. The walker has already restored parent state.
    ExitBody,
    /// All statements complete (stack empty). Walker is finished.
    Complete,
    /// Continue to the next step (stmt was skipped / irrelevant to mode).
    Continue,
    /// Error occurred.
    Error(RuntimeError),
}

/// Shared state machine for walking `ModifyStmt` lists.
#[derive(Debug, Clone)]
pub(crate) struct ModifyStmtWalker {
    /// Current statement list being processed.
    stmts: Vec<ttrpg_ast::ast::ModifyStmt>,
    /// Index into current stmts.
    index: usize,
    /// Saved (stmts, next_index) for parent contexts when inside If bodies.
    stack: Vec<(Vec<ttrpg_ast::ast::ModifyStmt>, usize)>,
    /// Result from a pushed ExprEval child frame.
    child_result: Option<Result<Value, RuntimeError>>,
    /// What the walker is waiting for.
    awaiting: ModifyWalkerAwait,
    /// Mode (determines which stmts to process/skip).
    mode: ModifyWalkerMode,
}

impl ModifyStmtWalker {
    pub(crate) fn new(stmts: Vec<ttrpg_ast::ast::ModifyStmt>, mode: ModifyWalkerMode) -> Self {
        ModifyStmtWalker {
            stmts,
            index: 0,
            stack: Vec::new(),
            child_result: None,
            awaiting: ModifyWalkerAwait::Ready,
            mode,
        }
    }

    /// Deliver a child frame result (ExprEval completed).
    pub(crate) fn receive_child(&mut self, result: Result<Value, RuntimeError>) {
        self.child_result = Some(result);
    }

    /// Drive one step. Returns what the parent should do.
    pub(crate) fn step(&mut self, core: &RuntimeCore) -> WalkerStep {
        use ttrpg_ast::ast::ModifyStmt;

        // 1. Handle pending child result.
        if let Some(result) = self.child_result.take() {
            let val = match result {
                Ok(v) => v,
                Err(e) => return WalkerStep::Error(e),
            };
            match std::mem::replace(&mut self.awaiting, ModifyWalkerAwait::Ready) {
                ModifyWalkerAwait::LetExpr(name) => {
                    self.index += 1;
                    return WalkerStep::Bind(name, val);
                }
                ModifyWalkerAwait::IfCondition => {
                    return match val {
                        Value::Bool(b) => {
                            // Pick the body to enter.
                            let stmt = &self.stmts[self.index];
                            if let ModifyStmt::If {
                                then_body,
                                else_body,
                                ..
                            } = stmt
                            {
                                let body = if b {
                                    Some(then_body.clone())
                                } else {
                                    else_body.clone()
                                };
                                match body {
                                    Some(body_stmts) => {
                                        // Push current context to stack and
                                        // switch to the chosen body.
                                        let parent_stmts =
                                            std::mem::replace(&mut self.stmts, body_stmts);
                                        self.stack.push((parent_stmts, self.index + 1));
                                        self.index = 0;
                                        WalkerStep::EnterBody
                                    }
                                    None => {
                                        // false with no else — skip.
                                        self.index += 1;
                                        WalkerStep::Continue
                                    }
                                }
                            } else {
                                WalkerStep::Error(RuntimeError::new(
                                    "internal: IfCondition on non-If stmt",
                                ))
                            }
                        }
                        _ => {
                            WalkerStep::Error(RuntimeError::new("modify if condition must be Bool"))
                        }
                    };
                }
                ModifyWalkerAwait::ParamOverride(name) => {
                    self.index += 1;
                    return WalkerStep::ParamOverride(name, val);
                }
                ModifyWalkerAwait::ResultOverride(field) => {
                    self.index += 1;
                    return WalkerStep::ResultOverride(field, val);
                }
                ModifyWalkerAwait::ResultParamOverride => {
                    self.index += 1;
                    return WalkerStep::ResultParamOverride(val);
                }
                ModifyWalkerAwait::Ready => {
                    // Shouldn't happen — child result without awaiting.
                    return WalkerStep::Error(RuntimeError::new(
                        "internal: ModifyStmtWalker received child result while not awaiting",
                    ));
                }
            }
        }

        // 2. Check if current body is done.
        if self.index >= self.stmts.len() {
            if self.stack.is_empty() {
                return WalkerStep::Complete;
            } else {
                return WalkerStep::ExitBody;
            }
        }

        // 3. Process current statement.
        let stmt = &self.stmts[self.index];
        match stmt {
            // ── Let: shared across all modes ──
            ModifyStmt::Let { name, value, .. } => {
                self.awaiting = ModifyWalkerAwait::LetExpr(name.clone());
                WalkerStep::PushExpr(compile_expr_to_frame(value, core))
            }

            // ── If: shared across all modes (with phase1 skip optimization) ──
            ModifyStmt::If {
                condition,
                then_body,
                else_body,
                ..
            } => {
                // Phase1 optimization: skip If when neither branch has phase1 stmts.
                if self.mode == ModifyWalkerMode::Phase1
                    && !crate::pipeline::has_phase1_stmts(then_body)
                    && !else_body
                        .as_ref()
                        .is_some_and(|e| crate::pipeline::has_phase1_stmts(e))
                {
                    self.index += 1;
                    return WalkerStep::Continue;
                }
                self.awaiting = ModifyWalkerAwait::IfCondition;
                WalkerStep::PushExpr(compile_expr_to_frame(condition, core))
            }

            // ── CostOverride: cost mode only, pure data ──
            ModifyStmt::CostOverride { tokens, free, .. } => {
                if self.mode == ModifyWalkerMode::Cost {
                    let t = tokens.clone();
                    let f = *free;
                    self.index += 1;
                    WalkerStep::CostOverride { tokens: t, free: f }
                } else {
                    // Irrelevant to this mode.
                    self.index += 1;
                    WalkerStep::Continue
                }
            }

            // ── ParamOverride: mode-specific ──
            ModifyStmt::ParamOverride { name, value, .. } => {
                match self.mode {
                    ModifyWalkerMode::Phase1 => {
                        if name == "result" {
                            // Phase1 skips result overrides.
                            self.index += 1;
                            WalkerStep::Continue
                        } else {
                            self.awaiting = ModifyWalkerAwait::ParamOverride(name.clone());
                            WalkerStep::PushExpr(compile_expr_to_frame(value, core))
                        }
                    }
                    ModifyWalkerMode::Phase2 => {
                        if name == "result" {
                            self.awaiting = ModifyWalkerAwait::ResultParamOverride;
                            WalkerStep::PushExpr(compile_expr_to_frame(value, core))
                        } else {
                            // Phase2 ignores non-result param overrides.
                            self.index += 1;
                            WalkerStep::Continue
                        }
                    }
                    ModifyWalkerMode::Cost => {
                        // Cost mode doesn't handle param overrides.
                        self.index += 1;
                        WalkerStep::Continue
                    }
                }
            }

            // ── ResultOverride: phase2 only ──
            ModifyStmt::ResultOverride { field, value, .. } => {
                if self.mode == ModifyWalkerMode::Phase2 {
                    self.awaiting = ModifyWalkerAwait::ResultOverride(field.clone());
                    WalkerStep::PushExpr(compile_expr_to_frame(value, core))
                } else {
                    self.index += 1;
                    WalkerStep::Continue
                }
            }
        }
    }

    /// Exit an If body. Called by parent after `WalkerStep::ExitBody`.
    /// The parent has already called `env.pop_scope()` and done mode-specific rebinding.
    /// Restores the parent stmt list and index from the stack.
    pub(crate) fn exit_body(&mut self) {
        let (parent_stmts, parent_idx) = self.stack.pop().expect("exit_body with empty stack");
        self.stmts = parent_stmts;
        self.index = parent_idx;
    }
}
