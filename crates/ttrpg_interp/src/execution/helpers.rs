use super::*;

// ── Frame-based assignment context ─────────────────────────────

/// Implements `AssignContext` for the frame-based execution path,
/// using frame-based expression evaluation instead of bridging to
/// the recursive `Interpreter`.
pub(super) struct FrameAssignCtx<'a> {
    pub(super) env: &'a mut ExecEnv,
    pub(super) core: &'a RuntimeCore,
    pub(super) state: &'a dyn StateProvider,
    pub(super) handler: &'a mut dyn EffectHandler,
    /// Effects collected during assignment instead of emitting them synchronously.
    /// Drained by the caller to push `MutationYield` frames.
    pub(super) collected: Vec<Effect>,
}

impl crate::eval::AssignContext for FrameAssignCtx<'_> {
    fn lookup(&self, name: &str) -> Option<&Value> {
        self.env.lookup(name)
    }
    fn lookup_mut(&mut self, name: &str) -> Option<&mut Value> {
        self.env.lookup_mut(name)
    }
    fn push_scope(&mut self) {
        self.env.push_scope();
    }
    fn pop_scope(&mut self) {
        self.env.pop_scope();
    }
    fn bind(&mut self, name: Name, value: Value) {
        self.env.bind(name, value);
    }
    fn emit(&mut self, effect: Effect) {
        self.collected.push(effect);
    }
    fn turn_actor(&self) -> Option<EntityRef> {
        self.env.turn_actor
    }
    fn type_env(&self) -> &ttrpg_checker::env::TypeEnv {
        &self.core.type_env
    }
    fn program(&self) -> &ttrpg_ast::ast::Program {
        &self.core.program
    }
    fn state_provider(&self) -> &dyn StateProvider {
        self.state
    }
    fn eval_expr(&mut self, expr: &Spanned<ExprKind>) -> Result<Value, RuntimeError> {
        eval_expr_via_frame(self.core, self.env, self.state, self.handler, expr)
    }
    fn scopes_mut_and_state(&mut self) -> (&mut Vec<Scope>, &dyn StateProvider) {
        (&mut self.env.scopes, self.state)
    }
}

/// Dispatch a builtin call (apply_condition, remove_condition, revoke)
/// as a `CallSetup` frame. The `target` parameter selects which builtin.
pub(super) fn dispatch_builtin_call(
    target: CallTarget,
    args: &[Arg],
    span: Span,
    awaiting: AwaitingFn,
) -> Result<Option<(Frame, AwaitingFn)>, RuntimeError> {
    Ok(Some((
        Frame::CallSetup {
            target,
            arg_exprs: args.iter().map(|a| a.value.clone()).collect(),
            arg_index: 0,
            evaluated: Vec::new(),
            child_result: None,
            awaiting_child: false,
            span,
        },
        awaiting,
    )))
}

/// Try to dispatch a statement via specialized frame (CallSetup/FunctionEval).
/// Returns `Some((frame, awaiting))` if the
/// statement is a bare function call or a let binding whose value is
/// a function call that can be dispatched via `CallSetup`/`FunctionEval`.
///
/// Arguments are evaluated one at a time via ExprEval children
/// inside a `CallSetup` frame, avoiding the probe-then-build pattern.
pub(super) fn try_frame_dispatch_stmt(
    core: &RuntimeCore,
    _env: &mut ExecEnv,
    _sp: &dyn StateProvider,
    _eh: &mut dyn EffectHandler,
    _tracker: &MutationTracker,
    stmt: &Spanned<StmtKind>,
) -> Result<Option<(Frame, AwaitingFn)>, RuntimeError> {
    // Extract the call expression and determine the awaiting type.
    let (call_expr, awaiting) = match &stmt.node {
        StmtKind::Expr(expr) => (expr, AwaitingFn::ExprStmt),
        StmtKind::Let { name, value, .. } => (value, AwaitingFn::LetBinding { name: name.clone() }),
        StmtKind::Assign { target, op, value } => (
            value,
            AwaitingFn::Assign {
                target: target.clone(),
                op: *op,
                span: stmt.span,
            },
        ),
        StmtKind::Return(Some(expr)) => (expr, AwaitingFn::Return),
        _ => return Ok(None),
    };

    // Only handle direct function calls: name(args).
    let (callee_name, args) = match &call_expr.node {
        ExprKind::Call { callee, args } => match &callee.node {
            ExprKind::Ident(name) => (name.clone(), args),
            _ => return Ok(None),
        },
        _ => return Ok(None),
    };

    // Dispatch builtins that yield effects (ConditionApplyGate, ConditionRemovalGate).
    let builtin_target = match callee_name.as_str() {
        "apply_condition" => Some(CallTarget::ApplyCondition {
            span: call_expr.span,
        }),
        "remove_condition" => Some(CallTarget::RemoveCondition {
            span: call_expr.span,
        }),
        "revoke" => Some(CallTarget::Revoke {
            span: call_expr.span,
        }),
        _ => None,
    };
    if let Some(target) = builtin_target {
        return dispatch_builtin_call(target, args, call_expr.span, awaiting);
    }

    // Must be a user-defined function (not a builtin, condition, etc.)
    let fn_decl = match core.program.functions.get(callee_name.as_str()) {
        Some(d) => d,
        None => return Ok(None),
    };
    let fn_info = match core.type_env.lookup_fn(callee_name.as_str()) {
        Some(i) => i,
        None => return Ok(None),
    };
    if fn_info.kind != ttrpg_checker::env::FnKind::Function {
        return Ok(None);
    }

    let params = &fn_info.params;

    // Build slot mapping (arg_index → param_slot) and collect arg expressions.
    // Positional args fill slots 0..N sequentially, named args fill by name.
    let mut slot_mapping: Vec<usize> = Vec::with_capacity(args.len());
    let mut slot_used: Vec<bool> = vec![false; params.len()];
    let mut next_positional = 0usize;

    for arg in args {
        let slot_idx = if let Some(ref name) = arg.name {
            match params.iter().position(|p| p.name == *name) {
                Some(p) if slot_used[p] => return Ok(None), // duplicate
                Some(p) => p,
                None => return Ok(None), // unknown param — caller will error
            }
        } else {
            if next_positional >= params.len() {
                return Ok(None); // too many positional args
            }
            let idx = next_positional;
            next_positional += 1;
            idx
        };
        slot_used[slot_idx] = true;
        slot_mapping.push(slot_idx);
    }

    // Build DefaultParam entries for each param slot.
    let param_names: Vec<Name> = params.iter().map(|p| p.name.clone()).collect();
    let mut default_params: Vec<DefaultParam> = Vec::with_capacity(params.len());
    for (i, param) in params.iter().enumerate() {
        if slot_used[i] {
            // Will be filled by evaluated arg.
            default_params.push(DefaultParam {
                name: param.name.clone(),
                provided_value: None,
                default_expr: None,
            });
        } else if param.has_default {
            if let Some(default_expr) = fn_decl.params.get(i).and_then(|p| p.default.as_ref()) {
                default_params.push(DefaultParam {
                    name: param.name.clone(),
                    provided_value: None,
                    default_expr: Some(default_expr.clone()),
                });
            } else {
                return Ok(None); // missing default expr
            }
        } else {
            return Ok(None); // missing required arg — caller will error
        }
    }

    let arg_exprs: Vec<Spanned<ExprKind>> = args.iter().map(|a| a.value.clone()).collect();

    Ok(Some((
        Frame::CallSetup {
            target: CallTarget::Function {
                callee: callee_name,
                body: fn_decl.body.clone(),
                slot_mapping,
                param_names,
                default_params,
            },
            arg_exprs,
            arg_index: 0,
            evaluated: Vec::new(),
            child_result: None,
            awaiting_child: false,
            span: stmt.span,
        },
        awaiting,
    )))
}

/// Evaluate an expression using the frame-based ExprEval machinery.
///
/// Compiles the expression to ExprWork and runs it synchronously via
/// `run_frame_to_completion_sync`.
pub(crate) fn eval_expr_via_frame(
    core: &RuntimeCore,
    env: &mut ExecEnv,
    sp: &dyn StateProvider,
    eh: &mut dyn EffectHandler,
    expr: &Spanned<ExprKind>,
) -> Result<Value, RuntimeError> {
    // Fast path for trivial expressions — avoid frame overhead.
    match &expr.node {
        ExprKind::IntLit(n) => return Ok(Value::Int(*n)),
        ExprKind::StringLit(s) => return Ok(Value::Str(s.clone())),
        ExprKind::BoolLit(b) => return Ok(Value::Bool(*b)),
        ExprKind::NoneLit => return Ok(Value::Option(None)),
        ExprKind::Ident(name) => {
            if let Some(val) = env.lookup(name) {
                return Ok(val.clone());
            }
        }
        _ => {}
    }
    let frame = compile_expr_to_frame(expr, core)?;
    run_frame_to_completion_sync(frame, core, env, sp, eh)
}

/// Run a frame (and any children it pushes) to completion synchronously.
///
/// This is the same loop as `Execution::drive()` but operates on a standalone
/// frame stack with borrowed `RuntimeCore`/`ExecEnv`/`StateProvider`/`EffectHandler`.
/// Used by `expr_eval::eval_expr_step` for synchronous evaluation of
/// child frames (DeriveEval, FunctionEval, etc.).
pub(crate) fn run_frame_to_completion_sync(
    initial: Frame,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    sp: &dyn StateProvider,
    eh: &mut dyn EffectHandler,
) -> Result<Value, RuntimeError> {
    let tracker = MutationTracker::new();
    let mut frames: Vec<Frame> = vec![initial];
    let mut final_result: Option<Result<Value, RuntimeError>> = None;

    loop {
        if frames.is_empty() {
            return final_result.unwrap_or(Ok(Value::Void));
        }

        let frame = frames
            .last_mut()
            .expect("frame stack non-empty (checked above)");
        let advance = frame.advance(core, env, sp, eh, &tracker);

        match advance {
            Advance::Yield(effect) => {
                let response = eh.handle(effect);
                if let Some(frame) = frames.last_mut() {
                    frame.receive_response(response);
                }
            }
            Advance::Push(child) => {
                frames.push(child);
            }
            Advance::Pop(value) => {
                frames.pop();
                if let Some(parent) = frames.last_mut() {
                    parent.receive_child_result(value);
                } else {
                    final_result = Some(Ok(value));
                }
            }
            Advance::Continue => {}
            Advance::Error(e) => {
                frames.pop();
                if let Some(parent) = frames.last_mut() {
                    match parent.receive_child_error(e) {
                        Ok(()) => {}
                        Err(e) => return Err(e),
                    }
                } else {
                    return Err(e);
                }
            }
        }
    }
}

/// Extract the expression from a Let/Assign/Expr/Return(Some) statement
/// for ExprEval dispatch on the async path. Returns the expression
/// to evaluate and the AwaitingFn to apply on completion.
///
/// Called only after `try_frame_dispatch_stmt` returns `Ok(None)`, so
/// call expressions have already been handled.
pub(super) fn extract_resumable_expr(
    stmt: &Spanned<StmtKind>,
) -> Option<(Spanned<ExprKind>, AwaitingFn)> {
    match &stmt.node {
        StmtKind::Expr(expr) => Some((expr.clone(), AwaitingFn::ExprStmt)),
        StmtKind::Let { name, value, .. } => {
            Some((value.clone(), AwaitingFn::LetBinding { name: name.clone() }))
        }
        StmtKind::Assign { target, op, value } => Some((
            value.clone(),
            AwaitingFn::Assign {
                target: target.clone(),
                op: *op,
                span: stmt.span,
            },
        )),
        StmtKind::Return(Some(expr)) => Some((expr.clone(), AwaitingFn::Return)),
        _ => None,
    }
}

/// Compile an expression for ExprEval, returning an error if compilation fails.
pub(super) fn compile_expr_to_frame(
    expr: &Spanned<ExprKind>,
    core: &RuntimeCore,
) -> Result<Frame, RuntimeError> {
    if let Some(work) = crate::expr_eval::compile_expr(expr, &core.type_env, &core.program) {
        Ok(Frame::ExprEval {
            work,
            operands: Vec::new(),
            pc: 0,
            child_result: None,
            scope_depth: 0,
        })
    } else {
        Err(RuntimeError::with_span(
            "expression could not be compiled for frame-based eval",
            expr.span,
        ))
    }
}

/// Compile an expression and wrap in `Advance::Push`, or return `Advance::Error`.
pub(super) fn compile_expr_push(expr: &Spanned<ExprKind>, core: &RuntimeCore) -> Advance {
    match compile_expr_to_frame(expr, core) {
        Ok(frame) => Advance::Push(frame),
        Err(e) => Advance::Error(e),
    }
}

/// Parse a list of BudgetSpec struct values into (actor, budget) pairs.
pub(super) fn parse_budget_spec_entries(
    spec_list: &[Value],
    span: Span,
) -> Result<Vec<(EntityRef, BTreeMap<Name, Value>)>, RuntimeError> {
    let mut entries = Vec::with_capacity(spec_list.len());
    for item in spec_list {
        match item {
            Value::Struct { name, fields } if name == "BudgetSpec" => {
                let actor = match fields.get("actor") {
                    Some(Value::Entity(r)) => *r,
                    _ => {
                        return Err(RuntimeError::with_span(
                            "with_budgets: BudgetSpec missing entity `actor` field",
                            span,
                        ));
                    }
                };
                let budget = match fields.get("budget") {
                    Some(Value::Struct {
                        name: bn,
                        fields: bf,
                    }) if bn == "TurnBudget" => bf.clone(),
                    _ => {
                        return Err(RuntimeError::with_span(
                            "with_budgets: BudgetSpec missing TurnBudget `budget` field",
                            span,
                        ));
                    }
                };
                entries.push((actor, budget));
            }
            _ => {
                return Err(RuntimeError::with_span(
                    "with_budgets: list elements must be BudgetSpec structs",
                    span,
                ));
            }
        }
    }
    Ok(entries)
}

// ── Modify-applied event helpers ───────────────────────────────

/// Build modify_applied event payloads from modifiers and find matching hooks.
///
/// This is the pure (no-Interpreter) equivalent of the payload-building and
/// hook-finding logic in `pipeline::emit_modify_applied_events`. Returns the
/// hooks and payloads needed to construct an `EmitHooks` frame, or `None` if
/// no hooks match (fast path).
pub(super) fn build_modify_hooks_frame(
    core: &RuntimeCore,
    sp: &dyn StateProvider,
    env: &ExecEnv,
    modifiers: &[OwnedModifier],
    fn_name: &str,
    span: Span,
) -> Result<Option<Frame>, RuntimeError> {
    use crate::effect::ModifySource;
    use std::collections::HashSet;

    // Fast path: skip if no hooks listen for modify_applied.
    if !core.type_env.trigger_index.contains_key("modify_applied") {
        return Ok(None);
    }

    // Check emit depth.
    if env.emit_depth >= crate::MAX_EMIT_DEPTH {
        return Err(RuntimeError::with_span(
            format!(
                "emit depth limit ({}) exceeded — possible circular emit chain from modify_applied",
                crate::MAX_EMIT_DEPTH,
            ),
            span,
        ));
    }

    // Deduplicate by condition_id and build payloads.
    let mut seen_ids: HashSet<u64> = HashSet::new();
    let mut all_hooks: Vec<HookInfo> = Vec::new();
    let mut all_cond_handlers: Vec<ConditionHandlerInfo> = Vec::new();
    let mut last_payload = None;

    for modifier in modifiers {
        let cond_id = match modifier.condition_id {
            Some(id) => id,
            None => continue,
        };
        if !seen_ids.insert(cond_id) {
            continue;
        }
        let bearer = match &modifier.bearer {
            Some(b) => b.clone(),
            None => continue,
        };
        let condition_name = match &modifier.source {
            ModifySource::Condition(name) => name.clone(),
            _ => continue,
        };

        let mut cond_fields = BTreeMap::new();
        cond_fields.insert(Name::from("name"), Value::Str(condition_name.to_string()));
        cond_fields.insert(Name::from("id"), Value::Int(cond_id as i64));
        cond_fields.insert(
            Name::from("duration"),
            modifier.condition_duration.clone().unwrap_or(Value::Void),
        );
        let condition_value = Value::Struct {
            name: Name::from("ActiveCondition"),
            fields: cond_fields,
        };

        let mut all_fields = BTreeMap::new();
        all_fields.insert(Name::from("bearer"), bearer);
        all_fields.insert(Name::from("condition"), condition_value);
        all_fields.insert(Name::from("target_fn"), Value::Str(fn_name.to_string()));
        let payload = Value::Struct {
            name: Name::from("__event_modify_applied"),
            fields: all_fields,
        };

        let candidates = sp.entities_in_play();

        let hook_result = crate::event::find_matching_hooks(
            &core.program,
            &core.type_env,
            sp,
            "modify_applied",
            &payload,
            &candidates,
        )?;
        for h in hook_result.hooks {
            all_hooks.push(HookInfo {
                hook_name: h.name,
                actor: h.target,
            });
        }

        let cond_result = crate::event::find_matching_condition_handlers(
            &core.program,
            &core.type_env,
            sp,
            "modify_applied",
            &payload,
            &candidates,
        )?;
        for h in cond_result.handlers {
            all_cond_handlers.push(ConditionHandlerInfo {
                target: h.bearer,
                condition_name: h.condition_name,
                instance_id: h.instance_id,
                handler_index: h.clause_index,
            });
        }

        last_payload = Some(payload);
    }

    if all_hooks.is_empty() && all_cond_handlers.is_empty() {
        return Ok(None);
    }

    // Use the last payload as the representative payload for hook dispatch.
    let payload = last_payload.expect("at least one hook matched (checked above)");

    Ok(Some(Frame::EmitHooks {
        hooks: all_hooks,
        condition_handlers: all_cond_handlers,
        index: 0,
        payload,
        initialized: false,
        child_result: None,
    }))
}

/// Local suppress-modify data for modifier collection.
pub(crate) struct NativeSuppressModify {
    pub(crate) clause: ttrpg_ast::ast::SuppressModifyClause,
    pub(crate) bearer: Value,
    pub(crate) receiver_name: Name,
    pub(crate) condition_params: BTreeMap<Name, Value>,
}

// ── Frame-based modifier collection ────────────────────────────
//
// These types support the CollectCheck / SuppressCheck phases of
// CostEval and DeriveEval. Instead of running BindingCheck frames
// synchronously, the parent frame pushes one BindingCheck child per
// candidate and collects results across multiple advance() calls.

/// A modifier candidate whose bindings need evaluation via a
/// BindingCheck child frame. Fields are `Option` because the frame
/// and modifier are moved out (taken) when the candidate is processed.
pub(crate) struct CollectCandidate {
    /// The BindingCheck frame to push as a child. Taken when pushed.
    pub(crate) frame: Option<Frame>,
    /// For Caller-mode checks: bindings to push into scope before the
    /// child runs. Empty for Owned-mode checks.
    pub(crate) caller_scope: Vec<(Name, Value)>,
    /// Sort key (condition gained_at, or u64::MAX for options).
    pub(crate) gained_at: u64,
    /// The modifier to add if the binding check passes. Taken on match.
    pub(crate) modifier: Option<OwnedModifier>,
}

/// A suppression candidate whose bindings need evaluation via a
/// BindingCheck child frame.
pub(crate) struct SuppressCandidate {
    /// The BindingCheck frame to push. Taken when pushed.
    pub(crate) frame: Option<Frame>,
    /// Caller-mode scope bindings.
    pub(crate) caller_scope: Vec<(Name, Value)>,
    /// Index of the modifier being checked for suppression.
    pub(crate) modifier_index: usize,
}

/// State for frame-based modifier collection iteration.
///
/// Boxed inside CostEval / DeriveEval to avoid bloating the Frame enum.
pub(crate) struct ModifierCollectState {
    /// Candidates needing a BindingCheck child frame.
    pub(crate) candidates: Vec<CollectCandidate>,
    /// Accumulated modifiers from passed checks and direct (no-binding) matches.
    /// Stored as (gained_at, modifier) for sorting.
    pub(crate) collected: Vec<(u64, OwnedModifier)>,
    /// Current index into `candidates`.
    pub(crate) index: usize,
    /// Boundary: candidates[0..condition_count] are condition-sourced,
    /// candidates[condition_count..] are option-sourced (DeriveEval only).
    pub(crate) condition_count: usize,
    /// Option modifiers that matched without needing binding checks.
    pub(crate) option_modifiers: Vec<OwnedModifier>,
    /// Suppression data collected during init (DeriveEval only).
    pub(crate) suppressions: Vec<NativeSuppressModify>,
    /// Suppression candidates built after collection completes.
    pub(crate) suppress_candidates: Vec<SuppressCandidate>,
    /// Current index into `suppress_candidates`.
    pub(crate) suppress_index: usize,
    /// Indices of modifiers marked as suppressed.
    pub(crate) suppressed: std::collections::HashSet<usize>,
    /// Result from the current BindingCheck child frame.
    pub(crate) child_result: Option<Result<Value, RuntimeError>>,
    /// Whether a caller-managed scope was pushed for the current candidate.
    pub(crate) scope_pushed: bool,
}

/// Apply a value to a named field of a `RollResult`.
/// Used by phase-2 ResultOverride handling.
pub(super) fn apply_roll_result_field(rr: &mut crate::value::RollResult, field: &str, val: Value) {
    match field {
        "total" => {
            if let Value::Int(n) = val {
                rr.total = n;
            }
        }
        "unmodified" => {
            if let Value::Int(n) = val {
                rr.unmodified = n;
            }
        }
        "modifier" => {
            if let Value::Int(n) = val {
                rr.modifier = n;
            }
        }
        "expr" => {
            if let Value::DiceExpr(de) = val {
                rr.expr = de;
            }
        }
        "dice" => {
            if let Value::List(items) = val {
                rr.dice = items
                    .iter()
                    .filter_map(|v| {
                        if let Value::Int(n) = v {
                            Some(*n)
                        } else {
                            None
                        }
                    })
                    .collect();
            }
        }
        "kept" => {
            if let Value::List(items) = val {
                rr.kept = items
                    .iter()
                    .filter_map(|v| {
                        if let Value::Int(n) = v {
                            Some(*n)
                        } else {
                            None
                        }
                    })
                    .collect();
            }
        }
        _ => {}
    }
}

// ── Shared modifier pipeline helpers ────────────────────────────
//
// These functions deduplicate logic shared between CostEval and
// DeriveEval modifier collection and application.

/// Build an `OwnedModifier` from a condition instance and its modify clause.
///
/// Used by both CostEval::CollectModifiers and DeriveEval::CollectModifiers
/// when building the candidate list from active conditions.
pub(super) fn owned_modifier_from_condition(
    condition: &ActiveCondition,
    cond_decl: &ttrpg_ast::ast::ConditionDecl,
    clause: &ttrpg_ast::ast::ModifyClause,
) -> OwnedModifier {
    use crate::effect::ModifySource;
    OwnedModifier {
        source: ModifySource::Condition(condition.name.clone()),
        clause: clause.clone(),
        bearer: Some(Value::Entity(condition.bearer)),
        receiver_name: Some(cond_decl.receiver_name.clone()),
        condition_params: condition.params.clone(),
        condition_id: Some(condition.id),
        condition_duration: Some(condition.duration.clone()),
        condition_state_fields: condition.state_fields.clone(),
    }
}

/// Build scope bindings from a condition (receiver + params + state fields).
///
/// Used to build both `caller_scope` (CostEval, Caller mode) and
/// `scope_bindings` (DeriveEval, Owned mode) during modifier collection.
/// The caller may extend the returned vec with additional bindings
/// (e.g. function params for Owned-mode BindingChecks).
pub(super) fn build_condition_scope_bindings(
    cond_decl: &ttrpg_ast::ast::ConditionDecl,
    condition: &ActiveCondition,
) -> Vec<(Name, Value)> {
    let mut bindings = Vec::new();
    bindings.push((
        cond_decl.receiver_name.clone(),
        Value::Entity(condition.bearer),
    ));
    for (name, val) in &condition.params {
        bindings.push((name.clone(), val.clone()));
    }
    if !condition.state_fields.is_empty() {
        bindings.push((
            Name::from("state"),
            Value::Struct {
                name: Name::from("state"),
                fields: condition.state_fields.clone(),
            },
        ));
    }
    bindings
}

/// Bind a modifier's condition context into the current scope.
///
/// Binds receiver, condition params, and state fields. Used by all three
/// modifier application phases (Cost, Phase1, Phase2) after pushing scope.
pub(super) fn bind_modifier_context(env: &mut ExecEnv, modifier: &OwnedModifier) {
    if let (Some(receiver_name), Some(bearer)) = (&modifier.receiver_name, &modifier.bearer) {
        env.bind(receiver_name.clone(), bearer.clone());
    }
    for (name, val) in &modifier.condition_params {
        env.bind(name.clone(), val.clone());
    }
    if !modifier.condition_state_fields.is_empty() {
        env.bind(
            Name::from("state"),
            Value::Struct {
                name: Name::from("state"),
                fields: modifier.condition_state_fields.clone(),
            },
        );
    }
}

/// Result of advancing a CollectCheck phase.
pub(super) enum CollectCheckAction {
    /// Push this BindingCheck child frame.
    PushChild(Box<Frame>),
    /// All candidates have been processed.
    Done,
}

/// Advance the CollectCheck phase shared by CostEval and DeriveEval.
///
/// Processes the previous BindingCheck child result (if any), routes the
/// modifier to the appropriate collection, and either pushes the next
/// candidate's BindingCheck frame or signals completion.
///
/// When `route_options` is true (DeriveEval), modifiers at index >=
/// `condition_count` are routed to `option_modifiers` instead of `collected`.
pub(super) fn advance_collect_check(
    cs: &mut ModifierCollectState,
    env: &mut ExecEnv,
    route_options: bool,
) -> Result<CollectCheckAction, RuntimeError> {
    // Process previous child result (if any).
    if let Some(result) = cs.child_result.take() {
        if cs.scope_pushed {
            env.pop_scope();
            cs.scope_pushed = false;
        }
        match result {
            Ok(Value::Bool(true)) => {
                let candidate = &mut cs.candidates[cs.index];
                let gained_at = candidate.gained_at;
                if let Some(modifier) = candidate.modifier.take() {
                    if route_options && cs.index >= cs.condition_count {
                        cs.option_modifiers.push(modifier);
                    } else {
                        cs.collected.push((gained_at, modifier));
                    }
                }
            }
            Ok(Value::Bool(false)) => { /* binding check failed, skip */ }
            Ok(other) => {
                return Err(RuntimeError::new(format!(
                    "BindingCheck returned non-Bool: {other:?}",
                )));
            }
            Err(e) => return Err(e),
        }
        cs.index += 1;
    }

    // Push next candidate or finish.
    if cs.index >= cs.candidates.len() {
        Ok(CollectCheckAction::Done)
    } else {
        let candidate = &mut cs.candidates[cs.index];
        if !candidate.caller_scope.is_empty() {
            env.push_scope();
            for (n, v) in &candidate.caller_scope {
                env.bind(n.clone(), v.clone());
            }
            cs.scope_pushed = true;
        }
        let child_frame = candidate
            .frame
            .take()
            .expect("CollectCheck: frame already taken");
        Ok(CollectCheckAction::PushChild(Box::new(child_frame)))
    }
}
