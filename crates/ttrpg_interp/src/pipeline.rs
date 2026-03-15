use std::collections::{BTreeMap, HashMap, HashSet};

use ttrpg_ast::ast::{
    ConditionClause, ModifyClause, ModifyStmt, ModifyTarget, SelectorPredicate,
    SuppressModifyClause,
};
use ttrpg_ast::{Name, Span};
use ttrpg_checker::env::FnInfo;

use crate::RuntimeError;
use crate::effect::{Effect, FieldChange, ModifySource, Phase, Response};
use crate::eval::{eval_expr, value_eq};
use crate::state::{ActiveCondition, EntityRef};
use crate::value::Value;
use crate::{Env, MAX_EMIT_DEPTH, action, event};

// ── Supporting types ────────────────────────────────────────────

use ttrpg_ast::ast::Program;

/// Compute the set of winning condition instance IDs for stacking policies.
///
/// Groups active conditions by `(condition_name, bearer)` and applies the
/// stacking policy declared on each condition. Returns the set of instance
/// IDs whose effects should be applied; all others are suppressed.
pub(crate) fn compute_stacking_winners(
    conditions: &[ActiveCondition],
    program: &Program,
) -> HashSet<u64> {
    use ttrpg_ast::ast::{Direction, StackingPolicy};

    let mut winners = HashSet::new();

    // Group by (condition_name, bearer_id)
    let mut groups: BTreeMap<(Name, u64), Vec<&ActiveCondition>> = BTreeMap::new();
    for cond in conditions {
        groups
            .entry((cond.name.clone(), cond.bearer.0))
            .or_default()
            .push(cond);
    }

    for ((cond_name, _bearer_id), instances) in &groups {
        let policy = program
            .conditions
            .get(cond_name.as_str())
            .map_or(&StackingPolicy::All, |decl| &decl.stacking);

        match policy {
            StackingPolicy::All => {
                for inst in instances {
                    winners.insert(inst.id);
                }
            }
            StackingPolicy::First => {
                // Oldest wins: min by (gained_at, id)
                if let Some(winner) = instances.iter().min_by_key(|c| (c.gained_at, c.id)) {
                    winners.insert(winner.id);
                }
            }
            StackingPolicy::BestBy { param, direction } => {
                let extract_int = |c: &ActiveCondition| -> Option<i64> {
                    match c.params.get(&param.node) {
                        Some(Value::Int(n)) => Some(*n),
                        _ => None,
                    }
                };
                if let Some(winner) = instances.iter().max_by(|a, b| {
                    let a_val = extract_int(a);
                    let b_val = extract_int(b);
                    match (a_val, b_val) {
                        (Some(av), Some(bv)) => {
                            let primary = match direction {
                                Direction::Highest => av.cmp(&bv),
                                Direction::Lowest => bv.cmp(&av),
                            };
                            // Tie-break: oldest (lowest gained_at), then lowest id
                            primary
                                .then_with(|| b.gained_at.cmp(&a.gained_at))
                                .then_with(|| b.id.cmp(&a.id))
                        }
                        // Instances without the param lose to those with it
                        (Some(_), None) => std::cmp::Ordering::Greater,
                        (None, Some(_)) => std::cmp::Ordering::Less,
                        (None, None) => {
                            // Both missing: fall back to oldest
                            b.gained_at.cmp(&a.gained_at).then_with(|| b.id.cmp(&a.id))
                        }
                    }
                }) {
                    winners.insert(winner.id);
                }
            }
        }
    }

    winners
}

// ── Condition traversal helper ──────────────────────────────────

/// Snapshotted conditions for a single entity with stacking winners computed.
pub(crate) struct ConditionSnapshot {
    pub conditions: Vec<ActiveCondition>,
    pub winners: HashSet<u64>,
}

/// Entity extraction + deduplication + per-entity condition snapshots.
///
/// Shared infrastructure for suppress scanning and
/// condition event handler dispatch.
pub(crate) struct ConditionTraversal {
    /// Entity-typed values from the payload, deduplicated by entity ID,
    /// in scan order (params first, then fields).
    pub entities: Vec<(Name, EntityRef)>,
    /// Per-entity snapshotted conditions with stacking winners.
    pub snapshots: HashMap<EntityRef, ConditionSnapshot>,
}

impl ConditionTraversal {
    /// Build a traversal from a list of `(name, entity)` pairs.
    ///
    /// Deduplicates by entity ID (keeping first occurrence), filters to
    /// only those entities in `candidates`, snapshots conditions, and
    /// computes stacking winners.
    pub fn build(
        named_entities: Vec<(Name, EntityRef)>,
        candidates: &[EntityRef],
        state: &dyn crate::state::StateProvider,
        program: &Program,
    ) -> Result<Self, RuntimeError> {
        let candidate_set: HashSet<EntityRef> = candidates.iter().copied().collect();
        let mut seen_ids: HashSet<u64> = HashSet::new();
        let mut entities: Vec<(Name, EntityRef)> = Vec::new();

        for (name, eref) in named_entities {
            if !candidate_set.contains(&eref) {
                continue;
            }
            if !seen_ids.insert(eref.0) {
                continue; // deduplicate by entity ID
            }
            entities.push((name, eref));
        }

        let mut snapshots = HashMap::new();
        for (_name, eref) in &entities {
            if snapshots.contains_key(eref) {
                continue;
            }
            let conditions = match state.read_conditions(eref) {
                Some(c) => c,
                None => {
                    return Err(RuntimeError::new(format!(
                        "read_conditions returned None for entity {eref:?} — host state out of sync",
                    )));
                }
            };
            let winners = compute_stacking_winners(&conditions, program);
            snapshots.insert(
                *eref,
                ConditionSnapshot {
                    conditions,
                    winners,
                },
            );
        }

        Ok(ConditionTraversal {
            entities,
            snapshots,
        })
    }
}

/// Which lifecycle hook to execute.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum LifecycleKind {
    OnApply,
    OnRemove,
}

/// Execute lifecycle blocks (on_apply or on_remove) for a condition.
///
/// Walks the ancestor chain (parents first), executing each matching block
/// with the bearer and condition params in scope. The `in_lifecycle_block`
/// counter is incremented to prevent `apply_condition`/`remove_condition`/`revoke()`
/// calls inside the blocks.
///
/// If `state_map` is `Some`, threads a mutable state map through all ancestor
/// blocks. Each block gets `state` bound as a mutable struct; after each block
/// the mutated value is read back. Returns the final state map.
pub(crate) fn execute_lifecycle_blocks(
    env: &mut Env,
    condition_name: &str,
    bearer: crate::state::EntityRef,
    params: &BTreeMap<Name, Value>,
    kind: LifecycleKind,
    condition_instance_id: u64,
    state_map: Option<BTreeMap<Name, Value>>,
) -> Result<Option<BTreeMap<Name, Value>>, RuntimeError> {
    let decl = env.interp.program.conditions.get(condition_name);
    env.lifecycle_condition_stack.push(condition_instance_id);
    env.in_lifecycle_block += 1;

    let mut current_state = state_map;

    let result = (|| {
        if let Some(decl) = decl {
            for clause in &decl.clauses {
                let block = match (kind, clause) {
                    (LifecycleKind::OnApply, ConditionClause::OnApply(lb)) => &lb.body,
                    (LifecycleKind::OnRemove, ConditionClause::OnRemove(lb)) => &lb.body,
                    _ => continue,
                };
                env.push_scope();
                env.bind(decl.receiver_name.clone(), Value::Entity(bearer));
                for (pname, pval) in params {
                    env.bind(pname.clone(), pval.clone());
                }
                // Bind state fields as a mutable struct if present
                if let Some(ref state_fields) = current_state {
                    env.bind(
                        Name::from("state"),
                        Value::Struct {
                            name: Name::from("state"),
                            fields: state_fields.clone(),
                        },
                    );
                }
                let r = crate::eval::eval_block(env, block);
                // Read back mutated state before popping scope
                if current_state.is_some()
                    && let Some(Value::Struct { fields, .. }) =
                        env.lookup(&Name::from("state")).cloned()
                {
                    current_state = Some(fields);
                }
                env.pop_scope();
                env.return_value = None; // clear early-return flag at call boundary
                r?;
            }
        }
        Ok(())
    })();

    env.in_lifecycle_block -= 1;
    env.lifecycle_condition_stack.pop();
    result?;
    Ok(current_state)
}

/// Collect modifiers from conditions and options, returning owned data.
///
/// Returns modifiers in application order:
/// - Condition modifiers ordered by `gained_at` (oldest first), declaration order within
/// - Option modifiers after all conditions, declaration order within
pub(crate) fn collect_modifiers_owned(
    env: &mut Env,
    fn_name: &str,
    fn_info: &FnInfo,
    bound_params: &[(Name, Value)],
) -> Result<Vec<OwnedModifier>, RuntimeError> {
    let mut condition_modifiers: Vec<(u64, OwnedModifier)> = Vec::new(); // (gained_at, modifier)
    let mut seen_condition_ids: HashSet<u64> = HashSet::new();
    let mut suppressions: Vec<ActiveSuppressModify> = Vec::new();

    // 1. For each entity-typed param, query conditions
    for (i, param_info) in fn_info.params.iter().enumerate() {
        if !param_info.ty.is_entity() {
            continue;
        }
        let entity_ref = match &bound_params[i].1 {
            Value::Entity(e) => *e,
            _ => continue,
        };

        let conditions = match env.state.read_conditions(&entity_ref) {
            Some(c) => c,
            None => {
                return Err(RuntimeError::new(format!(
                    "read_conditions returned None for entity {entity_ref:?} — host state out of sync",
                )));
            }
        };

        let stacking_winners = compute_stacking_winners(&conditions, env.interp.program);

        for condition in &conditions {
            // Deduplicate by condition id
            if !seen_condition_ids.insert(condition.id) {
                continue;
            }

            // Skip conditions that lost stacking precedence
            if !stacking_winners.contains(&condition.id) {
                continue;
            }

            // Look up the condition decl directly
            let cond_decl = match env.interp.program.conditions.get(condition.name.as_str()) {
                Some(d) => d,
                None => continue,
            };

            for clause_item in &cond_decl.clauses {
                // Collect suppress-modify clauses
                if let ConditionClause::SuppressModify(sm) = clause_item {
                    suppressions.push(ActiveSuppressModify {
                        clause: sm.clone(),
                        bearer: Value::Entity(condition.bearer),
                        receiver_name: cond_decl.receiver_name.clone(),
                        condition_params: condition.params.clone(),
                    });
                    continue;
                }

                let clause = match clause_item {
                    ConditionClause::Modify(c) => c,
                    ConditionClause::Suppress(_)
                    | ConditionClause::SuppressModify(_)
                    | ConditionClause::OnApply(_)
                    | ConditionClause::OnRemove(_)
                    | ConditionClause::OnEvent(_)
                    | ConditionClause::Include(_) => continue,
                };

                // Does the target function name match?
                match &clause.target {
                    ModifyTarget::Named(name) => {
                        if name != fn_name {
                            continue;
                        }
                    }
                    ModifyTarget::Selector(_) => {
                        match env.interp.type_env.selector_matches.get(&clause.id) {
                            Some(set) if set.contains(fn_name) => {}
                            _ => continue,
                        }
                    }
                    ModifyTarget::Cost(_) => {
                        // Cost modifiers are handled separately; skip here
                        continue;
                    }
                }

                // Check bindings: each binding maps a param name to an expression.
                // Evaluate the expression in a scope with the condition receiver bound.
                // The binding matches if param[binding.name] equals the evaluated value.
                if check_modify_bindings(
                    env,
                    clause,
                    condition,
                    &cond_decl.receiver_name,
                    fn_info,
                    bound_params,
                )? {
                    condition_modifiers.push((
                        condition.gained_at,
                        OwnedModifier {
                            source: ModifySource::Condition(condition.name.clone()),
                            clause: clause.clone(),
                            bearer: Some(Value::Entity(condition.bearer)),
                            receiver_name: Some(cond_decl.receiver_name.clone()),
                            condition_params: condition.params.clone(),
                            condition_id: Some(condition.id),
                            condition_duration: Some(condition.duration.clone()),
                            condition_state_fields: condition.state_fields.clone(),
                        },
                    ));
                }
            }
        }
    }

    // Sort condition modifiers by gained_at (stable sort preserves declaration order)
    condition_modifiers.sort_by_key(|(gained_at, _)| *gained_at);

    let mut result: Vec<OwnedModifier> = condition_modifiers.into_iter().map(|(_, m)| m).collect();

    // 2. Query enabled options and check their modify clauses
    let mut enabled_options = env.state.read_enabled_options();
    // Sort by declaration order for deterministic application
    let option_order = &env.interp.program.option_order;
    enabled_options.sort_by_key(|name| {
        option_order
            .iter()
            .position(|o| *o == name.as_str())
            .unwrap_or(usize::MAX)
    });
    for opt_name in &enabled_options {
        let opt_decl = match env.interp.program.options.get(opt_name.as_str()) {
            Some(decl) => decl,
            None => continue,
        };

        let clauses = match &opt_decl.when_enabled {
            Some(clauses) => clauses,
            None => continue,
        };

        for clause in clauses {
            match &clause.target {
                ModifyTarget::Named(name) => {
                    if name != fn_name {
                        continue;
                    }
                }
                ModifyTarget::Selector(_) => {
                    match env.interp.type_env.selector_matches.get(&clause.id) {
                        Some(set) if set.contains(fn_name) => {}
                        _ => continue,
                    }
                }
                ModifyTarget::Cost(_) => {
                    // Cost modifiers are handled separately; skip here
                    continue;
                }
            }

            // Options have no receiver — check bindings without bearer
            if check_option_modify_bindings(env, clause, fn_info, bound_params)? {
                result.push(OwnedModifier {
                    source: ModifySource::Option(opt_name.clone()),
                    clause: clause.clone(),
                    bearer: None,
                    receiver_name: None,
                    condition_params: BTreeMap::new(),
                    condition_id: None,
                    condition_duration: None,
                    condition_state_fields: BTreeMap::new(),
                });
            }
        }
    }

    // 3. Filter out modifiers suppressed by active suppress-modify clauses
    if !suppressions.is_empty() {
        let mut filtered = Vec::with_capacity(result.len());
        for modifier in result {
            if !is_modifier_suppressed(env, &modifier, fn_info, bound_params, &suppressions)? {
                filtered.push(modifier);
            }
        }
        result = filtered;
    }

    Ok(result)
}

/// A collected suppress-modify clause with its condition context.
struct ActiveSuppressModify {
    clause: SuppressModifyClause,
    bearer: Value,
    receiver_name: Name,
    condition_params: BTreeMap<Name, Value>,
}

/// Check if a modifier is suppressed by any active suppress-modify clause.
fn is_modifier_suppressed(
    env: &mut Env,
    modifier: &OwnedModifier,
    fn_info: &FnInfo,
    bound_params: &[(Name, Value)],
    suppressions: &[ActiveSuppressModify],
) -> Result<bool, RuntimeError> {
    for sup in suppressions {
        // Check selector predicates against the modifier
        let preds_match = sup.clause.predicates.iter().all(|pred| match pred {
            SelectorPredicate::Tag(tag) => modifier.clause.tags.contains(tag),
            SelectorPredicate::Returns(type_expr) => {
                // Match against fn return type via type_env
                if let Some(fi) = env.interp.type_env.functions.get(fn_info.name.as_str()) {
                    let resolved = env.interp.type_env.resolve_type(type_expr);
                    fi.return_type == resolved
                } else {
                    false
                }
            }
            SelectorPredicate::HasParam { name, ty } => fn_info.params.iter().any(|p| {
                if p.name != *name {
                    return false;
                }
                if let Some(te) = ty {
                    let resolved = env.interp.type_env.resolve_type(te);
                    p.ty == resolved
                } else {
                    true
                }
            }),
        });
        if !preds_match {
            continue;
        }

        // Check bindings: each suppress binding must match the modifier's bound params
        if sup.clause.bindings.is_empty() {
            return Ok(true);
        }

        // Evaluate suppress bindings in a scope with the condition receiver bound
        env.push_scope();
        env.bind(sup.receiver_name.clone(), sup.bearer.clone());
        for (pname, pval) in &sup.condition_params {
            env.bind(pname.clone(), pval.clone());
        }

        let mut bindings_match = true;
        for binding in &sup.clause.bindings {
            // Find the corresponding param value in the modifier's target function call
            let param_val = match bound_params.iter().find(|(name, _)| *name == binding.name) {
                Some((_, val)) => val.clone(),
                None => {
                    bindings_match = false;
                    break;
                }
            };

            if let Some(value_expr) = &binding.value {
                let binding_val = eval_expr(env, value_expr)?;
                if !value_eq(env.state, &param_val, &binding_val) {
                    bindings_match = false;
                    break;
                }
            }
        }

        env.pop_scope();

        if bindings_match {
            return Ok(true);
        }
    }
    Ok(false)
}

/// An owned modifier with cloned clause data.
#[derive(Clone)]
pub(crate) struct OwnedModifier {
    pub source: ModifySource,
    pub clause: ModifyClause,
    pub bearer: Option<Value>,
    pub receiver_name: Option<Name>,
    /// Condition parameters (e.g., source: Entity(1) for Frightened(source: attacker)).
    pub condition_params: BTreeMap<Name, Value>,
    /// Unique condition instance id (for deduplication in modify_applied events).
    pub condition_id: Option<u64>,
    /// Duration of the condition (for hooks that need to check e.g. "until_next_use").
    pub condition_duration: Option<Value>,
    /// Condition state fields (for read-only access in modify body/bindings).
    pub condition_state_fields: BTreeMap<Name, Value>,
}

/// Check if a condition modify clause's bindings match the current call params.
///
/// Each binding `name: expr` maps a target function param name to an expression
/// evaluated in a scope with the condition's receiver bound. The binding matches
/// if the param value equals the evaluated expression.
fn check_modify_bindings(
    env: &mut Env,
    clause: &ModifyClause,
    condition: &ActiveCondition,
    receiver_name: &Name,
    _fn_info: &FnInfo,
    bound_params: &[(Name, Value)],
) -> Result<bool, RuntimeError> {
    // Empty bindings always match
    if clause.bindings.is_empty() {
        return Ok(true);
    }

    let receiver_name = receiver_name.clone();

    for binding in &clause.bindings {
        // Find the param value for this binding name
        let param_val = match bound_params.iter().find(|(name, _)| *name == binding.name) {
            Some((_, val)) => val.clone(),
            None => return Ok(false),
        };

        // Evaluate binding expression in a temporary scope with receiver + condition params + fn params bound
        env.push_scope();
        env.bind(receiver_name.clone(), Value::Entity(condition.bearer));
        // Bind condition params (e.g., source, level)
        for (name, val) in &condition.params {
            env.bind(name.clone(), val.clone());
        }
        for (name, val) in bound_params {
            env.bind(name.clone(), val.clone());
        }
        // Bind state fields as read-only struct
        if !condition.state_fields.is_empty() {
            env.bind(
                Name::from("state"),
                Value::Struct {
                    name: Name::from("state"),
                    fields: condition.state_fields.clone(),
                },
            );
        }

        // Wildcard binding — always matches
        let binding_val = match binding.value {
            Some(ref expr) => eval_expr(env, expr),
            None => {
                env.pop_scope();
                continue;
            }
        };
        env.pop_scope();

        let val = binding_val?;
        if !value_eq(env.state, &param_val, &val) {
            return Ok(false);
        }
    }

    Ok(true)
}

/// Check if an option modify clause's bindings match the current call params.
///
/// Options have no receiver — bindings are evaluated in the current param context.
fn check_option_modify_bindings(
    env: &mut Env,
    clause: &ModifyClause,
    _fn_info: &FnInfo,
    bound_params: &[(Name, Value)],
) -> Result<bool, RuntimeError> {
    if clause.bindings.is_empty() {
        return Ok(true);
    }

    for binding in &clause.bindings {
        let param_val = match bound_params.iter().find(|(name, _)| *name == binding.name) {
            Some((_, val)) => val.clone(),
            None => return Ok(false),
        };

        // Wildcard binding — always matches
        let binding_expr = match binding.value {
            Some(ref expr) => expr,
            None => continue,
        };

        // Evaluate binding expression in a temporary scope with params bound
        env.push_scope();
        for (name, val) in bound_params {
            env.bind(name.clone(), val.clone());
        }

        let binding_val = eval_expr(env, binding_expr);
        env.pop_scope();

        let val = binding_val?;
        if !value_eq(env.state, &param_val, &val) {
            return Ok(false);
        }
    }

    Ok(true)
}

// ── Phase 1: Rewrite inputs ────────────────────────────────────

/// Execute Phase 1 of the modify pipeline: rewrite input parameters.
///
/// For each modifier, execute its modify stmts in a temporary scope.
/// ParamOverride updates params, Let binds in temp scope, If is conditional.
/// ResultOverride and ParamOverride(name="result") are skipped (Phase 2 only).
///
/// Returns the (possibly modified) params.
pub(crate) fn run_phase1(
    env: &mut Env,
    fn_name: &str,
    _fn_info: &FnInfo,
    mut params: Vec<(Name, Value)>,
    modifiers: &[OwnedModifier],
) -> Result<Vec<(Name, Value)>, RuntimeError> {
    for modifier in modifiers {
        let old_params: Vec<(Name, Value)> = params.clone();

        // Push temporary scope for this modifier
        env.push_scope();

        // Bind receiver if condition modifier
        if let (Some(bearer), Some(recv_name)) = (&modifier.bearer, &modifier.receiver_name) {
            env.bind(recv_name.clone(), bearer.clone());
        }

        // Bind condition params (e.g., source, level)
        for (name, val) in &modifier.condition_params {
            env.bind(name.clone(), val.clone());
        }

        // Bind all params of the target function (read-only access for expressions)
        for (name, val) in &params {
            env.bind(name.clone(), val.clone());
        }

        // Bind state fields as read-only struct for condition modifiers
        if !modifier.condition_state_fields.is_empty() {
            env.bind(
                Name::from("state"),
                Value::Struct {
                    name: Name::from("state"),
                    fields: modifier.condition_state_fields.clone(),
                },
            );
        }

        // Execute modify stmts (Phase 1: param overrides only)
        let result = exec_modify_stmts_phase1(env, &modifier.clause.body, &mut params);

        env.pop_scope();

        // Propagate errors after scope cleanup
        result?;

        // Collect changes for ModifyApplied effect
        let changes = collect_param_changes(&old_params, &params);
        if !changes.is_empty() {
            let response = env.emit(Effect::ModifyApplied {
                source: modifier.source.clone(),
                target_fn: Name::from(fn_name),
                phase: Phase::Phase1,
                changes,
                tags: modifier.clause.tags.clone(),
            });
            if !matches!(response, Response::Acknowledged) {
                return Err(RuntimeError::with_span(
                    format!(
                        "protocol error: expected Acknowledged for ModifyApplied, got {response:?}"
                    ),
                    modifier.clause.span,
                ));
            }
        }
    }

    Ok(params)
}

/// Execute Phase 2 of the modify pipeline: rewrite output result.
///
/// For each modifier, execute its modify stmts in a temporary scope.
/// ResultOverride and ParamOverride(name="result") update the result.
/// ParamOverride(name!=result) and regular Let/If still execute for their
/// side effects (Let bindings may be used by ResultOverride expressions).
///
/// Returns the (possibly modified) result.
pub(crate) fn run_phase2(
    env: &mut Env,
    fn_name: &str,
    fn_info: &FnInfo,
    params: &[(Name, Value)],
    mut result: Value,
    modifiers: &[OwnedModifier],
) -> Result<Value, RuntimeError> {
    for modifier in modifiers {
        // Check if this modifier has any Phase 2 stmts
        if !has_phase2_stmts(&modifier.clause.body) {
            continue;
        }

        let old_result = result.clone();

        // Push temporary scope for this modifier
        env.push_scope();

        // Bind receiver if condition modifier
        if let (Some(bearer), Some(recv_name)) = (&modifier.bearer, &modifier.receiver_name) {
            env.bind(recv_name.clone(), bearer.clone());
        }

        // Bind condition params (e.g., source, level)
        for (name, val) in &modifier.condition_params {
            env.bind(name.clone(), val.clone());
        }

        // Bind all params of the target function
        for (name, val) in params {
            env.bind(name.clone(), val.clone());
        }

        // Bind state fields as read-only struct for condition modifiers
        if !modifier.condition_state_fields.is_empty() {
            env.bind(
                Name::from("state"),
                Value::Struct {
                    name: Name::from("state"),
                    fields: modifier.condition_state_fields.clone(),
                },
            );
        }

        // Bind result
        env.bind(Name::from("result"), result.clone());

        // Execute modify stmts (Phase 2: result overrides only)
        let exec_result = exec_modify_stmts_phase2(env, &modifier.clause.body, &mut result);

        env.pop_scope();

        // Propagate errors after scope cleanup
        exec_result?;

        // Collect changes for ModifyApplied effect
        let changes = collect_result_changes(&old_result, &result, fn_info);
        if !changes.is_empty() {
            let response = env.emit(Effect::ModifyApplied {
                source: modifier.source.clone(),
                target_fn: Name::from(fn_name),
                phase: Phase::Phase2,
                changes,
                tags: modifier.clause.tags.clone(),
            });
            if !matches!(response, Response::Acknowledged) {
                return Err(RuntimeError::with_span(
                    format!(
                        "protocol error: expected Acknowledged for ModifyApplied, got {response:?}"
                    ),
                    modifier.clause.span,
                ));
            }
        }
    }

    Ok(result)
}

// ── Modify statement execution ──────────────────────────────────

fn exec_modify_stmts_phase1(
    env: &mut Env,
    stmts: &[ModifyStmt],
    params: &mut Vec<(Name, Value)>,
) -> Result<(), RuntimeError> {
    for stmt in stmts {
        match stmt {
            ModifyStmt::ParamOverride { name, value, .. } => {
                // Skip result overrides in Phase 1
                if name == "result" {
                    continue;
                }
                let val = eval_expr(env, value)?;
                // Update the param value
                if let Some(param) = params.iter_mut().find(|(n, _)| n == name) {
                    param.1 = val;
                    // Also update the scope binding so subsequent expressions see the new value
                    env.bind(name.clone(), param.1.clone());
                }
            }
            ModifyStmt::Let { name, value, .. } => {
                let val = eval_expr(env, value)?;
                env.bind(name.clone(), val);
            }
            ModifyStmt::If {
                condition,
                then_body,
                else_body,
                ..
            } => {
                // Skip if blocks that contain only Phase 2 stmts (result overrides).
                // Their conditions may reference `result` which isn't bound yet in Phase 1.
                if !has_phase1_stmts(then_body)
                    && !else_body.as_ref().is_some_and(|e| has_phase1_stmts(e))
                {
                    continue;
                }
                let cond = eval_expr(env, condition)?;
                match cond {
                    Value::Bool(true) => {
                        env.push_scope();
                        let r = exec_modify_stmts_phase1(env, then_body, params);
                        env.pop_scope();
                        // Re-sync param bindings into the outer scope after branch
                        for (name, val) in params.iter() {
                            env.bind(name.clone(), val.clone());
                        }
                        r?;
                    }
                    Value::Bool(false) => {
                        if let Some(else_stmts) = else_body {
                            env.push_scope();
                            let r = exec_modify_stmts_phase1(env, else_stmts, params);
                            env.pop_scope();
                            // Re-sync param bindings into the outer scope after branch
                            for (name, val) in params.iter() {
                                env.bind(name.clone(), val.clone());
                            }
                            r?;
                        }
                    }
                    _ => {
                        return Err(RuntimeError::with_span(
                            "modify if condition must be Bool",
                            condition.span,
                        ));
                    }
                }
            }
            ModifyStmt::ResultOverride { .. } | ModifyStmt::CostOverride { .. } => {
                // Skip in Phase 1 (CostOverride is handled in cost pipeline)
            }
        }
    }
    Ok(())
}

fn exec_modify_stmts_phase2(
    env: &mut Env,
    stmts: &[ModifyStmt],
    result: &mut Value,
) -> Result<(), RuntimeError> {
    for stmt in stmts {
        match stmt {
            ModifyStmt::ParamOverride { name, value, .. } => {
                if name == "result" {
                    // Whole-result override in Phase 2
                    let val = eval_expr(env, value)?;
                    *result = val;
                    env.bind(Name::from("result"), result.clone());
                }
                // Skip non-result param overrides in Phase 2
            }
            ModifyStmt::ResultOverride { field, value, .. } => {
                let val = eval_expr(env, value)?;
                // Update result field
                match result {
                    Value::Struct { fields, .. } => {
                        fields.insert(field.clone(), val);
                    }
                    Value::RollResult(rr) => match field.as_str() {
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
                    },
                    _ => {
                        // If result is not a struct/RollResult, this is unexpected
                        // but the checker should have caught it
                    }
                }
                env.bind(Name::from("result"), result.clone());
            }
            ModifyStmt::Let { name, value, .. } => {
                let val = eval_expr(env, value)?;
                env.bind(name.clone(), val);
            }
            ModifyStmt::If {
                condition,
                then_body,
                else_body,
                ..
            } => {
                let cond = eval_expr(env, condition)?;
                match cond {
                    Value::Bool(true) => {
                        env.push_scope();
                        let r = exec_modify_stmts_phase2(env, then_body, result);
                        env.pop_scope();
                        // Re-sync result binding into the outer scope after branch
                        env.bind(Name::from("result"), result.clone());
                        r?;
                    }
                    Value::Bool(false) => {
                        if let Some(else_stmts) = else_body {
                            env.push_scope();
                            let r = exec_modify_stmts_phase2(env, else_stmts, result);
                            env.pop_scope();
                            // Re-sync result binding into the outer scope after branch
                            env.bind(Name::from("result"), result.clone());
                            r?;
                        }
                    }
                    _ => {
                        return Err(RuntimeError::with_span(
                            "modify if condition must be Bool",
                            condition.span,
                        ));
                    }
                }
            }
            ModifyStmt::CostOverride { .. } => {
                // Skip in Phase 2 (handled in cost pipeline)
            }
        }
    }
    Ok(())
}

/// Check if any modify stmts contain Phase 1 operations (non-result param overrides, lets).
fn has_phase1_stmts(stmts: &[ModifyStmt]) -> bool {
    stmts.iter().any(|s| match s {
        ModifyStmt::ParamOverride { name, .. } => name != "result",
        ModifyStmt::Let { .. } => true,
        ModifyStmt::If {
            then_body,
            else_body,
            ..
        } => has_phase1_stmts(then_body) || else_body.as_ref().is_some_and(|e| has_phase1_stmts(e)),
        _ => false,
    })
}

/// Check if any modify stmts contain Phase 2 operations.
fn has_phase2_stmts(stmts: &[ModifyStmt]) -> bool {
    stmts.iter().any(|s| match s {
        ModifyStmt::ResultOverride { .. } => true,
        ModifyStmt::ParamOverride { name, .. } => name == "result",
        ModifyStmt::If {
            then_body,
            else_body,
            ..
        } => has_phase2_stmts(then_body) || else_body.as_ref().is_some_and(|e| has_phase2_stmts(e)),
        _ => false,
    })
}

// ── Change tracking ─────────────────────────────────────────────

fn collect_param_changes(old: &[(Name, Value)], new: &[(Name, Value)]) -> Vec<FieldChange> {
    let mut changes = Vec::new();
    for (i, (name, old_val)) in old.iter().enumerate() {
        let new_val = &new[i].1;
        if old_val != new_val {
            changes.push(FieldChange {
                name: name.clone(),
                old: old_val.clone(),
                new: new_val.clone(),
            });
        }
    }
    changes
}

fn collect_result_changes(old: &Value, new: &Value, _fn_info: &FnInfo) -> Vec<FieldChange> {
    if old == new {
        return Vec::new();
    }

    // For struct results, report per-field changes
    if let (
        Value::Struct {
            fields: old_fields, ..
        },
        Value::Struct {
            fields: new_fields, ..
        },
    ) = (old, new)
    {
        let mut changes = Vec::new();
        for (name, old_val) in old_fields {
            if let Some(new_val) = new_fields.get(name)
                && old_val != new_val
            {
                changes.push(FieldChange {
                    name: name.clone(),
                    old: old_val.clone(),
                    new: new_val.clone(),
                });
            }
        }
        return changes;
    }

    // For non-struct results, report as a single "result" change
    vec![FieldChange {
        name: Name::from("result"),
        old: old.clone(),
        new: new.clone(),
    }]
}

// ── Built-in modify_applied event emission ──────────────────────

/// Emit `modify_applied` events to fire matching DSL hooks.
///
/// Deduplicates by `condition_id` — a condition with multiple modify clauses
/// that all fired emits only one event. Skips option-sourced modifiers (no
/// condition to report). Skips entirely when no hooks are registered for
/// `modify_applied` (fast path).
pub(crate) fn emit_modify_applied_events(
    env: &mut Env,
    modifiers: &[OwnedModifier],
    fn_name: &str,
    span: Span,
) -> Result<(), RuntimeError> {
    // Fast path: skip if no hooks listen for modify_applied
    if !env
        .interp
        .type_env
        .trigger_index
        .contains_key("modify_applied")
    {
        return Ok(());
    }

    // Check emit depth
    if env.emit_depth >= MAX_EMIT_DEPTH {
        return Err(RuntimeError::with_span(
            format!(
                "emit depth limit ({MAX_EMIT_DEPTH}) exceeded — possible circular emit chain from modify_applied"
            ),
            span,
        ));
    }

    // Deduplicate by condition_id
    let mut seen_ids: HashSet<u64> = HashSet::new();
    let mut payloads: Vec<(Value, Value)> = Vec::new(); // (bearer, condition_value)

    for modifier in modifiers {
        let cond_id = match modifier.condition_id {
            Some(id) => id,
            None => continue, // option-sourced, skip
        };
        if !seen_ids.insert(cond_id) {
            continue; // already emitted for this condition instance
        }

        let bearer = match &modifier.bearer {
            Some(b) => b.clone(),
            None => continue,
        };

        // Build ActiveCondition-like struct value
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

        payloads.push((bearer, condition_value));
    }

    if payloads.is_empty() {
        return Ok(());
    }

    env.emit_depth += 1;
    let result = (|| {
        for (bearer, condition_value) in payloads {
            let mut all_fields = BTreeMap::new();
            all_fields.insert(Name::from("bearer"), bearer.clone());
            all_fields.insert(Name::from("condition"), condition_value);
            all_fields.insert(Name::from("target_fn"), Value::Str(fn_name.to_string()));

            let payload = Value::Struct {
                name: Name::from("__event_modify_applied"),
                fields: all_fields,
            };

            let candidates = env.state.entities_in_play();
            let hook_result = event::find_matching_hooks(
                env.interp.program,
                env.interp.type_env,
                env.state,
                "modify_applied",
                &payload,
                &candidates,
            )?;

            for hook_info in hook_result.hooks {
                let hook_decl = env
                    .interp
                    .program
                    .hooks
                    .get(&hook_info.name)
                    .ok_or_else(|| {
                        RuntimeError::with_span(
                            format!("undefined hook '{}'", hook_info.name),
                            span,
                        )
                    })?
                    .clone();

                action::execute_hook(env, &hook_decl, hook_info.target, payload.clone(), span)?;
            }
        }
        Ok(())
    })();
    env.emit_depth -= 1;

    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

    use ttrpg_ast::ast::*;
    use ttrpg_ast::{Span, Spanned};
    use ttrpg_checker::env::{ConditionInfo, FnInfo, FnKind, ParamInfo, TypeEnv};
    use ttrpg_checker::ty::Ty;

    use crate::Interpreter;
    use crate::effect::{Effect, EffectHandler, Response};
    use crate::state::{ActiveCondition, EntityRef, StateProvider};
    use crate::value::{Value, effect_source_unknown};

    // ── Test infrastructure ────────────────────────────────────

    struct ScriptedHandler {
        script: std::collections::VecDeque<Response>,
        log: Vec<Effect>,
    }

    impl ScriptedHandler {
        fn new() -> Self {
            ScriptedHandler {
                script: std::collections::VecDeque::new(),
                log: Vec::new(),
            }
        }

        #[allow(dead_code)]
        fn with_responses(responses: Vec<Response>) -> Self {
            ScriptedHandler {
                script: responses.into(),
                log: Vec::new(),
            }
        }
    }

    impl EffectHandler for ScriptedHandler {
        fn handle(&mut self, effect: Effect) -> Response {
            self.log.push(effect);
            self.script.pop_front().unwrap_or(Response::Acknowledged)
        }
    }

    struct TestState {
        fields: HashMap<(u64, String), Value>,
        conditions: HashMap<u64, Vec<ActiveCondition>>,
        turn_budgets: HashMap<u64, BTreeMap<Name, Value>>,
        enabled_options: Vec<Name>,
    }

    impl TestState {
        fn new() -> Self {
            TestState {
                fields: HashMap::new(),
                conditions: HashMap::new(),
                turn_budgets: HashMap::new(),
                enabled_options: Vec::new(),
            }
        }
    }

    impl StateProvider for TestState {
        fn read_field(&self, entity: &EntityRef, field: &str) -> Option<Value> {
            self.fields.get(&(entity.0, field.to_string())).cloned()
        }
        fn read_conditions(&self, entity: &EntityRef) -> Option<Vec<ActiveCondition>> {
            self.conditions.get(&entity.0).cloned()
        }
        fn read_turn_budget(&self, entity: &EntityRef) -> Option<BTreeMap<Name, Value>> {
            self.turn_budgets.get(&entity.0).cloned()
        }
        fn read_enabled_options(&self) -> Vec<Name> {
            self.enabled_options.clone()
        }
        fn position_eq(&self, _a: u64, _b: u64) -> bool {
            false
        }
        fn distance(&self, _a: u64, _b: u64) -> Option<i64> {
            None
        }
    }

    fn dummy_span() -> Span {
        Span::dummy()
    }

    fn spanned<T>(node: T) -> Spanned<T> {
        Spanned::new(node, dummy_span())
    }

    fn make_env<'a, 'p>(
        state: &'a TestState,
        handler: &'a mut ScriptedHandler,
        interp: &'a Interpreter<'p>,
    ) -> crate::Env<'a, 'p> {
        crate::Env::new(state, handler, interp)
    }

    /// Build a program with a single system block containing the given declarations.
    fn program_with_decls(decls: Vec<DeclKind>) -> Program {
        let mut program = Program {
            items: vec![spanned(TopLevel::System(SystemBlock {
                name: "Test".into(),
                decls: decls.into_iter().map(spanned).collect(),
            }))],
            ..Default::default()
        };
        program.build_index();
        program
    }

    // ── Test 1: Modify Phase 1 - param overridden correctly ──

    #[test]
    fn modify_phase1_param_override() {
        // derive attack_roll(attacker: Character, mode: String) -> Int { 42 }
        // condition Prone on target: Character { modify attack_roll(attacker: target) { mode = "disadvantage" } }
        // Entity 1 has Prone condition.
        // Call: attack_roll(attacker: entity(1), mode: "normal")
        // Expected: mode overridden to "disadvantage", ModifyApplied(Phase1) emitted.

        let program = program_with_decls(vec![
            DeclKind::Derive(FnDecl::new(
                "attack_roll",
                vec![
                    Param::new("attacker", spanned(TypeExpr::Named("Character".into()))),
                    Param::new("mode", spanned(TypeExpr::String)),
                ],
                spanned(TypeExpr::Int),
                // body: just return the mode as 42 if called — but we care about
                // the modified params, so body returns mode == "disadvantage" as int
                // For simplicity: body = if mode == "disadvantage" { 1 } else { 0 }
                spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::If {
                    condition: Box::new(spanned(ExprKind::BinOp {
                        op: BinOp::Eq,
                        lhs: Box::new(spanned(ExprKind::Ident("mode".into()))),
                        rhs: Box::new(spanned(ExprKind::StringLit("disadvantage".into()))),
                    })),
                    then_block: spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::IntLit(
                        1,
                    ))))]),
                    else_branch: Some(ElseBranch::Block(spanned(vec![spanned(StmtKind::Expr(
                        spanned(ExprKind::IntLit(0)),
                    ))]))),
                })))]),
            )),
            DeclKind::Condition(
                ConditionDecl::new(
                    "Prone",
                    "target",
                    spanned(TypeExpr::Named("Character".into())),
                )
                .with_clauses(vec![ConditionClause::Modify(ModifyClause {
                    target: ModifyTarget::Named("attack_roll".into()),
                    bindings: vec![ModifyBinding {
                        name: "attacker".into(),
                        value: Some(spanned(ExprKind::Ident("target".into()))),
                        span: dummy_span(),
                    }],
                    body: vec![ModifyStmt::ParamOverride {
                        name: "mode".into(),
                        value: spanned(ExprKind::StringLit("disadvantage".into())),
                        span: dummy_span(),
                    }],
                    span: dummy_span(),
                    id: ModifyClauseId(0),
                    tags: vec![],
                    included_from: None,
                })]),
            ),
        ]);

        let mut type_env = TypeEnv::new();
        type_env.functions.insert(
            "attack_roll".into(),
            FnInfo {
                name: "attack_roll".into(),
                kind: FnKind::Derive,
                params: vec![
                    ParamInfo {
                        name: "attacker".into(),
                        ty: Ty::Entity("Character".into()),
                        has_default: false,
                        with_groups: vec![],
                        with_disjunctive: false,
                    },
                    ParamInfo {
                        name: "mode".into(),
                        ty: Ty::String,
                        has_default: false,
                        with_groups: vec![],
                        with_disjunctive: false,
                    },
                ],
                return_type: Ty::Int,
                receiver: None,
                tags: HashSet::new(),
                synthetic: false,
                trigger: None,
            },
        );
        type_env.conditions.insert(
            "Prone".into(),
            ConditionInfo {
                name: "Prone".into(),
                params: vec![],

                receiver_name: "target".into(),
                receiver_type: Ty::Entity("Character".into()),
                tags: HashSet::new(),
                state_fields: vec![],
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let mut state = TestState::new();
        // Entity 1 has the Prone condition
        state.conditions.insert(
            1,
            vec![ActiveCondition {
                id: 100,
                name: "Prone".into(),
                params: BTreeMap::new(),
                bearer: EntityRef(1),
                gained_at: 5,
                duration: Value::Void,
                invocation: None,
                applied_at: 0,
                source: effect_source_unknown(),
                tags: BTreeSet::new(),
                state_fields: BTreeMap::new(),
            }],
        );

        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // Call: attack_roll(entity(1), "normal")
        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("attack_roll".into()))),
            args: vec![
                Arg {
                    name: None,
                    value: spanned(ExprKind::Ident("attacker_entity".into())),
                    span: dummy_span(),
                },
                Arg {
                    name: None,
                    value: spanned(ExprKind::StringLit("normal".into())),
                    span: dummy_span(),
                },
            ],
        });

        // Bind the entity in scope
        env.bind("attacker_entity".into(), Value::Entity(EntityRef(1)));

        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        // If mode was overridden to "disadvantage", body returns 1
        assert_eq!(result, Value::Int(1));

        // Verify ModifyApplied effect was emitted with Phase1
        let modify_effects: Vec<&Effect> = handler
            .log
            .iter()
            .filter(|e| matches!(e, Effect::ModifyApplied { .. }))
            .collect();
        assert_eq!(
            modify_effects.len(),
            1,
            "expected exactly one ModifyApplied effect"
        );

        match &modify_effects[0] {
            Effect::ModifyApplied {
                source,
                target_fn,
                phase,
                changes,
                ..
            } => {
                assert!(
                    matches!(source, ModifySource::Condition(name) if name == "Prone"),
                    "expected Condition(Prone) source"
                );
                assert_eq!(target_fn, "attack_roll");
                assert_eq!(*phase, Phase::Phase1);
                assert_eq!(changes.len(), 1);
                assert_eq!(changes[0].name, "mode");
                assert_eq!(changes[0].old, Value::Str("normal".into()));
                assert_eq!(changes[0].new, Value::Str("disadvantage".into()));
            }
            _ => panic!("expected ModifyApplied"),
        }
    }

    // ── Test 2: Modify Phase 2 - result field overridden ─────

    #[test]
    fn modify_phase2_result_override() {
        // derive compute(val: Character) -> Outcome { Outcome { score: 10 } }
        // condition Boosted on target: Character {
        //   modify compute(val: target) { result.score = 99 }
        // }
        // Entity 1 has Boosted condition.
        // Expected: result.score overridden from 10 to 99, ModifyApplied(Phase2) emitted.

        let program = program_with_decls(vec![
            DeclKind::Derive(FnDecl::new(
                "compute",
                vec![Param::new(
                    "val",
                    spanned(TypeExpr::Named("Character".into())),
                )],
                spanned(TypeExpr::Named("Outcome".into())),
                spanned(vec![spanned(StmtKind::Expr(spanned(
                    ExprKind::StructLit {
                        name: "Outcome".into(),
                        fields: vec![StructFieldInit {
                            name: "score".into(),
                            value: spanned(ExprKind::IntLit(10)),
                            span: dummy_span(),
                        }],
                        groups: Vec::new(),
                        base: None,
                        with_conditions: Vec::new(),
                    },
                )))]),
            )),
            DeclKind::Condition(
                ConditionDecl::new(
                    "Boosted",
                    "target",
                    spanned(TypeExpr::Named("Character".into())),
                )
                .with_clauses(vec![ConditionClause::Modify(ModifyClause {
                    target: ModifyTarget::Named("compute".into()),
                    bindings: vec![ModifyBinding {
                        name: "val".into(),
                        value: Some(spanned(ExprKind::Ident("target".into()))),
                        span: dummy_span(),
                    }],
                    body: vec![ModifyStmt::ResultOverride {
                        field: "score".into(),
                        value: spanned(ExprKind::IntLit(99)),
                        span: dummy_span(),
                    }],
                    span: dummy_span(),
                    id: ModifyClauseId(0),
                    tags: vec![],
                    included_from: None,
                })]),
            ),
        ]);

        let mut type_env = TypeEnv::new();
        type_env.functions.insert(
            "compute".into(),
            FnInfo {
                name: "compute".into(),
                kind: FnKind::Derive,
                params: vec![ParamInfo {
                    name: "val".into(),
                    ty: Ty::Entity("Character".into()),
                    has_default: false,
                    with_groups: vec![],
                    with_disjunctive: false,
                }],
                return_type: Ty::Struct("Outcome".into()),
                receiver: None,
                tags: HashSet::new(),
                synthetic: false,
                trigger: None,
            },
        );
        type_env.conditions.insert(
            "Boosted".into(),
            ConditionInfo {
                name: "Boosted".into(),
                params: vec![],

                receiver_name: "target".into(),
                receiver_type: Ty::Entity("Character".into()),
                tags: HashSet::new(),
                state_fields: vec![],
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let mut state = TestState::new();
        state.conditions.insert(
            1,
            vec![ActiveCondition {
                id: 200,
                name: "Boosted".into(),
                params: BTreeMap::new(),
                bearer: EntityRef(1),
                gained_at: 3,
                duration: Value::Void,
                invocation: None,
                applied_at: 0,
                source: effect_source_unknown(),
                tags: BTreeSet::new(),
                state_fields: BTreeMap::new(),
            }],
        );

        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("entity1".into(), Value::Entity(EntityRef(1)));

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("compute".into()))),
            args: vec![Arg {
                name: None,
                value: spanned(ExprKind::Ident("entity1".into())),
                span: dummy_span(),
            }],
        });

        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        // Result should have score = 99 (overridden from 10)
        match &result {
            Value::Struct { name, fields } => {
                assert_eq!(name, "Outcome");
                assert_eq!(fields.get("score"), Some(&Value::Int(99)));
            }
            _ => panic!("expected Struct result, got {result:?}"),
        }

        // Verify ModifyApplied effect was emitted with Phase2
        let modify_effects: Vec<&Effect> = handler
            .log
            .iter()
            .filter(|e| matches!(e, Effect::ModifyApplied { .. }))
            .collect();
        assert_eq!(
            modify_effects.len(),
            1,
            "expected exactly one ModifyApplied effect"
        );

        match &modify_effects[0] {
            Effect::ModifyApplied {
                source,
                target_fn,
                phase,
                changes,
                ..
            } => {
                assert!(matches!(source, ModifySource::Condition(name) if name == "Boosted"));
                assert_eq!(target_fn, "compute");
                assert_eq!(*phase, Phase::Phase2);
                assert_eq!(changes.len(), 1);
                assert_eq!(changes[0].name, "score");
                assert_eq!(changes[0].old, Value::Int(10));
                assert_eq!(changes[0].new, Value::Int(99));
            }
            _ => panic!("expected ModifyApplied"),
        }
    }

    // ── Test 3: Multiple conditions ordered by gained_at ─────

    #[test]
    fn multiple_conditions_ordered_by_gained_at() {
        // derive calc(target: Character, x: Int) -> Int { x }
        // condition Alpha on t: Character { modify calc(target: t) { x = x + 10 } }
        // condition Beta  on t: Character { modify calc(target: t) { x = x * 2 } }
        // Entity 1 has Alpha (gained_at=10) and Beta (gained_at=5).
        // Beta (older, gained_at=5) applies first: x = 1 * 2 = 2
        // Alpha (newer, gained_at=10) applies second: x = 2 + 10 = 12
        // Expected result: 12

        let program = program_with_decls(vec![
            DeclKind::Derive(FnDecl::new(
                "calc",
                vec![
                    Param::new("target", spanned(TypeExpr::Named("Character".into()))),
                    Param::new("x", spanned(TypeExpr::Int)),
                ],
                spanned(TypeExpr::Int),
                spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::Ident(
                    "x".into(),
                ))))]),
            )),
            DeclKind::Condition(
                ConditionDecl::new("Alpha", "t", spanned(TypeExpr::Named("Character".into())))
                    .with_clauses(vec![ConditionClause::Modify(ModifyClause {
                        target: ModifyTarget::Named("calc".into()),
                        bindings: vec![ModifyBinding {
                            name: "target".into(),
                            value: Some(spanned(ExprKind::Ident("t".into()))),
                            span: dummy_span(),
                        }],
                        body: vec![ModifyStmt::ParamOverride {
                            name: "x".into(),
                            value: spanned(ExprKind::BinOp {
                                op: BinOp::Add,
                                lhs: Box::new(spanned(ExprKind::Ident("x".into()))),
                                rhs: Box::new(spanned(ExprKind::IntLit(10))),
                            }),
                            span: dummy_span(),
                        }],
                        span: dummy_span(),
                        id: ModifyClauseId(0),
                        tags: vec![],
                        included_from: None,
                    })]),
            ),
            DeclKind::Condition(
                ConditionDecl::new("Beta", "t", spanned(TypeExpr::Named("Character".into())))
                    .with_clauses(vec![ConditionClause::Modify(ModifyClause {
                        target: ModifyTarget::Named("calc".into()),
                        bindings: vec![ModifyBinding {
                            name: "target".into(),
                            value: Some(spanned(ExprKind::Ident("t".into()))),
                            span: dummy_span(),
                        }],
                        body: vec![ModifyStmt::ParamOverride {
                            name: "x".into(),
                            value: spanned(ExprKind::BinOp {
                                op: BinOp::Mul,
                                lhs: Box::new(spanned(ExprKind::Ident("x".into()))),
                                rhs: Box::new(spanned(ExprKind::IntLit(2))),
                            }),
                            span: dummy_span(),
                        }],
                        span: dummy_span(),
                        id: ModifyClauseId(0),
                        tags: vec![],
                        included_from: None,
                    })]),
            ),
        ]);

        let mut type_env = TypeEnv::new();
        type_env.functions.insert(
            "calc".into(),
            FnInfo {
                name: "calc".into(),
                kind: FnKind::Derive,
                params: vec![
                    ParamInfo {
                        name: "target".into(),
                        ty: Ty::Entity("Character".into()),
                        has_default: false,
                        with_groups: vec![],
                        with_disjunctive: false,
                    },
                    ParamInfo {
                        name: "x".into(),
                        ty: Ty::Int,
                        has_default: false,
                        with_groups: vec![],
                        with_disjunctive: false,
                    },
                ],
                return_type: Ty::Int,
                receiver: None,
                tags: HashSet::new(),
                synthetic: false,
                trigger: None,
            },
        );
        type_env.conditions.insert(
            "Alpha".into(),
            ConditionInfo {
                name: "Alpha".into(),
                params: vec![],

                receiver_name: "t".into(),
                receiver_type: Ty::Entity("Character".into()),
                tags: HashSet::new(),
                state_fields: vec![],
            },
        );
        type_env.conditions.insert(
            "Beta".into(),
            ConditionInfo {
                name: "Beta".into(),
                params: vec![],

                receiver_name: "t".into(),
                receiver_type: Ty::Entity("Character".into()),
                tags: HashSet::new(),
                state_fields: vec![],
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let mut state = TestState::new();
        // Entity 1 has both conditions: Beta is older (gained_at=5), Alpha is newer (gained_at=10)
        state.conditions.insert(
            1,
            vec![
                ActiveCondition {
                    id: 1,
                    name: "Alpha".into(),
                    params: BTreeMap::new(),
                    bearer: EntityRef(1),
                    gained_at: 10,
                    duration: Value::Void,
                    invocation: None,
                    applied_at: 0,
                    source: effect_source_unknown(),
                    tags: BTreeSet::new(),
                    state_fields: BTreeMap::new(),
                },
                ActiveCondition {
                    id: 2,
                    name: "Beta".into(),
                    params: BTreeMap::new(),
                    bearer: EntityRef(1),
                    gained_at: 5,
                    duration: Value::Void,
                    invocation: None,
                    applied_at: 0,
                    source: effect_source_unknown(),
                    tags: BTreeSet::new(),
                    state_fields: BTreeMap::new(),
                },
            ],
        );

        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("entity1".into(), Value::Entity(EntityRef(1)));

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("calc".into()))),
            args: vec![
                Arg {
                    name: None,
                    value: spanned(ExprKind::Ident("entity1".into())),
                    span: dummy_span(),
                },
                Arg {
                    name: None,
                    value: spanned(ExprKind::IntLit(1)),
                    span: dummy_span(),
                },
            ],
        });

        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        // Beta (gained_at=5) applies first: x = 1 * 2 = 2
        // Alpha (gained_at=10) applies second: x = 2 + 10 = 12
        assert_eq!(result, Value::Int(12));

        // Two ModifyApplied effects should be emitted
        let modify_effects: Vec<&Effect> = handler
            .log
            .iter()
            .filter(|e| matches!(e, Effect::ModifyApplied { .. }))
            .collect();
        assert_eq!(modify_effects.len(), 2);

        // First effect should be from Beta (older)
        match &modify_effects[0] {
            Effect::ModifyApplied { source, .. } => {
                assert!(
                    matches!(source, ModifySource::Condition(name) if name == "Beta"),
                    "first modifier should be Beta (older)"
                );
            }
            _ => panic!("expected ModifyApplied"),
        }

        // Second effect should be from Alpha (newer)
        match &modify_effects[1] {
            Effect::ModifyApplied { source, .. } => {
                assert!(
                    matches!(source, ModifySource::Condition(name) if name == "Alpha"),
                    "second modifier should be Alpha (newer)"
                );
            }
            _ => panic!("expected ModifyApplied"),
        }
    }

    // ── Test 4: Option modifiers applied after conditions ────

    #[test]
    fn option_modifiers_applied_after_conditions() {
        // derive calc(target: Character, x: Int) -> Int { x }
        // condition Buff on t: Character { modify calc(target: t) { x = x + 100 } }
        // option Variant { when_enabled { modify calc { x = x + 1 } } }
        // Entity 1 has Buff. Option Variant is enabled.
        // Expected order: Buff first (x = 1 + 100 = 101), then Variant (x = 101 + 1 = 102).

        let program = program_with_decls(vec![
            DeclKind::Derive(FnDecl::new(
                "calc",
                vec![
                    Param::new("target", spanned(TypeExpr::Named("Character".into()))),
                    Param::new("x", spanned(TypeExpr::Int)),
                ],
                spanned(TypeExpr::Int),
                spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::Ident(
                    "x".into(),
                ))))]),
            )),
            DeclKind::Condition(
                ConditionDecl::new("Buff", "t", spanned(TypeExpr::Named("Character".into())))
                    .with_clauses(vec![ConditionClause::Modify(ModifyClause {
                        target: ModifyTarget::Named("calc".into()),
                        bindings: vec![ModifyBinding {
                            name: "target".into(),
                            value: Some(spanned(ExprKind::Ident("t".into()))),
                            span: dummy_span(),
                        }],
                        body: vec![ModifyStmt::ParamOverride {
                            name: "x".into(),
                            value: spanned(ExprKind::BinOp {
                                op: BinOp::Add,
                                lhs: Box::new(spanned(ExprKind::Ident("x".into()))),
                                rhs: Box::new(spanned(ExprKind::IntLit(100))),
                            }),
                            span: dummy_span(),
                        }],
                        span: dummy_span(),
                        id: ModifyClauseId(0),
                        tags: vec![],
                        included_from: None,
                    })]),
            ),
            DeclKind::Option(OptionDecl {
                name: "Variant".into(),
                extends: None,
                description: None,
                default_on: None,
                when_enabled: Some(vec![ModifyClause {
                    target: ModifyTarget::Named("calc".into()),
                    bindings: vec![],
                    body: vec![ModifyStmt::ParamOverride {
                        name: "x".into(),
                        value: spanned(ExprKind::BinOp {
                            op: BinOp::Add,
                            lhs: Box::new(spanned(ExprKind::Ident("x".into()))),
                            rhs: Box::new(spanned(ExprKind::IntLit(1))),
                        }),
                        span: dummy_span(),
                    }],
                    span: dummy_span(),
                    id: ModifyClauseId(0),
                    tags: vec![],
                    included_from: None,
                }]),
            }),
        ]);

        let mut type_env = TypeEnv::new();
        type_env.functions.insert(
            "calc".into(),
            FnInfo {
                name: "calc".into(),
                kind: FnKind::Derive,
                params: vec![
                    ParamInfo {
                        name: "target".into(),
                        ty: Ty::Entity("Character".into()),
                        has_default: false,
                        with_groups: vec![],
                        with_disjunctive: false,
                    },
                    ParamInfo {
                        name: "x".into(),
                        ty: Ty::Int,
                        has_default: false,
                        with_groups: vec![],
                        with_disjunctive: false,
                    },
                ],
                return_type: Ty::Int,
                receiver: None,
                tags: HashSet::new(),
                synthetic: false,
                trigger: None,
            },
        );
        type_env.conditions.insert(
            "Buff".into(),
            ConditionInfo {
                name: "Buff".into(),
                params: vec![],

                receiver_name: "t".into(),
                receiver_type: Ty::Entity("Character".into()),
                tags: HashSet::new(),
                state_fields: vec![],
            },
        );
        type_env.options.insert("Variant".into());

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let mut state = TestState::new();
        state.conditions.insert(
            1,
            vec![ActiveCondition {
                id: 10,
                name: "Buff".into(),
                params: BTreeMap::new(),
                bearer: EntityRef(1),
                gained_at: 1,
                duration: Value::Void,
                invocation: None,
                applied_at: 0,
                source: effect_source_unknown(),
                tags: BTreeSet::new(),
                state_fields: BTreeMap::new(),
            }],
        );
        state.enabled_options.push("Variant".into());

        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("entity1".into(), Value::Entity(EntityRef(1)));

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("calc".into()))),
            args: vec![
                Arg {
                    name: None,
                    value: spanned(ExprKind::Ident("entity1".into())),
                    span: dummy_span(),
                },
                Arg {
                    name: None,
                    value: spanned(ExprKind::IntLit(1)),
                    span: dummy_span(),
                },
            ],
        });

        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        // Condition Buff first: x = 1 + 100 = 101
        // Option Variant second: x = 101 + 1 = 102
        assert_eq!(result, Value::Int(102));

        // Verify ordering: condition modifier first, then option modifier
        let modify_effects: Vec<&Effect> = handler
            .log
            .iter()
            .filter(|e| matches!(e, Effect::ModifyApplied { .. }))
            .collect();
        assert_eq!(modify_effects.len(), 2);

        match &modify_effects[0] {
            Effect::ModifyApplied { source, .. } => {
                assert!(
                    matches!(source, ModifySource::Condition(name) if name == "Buff"),
                    "first modifier should be condition Buff"
                );
            }
            _ => panic!("expected ModifyApplied"),
        }
        match &modify_effects[1] {
            Effect::ModifyApplied { source, .. } => {
                assert!(
                    matches!(source, ModifySource::Option(name) if name == "Variant"),
                    "second modifier should be option Variant"
                );
            }
            _ => panic!("expected ModifyApplied"),
        }
    }

    // ── Test 5: Modifier deduplication ───────────────────────

    #[test]
    fn modifier_dedup_same_condition_via_multiple_params() {
        // derive interact(a: Character, b: Character) -> Int { 1 }
        // condition Shared on t: Character { modify interact(a: t) { } }
        // (empty body so it matches but doesn't change anything)
        // Entity 1 has Shared condition.
        // Both params a and b are entity 1 — condition should only apply once.

        let program = program_with_decls(vec![
            DeclKind::Derive(FnDecl::new(
                "interact",
                vec![
                    Param::new("a", spanned(TypeExpr::Named("Character".into()))),
                    Param::new("b", spanned(TypeExpr::Named("Character".into()))),
                ],
                spanned(TypeExpr::Int),
                spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::Ident(
                    "x_val".into(),
                ))))]),
            )),
            DeclKind::Condition(
                ConditionDecl::new("Shared", "t", spanned(TypeExpr::Named("Character".into())))
                    .with_clauses(vec![ConditionClause::Modify(ModifyClause {
                        target: ModifyTarget::Named("interact".into()),
                        bindings: vec![ModifyBinding {
                            name: "a".into(),
                            value: Some(spanned(ExprKind::Ident("t".into()))),
                            span: dummy_span(),
                        }],
                        // Non-empty body to generate a ModifyApplied effect
                        // We need to set something for the change to appear.
                        // Actually we need an additional param to override.
                        // Let's instead verify at the collect_modifiers_owned level.
                        body: vec![],
                        span: dummy_span(),
                        id: ModifyClauseId(0),
                        tags: vec![],
                        included_from: None,
                    })]),
            ),
        ]);

        let mut type_env = TypeEnv::new();
        type_env.functions.insert(
            "interact".into(),
            FnInfo {
                name: "interact".into(),
                kind: FnKind::Derive,
                params: vec![
                    ParamInfo {
                        name: "a".into(),
                        ty: Ty::Entity("Character".into()),
                        has_default: false,
                        with_groups: vec![],
                        with_disjunctive: false,
                    },
                    ParamInfo {
                        name: "b".into(),
                        ty: Ty::Entity("Character".into()),
                        has_default: false,
                        with_groups: vec![],
                        with_disjunctive: false,
                    },
                ],
                return_type: Ty::Int,
                receiver: None,
                tags: HashSet::new(),
                synthetic: false,
                trigger: None,
            },
        );
        type_env.conditions.insert(
            "Shared".into(),
            ConditionInfo {
                name: "Shared".into(),
                params: vec![],

                receiver_name: "t".into(),
                receiver_type: Ty::Entity("Character".into()),
                tags: HashSet::new(),
                state_fields: vec![],
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let mut state = TestState::new();
        // Entity 1 has Shared condition (one instance)
        state.conditions.insert(
            1,
            vec![ActiveCondition {
                id: 42,
                name: "Shared".into(),
                params: BTreeMap::new(),
                bearer: EntityRef(1),
                gained_at: 1,
                duration: Value::Void,
                invocation: None,
                applied_at: 0,
                source: effect_source_unknown(),
                tags: BTreeSet::new(),
                state_fields: BTreeMap::new(),
            }],
        );

        let handler = &mut ScriptedHandler::new();
        let mut env = crate::Env::new(&state, handler, &interp);

        let fn_info = type_env.lookup_fn("interact").unwrap();
        // Both params point to the same entity
        let bound_params = vec![
            (Name::from("a"), Value::Entity(EntityRef(1))),
            (Name::from("b"), Value::Entity(EntityRef(1))),
        ];

        let modifiers =
            collect_modifiers_owned(&mut env, "interact", fn_info, &bound_params).unwrap();

        // The condition should only be collected once despite both params referencing it
        assert_eq!(
            modifiers.len(),
            1,
            "same condition via multiple params should be deduplicated to one modifier"
        );
    }

    // ── Test 6: No modifiers - derive call unchanged ─────────

    #[test]
    fn no_modifiers_derive_unchanged() {
        // derive simple(x: Int) -> Int { x + 1 }
        // No conditions, no options.
        // Call: simple(5) = 6
        // No ModifyApplied effects emitted.

        let program = program_with_decls(vec![DeclKind::Derive(FnDecl::new(
            "simple",
            vec![Param::new("x", spanned(TypeExpr::Int))],
            spanned(TypeExpr::Int),
            spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::BinOp {
                op: BinOp::Add,
                lhs: Box::new(spanned(ExprKind::Ident("x".into()))),
                rhs: Box::new(spanned(ExprKind::IntLit(1))),
            })))]),
        ))]);

        let mut type_env = TypeEnv::new();
        type_env.functions.insert(
            "simple".into(),
            FnInfo {
                name: "simple".into(),
                kind: FnKind::Derive,
                params: vec![ParamInfo {
                    name: "x".into(),
                    ty: Ty::Int,
                    has_default: false,
                    with_groups: vec![],
                    with_disjunctive: false,
                }],
                return_type: Ty::Int,
                receiver: None,
                tags: HashSet::new(),
                synthetic: false,
                trigger: None,
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("simple".into()))),
            args: vec![Arg {
                name: None,
                value: spanned(ExprKind::IntLit(5)),
                span: dummy_span(),
            }],
        });

        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        assert_eq!(result, Value::Int(6));

        // No ModifyApplied effects
        let modify_effects: Vec<&Effect> = handler
            .log
            .iter()
            .filter(|e| matches!(e, Effect::ModifyApplied { .. }))
            .collect();
        assert_eq!(
            modify_effects.len(),
            0,
            "no ModifyApplied effects should be emitted when no modifiers exist"
        );
    }

    // ── Test 7: Binding with string literal (non-Ident) matches ─

    #[test]
    fn binding_with_string_literal_matches() {
        // derive calc(mode: String, x: Int) -> Int { x }
        // option SpecialMode {
        //   when_enabled { modify calc(mode: "special") { x = x + 50 } }
        // }
        // Call calc("special", 1) → x = 1 + 50 = 51

        let program = program_with_decls(vec![
            DeclKind::Derive(FnDecl::new(
                "calc",
                vec![
                    Param::new("mode", spanned(TypeExpr::String)),
                    Param::new("x", spanned(TypeExpr::Int)),
                ],
                spanned(TypeExpr::Int),
                spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::Ident(
                    "x".into(),
                ))))]),
            )),
            DeclKind::Option(OptionDecl {
                name: "SpecialMode".into(),
                extends: None,
                description: None,
                default_on: None,
                when_enabled: Some(vec![ModifyClause {
                    target: ModifyTarget::Named("calc".into()),
                    bindings: vec![ModifyBinding {
                        name: "mode".into(),
                        value: Some(spanned(ExprKind::StringLit("special".into()))),
                        span: dummy_span(),
                    }],
                    body: vec![ModifyStmt::ParamOverride {
                        name: "x".into(),
                        value: spanned(ExprKind::BinOp {
                            op: BinOp::Add,
                            lhs: Box::new(spanned(ExprKind::Ident("x".into()))),
                            rhs: Box::new(spanned(ExprKind::IntLit(50))),
                        }),
                        span: dummy_span(),
                    }],
                    span: dummy_span(),
                    id: ModifyClauseId(0),
                    tags: vec![],
                    included_from: None,
                }]),
            }),
        ]);

        let mut type_env = TypeEnv::new();
        type_env.functions.insert(
            "calc".into(),
            FnInfo {
                name: "calc".into(),
                kind: FnKind::Derive,
                params: vec![
                    ParamInfo {
                        name: "mode".into(),
                        ty: Ty::String,
                        has_default: false,
                        with_groups: vec![],
                        with_disjunctive: false,
                    },
                    ParamInfo {
                        name: "x".into(),
                        ty: Ty::Int,
                        has_default: false,
                        with_groups: vec![],
                        with_disjunctive: false,
                    },
                ],
                return_type: Ty::Int,
                receiver: None,
                tags: HashSet::new(),
                synthetic: false,
                trigger: None,
            },
        );
        type_env.options.insert("SpecialMode".into());

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let mut state = TestState::new();
        state.enabled_options.push("SpecialMode".into());

        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("calc".into()))),
            args: vec![
                Arg {
                    name: None,
                    value: spanned(ExprKind::StringLit("special".into())),
                    span: dummy_span(),
                },
                Arg {
                    name: None,
                    value: spanned(ExprKind::IntLit(1)),
                    span: dummy_span(),
                },
            ],
        });

        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        assert_eq!(
            result,
            Value::Int(51),
            "string literal binding should match"
        );

        // Also verify it does NOT match when mode is different
        let mut handler2 = ScriptedHandler::new();
        let mut env2 = make_env(&state, &mut handler2, &interp);
        let expr2 = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("calc".into()))),
            args: vec![
                Arg {
                    name: None,
                    value: spanned(ExprKind::StringLit("normal".into())),
                    span: dummy_span(),
                },
                Arg {
                    name: None,
                    value: spanned(ExprKind::IntLit(1)),
                    span: dummy_span(),
                },
            ],
        });

        let result2 = crate::eval::eval_expr(&mut env2, &expr2).unwrap();
        assert_eq!(
            result2,
            Value::Int(1),
            "non-matching binding should not apply modifier"
        );
    }

    // ── Test 8: Non-Acknowledged ModifyApplied returns protocol error ─

    #[test]
    fn modify_applied_non_acknowledged_returns_error() {
        // derive calc(target: Character, x: Int) -> Int { x }
        // condition Buff on t: Character { modify calc(target: t) { x = x + 10 } }
        // Handler returns Vetoed for ModifyApplied → protocol error

        let program = program_with_decls(vec![
            DeclKind::Derive(FnDecl::new(
                "calc",
                vec![
                    Param::new("target", spanned(TypeExpr::Named("Character".into()))),
                    Param::new("x", spanned(TypeExpr::Int)),
                ],
                spanned(TypeExpr::Int),
                spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::Ident(
                    "x".into(),
                ))))]),
            )),
            DeclKind::Condition(
                ConditionDecl::new("Buff", "t", spanned(TypeExpr::Named("Character".into())))
                    .with_clauses(vec![ConditionClause::Modify(ModifyClause {
                        target: ModifyTarget::Named("calc".into()),
                        bindings: vec![ModifyBinding {
                            name: "target".into(),
                            value: Some(spanned(ExprKind::Ident("t".into()))),
                            span: dummy_span(),
                        }],
                        body: vec![ModifyStmt::ParamOverride {
                            name: "x".into(),
                            value: spanned(ExprKind::BinOp {
                                op: BinOp::Add,
                                lhs: Box::new(spanned(ExprKind::Ident("x".into()))),
                                rhs: Box::new(spanned(ExprKind::IntLit(10))),
                            }),
                            span: dummy_span(),
                        }],
                        span: dummy_span(),
                        id: ModifyClauseId(0),
                        tags: vec![],
                        included_from: None,
                    })]),
            ),
        ]);

        let mut type_env = TypeEnv::new();
        type_env.functions.insert(
            "calc".into(),
            FnInfo {
                name: "calc".into(),
                kind: FnKind::Derive,
                params: vec![
                    ParamInfo {
                        name: "target".into(),
                        ty: Ty::Entity("Character".into()),
                        has_default: false,
                        with_groups: vec![],
                        with_disjunctive: false,
                    },
                    ParamInfo {
                        name: "x".into(),
                        ty: Ty::Int,
                        has_default: false,
                        with_groups: vec![],
                        with_disjunctive: false,
                    },
                ],
                return_type: Ty::Int,
                receiver: None,
                tags: HashSet::new(),
                synthetic: false,
                trigger: None,
            },
        );
        type_env.conditions.insert(
            "Buff".into(),
            ConditionInfo {
                name: "Buff".into(),
                params: vec![],

                receiver_name: "t".into(),
                receiver_type: Ty::Entity("Character".into()),
                tags: HashSet::new(),
                state_fields: vec![],
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let mut state = TestState::new();
        state.conditions.insert(
            1,
            vec![ActiveCondition {
                id: 10,
                name: "Buff".into(),
                params: BTreeMap::new(),
                bearer: EntityRef(1),
                gained_at: 1,
                duration: Value::Void,
                invocation: None,
                applied_at: 0,
                source: effect_source_unknown(),
                tags: BTreeSet::new(),
                state_fields: BTreeMap::new(),
            }],
        );

        // Handler returns Vetoed for ModifyApplied
        let mut handler = ScriptedHandler::with_responses(vec![Response::Vetoed]);
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("entity1".into(), Value::Entity(EntityRef(1)));

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("calc".into()))),
            args: vec![
                Arg {
                    name: None,
                    value: spanned(ExprKind::Ident("entity1".into())),
                    span: dummy_span(),
                },
                Arg {
                    name: None,
                    value: spanned(ExprKind::IntLit(1)),
                    span: dummy_span(),
                },
            ],
        });

        let err = crate::eval::eval_expr(&mut env, &expr).unwrap_err();
        assert!(
            err.message
                .contains("protocol error: expected Acknowledged for ModifyApplied"),
            "expected protocol error, got: {}",
            err.message
        );
    }

    // ── Test 9: Override dice, kept, expr fields on RollResult ─

    #[test]
    fn modify_phase2_roll_result_dice_kept_expr() {
        use crate::value::{DiceExpr, RollResult};

        // Test the exec_modify_stmts_phase2 function directly for RollResult fields
        let state = TestState::new();
        let program = program_with_decls(vec![]);
        let mut type_env = TypeEnv::new();
        type_env.functions.insert(
            "dummy".into(),
            FnInfo {
                name: "dummy".into(),
                kind: FnKind::Derive,
                params: vec![],
                return_type: Ty::Int,
                receiver: None,
                tags: HashSet::new(),
                synthetic: false,
                trigger: None,
            },
        );
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let original_expr = DiceExpr::single(1, 20, None, 5);

        let mut result = Value::RollResult(RollResult {
            expr: original_expr.clone(),
            dice: vec![10],
            kept: vec![10],
            modifier: 5,
            total: 15,
            unmodified: 10,
        });

        env.push_scope();
        env.bind(Name::from("result"), result.clone());

        // Override "dice" field
        let stmts_dice = vec![ModifyStmt::ResultOverride {
            field: "dice".into(),
            value: spanned(ExprKind::ListLit(vec![
                spanned(ExprKind::IntLit(3)),
                spanned(ExprKind::IntLit(4)),
            ])),
            span: dummy_span(),
        }];
        exec_modify_stmts_phase2(&mut env, &stmts_dice, &mut result).unwrap();
        match &result {
            Value::RollResult(rr) => {
                assert_eq!(rr.dice, vec![3, 4], "dice field should be overridden");
            }
            _ => panic!("expected RollResult"),
        }

        // Override "kept" field
        let stmts_kept = vec![ModifyStmt::ResultOverride {
            field: "kept".into(),
            value: spanned(ExprKind::ListLit(vec![spanned(ExprKind::IntLit(4))])),
            span: dummy_span(),
        }];
        exec_modify_stmts_phase2(&mut env, &stmts_kept, &mut result).unwrap();
        match &result {
            Value::RollResult(rr) => {
                assert_eq!(rr.kept, vec![4], "kept field should be overridden");
            }
            _ => panic!("expected RollResult"),
        }

        // Override "expr" field — use a DiceExpr literal via a Let + ResultOverride
        // Since we can't construct a DiceExpr in the DSL directly from ExprKind,
        // we test by binding a DiceExpr value and referencing it.
        env.bind(
            Name::from("new_expr"),
            Value::DiceExpr(DiceExpr::single(2, 6, None, 0)),
        );
        let stmts_expr = vec![ModifyStmt::ResultOverride {
            field: "expr".into(),
            value: spanned(ExprKind::Ident("new_expr".into())),
            span: dummy_span(),
        }];
        exec_modify_stmts_phase2(&mut env, &stmts_expr, &mut result).unwrap();
        match &result {
            Value::RollResult(rr) => {
                assert_eq!(
                    rr.expr.groups[0].count, 2,
                    "expr.count should be overridden"
                );
                assert_eq!(
                    rr.expr.groups[0].sides, 6,
                    "expr.sides should be overridden"
                );
                assert_eq!(rr.expr.modifier, 0, "expr.modifier should be overridden");
            }
            _ => panic!("expected RollResult"),
        }

        env.pop_scope();
    }

    // ── Test 10: Options applied in declaration order ─────────

    #[test]
    fn options_applied_in_declaration_order() {
        // derive calc(x: Int) -> Int { x }
        // option Beta { when_enabled { modify calc { x = x * 3 } } }
        // option Alpha { when_enabled { modify calc { x = x + 10 } } }
        //
        // Both enabled. Despite "Alpha" sorting before "Beta" alphabetically,
        // Beta was declared first, so it applies first.
        // Expected: x = 1 * 3 = 3, then x = 3 + 10 = 13.

        let program = program_with_decls(vec![
            DeclKind::Derive(FnDecl::new(
                "calc",
                vec![Param::new("x", spanned(TypeExpr::Int))],
                spanned(TypeExpr::Int),
                spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::Ident(
                    "x".into(),
                ))))]),
            )),
            // Beta declared first
            DeclKind::Option(OptionDecl {
                name: "Beta".into(),
                extends: None,
                description: None,
                default_on: None,
                when_enabled: Some(vec![ModifyClause {
                    target: ModifyTarget::Named("calc".into()),
                    bindings: vec![],
                    body: vec![ModifyStmt::ParamOverride {
                        name: "x".into(),
                        value: spanned(ExprKind::BinOp {
                            op: BinOp::Mul,
                            lhs: Box::new(spanned(ExprKind::Ident("x".into()))),
                            rhs: Box::new(spanned(ExprKind::IntLit(3))),
                        }),
                        span: dummy_span(),
                    }],
                    span: dummy_span(),
                    id: ModifyClauseId(0),
                    tags: vec![],
                    included_from: None,
                }]),
            }),
            // Alpha declared second
            DeclKind::Option(OptionDecl {
                name: "Alpha".into(),
                extends: None,
                description: None,
                default_on: None,
                when_enabled: Some(vec![ModifyClause {
                    target: ModifyTarget::Named("calc".into()),
                    bindings: vec![],
                    body: vec![ModifyStmt::ParamOverride {
                        name: "x".into(),
                        value: spanned(ExprKind::BinOp {
                            op: BinOp::Add,
                            lhs: Box::new(spanned(ExprKind::Ident("x".into()))),
                            rhs: Box::new(spanned(ExprKind::IntLit(10))),
                        }),
                        span: dummy_span(),
                    }],
                    span: dummy_span(),
                    id: ModifyClauseId(0),
                    tags: vec![],
                    included_from: None,
                }]),
            }),
        ]);

        let mut type_env = TypeEnv::new();
        type_env.functions.insert(
            "calc".into(),
            FnInfo {
                name: "calc".into(),
                kind: FnKind::Derive,
                params: vec![ParamInfo {
                    name: "x".into(),
                    ty: Ty::Int,
                    has_default: false,
                    with_groups: vec![],
                    with_disjunctive: false,
                }],
                return_type: Ty::Int,
                receiver: None,
                tags: HashSet::new(),
                synthetic: false,
                trigger: None,
            },
        );
        type_env.options.insert("Beta".into());
        type_env.options.insert("Alpha".into());

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let mut state = TestState::new();
        // Host returns options in alphabetical order (Alpha before Beta)
        state.enabled_options.push("Alpha".into());
        state.enabled_options.push("Beta".into());

        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("calc".into()))),
            args: vec![Arg {
                name: None,
                value: spanned(ExprKind::IntLit(1)),
                span: dummy_span(),
            }],
        });

        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        // Beta (declared first) applies first: x = 1 * 3 = 3
        // Alpha (declared second) applies second: x = 3 + 10 = 13
        assert_eq!(
            result,
            Value::Int(13),
            "options should apply in declaration order, not alphabetical"
        );

        // Verify order via effects
        let modify_effects: Vec<&Effect> = handler
            .log
            .iter()
            .filter(|e| matches!(e, Effect::ModifyApplied { .. }))
            .collect();
        assert_eq!(modify_effects.len(), 2);

        match &modify_effects[0] {
            Effect::ModifyApplied { source, .. } => {
                assert!(
                    matches!(source, ModifySource::Option(name) if name == "Beta"),
                    "first modifier should be Beta (declared first)"
                );
            }
            _ => panic!("expected ModifyApplied"),
        }
        match &modify_effects[1] {
            Effect::ModifyApplied { source, .. } => {
                assert!(
                    matches!(source, ModifySource::Option(name) if name == "Alpha"),
                    "second modifier should be Alpha (declared second)"
                );
            }
            _ => panic!("expected ModifyApplied"),
        }
    }

    // ── If-branch param override visibility (tdsl-lm6) ──────

    #[test]
    fn modify_phase1_if_branch_override_visible_after_branch() {
        // derive f(actor: Character, x: int) -> int { x }
        // condition C on target: Character {
        //   modify f(actor: target) { if true { x = 10 }; x = x + 1 }
        // }
        // Entity 1 has C. Call: f(entity(1), 1).
        // Expected: x overridden to 10 in if-branch, then x = x + 1 = 11.

        let program = program_with_decls(vec![
            DeclKind::Derive(FnDecl::new(
                "f",
                vec![
                    Param::new("actor", spanned(TypeExpr::Named("Character".into()))),
                    Param::new("x", spanned(TypeExpr::Int)),
                ],
                spanned(TypeExpr::Int),
                spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::Ident(
                    "x".into(),
                ))))]),
            )),
            DeclKind::Condition(
                ConditionDecl::new("C", "target", spanned(TypeExpr::Named("Character".into())))
                    .with_clauses(vec![ConditionClause::Modify(ModifyClause {
                        target: ModifyTarget::Named("f".into()),
                        bindings: vec![ModifyBinding {
                            name: "actor".into(),
                            value: Some(spanned(ExprKind::Ident("target".into()))),
                            span: dummy_span(),
                        }],
                        body: vec![
                            ModifyStmt::If {
                                condition: spanned(ExprKind::BoolLit(true)),
                                then_body: vec![ModifyStmt::ParamOverride {
                                    name: "x".into(),
                                    value: spanned(ExprKind::IntLit(10)),
                                    span: dummy_span(),
                                }],
                                else_body: None,
                                span: dummy_span(),
                            },
                            ModifyStmt::ParamOverride {
                                name: "x".into(),
                                value: spanned(ExprKind::BinOp {
                                    op: BinOp::Add,
                                    lhs: Box::new(spanned(ExprKind::Ident("x".into()))),
                                    rhs: Box::new(spanned(ExprKind::IntLit(1))),
                                }),
                                span: dummy_span(),
                            },
                        ],
                        span: dummy_span(),
                        id: ModifyClauseId(0),
                        tags: vec![],
                        included_from: None,
                    })]),
            ),
        ]);

        let mut type_env = TypeEnv::new();
        type_env.functions.insert(
            "f".into(),
            FnInfo {
                name: "f".into(),
                kind: FnKind::Derive,
                params: vec![
                    ParamInfo {
                        name: "actor".into(),
                        ty: Ty::Entity("Character".into()),
                        has_default: false,
                        with_groups: vec![],
                        with_disjunctive: false,
                    },
                    ParamInfo {
                        name: "x".into(),
                        ty: Ty::Int,
                        has_default: false,
                        with_groups: vec![],
                        with_disjunctive: false,
                    },
                ],
                return_type: Ty::Int,
                receiver: None,
                tags: HashSet::new(),
                synthetic: false,
                trigger: None,
            },
        );
        type_env.conditions.insert(
            "C".into(),
            ConditionInfo {
                name: "C".into(),

                receiver_name: "target".into(),
                receiver_type: Ty::Entity("Character".into()),
                params: vec![],
                tags: HashSet::new(),
                state_fields: vec![],
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();

        let mut state = TestState::new();
        state.conditions.insert(
            1,
            vec![ActiveCondition {
                id: 1,
                name: "C".into(),
                params: BTreeMap::new(),
                bearer: EntityRef(1),
                gained_at: 0,
                duration: Value::Void,
                invocation: None,
                applied_at: 0,
                source: effect_source_unknown(),
                tags: BTreeSet::new(),
                state_fields: BTreeMap::new(),
            }],
        );

        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("e".into(), Value::Entity(EntityRef(1)));
        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("f".into()))),
            args: vec![
                Arg {
                    name: None,
                    value: spanned(ExprKind::Ident("e".into())),
                    span: dummy_span(),
                },
                Arg {
                    name: None,
                    value: spanned(ExprKind::IntLit(1)),
                    span: dummy_span(),
                },
            ],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();

        // x=1, if-branch sets x=10, then x = x + 1 = 11
        assert_eq!(result, Value::Int(11));
    }

    #[test]
    fn modify_phase1_false_branch_does_not_override() {
        // Same setup as above but if false { x = 10 }; x = x + 1
        // Expected: x = 1 + 1 = 2 (branch not taken)

        let program = program_with_decls(vec![
            DeclKind::Derive(FnDecl::new(
                "f",
                vec![
                    Param::new("actor", spanned(TypeExpr::Named("Character".into()))),
                    Param::new("x", spanned(TypeExpr::Int)),
                ],
                spanned(TypeExpr::Int),
                spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::Ident(
                    "x".into(),
                ))))]),
            )),
            DeclKind::Condition(
                ConditionDecl::new("C", "target", spanned(TypeExpr::Named("Character".into())))
                    .with_clauses(vec![ConditionClause::Modify(ModifyClause {
                        target: ModifyTarget::Named("f".into()),
                        bindings: vec![ModifyBinding {
                            name: "actor".into(),
                            value: Some(spanned(ExprKind::Ident("target".into()))),
                            span: dummy_span(),
                        }],
                        body: vec![
                            ModifyStmt::If {
                                condition: spanned(ExprKind::BoolLit(false)),
                                then_body: vec![ModifyStmt::ParamOverride {
                                    name: "x".into(),
                                    value: spanned(ExprKind::IntLit(10)),
                                    span: dummy_span(),
                                }],
                                else_body: None,
                                span: dummy_span(),
                            },
                            ModifyStmt::ParamOverride {
                                name: "x".into(),
                                value: spanned(ExprKind::BinOp {
                                    op: BinOp::Add,
                                    lhs: Box::new(spanned(ExprKind::Ident("x".into()))),
                                    rhs: Box::new(spanned(ExprKind::IntLit(1))),
                                }),
                                span: dummy_span(),
                            },
                        ],
                        span: dummy_span(),
                        id: ModifyClauseId(0),
                        tags: vec![],
                        included_from: None,
                    })]),
            ),
        ]);

        let mut type_env = TypeEnv::new();
        type_env.functions.insert(
            "f".into(),
            FnInfo {
                name: "f".into(),
                kind: FnKind::Derive,
                params: vec![
                    ParamInfo {
                        name: "actor".into(),
                        ty: Ty::Entity("Character".into()),
                        has_default: false,
                        with_groups: vec![],
                        with_disjunctive: false,
                    },
                    ParamInfo {
                        name: "x".into(),
                        ty: Ty::Int,
                        has_default: false,
                        with_groups: vec![],
                        with_disjunctive: false,
                    },
                ],
                return_type: Ty::Int,
                receiver: None,
                tags: HashSet::new(),
                synthetic: false,
                trigger: None,
            },
        );
        type_env.conditions.insert(
            "C".into(),
            ConditionInfo {
                name: "C".into(),

                receiver_name: "target".into(),
                receiver_type: Ty::Entity("Character".into()),
                params: vec![],
                tags: HashSet::new(),
                state_fields: vec![],
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();

        let mut state = TestState::new();
        state.conditions.insert(
            1,
            vec![ActiveCondition {
                id: 1,
                name: "C".into(),
                params: BTreeMap::new(),
                bearer: EntityRef(1),
                gained_at: 0,
                duration: Value::Void,
                invocation: None,
                applied_at: 0,
                source: effect_source_unknown(),
                tags: BTreeSet::new(),
                state_fields: BTreeMap::new(),
            }],
        );

        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("e".into(), Value::Entity(EntityRef(1)));
        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("f".into()))),
            args: vec![
                Arg {
                    name: None,
                    value: spanned(ExprKind::Ident("e".into())),
                    span: dummy_span(),
                },
                Arg {
                    name: None,
                    value: spanned(ExprKind::IntLit(1)),
                    span: dummy_span(),
                },
            ],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();

        // x=1, branch not taken, x = 1 + 1 = 2
        assert_eq!(result, Value::Int(2));
    }
}
