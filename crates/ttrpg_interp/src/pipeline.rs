use std::collections::HashSet;

use ttrpg_ast::ast::{ConditionClause, ModifyClause, ModifyStmt};
use ttrpg_checker::env::FnInfo;
use ttrpg_checker::ty::Ty;

use crate::Env;
use crate::RuntimeError;
use crate::effect::{Effect, FieldChange, ModifySource, Phase, Response};
use crate::eval::{eval_expr, value_eq};
use crate::state::ActiveCondition;
use crate::value::Value;

// ── Supporting types ────────────────────────────────────────────

/// Collect modifiers from conditions and options, returning owned data.
///
/// Returns modifiers in application order:
/// - Condition modifiers ordered by `gained_at` (oldest first), declaration order within
/// - Option modifiers after all conditions, declaration order within
pub(crate) fn collect_modifiers_owned(
    env: &mut Env,
    fn_name: &str,
    fn_info: &FnInfo,
    bound_params: &[(String, Value)],
) -> Result<Vec<OwnedModifier>, RuntimeError> {
    let mut condition_modifiers: Vec<(u64, OwnedModifier)> = Vec::new(); // (gained_at, modifier)
    let mut seen_condition_ids: HashSet<u64> = HashSet::new();

    // 1. For each entity-typed param, query conditions
    for (i, param_info) in fn_info.params.iter().enumerate() {
        if !matches!(param_info.ty, Ty::Entity(_)) {
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
                    "read_conditions returned None for entity {:?} — host state out of sync",
                    entity_ref,
                )));
            }
        };

        for condition in &conditions {
            // Deduplicate by condition id
            if !seen_condition_ids.insert(condition.id) {
                continue;
            }

            // Look up the condition declaration
            let cond_decl = match env.interp.program.conditions.get(condition.name.as_str()) {
                Some(decl) => decl,
                None => continue,
            };

            // Check each modify clause
            for clause_item in &cond_decl.clauses {
                let clause = match clause_item {
                    ConditionClause::Modify(c) => c,
                    ConditionClause::Suppress(_) => continue,
                };

                // Does the target function name match?
                if clause.target != fn_name {
                    continue;
                }

                // Check bindings: each binding maps a param name to an expression.
                // Evaluate the expression in a scope with the condition receiver bound.
                // The binding matches if param[binding.name] equals the evaluated value.
                if check_modify_bindings(env, clause, condition, fn_info, bound_params)? {
                    condition_modifiers.push((
                        condition.gained_at,
                        OwnedModifier {
                            source: ModifySource::Condition(condition.name.clone()),
                            clause: clause.clone(),
                            bearer: Some(Value::Entity(condition.bearer)),
                            receiver_name: Some(cond_decl.receiver_name.clone()),
                        },
                    ));
                }
            }
        }
    }

    // Sort condition modifiers by gained_at (stable sort preserves declaration order)
    condition_modifiers.sort_by_key(|(gained_at, _)| *gained_at);

    let mut result: Vec<OwnedModifier> = condition_modifiers
        .into_iter()
        .map(|(_, m)| m)
        .collect();

    // 2. Query enabled options and check their modify clauses
    let mut enabled_options = env.state.read_enabled_options();
    // Sort by declaration order for deterministic application
    let option_order = &env.interp.program.option_order;
    enabled_options.sort_by_key(|name| {
        option_order.iter().position(|o| *o == name.as_str()).unwrap_or(usize::MAX)
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
            if clause.target != fn_name {
                continue;
            }

            // Options have no receiver — check bindings without bearer
            if check_option_modify_bindings(env, clause, fn_info, bound_params)? {
                result.push(OwnedModifier {
                    source: ModifySource::Option(opt_name.clone()),
                    clause: clause.clone(),
                    bearer: None,
                    receiver_name: None,
                });
            }
        }
    }

    Ok(result)
}

/// An owned modifier with cloned clause data.
pub(crate) struct OwnedModifier {
    pub source: ModifySource,
    pub clause: ModifyClause,
    pub bearer: Option<Value>,
    pub receiver_name: Option<String>,
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
    _fn_info: &FnInfo,
    bound_params: &[(String, Value)],
) -> Result<bool, RuntimeError> {
    // Empty bindings always match
    if clause.bindings.is_empty() {
        return Ok(true);
    }

    // Look up the condition declaration to get receiver name
    let cond_decl = match env.interp.program.conditions.get(condition.name.as_str()) {
        Some(decl) => decl,
        None => return Ok(false),
    };
    let receiver_name = cond_decl.receiver_name.clone();

    for binding in &clause.bindings {
        // Find the param value for this binding name
        let param_val = match bound_params.iter().find(|(name, _)| *name == binding.name) {
            Some((_, val)) => val.clone(),
            None => return Ok(false),
        };

        // Evaluate binding expression in a temporary scope with receiver + params bound
        env.push_scope();
        env.bind(receiver_name.clone(), Value::Entity(condition.bearer));
        for (name, val) in bound_params {
            env.bind(name.clone(), val.clone());
        }

        let binding_val = eval_expr(env, &binding.value);
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
    bound_params: &[(String, Value)],
) -> Result<bool, RuntimeError> {
    if clause.bindings.is_empty() {
        return Ok(true);
    }

    for binding in &clause.bindings {
        let param_val = match bound_params.iter().find(|(name, _)| *name == binding.name) {
            Some((_, val)) => val.clone(),
            None => return Ok(false),
        };

        // Evaluate binding expression in a temporary scope with params bound
        env.push_scope();
        for (name, val) in bound_params {
            env.bind(name.clone(), val.clone());
        }

        let binding_val = eval_expr(env, &binding.value);
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
    mut params: Vec<(String, Value)>,
    modifiers: &[OwnedModifier],
) -> Result<Vec<(String, Value)>, RuntimeError> {
    for modifier in modifiers {
        let old_params: Vec<(String, Value)> = params.clone();

        // Push temporary scope for this modifier
        env.push_scope();

        // Bind receiver if condition modifier
        if let (Some(ref bearer), Some(ref recv_name)) =
            (&modifier.bearer, &modifier.receiver_name)
        {
            env.bind(recv_name.clone(), bearer.clone());
        }

        // Bind all params of the target function (read-only access for expressions)
        for (name, val) in &params {
            env.bind(name.clone(), val.clone());
        }

        // Execute modify stmts (Phase 1: param overrides only)
        let result = exec_modify_stmts_phase1(env, &modifier.clause.body, &mut params);

        env.pop_scope();

        // Propagate errors after scope cleanup
        result?;

        // Collect changes for ModifyApplied effect
        let changes = collect_param_changes(&old_params, &params);
        if !changes.is_empty() {
            let response = env.handler.handle(Effect::ModifyApplied {
                source: modifier.source.clone(),
                target_fn: fn_name.to_string(),
                phase: Phase::Phase1,
                changes,
            });
            if !matches!(response, Response::Acknowledged) {
                return Err(RuntimeError::with_span(
                    format!("protocol error: expected Acknowledged for ModifyApplied, got {:?}", response),
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
    params: &[(String, Value)],
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
        if let (Some(ref bearer), Some(ref recv_name)) =
            (&modifier.bearer, &modifier.receiver_name)
        {
            env.bind(recv_name.clone(), bearer.clone());
        }

        // Bind all params of the target function
        for (name, val) in params {
            env.bind(name.clone(), val.clone());
        }

        // Bind result
        env.bind("result".to_string(), result.clone());

        // Execute modify stmts (Phase 2: result overrides only)
        let exec_result = exec_modify_stmts_phase2(env, &modifier.clause.body, &mut result);

        env.pop_scope();

        // Propagate errors after scope cleanup
        exec_result?;

        // Collect changes for ModifyApplied effect
        let changes = collect_result_changes(&old_result, &result, fn_info);
        if !changes.is_empty() {
            let response = env.handler.handle(Effect::ModifyApplied {
                source: modifier.source.clone(),
                target_fn: fn_name.to_string(),
                phase: Phase::Phase2,
                changes,
            });
            if !matches!(response, Response::Acknowledged) {
                return Err(RuntimeError::with_span(
                    format!("protocol error: expected Acknowledged for ModifyApplied, got {:?}", response),
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
    params: &mut Vec<(String, Value)>,
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
                let cond = eval_expr(env, condition)?;
                match cond {
                    Value::Bool(true) => {
                        env.push_scope();
                        let r = exec_modify_stmts_phase1(env, then_body, params);
                        env.pop_scope();
                        r?;
                    }
                    Value::Bool(false) => {
                        if let Some(else_stmts) = else_body {
                            env.push_scope();
                            let r = exec_modify_stmts_phase1(env, else_stmts, params);
                            env.pop_scope();
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
            ModifyStmt::ResultOverride { .. } => {
                // Skip in Phase 1
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
                    env.bind("result".to_string(), result.clone());
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
                    Value::RollResult(ref mut rr) => {
                        match field.as_str() {
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
                                    rr.dice = items.iter().filter_map(|v| {
                                        if let Value::Int(n) = v { Some(*n) } else { None }
                                    }).collect();
                                }
                            }
                            "kept" => {
                                if let Value::List(items) = val {
                                    rr.kept = items.iter().filter_map(|v| {
                                        if let Value::Int(n) = v { Some(*n) } else { None }
                                    }).collect();
                                }
                            }
                            _ => {}
                        }
                    }
                    _ => {
                        // If result is not a struct/RollResult, this is unexpected
                        // but the checker should have caught it
                    }
                }
                env.bind("result".to_string(), result.clone());
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
                        r?;
                    }
                    Value::Bool(false) => {
                        if let Some(else_stmts) = else_body {
                            env.push_scope();
                            let r = exec_modify_stmts_phase2(env, else_stmts, result);
                            env.pop_scope();
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
        }
    }
    Ok(())
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
        } => {
            has_phase2_stmts(then_body)
                || else_body
                    .as_ref()
                    .is_some_and(|e| has_phase2_stmts(e))
        }
        _ => false,
    })
}

// ── Change tracking ─────────────────────────────────────────────

fn collect_param_changes(
    old: &[(String, Value)],
    new: &[(String, Value)],
) -> Vec<FieldChange> {
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

fn collect_result_changes(
    old: &Value,
    new: &Value,
    _fn_info: &FnInfo,
) -> Vec<FieldChange> {
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
            if let Some(new_val) = new_fields.get(name) {
                if old_val != new_val {
                    changes.push(FieldChange {
                        name: name.clone(),
                        old: old_val.clone(),
                        new: new_val.clone(),
                    });
                }
            }
        }
        return changes;
    }

    // For non-struct results, report as a single "result" change
    vec![FieldChange {
        name: "result".to_string(),
        old: old.clone(),
        new: new.clone(),
    }]
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::{BTreeMap, HashMap};

    use ttrpg_ast::{Span, Spanned};
    use ttrpg_ast::ast::*;
    use ttrpg_checker::env::{
        ConditionInfo, FnInfo, FnKind, ParamInfo, TypeEnv,
    };
    use ttrpg_checker::ty::Ty;

    use crate::effect::{Effect, EffectHandler, Response};
    use crate::state::{ActiveCondition, EntityRef, StateProvider};
    use crate::value::Value;
    use crate::Interpreter;

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
        turn_budgets: HashMap<u64, BTreeMap<String, Value>>,
        enabled_options: Vec<String>,
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
        fn read_turn_budget(&self, entity: &EntityRef) -> Option<BTreeMap<String, Value>> {
            self.turn_budgets.get(&entity.0).cloned()
        }
        fn read_enabled_options(&self) -> Vec<String> {
            self.enabled_options.clone()
        }
        fn position_eq(&self, _a: &Value, _b: &Value) -> bool {
            false
        }
        fn distance(&self, _a: &Value, _b: &Value) -> Option<i64> {
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
            DeclKind::Derive(FnDecl {
                name: "attack_roll".into(),
                params: vec![
                    Param {
                        name: "attacker".into(),
                        ty: spanned(TypeExpr::Named("Character".into())),
                        default: None,
                        span: dummy_span(),
                    },
                    Param {
                        name: "mode".into(),
                        ty: spanned(TypeExpr::String),
                        default: None,
                        span: dummy_span(),
                    },
                ],
                return_type: spanned(TypeExpr::Int),
                // body: just return the mode as 42 if called — but we care about
                // the modified params, so body returns mode == "disadvantage" as int
                // For simplicity: body = if mode == "disadvantage" { 1 } else { 0 }
                body: spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::If {
                    condition: Box::new(spanned(ExprKind::BinOp {
                        op: BinOp::Eq,
                        lhs: Box::new(spanned(ExprKind::Ident("mode".into()))),
                        rhs: Box::new(spanned(ExprKind::StringLit("disadvantage".into()))),
                    })),
                    then_block: spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::IntLit(1))))]),
                    else_branch: Some(ElseBranch::Block(spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::IntLit(0))))]))),
                })))]),
                synthetic: false,
            }),
            DeclKind::Condition(ConditionDecl {
                name: "Prone".into(),
                receiver_name: "target".into(),
                receiver_type: spanned(TypeExpr::Named("Character".into())),
                clauses: vec![ConditionClause::Modify(ModifyClause {
                    target: "attack_roll".into(),
                    bindings: vec![ModifyBinding {
                        name: "attacker".into(),
                        value: spanned(ExprKind::Ident("target".into())),
                        span: dummy_span(),
                    }],
                    body: vec![ModifyStmt::ParamOverride {
                        name: "mode".into(),
                        value: spanned(ExprKind::StringLit("disadvantage".into())),
                        span: dummy_span(),
                    }],
                    span: dummy_span(),
                })],
            }),
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
                    },
                    ParamInfo {
                        name: "mode".into(),
                        ty: Ty::String,
                        has_default: false,
                    },
                ],
                return_type: Ty::Int,
                receiver: None,
            },
        );
        type_env.conditions.insert(
            "Prone".into(),
            ConditionInfo {
                name: "Prone".into(),
                receiver_name: "target".into(),
                receiver_type: Ty::Entity("Character".into()),
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
                bearer: EntityRef(1),
                gained_at: 5,
                duration: Value::None,
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
        assert_eq!(modify_effects.len(), 1, "expected exactly one ModifyApplied effect");

        match &modify_effects[0] {
            Effect::ModifyApplied {
                source,
                target_fn,
                phase,
                changes,
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
            DeclKind::Derive(FnDecl {
                name: "compute".into(),
                params: vec![Param {
                    name: "val".into(),
                    ty: spanned(TypeExpr::Named("Character".into())),
                    default: None,
                    span: dummy_span(),
                }],
                return_type: spanned(TypeExpr::Named("Outcome".into())),
                body: spanned(vec![spanned(StmtKind::Expr(spanned(
                    ExprKind::StructLit {
                        name: "Outcome".into(),
                        fields: vec![StructFieldInit {
                            name: "score".into(),
                            value: spanned(ExprKind::IntLit(10)),
                            span: dummy_span(),
                        }],
                    },
                )))]),
                synthetic: false,
            }),
            DeclKind::Condition(ConditionDecl {
                name: "Boosted".into(),
                receiver_name: "target".into(),
                receiver_type: spanned(TypeExpr::Named("Character".into())),
                clauses: vec![ConditionClause::Modify(ModifyClause {
                    target: "compute".into(),
                    bindings: vec![ModifyBinding {
                        name: "val".into(),
                        value: spanned(ExprKind::Ident("target".into())),
                        span: dummy_span(),
                    }],
                    body: vec![ModifyStmt::ResultOverride {
                        field: "score".into(),
                        value: spanned(ExprKind::IntLit(99)),
                        span: dummy_span(),
                    }],
                    span: dummy_span(),
                })],
            }),
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
                }],
                return_type: Ty::Struct("Outcome".into()),
                receiver: None,
            },
        );
        type_env.conditions.insert(
            "Boosted".into(),
            ConditionInfo {
                name: "Boosted".into(),
                receiver_name: "target".into(),
                receiver_type: Ty::Entity("Character".into()),
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let mut state = TestState::new();
        state.conditions.insert(
            1,
            vec![ActiveCondition {
                id: 200,
                name: "Boosted".into(),
                bearer: EntityRef(1),
                gained_at: 3,
                duration: Value::None,
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
            _ => panic!("expected Struct result, got {:?}", result),
        }

        // Verify ModifyApplied effect was emitted with Phase2
        let modify_effects: Vec<&Effect> = handler
            .log
            .iter()
            .filter(|e| matches!(e, Effect::ModifyApplied { .. }))
            .collect();
        assert_eq!(modify_effects.len(), 1, "expected exactly one ModifyApplied effect");

        match &modify_effects[0] {
            Effect::ModifyApplied {
                source,
                target_fn,
                phase,
                changes,
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
            DeclKind::Derive(FnDecl {
                name: "calc".into(),
                params: vec![
                    Param {
                        name: "target".into(),
                        ty: spanned(TypeExpr::Named("Character".into())),
                        default: None,
                        span: dummy_span(),
                    },
                    Param {
                        name: "x".into(),
                        ty: spanned(TypeExpr::Int),
                        default: None,
                        span: dummy_span(),
                    },
                ],
                return_type: spanned(TypeExpr::Int),
                body: spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::Ident(
                    "x".into(),
                ))))]),
                synthetic: false,
            }),
            DeclKind::Condition(ConditionDecl {
                name: "Alpha".into(),
                receiver_name: "t".into(),
                receiver_type: spanned(TypeExpr::Named("Character".into())),
                clauses: vec![ConditionClause::Modify(ModifyClause {
                    target: "calc".into(),
                    bindings: vec![ModifyBinding {
                        name: "target".into(),
                        value: spanned(ExprKind::Ident("t".into())),
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
                })],
            }),
            DeclKind::Condition(ConditionDecl {
                name: "Beta".into(),
                receiver_name: "t".into(),
                receiver_type: spanned(TypeExpr::Named("Character".into())),
                clauses: vec![ConditionClause::Modify(ModifyClause {
                    target: "calc".into(),
                    bindings: vec![ModifyBinding {
                        name: "target".into(),
                        value: spanned(ExprKind::Ident("t".into())),
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
                })],
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
                    },
                    ParamInfo {
                        name: "x".into(),
                        ty: Ty::Int,
                        has_default: false,
                    },
                ],
                return_type: Ty::Int,
                receiver: None,
            },
        );
        type_env.conditions.insert(
            "Alpha".into(),
            ConditionInfo {
                name: "Alpha".into(),
                receiver_name: "t".into(),
                receiver_type: Ty::Entity("Character".into()),
            },
        );
        type_env.conditions.insert(
            "Beta".into(),
            ConditionInfo {
                name: "Beta".into(),
                receiver_name: "t".into(),
                receiver_type: Ty::Entity("Character".into()),
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
                    bearer: EntityRef(1),
                    gained_at: 10,
                    duration: Value::None,
                },
                ActiveCondition {
                    id: 2,
                    name: "Beta".into(),
                    bearer: EntityRef(1),
                    gained_at: 5,
                    duration: Value::None,
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
            DeclKind::Derive(FnDecl {
                name: "calc".into(),
                params: vec![
                    Param {
                        name: "target".into(),
                        ty: spanned(TypeExpr::Named("Character".into())),
                        default: None,
                        span: dummy_span(),
                    },
                    Param {
                        name: "x".into(),
                        ty: spanned(TypeExpr::Int),
                        default: None,
                        span: dummy_span(),
                    },
                ],
                return_type: spanned(TypeExpr::Int),
                body: spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::Ident(
                    "x".into(),
                ))))]),
                synthetic: false,
            }),
            DeclKind::Condition(ConditionDecl {
                name: "Buff".into(),
                receiver_name: "t".into(),
                receiver_type: spanned(TypeExpr::Named("Character".into())),
                clauses: vec![ConditionClause::Modify(ModifyClause {
                    target: "calc".into(),
                    bindings: vec![ModifyBinding {
                        name: "target".into(),
                        value: spanned(ExprKind::Ident("t".into())),
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
                })],
            }),
            DeclKind::Option(OptionDecl {
                name: "Variant".into(),
                extends: None,
                description: None,
                default_on: None,
                when_enabled: Some(vec![ModifyClause {
                    target: "calc".into(),
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
                    },
                    ParamInfo {
                        name: "x".into(),
                        ty: Ty::Int,
                        has_default: false,
                    },
                ],
                return_type: Ty::Int,
                receiver: None,
            },
        );
        type_env.conditions.insert(
            "Buff".into(),
            ConditionInfo {
                name: "Buff".into(),
                receiver_name: "t".into(),
                receiver_type: Ty::Entity("Character".into()),
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
                bearer: EntityRef(1),
                gained_at: 1,
                duration: Value::None,
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
            DeclKind::Derive(FnDecl {
                name: "interact".into(),
                params: vec![
                    Param {
                        name: "a".into(),
                        ty: spanned(TypeExpr::Named("Character".into())),
                        default: None,
                        span: dummy_span(),
                    },
                    Param {
                        name: "b".into(),
                        ty: spanned(TypeExpr::Named("Character".into())),
                        default: None,
                        span: dummy_span(),
                    },
                ],
                return_type: spanned(TypeExpr::Int),
                body: spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::Ident(
                    "x_val".into(),
                ))))]),
                synthetic: false,
            }),
            DeclKind::Condition(ConditionDecl {
                name: "Shared".into(),
                receiver_name: "t".into(),
                receiver_type: spanned(TypeExpr::Named("Character".into())),
                clauses: vec![ConditionClause::Modify(ModifyClause {
                    target: "interact".into(),
                    bindings: vec![ModifyBinding {
                        name: "a".into(),
                        value: spanned(ExprKind::Ident("t".into())),
                        span: dummy_span(),
                    }],
                    // Non-empty body to generate a ModifyApplied effect
                    // We need to set something for the change to appear.
                    // Actually we need an additional param to override.
                    // Let's instead verify at the collect_modifiers_owned level.
                    body: vec![],
                    span: dummy_span(),
                })],
            }),
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
                    },
                    ParamInfo {
                        name: "b".into(),
                        ty: Ty::Entity("Character".into()),
                        has_default: false,
                    },
                ],
                return_type: Ty::Int,
                receiver: None,
            },
        );
        type_env.conditions.insert(
            "Shared".into(),
            ConditionInfo {
                name: "Shared".into(),
                receiver_name: "t".into(),
                receiver_type: Ty::Entity("Character".into()),
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
                bearer: EntityRef(1),
                gained_at: 1,
                duration: Value::None,
            }],
        );

        let handler = &mut ScriptedHandler::new();
        let mut env = crate::Env::new(&state, handler, &interp);

        let fn_info = type_env.lookup_fn("interact").unwrap();
        // Both params point to the same entity
        let bound_params = vec![
            ("a".to_string(), Value::Entity(EntityRef(1))),
            ("b".to_string(), Value::Entity(EntityRef(1))),
        ];

        let modifiers = collect_modifiers_owned(&mut env, "interact", fn_info, &bound_params).unwrap();

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

        let program = program_with_decls(vec![DeclKind::Derive(FnDecl {
            name: "simple".into(),
            params: vec![Param {
                name: "x".into(),
                ty: spanned(TypeExpr::Int),
                default: None,
                span: dummy_span(),
            }],
            return_type: spanned(TypeExpr::Int),
            body: spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::BinOp {
                op: BinOp::Add,
                lhs: Box::new(spanned(ExprKind::Ident("x".into()))),
                rhs: Box::new(spanned(ExprKind::IntLit(1))),
            })))]),
            synthetic: false,
        })]);

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
                }],
                return_type: Ty::Int,
                receiver: None,
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
            DeclKind::Derive(FnDecl {
                name: "calc".into(),
                params: vec![
                    Param {
                        name: "mode".into(),
                        ty: spanned(TypeExpr::String),
                        default: None,
                        span: dummy_span(),
                    },
                    Param {
                        name: "x".into(),
                        ty: spanned(TypeExpr::Int),
                        default: None,
                        span: dummy_span(),
                    },
                ],
                return_type: spanned(TypeExpr::Int),
                body: spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::Ident(
                    "x".into(),
                ))))]),
                synthetic: false,
            }),
            DeclKind::Option(OptionDecl {
                name: "SpecialMode".into(),
                extends: None,
                description: None,
                default_on: None,
                when_enabled: Some(vec![ModifyClause {
                    target: "calc".into(),
                    bindings: vec![ModifyBinding {
                        name: "mode".into(),
                        value: spanned(ExprKind::StringLit("special".into())),
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
                    },
                    ParamInfo {
                        name: "x".into(),
                        ty: Ty::Int,
                        has_default: false,
                    },
                ],
                return_type: Ty::Int,
                receiver: None,
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
        assert_eq!(result, Value::Int(51), "string literal binding should match");

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
        assert_eq!(result2, Value::Int(1), "non-matching binding should not apply modifier");
    }

    // ── Test 8: Non-Acknowledged ModifyApplied returns protocol error ─

    #[test]
    fn modify_applied_non_acknowledged_returns_error() {
        // derive calc(target: Character, x: Int) -> Int { x }
        // condition Buff on t: Character { modify calc(target: t) { x = x + 10 } }
        // Handler returns Vetoed for ModifyApplied → protocol error

        let program = program_with_decls(vec![
            DeclKind::Derive(FnDecl {
                name: "calc".into(),
                params: vec![
                    Param {
                        name: "target".into(),
                        ty: spanned(TypeExpr::Named("Character".into())),
                        default: None,
                        span: dummy_span(),
                    },
                    Param {
                        name: "x".into(),
                        ty: spanned(TypeExpr::Int),
                        default: None,
                        span: dummy_span(),
                    },
                ],
                return_type: spanned(TypeExpr::Int),
                body: spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::Ident(
                    "x".into(),
                ))))]),
                synthetic: false,
            }),
            DeclKind::Condition(ConditionDecl {
                name: "Buff".into(),
                receiver_name: "t".into(),
                receiver_type: spanned(TypeExpr::Named("Character".into())),
                clauses: vec![ConditionClause::Modify(ModifyClause {
                    target: "calc".into(),
                    bindings: vec![ModifyBinding {
                        name: "target".into(),
                        value: spanned(ExprKind::Ident("t".into())),
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
                })],
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
                    },
                    ParamInfo {
                        name: "x".into(),
                        ty: Ty::Int,
                        has_default: false,
                    },
                ],
                return_type: Ty::Int,
                receiver: None,
            },
        );
        type_env.conditions.insert(
            "Buff".into(),
            ConditionInfo {
                name: "Buff".into(),
                receiver_name: "t".into(),
                receiver_type: Ty::Entity("Character".into()),
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let mut state = TestState::new();
        state.conditions.insert(
            1,
            vec![ActiveCondition {
                id: 10,
                name: "Buff".into(),
                bearer: EntityRef(1),
                gained_at: 1,
                duration: Value::None,
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
            err.message.contains("protocol error: expected Acknowledged for ModifyApplied"),
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
            },
        );
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let original_expr = DiceExpr {
            count: 1,
            sides: 20,
            filter: None,
            modifier: 5,
        };

        let mut result = Value::RollResult(RollResult {
            expr: original_expr.clone(),
            dice: vec![10],
            kept: vec![10],
            modifier: 5,
            total: 15,
            unmodified: 10,
        });

        env.push_scope();
        env.bind("result".to_string(), result.clone());

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
            value: spanned(ExprKind::ListLit(vec![
                spanned(ExprKind::IntLit(4)),
            ])),
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
        env.bind("new_expr".to_string(), Value::DiceExpr(DiceExpr {
            count: 2,
            sides: 6,
            filter: None,
            modifier: 0,
        }));
        let stmts_expr = vec![ModifyStmt::ResultOverride {
            field: "expr".into(),
            value: spanned(ExprKind::Ident("new_expr".into())),
            span: dummy_span(),
        }];
        exec_modify_stmts_phase2(&mut env, &stmts_expr, &mut result).unwrap();
        match &result {
            Value::RollResult(rr) => {
                assert_eq!(rr.expr.count, 2, "expr.count should be overridden");
                assert_eq!(rr.expr.sides, 6, "expr.sides should be overridden");
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
            DeclKind::Derive(FnDecl {
                name: "calc".into(),
                params: vec![Param {
                    name: "x".into(),
                    ty: spanned(TypeExpr::Int),
                    default: None,
                    span: dummy_span(),
                }],
                return_type: spanned(TypeExpr::Int),
                body: spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::Ident(
                    "x".into(),
                ))))]),
                synthetic: false,
            }),
            // Beta declared first
            DeclKind::Option(OptionDecl {
                name: "Beta".into(),
                extends: None,
                description: None,
                default_on: None,
                when_enabled: Some(vec![ModifyClause {
                    target: "calc".into(),
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
                }]),
            }),
            // Alpha declared second
            DeclKind::Option(OptionDecl {
                name: "Alpha".into(),
                extends: None,
                description: None,
                default_on: None,
                when_enabled: Some(vec![ModifyClause {
                    target: "calc".into(),
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
                }],
                return_type: Ty::Int,
                receiver: None,
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
        assert_eq!(result, Value::Int(13), "options should apply in declaration order, not alphabetical");

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
}
