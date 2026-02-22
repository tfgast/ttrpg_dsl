use ttrpg_ast::Span;
use ttrpg_ast::ast::{ActionDecl, ReactionDecl};

use crate::Env;
use crate::RuntimeError;
use crate::effect::{ActionKind, Effect, Response};
use crate::eval::{eval_block, eval_expr};
use crate::state::EntityRef;
use crate::value::Value;

// ── Cost token → budget field mapping ──────────────────────────

/// Maps a cost token (e.g., "action") to its TurnBudget field name (e.g., "actions").
///
/// The singular token is the DSL-facing name (matches D&D terminology).
/// The plural field is the counter in TurnBudget.
fn token_to_budget_field(token: &str) -> Option<&'static str> {
    match token {
        "action" => Some("actions"),
        "bonus_action" => Some("bonus_actions"),
        "reaction" => Some("reactions"),
        _ => None,
    }
}

// ── Action execution ───────────────────────────────────────────

/// Execute an action through the full pipeline:
///
/// 1. Emit `ActionStarted` (veto → early return)
/// 2. Bind scope: receiver + params, save/restore `turn_actor`
/// 3. Requires clause (if present): evaluate, emit `RequiresCheck`
/// 4. Cost deduction: emit `DeductCost` per token
/// 5. Execute resolve block
/// 6. Emit `ActionCompleted`
pub(crate) fn execute_action(
    env: &mut Env,
    action: &ActionDecl,
    actor: EntityRef,
    args: Vec<(String, Value)>,
    call_span: Span,
) -> Result<Value, RuntimeError> {
    let action_name = action.name.clone();
    let param_values: Vec<Value> = args.iter().map(|(_, v)| v.clone()).collect();

    // 1. Emit ActionStarted
    let response = env.handler.handle(Effect::ActionStarted {
        name: action_name.clone(),
        kind: ActionKind::Action,
        actor,
        params: param_values,
    });

    match response {
        Response::Acknowledged => {}
        Response::Vetoed => {
            let completion_response = env.handler.handle(Effect::ActionCompleted {
                name: action_name,
                actor,
            });
            match completion_response {
                Response::Acknowledged => {}
                other => {
                    return Err(RuntimeError::with_span(
                        format!(
                            "protocol error: expected Acknowledged for ActionCompleted, got {:?}",
                            other
                        ),
                        call_span,
                    ));
                }
            }
            return Ok(Value::None);
        }
        other => {
            return Err(RuntimeError::with_span(
                format!(
                    "protocol error: expected Acknowledged or Vetoed for ActionStarted, got {:?}",
                    other
                ),
                call_span,
            ));
        }
    }

    // 2. Bind scope: receiver + params. Save previous turn_actor.
    let prev_turn_actor = env.turn_actor.take();
    env.turn_actor = Some(actor);
    env.push_scope();

    // Bind receiver
    env.bind(action.receiver_name.clone(), Value::Entity(actor));

    // Bind regular params
    for (name, value) in &args {
        env.bind(name.clone(), value.clone());
    }

    // Run the rest of the pipeline with scope cleanup on all exit paths
    let result = execute_action_inner(env, action, &actor, call_span);

    env.pop_scope();
    env.turn_actor = prev_turn_actor;

    // 6. Emit ActionCompleted (only on success)
    if result.is_ok() {
        let response = env.handler.handle(Effect::ActionCompleted {
            name: action_name,
            actor,
        });
        match response {
            Response::Acknowledged => {}
            other => {
                return Err(RuntimeError::with_span(
                    format!(
                        "protocol error: expected Acknowledged for ActionCompleted, got {:?}",
                        other
                    ),
                    call_span,
                ));
            }
        }
    }

    result
}

/// Inner pipeline after scope is established. Separated so that cleanup
/// (pop_scope, restore turn_actor, ActionCompleted) is unconditional.
fn execute_action_inner(
    env: &mut Env,
    action: &ActionDecl,
    actor: &EntityRef,
    call_span: Span,
) -> Result<Value, RuntimeError> {
    // 3. Requires clause (if present)
    if let Some(ref requires_expr) = action.requires {
        let requires_val = eval_expr(env, requires_expr)?;
        let passed = match &requires_val {
            Value::Bool(b) => *b,
            _ => {
                return Err(RuntimeError::with_span(
                    format!(
                        "requires clause must evaluate to Bool, got {:?}",
                        requires_val
                    ),
                    requires_expr.span,
                ));
            }
        };

        let response = env.handler.handle(Effect::RequiresCheck {
            action: action.name.clone(),
            passed,
            reason: None,
        });

        // Override can force pass or fail
        let effective_passed = match response {
            Response::Override(Value::Bool(b)) => b,
            Response::Acknowledged => passed,
            other => {
                return Err(RuntimeError::with_span(
                    format!(
                        "protocol error: expected Acknowledged or Override(Bool) for RequiresCheck, got {:?}",
                        other
                    ),
                    requires_expr.span,
                ));
            }
        };

        if !effective_passed {
            // Requires failed: no cost spent, action ends
            return Ok(Value::None);
        }
    }

    // 4. Cost deduction
    if let Some(ref cost) = action.cost {
        deduct_costs(env, actor, cost, call_span)?;
    }

    // 5. Execute resolve block
    let resolve = action.resolve.clone();
    eval_block(env, &resolve)
}

// ── Reaction execution ─────────────────────────────────────────

/// Execute a reaction through the pipeline:
///
/// 1. Emit `ActionStarted` with kind: Reaction (veto → early return)
/// 2. Bind scope: receiver + trigger payload, save/restore `turn_actor`
/// 3. Cost deduction
/// 4. Execute resolve block
/// 5. Emit `ActionCompleted`
pub(crate) fn execute_reaction(
    env: &mut Env,
    reaction: &ReactionDecl,
    reactor: EntityRef,
    event_payload: Value,
    call_span: Span,
) -> Result<Value, RuntimeError> {
    let reaction_name = reaction.name.clone();

    // 1. Emit ActionStarted with Reaction kind
    let response = env.handler.handle(Effect::ActionStarted {
        name: reaction_name.clone(),
        kind: ActionKind::Reaction {
            event: reaction.trigger.event_name.clone(),
            trigger: event_payload.clone(),
        },
        actor: reactor,
        params: vec![],
    });

    match response {
        Response::Acknowledged => {}
        Response::Vetoed => {
            let completion_response = env.handler.handle(Effect::ActionCompleted {
                name: reaction_name,
                actor: reactor,
            });
            match completion_response {
                Response::Acknowledged => {}
                other => {
                    return Err(RuntimeError::with_span(
                        format!(
                            "protocol error: expected Acknowledged for ActionCompleted, got {:?}",
                            other
                        ),
                        call_span,
                    ));
                }
            }
            return Ok(Value::None);
        }
        other => {
            return Err(RuntimeError::with_span(
                format!(
                    "protocol error: expected Acknowledged or Vetoed for ActionStarted, got {:?}",
                    other
                ),
                call_span,
            ));
        }
    }

    // 2. Bind scope: receiver + trigger payload. Save previous turn_actor.
    let prev_turn_actor = env.turn_actor.take();
    env.turn_actor = Some(reactor);
    env.push_scope();

    // Bind receiver
    env.bind(
        reaction.receiver_name.clone(),
        Value::Entity(reactor),
    );

    // Bind trigger payload as "trigger"
    env.bind("trigger".to_string(), event_payload);

    // Run the rest of the pipeline with scope cleanup on all exit paths
    let result = execute_reaction_inner(env, reaction, &reactor, call_span);

    env.pop_scope();
    env.turn_actor = prev_turn_actor;

    // 5. Emit ActionCompleted (only on success)
    if result.is_ok() {
        let response = env.handler.handle(Effect::ActionCompleted {
            name: reaction_name,
            actor: reactor,
        });
        match response {
            Response::Acknowledged => {}
            other => {
                return Err(RuntimeError::with_span(
                    format!(
                        "protocol error: expected Acknowledged for ActionCompleted, got {:?}",
                        other
                    ),
                    call_span,
                ));
            }
        }
    }

    result
}

/// Inner pipeline after scope is established.
fn execute_reaction_inner(
    env: &mut Env,
    reaction: &ReactionDecl,
    reactor: &EntityRef,
    call_span: Span,
) -> Result<Value, RuntimeError> {
    // No requires clause for reactions

    // 3. Cost deduction
    if let Some(ref cost) = reaction.cost {
        deduct_costs(env, reactor, cost, call_span)?;
    }

    // 4. Execute resolve block
    let resolve = reaction.resolve.clone();
    eval_block(env, &resolve)
}

// ── Cost deduction ─────────────────────────────────────────────

/// Emit `DeductCost` for each token in the cost clause.
///
/// Handles three response types:
/// - `Acknowledged`: host accepts the deduction (host is responsible for applying it at Layer 1)
/// - `Override(Str(replacement))`: redirect to a different budget field
/// - `Vetoed`: cost waived, no deduction
fn deduct_costs(
    env: &mut Env,
    actor: &EntityRef,
    cost: &ttrpg_ast::ast::CostClause,
    call_span: Span,
) -> Result<(), RuntimeError> {
    for token in &cost.tokens {
        let budget_field = token_to_budget_field(&token.node).ok_or_else(|| {
            RuntimeError::with_span(
                format!(
                    "internal error: unknown cost token '{}' (should have been caught by checker)",
                    token.node
                ),
                token.span,
            )
        })?;

        let response = env.handler.handle(Effect::DeductCost {
            actor: *actor,
            token: token.node.clone(),
            budget_field: budget_field.to_string(),
        });

        match response {
            Response::Acknowledged => {
                // Layer 1: host is responsible for the deduction
                // Layer 2: adapter handles this
            }
            Response::Override(Value::Str(replacement)) => {
                // Validate that the replacement is a valid cost token
                if token_to_budget_field(&replacement).is_none() {
                    return Err(RuntimeError::with_span(
                        format!(
                            "invalid cost override '{}'; expected one of: action, bonus_action, reaction",
                            replacement
                        ),
                        call_span,
                    ));
                }
                // Layer 1: host applies deduction to replacement field
                // Layer 2: adapter handles this
            }
            Response::Vetoed => {
                // Cost waived — no deduction
            }
            other => {
                return Err(RuntimeError::with_span(
                    format!(
                        "protocol error: expected Acknowledged, Override(Str), or Vetoed for DeductCost, got {:?}",
                        other
                    ),
                    call_span,
                ));
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::{BTreeMap, HashMap};

    use ttrpg_ast::Span;
    use ttrpg_ast::Spanned;
    use ttrpg_ast::ast::*;
    use ttrpg_checker::env::TypeEnv;

    use crate::effect::{EffectHandler, Response};
    use crate::state::{ActiveCondition, StateProvider};
    use crate::Interpreter;

    // ── Test infrastructure ────────────────────────────────────

    fn span() -> Span {
        Span { start: 0, end: 0 }
    }

    fn spanned<T>(node: T) -> Spanned<T> {
        Spanned { node, span: span() }
    }

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

    fn empty_program() -> Program {
        Program { items: vec![] }
    }

    fn empty_type_env() -> TypeEnv {
        TypeEnv::new()
    }

    fn make_env<'a, 'p>(
        state: &'a TestState,
        handler: &'a mut ScriptedHandler,
        interp: &'a Interpreter<'p>,
    ) -> Env<'a, 'p> {
        Env::new(state, handler, interp)
    }

    // Helper to make a simple action declaration with a resolve block
    fn make_action(
        name: &str,
        receiver_name: &str,
        params: Vec<Param>,
        cost: Option<CostClause>,
        requires: Option<Spanned<ExprKind>>,
        resolve_stmts: Vec<Spanned<StmtKind>>,
    ) -> ActionDecl {
        ActionDecl {
            name: name.to_string(),
            receiver_name: receiver_name.to_string(),
            receiver_type: spanned(TypeExpr::Named("Character".to_string())),
            params,
            cost,
            requires,
            resolve: spanned(resolve_stmts),
            trigger_text: None,
            synthetic: false,
        }
    }

    // Helper to make a simple reaction declaration
    fn make_reaction(
        name: &str,
        receiver_name: &str,
        event_name: &str,
        cost: Option<CostClause>,
        resolve_stmts: Vec<Spanned<StmtKind>>,
    ) -> ReactionDecl {
        ReactionDecl {
            name: name.to_string(),
            receiver_name: receiver_name.to_string(),
            receiver_type: spanned(TypeExpr::Named("Character".to_string())),
            trigger: TriggerExpr {
                event_name: event_name.to_string(),
                bindings: vec![],
                span: span(),
            },
            cost,
            resolve: spanned(resolve_stmts),
        }
    }

    // ── Token to budget field tests ────────────────────────────

    #[test]
    fn token_mapping_valid() {
        assert_eq!(token_to_budget_field("action"), Some("actions"));
        assert_eq!(token_to_budget_field("bonus_action"), Some("bonus_actions"));
        assert_eq!(token_to_budget_field("reaction"), Some("reactions"));
    }

    #[test]
    fn token_mapping_invalid() {
        assert_eq!(token_to_budget_field("unknown"), None);
        assert_eq!(token_to_budget_field("move"), None);
    }

    // ── Action execution tests ─────────────────────────────────

    #[test]
    fn action_basic_requires_pass_cost_resolve() {
        // Action with requires(true), cost{action}, and resolve block that returns 42
        let action = make_action(
            "Attack",
            "actor",
            vec![],
            Some(CostClause {
                tokens: vec![spanned("action".to_string())],
                span: span(),
            }),
            Some(spanned(ExprKind::BoolLit(true))),
            vec![spanned(StmtKind::Expr(spanned(ExprKind::IntLit(42))))],
        );

        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);
        let actor = EntityRef(1);

        let result = execute_action(&mut env, &action, actor, vec![], span()).unwrap();
        assert_eq!(result, Value::Int(42));

        // Check effect sequence: ActionStarted, RequiresCheck, DeductCost, ActionCompleted
        assert_eq!(handler.log.len(), 4);
        assert!(matches!(&handler.log[0], Effect::ActionStarted { name, kind: ActionKind::Action, .. } if name == "Attack"));
        assert!(matches!(&handler.log[1], Effect::RequiresCheck { action, passed: true, .. } if action == "Attack"));
        assert!(matches!(&handler.log[2], Effect::DeductCost { token, budget_field, .. } if token == "action" && budget_field == "actions"));
        assert!(matches!(&handler.log[3], Effect::ActionCompleted { name, .. } if name == "Attack"));
    }

    #[test]
    fn action_requires_fail_no_cost_spent() {
        // Action with requires(false) — should skip cost and resolve
        let action = make_action(
            "Attack",
            "actor",
            vec![],
            Some(CostClause {
                tokens: vec![spanned("action".to_string())],
                span: span(),
            }),
            Some(spanned(ExprKind::BoolLit(false))),
            vec![spanned(StmtKind::Expr(spanned(ExprKind::IntLit(42))))],
        );

        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);
        let actor = EntityRef(1);

        let result = execute_action(&mut env, &action, actor, vec![], span()).unwrap();
        assert_eq!(result, Value::None);

        // Effect sequence: ActionStarted, RequiresCheck, ActionCompleted (no DeductCost!)
        assert_eq!(handler.log.len(), 3);
        assert!(matches!(&handler.log[0], Effect::ActionStarted { .. }));
        assert!(matches!(&handler.log[1], Effect::RequiresCheck { passed: false, .. }));
        assert!(matches!(&handler.log[2], Effect::ActionCompleted { .. }));
    }

    #[test]
    fn action_started_veto_immediate_completion() {
        // Host vetoes at ActionStarted — no requires, cost, or resolve
        let action = make_action(
            "Attack",
            "actor",
            vec![],
            Some(CostClause {
                tokens: vec![spanned("action".to_string())],
                span: span(),
            }),
            Some(spanned(ExprKind::BoolLit(true))),
            vec![spanned(StmtKind::Expr(spanned(ExprKind::IntLit(42))))],
        );

        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::with_responses(vec![Response::Vetoed]);
        let mut env = make_env(&state, &mut handler, &interp);
        let actor = EntityRef(1);

        let result = execute_action(&mut env, &action, actor, vec![], span()).unwrap();
        assert_eq!(result, Value::None);

        // Only ActionStarted and ActionCompleted
        assert_eq!(handler.log.len(), 2);
        assert!(matches!(&handler.log[0], Effect::ActionStarted { .. }));
        assert!(matches!(&handler.log[1], Effect::ActionCompleted { .. }));
    }

    #[test]
    fn action_cost_vetoed() {
        // Host vetoes the cost — cost is waived but resolve still executes
        let action = make_action(
            "Attack",
            "actor",
            vec![],
            Some(CostClause {
                tokens: vec![spanned("action".to_string())],
                span: span(),
            }),
            None, // no requires
            vec![spanned(StmtKind::Expr(spanned(ExprKind::IntLit(99))))],
        );

        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        // ActionStarted → Acknowledged, DeductCost → Vetoed
        let mut handler = ScriptedHandler::with_responses(vec![
            Response::Acknowledged,
            Response::Vetoed,
        ]);
        let mut env = make_env(&state, &mut handler, &interp);
        let actor = EntityRef(1);

        let result = execute_action(&mut env, &action, actor, vec![], span()).unwrap();
        assert_eq!(result, Value::Int(99));

        assert_eq!(handler.log.len(), 3);
        assert!(matches!(&handler.log[0], Effect::ActionStarted { .. }));
        assert!(matches!(&handler.log[1], Effect::DeductCost { .. }));
        assert!(matches!(&handler.log[2], Effect::ActionCompleted { .. }));
    }

    #[test]
    fn action_cost_overridden() {
        // Host overrides cost token to use bonus_actions instead
        let action = make_action(
            "Attack",
            "actor",
            vec![],
            Some(CostClause {
                tokens: vec![spanned("action".to_string())],
                span: span(),
            }),
            None,
            vec![spanned(StmtKind::Expr(spanned(ExprKind::IntLit(77))))],
        );

        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::with_responses(vec![
            Response::Acknowledged, // ActionStarted
            Response::Override(Value::Str("bonus_action".to_string())), // DeductCost
        ]);
        let mut env = make_env(&state, &mut handler, &interp);
        let actor = EntityRef(1);

        let result = execute_action(&mut env, &action, actor, vec![], span()).unwrap();
        assert_eq!(result, Value::Int(77));
    }

    #[test]
    fn action_cost_override_invalid_field() {
        // Host overrides cost to an invalid field — should error
        let action = make_action(
            "Attack",
            "actor",
            vec![],
            Some(CostClause {
                tokens: vec![spanned("action".to_string())],
                span: span(),
            }),
            None,
            vec![spanned(StmtKind::Expr(spanned(ExprKind::IntLit(1))))],
        );

        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::with_responses(vec![
            Response::Acknowledged,
            Response::Override(Value::Str("invalid_field".to_string())),
        ]);
        let mut env = make_env(&state, &mut handler, &interp);
        let actor = EntityRef(1);

        let result = execute_action(&mut env, &action, actor, vec![], span());
        assert!(result.is_err());
        assert!(result.unwrap_err().message.contains("invalid cost override"));
    }

    #[test]
    fn action_no_cost_no_requires() {
        // Simple action with just a resolve block
        let action = make_action(
            "SimpleAction",
            "actor",
            vec![],
            None,
            None,
            vec![spanned(StmtKind::Expr(spanned(ExprKind::IntLit(10))))],
        );

        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);
        let actor = EntityRef(1);

        let result = execute_action(&mut env, &action, actor, vec![], span()).unwrap();
        assert_eq!(result, Value::Int(10));

        // Only ActionStarted + ActionCompleted
        assert_eq!(handler.log.len(), 2);
    }

    #[test]
    fn action_requires_override_forces_pass() {
        // requires evaluates to false, but host overrides to true
        let action = make_action(
            "Attack",
            "actor",
            vec![],
            None,
            Some(spanned(ExprKind::BoolLit(false))),
            vec![spanned(StmtKind::Expr(spanned(ExprKind::IntLit(55))))],
        );

        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::with_responses(vec![
            Response::Acknowledged,                   // ActionStarted
            Response::Override(Value::Bool(true)),     // RequiresCheck — force pass
        ]);
        let mut env = make_env(&state, &mut handler, &interp);
        let actor = EntityRef(1);

        let result = execute_action(&mut env, &action, actor, vec![], span()).unwrap();
        assert_eq!(result, Value::Int(55));
    }

    #[test]
    fn action_requires_override_forces_fail() {
        // requires evaluates to true, but host overrides to false
        let action = make_action(
            "Attack",
            "actor",
            vec![],
            None,
            Some(spanned(ExprKind::BoolLit(true))),
            vec![spanned(StmtKind::Expr(spanned(ExprKind::IntLit(55))))],
        );

        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::with_responses(vec![
            Response::Acknowledged,                    // ActionStarted
            Response::Override(Value::Bool(false)),     // RequiresCheck — force fail
        ]);
        let mut env = make_env(&state, &mut handler, &interp);
        let actor = EntityRef(1);

        let result = execute_action(&mut env, &action, actor, vec![], span()).unwrap();
        assert_eq!(result, Value::None);

        // ActionStarted, RequiresCheck, ActionCompleted (no resolve)
        assert_eq!(handler.log.len(), 3);
    }

    #[test]
    fn action_with_params_bound_in_scope() {
        // Action with a parameter, resolve block references it
        // resolve: { target } — returns the target param value
        let action = make_action(
            "Attack",
            "actor",
            vec![Param {
                name: "target".to_string(),
                ty: spanned(TypeExpr::Named("Character".to_string())),
                default: None,
                span: span(),
            }],
            None,
            None,
            vec![spanned(StmtKind::Expr(spanned(ExprKind::Ident(
                "target".to_string(),
            ))))],
        );

        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);
        let actor = EntityRef(1);
        let target = EntityRef(2);

        let result = execute_action(
            &mut env,
            &action,
            actor,
            vec![("target".to_string(), Value::Entity(target))],
            span(),
        )
        .unwrap();

        assert_eq!(result, Value::Entity(EntityRef(2)));
    }

    #[test]
    fn action_turn_actor_set_during_execution() {
        // Verify turn_actor is set to actor during execution and restored after
        let action = make_action(
            "Attack",
            "actor",
            vec![],
            None,
            None,
            vec![spanned(StmtKind::Expr(spanned(ExprKind::IntLit(1))))],
        );

        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);
        let actor = EntityRef(42);

        // Set a prior turn_actor to verify it's restored
        env.turn_actor = Some(EntityRef(99));

        execute_action(&mut env, &action, actor, vec![], span()).unwrap();

        // turn_actor should be restored to the prior value
        assert_eq!(env.turn_actor, Some(EntityRef(99)));
    }

    #[test]
    fn action_multiple_cost_tokens() {
        // Action with cost { action, bonus_action }
        let action = make_action(
            "MultiCost",
            "actor",
            vec![],
            Some(CostClause {
                tokens: vec![
                    spanned("action".to_string()),
                    spanned("bonus_action".to_string()),
                ],
                span: span(),
            }),
            None,
            vec![spanned(StmtKind::Expr(spanned(ExprKind::IntLit(1))))],
        );

        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);
        let actor = EntityRef(1);

        execute_action(&mut env, &action, actor, vec![], span()).unwrap();

        // ActionStarted, DeductCost(action), DeductCost(bonus_action), ActionCompleted
        assert_eq!(handler.log.len(), 4);
        assert!(matches!(
            &handler.log[1],
            Effect::DeductCost { token, budget_field, .. }
            if token == "action" && budget_field == "actions"
        ));
        assert!(matches!(
            &handler.log[2],
            Effect::DeductCost { token, budget_field, .. }
            if token == "bonus_action" && budget_field == "bonus_actions"
        ));
    }

    // ── Reaction execution tests ───────────────────────────────

    #[test]
    fn reaction_basic_trigger_bound() {
        // Reaction that returns its trigger payload
        let reaction = make_reaction(
            "OpportunityAttack",
            "reactor",
            "entity_leaves_reach",
            None,
            vec![spanned(StmtKind::Expr(spanned(ExprKind::Ident(
                "trigger".to_string(),
            ))))],
        );

        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);
        let reactor = EntityRef(1);
        let payload = Value::Struct {
            name: "__event_entity_leaves_reach".to_string(),
            fields: {
                let mut f = BTreeMap::new();
                f.insert("entity".to_string(), Value::Entity(EntityRef(2)));
                f
            },
        };

        let result =
            execute_reaction(&mut env, &reaction, reactor, payload.clone(), span()).unwrap();

        assert_eq!(result, payload);

        // ActionStarted(Reaction), ActionCompleted
        assert_eq!(handler.log.len(), 2);
        assert!(matches!(
            &handler.log[0],
            Effect::ActionStarted { kind: ActionKind::Reaction { event, .. }, .. }
            if event == "entity_leaves_reach"
        ));
        assert!(matches!(&handler.log[1], Effect::ActionCompleted { .. }));
    }

    #[test]
    fn reaction_started_veto() {
        let reaction = make_reaction(
            "OpportunityAttack",
            "reactor",
            "entity_leaves_reach",
            None,
            vec![spanned(StmtKind::Expr(spanned(ExprKind::IntLit(42))))],
        );

        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::with_responses(vec![Response::Vetoed]);
        let mut env = make_env(&state, &mut handler, &interp);
        let reactor = EntityRef(1);

        let result =
            execute_reaction(&mut env, &reaction, reactor, Value::None, span()).unwrap();
        assert_eq!(result, Value::None);

        // Only ActionStarted + ActionCompleted
        assert_eq!(handler.log.len(), 2);
    }

    #[test]
    fn reaction_with_cost() {
        let reaction = make_reaction(
            "OpportunityAttack",
            "reactor",
            "entity_leaves_reach",
            Some(CostClause {
                tokens: vec![spanned("reaction".to_string())],
                span: span(),
            }),
            vec![spanned(StmtKind::Expr(spanned(ExprKind::IntLit(1))))],
        );

        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);
        let reactor = EntityRef(1);

        execute_reaction(&mut env, &reaction, reactor, Value::None, span()).unwrap();

        // ActionStarted, DeductCost(reaction), ActionCompleted
        assert_eq!(handler.log.len(), 3);
        assert!(matches!(
            &handler.log[1],
            Effect::DeductCost { token, budget_field, .. }
            if token == "reaction" && budget_field == "reactions"
        ));
    }

    #[test]
    fn reaction_turn_actor_save_restore() {
        let reaction = make_reaction(
            "OpportunityAttack",
            "reactor",
            "entity_leaves_reach",
            None,
            vec![spanned(StmtKind::Expr(spanned(ExprKind::IntLit(1))))],
        );

        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);
        let reactor = EntityRef(5);

        env.turn_actor = Some(EntityRef(10));
        execute_reaction(&mut env, &reaction, reactor, Value::None, span()).unwrap();
        assert_eq!(env.turn_actor, Some(EntityRef(10)));
    }

    #[test]
    fn reaction_receiver_bound_in_scope() {
        // Reaction resolve block returns the receiver variable
        let reaction = make_reaction(
            "OpportunityAttack",
            "reactor",
            "entity_leaves_reach",
            None,
            vec![spanned(StmtKind::Expr(spanned(ExprKind::Ident(
                "reactor".to_string(),
            ))))],
        );

        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);
        let reactor = EntityRef(7);

        let result =
            execute_reaction(&mut env, &reaction, reactor, Value::None, span()).unwrap();
        assert_eq!(result, Value::Entity(EntityRef(7)));
    }

    // ── Negative protocol tests ──────────────────────────────────

    #[test]
    fn action_started_invalid_response_errors() {
        // ActionStarted only accepts Acknowledged or Vetoed
        let action = make_action(
            "Attack",
            "actor",
            vec![],
            None,
            None,
            vec![spanned(StmtKind::Expr(spanned(ExprKind::IntLit(1))))],
        );

        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::with_responses(vec![
            Response::Override(Value::Bool(true)), // invalid for ActionStarted
        ]);
        let mut env = make_env(&state, &mut handler, &interp);
        let actor = EntityRef(1);

        let result = execute_action(&mut env, &action, actor, vec![], span());
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .message
            .contains("protocol error"));
    }

    #[test]
    fn requires_check_invalid_response_errors() {
        // RequiresCheck only accepts Acknowledged or Override(Bool)
        let action = make_action(
            "Attack",
            "actor",
            vec![],
            None,
            Some(spanned(ExprKind::BoolLit(true))),
            vec![spanned(StmtKind::Expr(spanned(ExprKind::IntLit(1))))],
        );

        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::with_responses(vec![
            Response::Acknowledged,  // ActionStarted
            Response::Vetoed,        // invalid for RequiresCheck
        ]);
        let mut env = make_env(&state, &mut handler, &interp);
        let actor = EntityRef(1);

        let result = execute_action(&mut env, &action, actor, vec![], span());
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .message
            .contains("protocol error"));
    }

    #[test]
    fn action_completed_invalid_response_errors() {
        // ActionCompleted only accepts Acknowledged
        let action = make_action(
            "Attack",
            "actor",
            vec![],
            None,
            None,
            vec![spanned(StmtKind::Expr(spanned(ExprKind::IntLit(1))))],
        );

        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::with_responses(vec![
            Response::Acknowledged,  // ActionStarted
            Response::Vetoed,        // invalid for ActionCompleted
        ]);
        let mut env = make_env(&state, &mut handler, &interp);
        let actor = EntityRef(1);

        let result = execute_action(&mut env, &action, actor, vec![], span());
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .message
            .contains("protocol error"));
    }

    #[test]
    fn action_veto_path_completed_invalid_response_errors() {
        // When ActionStarted is vetoed, the subsequent ActionCompleted
        // must still validate that only Acknowledged is returned.
        let action = make_action(
            "Attack",
            "actor",
            vec![],
            None,
            None,
            vec![spanned(StmtKind::Expr(spanned(ExprKind::IntLit(1))))],
        );

        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::with_responses(vec![
            Response::Vetoed,        // ActionStarted → veto
            Response::Vetoed,        // invalid for ActionCompleted on veto path
        ]);
        let mut env = make_env(&state, &mut handler, &interp);
        let actor = EntityRef(1);

        let result = execute_action(&mut env, &action, actor, vec![], span());
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .message
            .contains("protocol error"));
    }

    #[test]
    fn reaction_veto_path_completed_invalid_response_errors() {
        // When reaction's ActionStarted is vetoed, ActionCompleted
        // must still validate that only Acknowledged is returned.
        let reaction = make_reaction(
            "OpportunityAttack",
            "entity_leaves_reach",
            "actor",
            None,
            vec![spanned(StmtKind::Expr(spanned(ExprKind::IntLit(1))))],
        );

        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::with_responses(vec![
            Response::Vetoed,                    // ActionStarted → veto
            Response::Override(Value::Int(99)),   // invalid for ActionCompleted
        ]);
        let mut env = make_env(&state, &mut handler, &interp);
        let reactor = EntityRef(1);

        let result =
            execute_reaction(&mut env, &reaction, reactor, Value::None, span());
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .message
            .contains("protocol error"));
    }
}
