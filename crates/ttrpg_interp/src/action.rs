use ttrpg_ast::ast::{ActionDecl, Block, CostClause, ExprKind, HookDecl, ReactionDecl};
use ttrpg_ast::{Name, Span, Spanned};

use crate::effect::{ActionKind, Effect, Response};
use crate::eval::{eval_block, eval_expr};
use crate::state::EntityRef;
use crate::value::Value;
use crate::Env;
use crate::RuntimeError;

// ── Shared lifecycle helpers ──────────────────────────────────

/// Whether the action lifecycle should proceed or was vetoed at start.
enum LifecycleStart {
    Proceed,
    Vetoed,
}

/// Emit `ActionStarted` and handle the response.
///
/// On `Vetoed`, emits `ActionCompleted` (with protocol validation) and returns
/// `LifecycleStart::Vetoed` — the caller should return `Ok(Value::None)`.
fn emit_action_started(
    env: &mut Env,
    name: &str,
    effect: Effect,
    actor: EntityRef,
    call_span: Span,
) -> Result<LifecycleStart, RuntimeError> {
    let response = env.handler.handle(effect);
    match response {
        Response::Acknowledged => Ok(LifecycleStart::Proceed),
        Response::Vetoed => {
            emit_action_completed(env, name, actor, call_span)?;
            Ok(LifecycleStart::Vetoed)
        }
        other => Err(RuntimeError::with_span(
            format!(
                "protocol error: expected Acknowledged or Vetoed for ActionStarted, got {:?}",
                other
            ),
            call_span,
        )),
    }
}

/// Emit `ActionCompleted` with protocol validation (only `Acknowledged` is valid).
fn emit_action_completed(
    env: &mut Env,
    name: &str,
    actor: EntityRef,
    call_span: Span,
) -> Result<(), RuntimeError> {
    let response = env.handler.handle(Effect::ActionCompleted {
        name: Name::from(name),
        actor,
    });
    match response {
        Response::Acknowledged => Ok(()),
        other => Err(RuntimeError::with_span(
            format!(
                "protocol error: expected Acknowledged for ActionCompleted, got {:?}",
                other
            ),
            call_span,
        )),
    }
}

/// Run `body` inside a scoped environment with `turn_actor` set to `actor`.
///
/// Handles: save/restore `turn_actor`, push/pop scope, and emit
/// `ActionCompleted` on success.
fn scoped_execute(
    env: &mut Env,
    name: &str,
    actor: EntityRef,
    call_span: Span,
    body: impl FnOnce(&mut Env) -> Result<Value, RuntimeError>,
) -> Result<Value, RuntimeError> {
    let prev_turn_actor = env.turn_actor.take();
    env.turn_actor = Some(actor);
    env.push_scope();

    let result = body(env);

    env.pop_scope();
    env.turn_actor = prev_turn_actor;

    if result.is_ok() {
        emit_action_completed(env, name, actor, call_span)?;
    }

    result
}

/// Inner pipeline shared by actions and reactions: optional requires → optional
/// cost → resolve block.
fn execute_pipeline(
    env: &mut Env,
    actor: &EntityRef,
    action_name: &str,
    requires: Option<&Spanned<ExprKind>>,
    cost: Option<&CostClause>,
    resolve: &Block,
    call_span: Span,
) -> Result<Value, RuntimeError> {
    // Requires clause (if present)
    if let Some(requires_expr) = requires {
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
            action: Name::from(action_name),
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

    // Cost deduction
    if let Some(cost) = cost {
        deduct_costs(env, actor, cost, call_span)?;
    }

    // Execute resolve block
    let resolve = resolve.clone();
    eval_block(env, &resolve)
}

// ── Action execution ───────────────────────────────────────────

/// Execute an action through the full pipeline:
///
/// 1. Emit `ActionStarted` (veto → early return)
/// 2. Fill defaults for missing optional params
/// 3. Bind scope: receiver + params, save/restore `turn_actor`
/// 4. Requires clause → cost deduction → resolve block
/// 5. Emit `ActionCompleted`
pub(crate) fn execute_action(
    env: &mut Env,
    action: &ActionDecl,
    actor: EntityRef,
    mut args: Vec<(Name, Value)>,
    call_span: Span,
) -> Result<Value, RuntimeError> {
    let action_name = action.name.clone();
    let param_values: Vec<Value> = args.iter().map(|(_, v)| v.clone()).collect();

    // 1. Emit ActionStarted (veto → early return)
    if let LifecycleStart::Vetoed = emit_action_started(
        env,
        &action_name,
        Effect::ActionStarted {
            name: action_name.clone(),
            kind: ActionKind::Action,
            actor,
            params: param_values,
        },
        actor,
        call_span,
    )? {
        return Ok(Value::None);
    }

    // 2. Fill defaults for missing optional params (after veto check)
    for i in args.len()..action.params.len() {
        if let Some(ref default_expr) = action.params[i].default {
            env.push_scope();
            env.bind(action.receiver_name.clone(), Value::Entity(actor));
            for (pname, pval) in &args {
                env.bind(pname.clone(), pval.clone());
            }
            let result = eval_expr(env, default_expr);
            env.pop_scope();
            args.push((action.params[i].name.clone(), result?));
        }
    }

    // 3–5. Scoped execution with lifecycle completion
    scoped_execute(env, &action_name, actor, call_span, |env| {
        env.bind(action.receiver_name.clone(), Value::Entity(actor));
        for (name, value) in &args {
            env.bind(name.clone(), value.clone());
        }
        execute_pipeline(
            env,
            &actor,
            &action.name,
            action.requires.as_ref(),
            action.cost.as_ref(),
            &action.resolve,
            call_span,
        )
    })
}

// ── Reaction execution ─────────────────────────────────────────

/// Execute a reaction through the pipeline:
///
/// 1. Emit `ActionStarted` with kind: Reaction (veto → early return)
/// 2. Bind scope: receiver + trigger payload, save/restore `turn_actor`
/// 3. Cost deduction → resolve block
/// 4. Emit `ActionCompleted`
pub(crate) fn execute_reaction(
    env: &mut Env,
    reaction: &ReactionDecl,
    reactor: EntityRef,
    event_payload: Value,
    call_span: Span,
) -> Result<Value, RuntimeError> {
    let reaction_name = reaction.name.clone();

    // 1. Emit ActionStarted (veto → early return)
    if let LifecycleStart::Vetoed = emit_action_started(
        env,
        &reaction_name,
        Effect::ActionStarted {
            name: reaction_name.clone(),
            kind: ActionKind::Reaction {
                event: reaction.trigger.event_name.clone(),
                trigger: event_payload.clone(),
            },
            actor: reactor,
            params: vec![],
        },
        reactor,
        call_span,
    )? {
        return Ok(Value::None);
    }

    // 2–4. Scoped execution with lifecycle completion
    scoped_execute(env, &reaction_name, reactor, call_span, |env| {
        env.bind(reaction.receiver_name.clone(), Value::Entity(reactor));
        env.bind(Name::from("trigger"), event_payload);
        execute_pipeline(
            env,
            &reactor,
            &reaction.name,
            None,
            reaction.cost.as_ref(),
            &reaction.resolve,
            call_span,
        )
    })
}

// ── Hook execution ────────────────────────────────────────────

/// Execute a hook through the pipeline:
///
/// 1. Emit `ActionStarted` with kind: Hook (veto → early return)
/// 2. Bind scope: receiver + trigger payload, save/restore `turn_actor`
/// 3. Execute resolve block (no cost deduction for hooks)
/// 4. Emit `ActionCompleted`
pub(crate) fn execute_hook(
    env: &mut Env,
    hook: &HookDecl,
    target: EntityRef,
    event_payload: Value,
    call_span: Span,
) -> Result<Value, RuntimeError> {
    let hook_name = hook.name.clone();

    // 1. Emit ActionStarted (veto → early return)
    if let LifecycleStart::Vetoed = emit_action_started(
        env,
        &hook_name,
        Effect::ActionStarted {
            name: hook_name.clone(),
            kind: ActionKind::Hook {
                event: hook.trigger.event_name.clone(),
                trigger: event_payload.clone(),
            },
            actor: target,
            params: vec![],
        },
        target,
        call_span,
    )? {
        return Ok(Value::None);
    }

    // 2–4. Scoped execution with lifecycle completion
    scoped_execute(env, &hook_name, target, call_span, |env| {
        env.bind(hook.receiver_name.clone(), Value::Entity(target));
        env.bind(Name::from("trigger"), event_payload);
        let resolve = hook.resolve.clone();
        eval_block(env, &resolve)
    })
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
    let expected_tokens = env
        .interp
        .type_env
        .valid_cost_tokens()
        .into_iter()
        .map(|n| n.to_string())
        .collect::<Vec<_>>();

    for token in &cost.tokens {
        let budget_field = env
            .interp
            .type_env
            .resolve_cost_token(&token.node)
            .ok_or_else(|| {
                RuntimeError::with_span(
                    format!(
                        "internal error: unknown cost token '{}'; expected one of: {}",
                        token.node,
                        expected_tokens.join(", ")
                    ),
                    token.span,
                )
            })?;

        let response = env.handler.handle(Effect::DeductCost {
            actor: *actor,
            token: token.node.clone(),
            budget_field: budget_field.clone(),
        });

        match response {
            Response::Acknowledged => {
                // Layer 1: host is responsible for the deduction
                // Layer 2: adapter handles this
            }
            Response::Override(Value::Str(replacement)) => {
                // Validate that the replacement is a valid cost token
                if env
                    .interp
                    .type_env
                    .resolve_cost_token(&replacement)
                    .is_none()
                {
                    return Err(RuntimeError::with_span(
                        format!(
                            "invalid cost override '{}'; expected one of: {}",
                            replacement,
                            expected_tokens.join(", ")
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

    use ttrpg_ast::ast::*;
    use ttrpg_ast::{Name, Span, Spanned};
    use ttrpg_checker::env::TypeEnv;

    use crate::effect::{EffectHandler, Response};
    use crate::state::{ActiveCondition, StateProvider};
    use crate::Interpreter;

    // ── Test infrastructure ────────────────────────────────────

    fn span() -> Span {
        Span::dummy()
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
        fn position_eq(&self, _a: &Value, _b: &Value) -> bool {
            false
        }
        fn distance(&self, _a: &Value, _b: &Value) -> Option<i64> {
            None
        }
    }

    fn empty_program() -> Program {
        Program::default()
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
            name: Name::from(name),
            receiver_name: Name::from(receiver_name),
            receiver_type: spanned(TypeExpr::Named("Character".into())),
            receiver_with_groups: vec![],
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
            name: Name::from(name),
            receiver_name: Name::from(receiver_name),
            receiver_type: spanned(TypeExpr::Named("Character".into())),
            receiver_with_groups: vec![],
            trigger: TriggerExpr {
                event_name: Name::from(event_name),
                bindings: vec![],
                span: span(),
            },
            cost,
            resolve: spanned(resolve_stmts),
        }
    }

    // ── Token resolution tests ─────────────────────────────────

    fn type_env_with_turn_budget(fields: &[&str]) -> TypeEnv {
        let mut env = TypeEnv::new();
        env.types.insert(
            "TurnBudget".into(),
            ttrpg_checker::env::DeclInfo::Struct(ttrpg_checker::env::StructInfo {
                name: "TurnBudget".into(),
                fields: fields
                    .iter()
                    .map(|name| ttrpg_checker::env::FieldInfo {
                        name: Name::from(*name),
                        ty: ttrpg_checker::ty::Ty::Int,
                        has_default: false,
                    })
                    .collect(),
            }),
        );
        env
    }

    #[test]
    fn token_resolution_legacy_aliases() {
        let env = TypeEnv::new();
        assert_eq!(
            env.resolve_cost_token("action"),
            Some(Name::from("actions"))
        );
        assert_eq!(
            env.resolve_cost_token("bonus_action"),
            Some(Name::from("bonus_actions"))
        );
        assert_eq!(
            env.resolve_cost_token("reaction"),
            Some(Name::from("reactions"))
        );
    }

    #[test]
    fn token_resolution_custom_turn_budget_fields() {
        let env = type_env_with_turn_budget(&["attack", "movement"]);
        assert_eq!(env.resolve_cost_token("attack"), Some(Name::from("attack")));
        assert_eq!(
            env.resolve_cost_token("movement"),
            Some(Name::from("movement"))
        );
        assert_eq!(env.resolve_cost_token("action"), None);
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
                tokens: vec![spanned(Name::from("action"))],
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
        assert!(
            matches!(&handler.log[0], Effect::ActionStarted { name, kind: ActionKind::Action, .. } if name == "Attack")
        );
        assert!(
            matches!(&handler.log[1], Effect::RequiresCheck { action, passed: true, .. } if action == "Attack")
        );
        assert!(
            matches!(&handler.log[2], Effect::DeductCost { token, budget_field, .. } if token == "action" && budget_field == "actions")
        );
        assert!(
            matches!(&handler.log[3], Effect::ActionCompleted { name, .. } if name == "Attack")
        );
    }

    #[test]
    fn action_requires_fail_no_cost_spent() {
        // Action with requires(false) — should skip cost and resolve
        let action = make_action(
            "Attack",
            "actor",
            vec![],
            Some(CostClause {
                tokens: vec![spanned(Name::from("action"))],
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
        assert!(matches!(
            &handler.log[1],
            Effect::RequiresCheck { passed: false, .. }
        ));
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
                tokens: vec![spanned(Name::from("action"))],
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
                tokens: vec![spanned(Name::from("action"))],
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
        let mut handler =
            ScriptedHandler::with_responses(vec![Response::Acknowledged, Response::Vetoed]);
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
                tokens: vec![spanned(Name::from("action"))],
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
            Response::Acknowledged,                                     // ActionStarted
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
                tokens: vec![spanned(Name::from("action"))],
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
        assert!(result
            .unwrap_err()
            .message
            .contains("invalid cost override"));
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
            Response::Acknowledged,                // ActionStarted
            Response::Override(Value::Bool(true)), // RequiresCheck — force pass
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
            Response::Acknowledged,                 // ActionStarted
            Response::Override(Value::Bool(false)), // RequiresCheck — force fail
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
                name: "target".into(),
                ty: spanned(TypeExpr::Named("Character".into())),
                default: None,
                with_groups: vec![],
                span: span(),
            }],
            None,
            None,
            vec![spanned(StmtKind::Expr(spanned(ExprKind::Ident(
                "target".into(),
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
            vec![(Name::from("target"), Value::Entity(target))],
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
                    spanned(Name::from("action")),
                    spanned(Name::from("bonus_action")),
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

    #[test]
    fn action_custom_cost_token_uses_matching_turn_budget_field() {
        let action = make_action(
            "Advance",
            "actor",
            vec![],
            Some(CostClause {
                tokens: vec![spanned(Name::from("movement"))],
                span: span(),
            }),
            None,
            vec![spanned(StmtKind::Expr(spanned(ExprKind::IntLit(1))))],
        );

        let program = empty_program();
        let type_env = type_env_with_turn_budget(&["movement"]);
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);
        let actor = EntityRef(1);

        execute_action(&mut env, &action, actor, vec![], span()).unwrap();

        assert!(matches!(
            handler.log.get(1),
            Some(Effect::DeductCost { token, budget_field, .. })
                if token == "movement" && budget_field == "movement"
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
                "trigger".into(),
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
            name: "__event_entity_leaves_reach".into(),
            fields: {
                let mut f = BTreeMap::new();
                f.insert("entity".into(), Value::Entity(EntityRef(2)));
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

        let result = execute_reaction(&mut env, &reaction, reactor, Value::None, span()).unwrap();
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
                tokens: vec![spanned(Name::from("reaction"))],
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
                "reactor".into(),
            ))))],
        );

        let program = empty_program();
        let type_env = empty_type_env();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);
        let reactor = EntityRef(7);

        let result = execute_reaction(&mut env, &reaction, reactor, Value::None, span()).unwrap();
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
        assert!(result.unwrap_err().message.contains("protocol error"));
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
            Response::Acknowledged, // ActionStarted
            Response::Vetoed,       // invalid for RequiresCheck
        ]);
        let mut env = make_env(&state, &mut handler, &interp);
        let actor = EntityRef(1);

        let result = execute_action(&mut env, &action, actor, vec![], span());
        assert!(result.is_err());
        assert!(result.unwrap_err().message.contains("protocol error"));
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
            Response::Acknowledged, // ActionStarted
            Response::Vetoed,       // invalid for ActionCompleted
        ]);
        let mut env = make_env(&state, &mut handler, &interp);
        let actor = EntityRef(1);

        let result = execute_action(&mut env, &action, actor, vec![], span());
        assert!(result.is_err());
        assert!(result.unwrap_err().message.contains("protocol error"));
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
            Response::Vetoed, // ActionStarted → veto
            Response::Vetoed, // invalid for ActionCompleted on veto path
        ]);
        let mut env = make_env(&state, &mut handler, &interp);
        let actor = EntityRef(1);

        let result = execute_action(&mut env, &action, actor, vec![], span());
        assert!(result.is_err());
        assert!(result.unwrap_err().message.contains("protocol error"));
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
            Response::Vetoed,                   // ActionStarted → veto
            Response::Override(Value::Int(99)), // invalid for ActionCompleted
        ]);
        let mut env = make_env(&state, &mut handler, &interp);
        let reactor = EntityRef(1);

        let result = execute_reaction(&mut env, &reaction, reactor, Value::None, span());
        assert!(result.is_err());
        assert!(result.unwrap_err().message.contains("protocol error"));
    }
}
