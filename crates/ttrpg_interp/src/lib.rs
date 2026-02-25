pub mod value;
pub mod effect;
pub mod state;
pub mod eval;
pub mod call;
pub mod builtins;
pub mod action;
pub mod pipeline;
pub mod event;
pub mod adapter;
pub mod reference_state;

use std::collections::HashMap;

use ttrpg_ast::{Name, Span, Spanned};
use ttrpg_ast::ast::{
    DeclKind, ExprKind, Program, TopLevel,
};
use ttrpg_checker::env::TypeEnv;

use crate::effect::EffectHandler;
use crate::event::{EventResult, HookResult};
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

// ── Interpreter ────────────────────────────────────────────────

/// The main interpreter. Holds a reference to the checked program and
/// provides methods for executing actions, evaluating derives, etc.
pub struct Interpreter<'p> {
    pub(crate) type_env: &'p TypeEnv,
    pub(crate) program: &'p Program,
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

        Ok(Interpreter {
            type_env,
            program,
        })
    }

    /// Execute a named action through the full pipeline.
    ///
    /// `actor` is the entity performing the action. `args` are positional
    /// values for the action's declared parameters (excluding the receiver).
    pub fn execute_action(
        &self,
        state: &dyn StateProvider,
        handler: &mut dyn EffectHandler,
        name: &str,
        actor: EntityRef,
        args: Vec<Value>,
    ) -> Result<Value, RuntimeError> {
        let action_decl = self
            .program
            .actions
            .get(name)
            .ok_or_else(|| RuntimeError::new(format!("undefined action '{}'", name)))?;
        let action_decl = action_decl.clone();

        // Map positional args to param names
        if args.len() > action_decl.params.len() {
            return Err(RuntimeError::new(format!(
                "too many arguments: action '{}' takes {} params, got {}",
                name,
                action_decl.params.len(),
                args.len()
            )));
        }
        if args.len() < action_decl.params.len() {
            // Check if the missing ones have defaults
            for i in args.len()..action_decl.params.len() {
                if action_decl.params[i].default.is_none() {
                    return Err(RuntimeError::new(format!(
                        "missing required argument '{}' for action '{}'",
                        action_decl.params[i].name, name
                    )));
                }
            }
        }

        let mut named_args: Vec<(Name, Value)> = Vec::new();
        for (i, val) in args.into_iter().enumerate() {
            named_args.push((action_decl.params[i].name.clone(), val));
        }

        let mut env = Env::new(state, handler, self);
        let span = Span::dummy();
        action::execute_action(&mut env, &action_decl, actor, named_args, span)
    }

    /// Execute a named reaction through the full pipeline.
    ///
    /// `reactor` is the entity performing the reaction. `event_payload`
    /// is the event struct value that triggered the reaction.
    pub fn execute_reaction(
        &self,
        state: &dyn StateProvider,
        handler: &mut dyn EffectHandler,
        name: &str,
        reactor: EntityRef,
        event_payload: Value,
    ) -> Result<Value, RuntimeError> {
        let reaction_decl = self
            .program
            .reactions
            .get(name)
            .ok_or_else(|| RuntimeError::new(format!("undefined reaction '{}'", name)))?;
        let reaction_decl = reaction_decl.clone();

        let mut env = Env::new(state, handler, self);
        let span = Span::dummy();
        action::execute_reaction(&mut env, &reaction_decl, reactor, event_payload, span)
    }

    /// Evaluate a named mechanic function with pre-evaluated arguments.
    ///
    /// Mechanics can produce dice effects during execution.
    pub fn evaluate_mechanic(
        &self,
        state: &dyn StateProvider,
        handler: &mut dyn EffectHandler,
        name: &str,
        args: Vec<Value>,
    ) -> Result<Value, RuntimeError> {
        if !self.program.mechanics.contains_key(name) {
            return Err(RuntimeError::new(format!(
                "undefined mechanic '{}'",
                name
            )));
        }
        let mut env = Env::new(state, handler, self);
        call::evaluate_fn_with_values(&mut env, name, args, Span::dummy())
    }

    /// Evaluate a named derive or table with pre-evaluated arguments.
    ///
    /// Derives compute values from entity state. The modify pipeline
    /// (condition/option modifiers) runs automatically. Tables are
    /// static lookups that match arguments against entry keys.
    pub fn evaluate_derive(
        &self,
        state: &dyn StateProvider,
        handler: &mut dyn EffectHandler,
        name: &str,
        args: Vec<Value>,
    ) -> Result<Value, RuntimeError> {
        if self.program.derives.contains_key(name) {
            let mut env = Env::new(state, handler, self);
            return call::evaluate_fn_with_values(&mut env, name, args, Span::dummy());
        }
        if self.program.tables.contains_key(name) {
            let mut env = Env::new(state, handler, self);
            return call::dispatch_table_with_values(&mut env, name, args, Span::dummy());
        }
        Err(RuntimeError::new(format!(
            "undefined derive or table '{}'",
            name
        )))
    }

    /// Evaluate a standalone expression against the current program state.
    ///
    /// Used by the CLI `eval` command for ad-hoc expression evaluation.
    pub fn evaluate_expr(
        &self,
        state: &dyn StateProvider,
        handler: &mut dyn EffectHandler,
        expr: &Spanned<ExprKind>,
    ) -> Result<Value, RuntimeError> {
        let mut env = Env::new(state, handler, self);
        eval::eval_expr(&mut env, expr)
    }

    /// Evaluate a standalone expression with pre-populated variable bindings.
    ///
    /// Like [`evaluate_expr`], but injects the given bindings into the initial
    /// scope before evaluation. Used by the CLI to make handle names resolvable
    /// as entity references (e.g. `eval hero.HP`).
    pub fn evaluate_expr_with_bindings(
        &self,
        state: &dyn StateProvider,
        handler: &mut dyn EffectHandler,
        expr: &Spanned<ExprKind>,
        bindings: HashMap<Name, Value>,
    ) -> Result<Value, RuntimeError> {
        let mut env = Env::new(state, handler, self);
        for (name, value) in bindings {
            env.bind(name, value);
        }
        eval::eval_expr(&mut env, expr)
    }

    /// Access the type environment for direct introspection.
    pub fn type_env(&self) -> &TypeEnv {
        self.type_env
    }

    /// Return the variant names for a given enum type.
    ///
    /// Returns `None` if `enum_name` doesn't refer to a defined enum.
    /// This is the primary API for building data-driven registries from
    /// DSL enum definitions at startup.
    pub fn enum_variants(&self, enum_name: &str) -> Option<Vec<String>> {
        self.type_env
            .enum_variants(enum_name)
            .map(|v| v.into_iter().map(|s| s.to_owned()).collect())
    }

    /// Check whether a named action exists in the loaded program.
    pub fn has_action(&self, name: &str) -> bool {
        self.program.actions.contains_key(name)
    }

    /// Check whether a named derive exists in the loaded program.
    pub fn has_derive(&self, name: &str) -> bool {
        self.program.derives.contains_key(name)
    }

    /// Check whether a named mechanic exists in the loaded program.
    pub fn has_mechanic(&self, name: &str) -> bool {
        self.program.mechanics.contains_key(name)
    }

    /// Query which reactions would trigger for a given event.
    ///
    /// This is a **pure query** — no effects are emitted, no state is modified.
    /// Returns which reactions are triggerable and which are suppressed by conditions.
    /// `candidates` is the host-provided set of entities to consider as
    /// potential reactors.
    pub fn what_triggers(
        &self,
        state: &dyn StateProvider,
        name: &str,
        payload: Value,
        candidates: &[EntityRef],
    ) -> Result<EventResult, RuntimeError> {
        event::what_triggers(self, state, name, &payload, candidates)
    }

    /// Query which hooks would match for a given event.
    ///
    /// This is a **pure query** — no effects are emitted, no state is modified.
    /// Hooks have no suppression logic; all matching hooks are returned.
    /// `candidates` is the host-provided set of entities to consider.
    pub fn what_hooks(
        &self,
        state: &dyn StateProvider,
        name: &str,
        payload: Value,
        candidates: &[EntityRef],
    ) -> Result<HookResult, RuntimeError> {
        event::find_matching_hooks(self, state, name, &payload, candidates)
    }

    /// Execute a named hook through the full pipeline.
    ///
    /// `target` is the entity the hook is bound to. `event_payload`
    /// is the event struct value that triggered the hook.
    pub fn execute_hook(
        &self,
        state: &dyn StateProvider,
        handler: &mut dyn EffectHandler,
        name: &str,
        target: EntityRef,
        event_payload: Value,
    ) -> Result<Value, RuntimeError> {
        let hook_decl = self
            .program
            .hooks
            .get(name)
            .ok_or_else(|| RuntimeError::new(format!("undefined hook '{}'", name)))?;
        let hook_decl = hook_decl.clone();

        let mut env = Env::new(state, handler, self);
        let span = Span::dummy();
        action::execute_hook(&mut env, &hook_decl, target, event_payload, span)
    }

    /// Fire all hooks that match an event, executing each one.
    ///
    /// This is the convenience method that combines `what_hooks` + `execute_hook`
    /// for each match. Returns the list of hook results in execution order.
    pub fn fire_hooks(
        &self,
        state: &dyn StateProvider,
        handler: &mut dyn EffectHandler,
        event_name: &str,
        payload: Value,
        candidates: &[EntityRef],
    ) -> Result<Vec<(Name, EntityRef, Value)>, RuntimeError> {
        let hook_result = self.what_hooks(state, event_name, payload.clone(), candidates)?;

        let mut results = Vec::new();
        for hook_info in hook_result.hooks {
            let val = self.execute_hook(
                state,
                handler,
                &hook_info.name,
                hook_info.target,
                payload.clone(),
            )?;
            results.push((hook_info.name, hook_info.target, val));
        }

        Ok(results)
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
    pub fn bind(&mut self, name: Name, value: Value) {
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
    pub bindings: HashMap<Name, Value>,
}

impl Scope {
    pub fn new() -> Self {
        Scope {
            bindings: HashMap::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::{BTreeMap, VecDeque};

    use ttrpg_ast::diagnostic::Severity;

    use crate::effect::{ActionKind, Effect, Response};
    use crate::state::ActiveCondition;
    use crate::value::{DiceExpr, RollResult};

    // ── Test infrastructure ────────────────────────────────────

    /// Parse → lower → check → build interpreter. Panics on any error.
    fn setup(source: &str) -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
        let (program, parse_errors) = ttrpg_parser::parse(source, ttrpg_ast::FileId::SYNTH);
        assert!(
            parse_errors.is_empty(),
            "parse errors: {:?}",
            parse_errors.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
        let mut lower_diags = Vec::new();
        let program = ttrpg_parser::lower_moves(program, &mut lower_diags);
        assert!(
            lower_diags.is_empty(),
            "lowering errors: {:?}",
            lower_diags.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
        let result = ttrpg_checker::check(&program);
        let errors: Vec<_> = result
            .diagnostics
            .iter()
            .filter(|d| d.severity == Severity::Error)
            .collect();
        assert!(
            errors.is_empty(),
            "checker errors: {:?}",
            errors.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
        (program, result)
    }

    struct ScriptedHandler {
        script: VecDeque<Response>,
        log: Vec<Effect>,
    }

    impl ScriptedHandler {
        fn new() -> Self {
            ScriptedHandler {
                script: VecDeque::new(),
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

    // ── End-to-end: parse → lower → check → interpret (small program) ──

    #[test]
    fn e2e_simple_derive() {
        let source = r#"
system "test" {
    derive add(a: int, b: int) -> int { a + b }
}
"#;
        let (program, result) = setup(source);
        let interp = Interpreter::new(&program, &result.env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();

        let val = interp
            .evaluate_derive(&state, &mut handler, "add", vec![Value::Int(3), Value::Int(4)])
            .unwrap();
        assert_eq!(val, Value::Int(7));
    }

    #[test]
    fn e2e_derive_with_pattern_match() {
        let source = r#"
system "test" {
    derive classify(x: int) -> string {
        match {
            x > 100 => "high",
            x > 50 => "medium",
            _ => "low"
        }
    }
}
"#;
        let (program, result) = setup(source);
        let interp = Interpreter::new(&program, &result.env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();

        assert_eq!(
            interp
                .evaluate_derive(&state, &mut handler, "classify", vec![Value::Int(150)])
                .unwrap(),
            Value::Str("high".into())
        );
        assert_eq!(
            interp
                .evaluate_derive(&state, &mut handler, "classify", vec![Value::Int(75)])
                .unwrap(),
            Value::Str("medium".into())
        );
        assert_eq!(
            interp
                .evaluate_derive(&state, &mut handler, "classify", vec![Value::Int(10)])
                .unwrap(),
            Value::Str("low".into())
        );
    }

    // ── End-to-end: action with requires + cost + resolve ──

    #[test]
    fn e2e_action_requires_cost_resolve() {
        let source = r#"
system "test" {
    entity Character {
        HP: int
    }
    action Heal on actor: Character (target: Character) {
        cost { action }
        requires { actor != target }
        resolve {
            target.HP += 10
        }
    }
}
"#;
        let (program, result) = setup(source);
        let interp = Interpreter::new(&program, &result.env).unwrap();
        let mut state = TestState::new();
        let actor = EntityRef(1);
        let target = EntityRef(2);
        state.fields.insert((1, "HP".into()), Value::Int(20));
        state.fields.insert((2, "HP".into()), Value::Int(15));
        state.conditions.insert(1, vec![]);
        state.conditions.insert(2, vec![]);

        let mut handler = ScriptedHandler::new();

        let val = interp
            .execute_action(
                &state,
                &mut handler,
                "Heal",
                actor,
                vec![Value::Entity(target)],
            )
            .unwrap();
        // Resolve block ends with assignment (returns None)
        assert_eq!(val, Value::None);

        // Verify effect sequence: ActionStarted, RequiresCheck, DeductCost, MutateField, ActionCompleted
        assert_eq!(handler.log.len(), 5);
        assert!(matches!(
            &handler.log[0],
            Effect::ActionStarted { name, kind: ActionKind::Action, .. } if name == "Heal"
        ));
        assert!(matches!(
            &handler.log[1],
            Effect::RequiresCheck { action, passed: true, .. } if action == "Heal"
        ));
        assert!(matches!(
            &handler.log[2],
            Effect::DeductCost { token, budget_field, .. }
            if token == "action" && budget_field == "actions"
        ));
        assert!(matches!(
            &handler.log[3],
            Effect::MutateField { entity, path, .. } if entity.0 == 2 && path[0] == crate::effect::FieldPathSegment::Field("HP".into())
        ));
        assert!(matches!(
            &handler.log[4],
            Effect::ActionCompleted { name, .. } if name == "Heal"
        ));
    }

    #[test]
    fn e2e_action_requires_fails() {
        let source = r#"
system "test" {
    entity Character {
        HP: int
    }
    action SelfHeal on actor: Character () {
        requires { false }
        resolve {
            actor.HP += 5
        }
    }
}
"#;
        let (program, result) = setup(source);
        let interp = Interpreter::new(&program, &result.env).unwrap();
        let mut state = TestState::new();
        let actor = EntityRef(1);
        state.fields.insert((1, "HP".into()), Value::Int(20));
        state.conditions.insert(1, vec![]);

        let mut handler = ScriptedHandler::new();
        let val = interp
            .execute_action(&state, &mut handler, "SelfHeal", actor, vec![])
            .unwrap();
        assert_eq!(val, Value::None);

        // ActionStarted, RequiresCheck (failed), ActionCompleted — no MutateField
        assert_eq!(handler.log.len(), 3);
        assert!(matches!(&handler.log[1], Effect::RequiresCheck { passed: false, .. }));
        // No mutation effects
        assert!(!handler.log.iter().any(|e| matches!(e, Effect::MutateField { .. })));
    }

    // ── End-to-end: derive with modify pipeline ──

    #[test]
    fn e2e_derive_with_condition_modifier() {
        let source = r#"
system "test" {
    entity Character {
        speed: int
    }
    derive get_speed(actor: Character) -> int {
        actor.speed
    }
    condition Slow on bearer: Character {
        modify get_speed(actor: bearer) {
            result = result - 10
        }
    }
}
"#;
        let (program, result) = setup(source);
        let interp = Interpreter::new(&program, &result.env).unwrap();
        let mut state = TestState::new();
        let entity = EntityRef(1);
        state.fields.insert((1, "speed".into()), Value::Int(30));
        state.conditions.insert(
            1,
            vec![ActiveCondition {
                id: 100,
                name: "Slow".into(),
                params: BTreeMap::new(),
                bearer: entity,
                gained_at: 1,
                duration: Value::None,
            }],
        );

        let mut handler = ScriptedHandler::new();
        let val = interp
            .evaluate_derive(
                &state,
                &mut handler,
                "get_speed",
                vec![Value::Entity(entity)],
            )
            .unwrap();
        // 30 - 10 = 20
        assert_eq!(val, Value::Int(20));

        // Should have ModifyApplied effects
        assert!(handler.log.iter().any(|e| matches!(e, Effect::ModifyApplied { .. })));
    }

    #[test]
    fn e2e_derive_without_modifier() {
        let source = r#"
system "test" {
    entity Character {
        speed: int
    }
    derive get_speed(actor: Character) -> int {
        actor.speed
    }
    condition Slow on bearer: Character {
        modify get_speed(actor: bearer) {
            result = result - 10
        }
    }
}
"#;
        let (program, result) = setup(source);
        let interp = Interpreter::new(&program, &result.env).unwrap();
        let mut state = TestState::new();
        let entity = EntityRef(1);
        state.fields.insert((1, "speed".into()), Value::Int(30));
        // No conditions — modifier should not apply
        state.conditions.insert(1, vec![]);

        let mut handler = ScriptedHandler::new();
        let val = interp
            .evaluate_derive(
                &state,
                &mut handler,
                "get_speed",
                vec![Value::Entity(entity)],
            )
            .unwrap();
        assert_eq!(val, Value::Int(30));
    }

    // ── End-to-end: event fire + reaction execution ──

    #[test]
    fn e2e_event_fire_and_reaction() {
        let source = r#"
system "test" {
    entity Character {
        name: string
    }
    event flee(actor: Character) {}
    reaction Intercept on defender: Character (trigger: flee(defender)) {
        cost { reaction }
        resolve {
            0
        }
    }
}
"#;
        let (program, result) = setup(source);
        let interp = Interpreter::new(&program, &result.env).unwrap();
        let mut state = TestState::new();
        let entity1 = EntityRef(1);
        let entity2 = EntityRef(2);
        state.fields.insert((1, "name".into()), Value::Str("Alice".into()));
        state.fields.insert((2, "name".into()), Value::Str("Bob".into()));
        state.conditions.insert(1, vec![]);
        state.conditions.insert(2, vec![]);

        // Fire event: flee(actor=entity1)
        let payload = Value::Struct {
            name: "__event_flee".into(),
            fields: {
                let mut f = BTreeMap::new();
                f.insert("actor".into(), Value::Entity(entity1));
                f
            },
        };

        let event_result = interp
            .what_triggers(&state, "flee", payload.clone(), &[entity1, entity2])
            .unwrap();

        // entity1 matches (defender=entity1, positional 'defender' fills actor slot)
        assert_eq!(event_result.triggerable.len(), 1);
        assert_eq!(event_result.triggerable[0].name, "Intercept");
        assert_eq!(event_result.triggerable[0].reactor, entity1);

        // Now execute the matched reaction
        let mut handler = ScriptedHandler::new();
        let val = interp
            .execute_reaction(&state, &mut handler, "Intercept", entity1, payload)
            .unwrap();
        assert_eq!(val, Value::Int(0));

        // Verify effect sequence: ActionStarted (Reaction), DeductCost, ActionCompleted
        assert_eq!(handler.log.len(), 3);
        assert!(matches!(
            &handler.log[0],
            Effect::ActionStarted { kind: ActionKind::Reaction { event, .. }, .. }
            if event == "flee"
        ));
        assert!(matches!(&handler.log[1], Effect::DeductCost { .. }));
        assert!(matches!(&handler.log[2], Effect::ActionCompleted { .. }));
    }

    // ── End-to-end: mechanic with roll ──

    #[test]
    fn e2e_mechanic_with_roll() {
        let source = r#"
system "test" {
    mechanic attack_roll(bonus: int) -> RollResult {
        roll(1d20 + bonus)
    }
}
"#;
        let (program, result) = setup(source);
        let interp = Interpreter::new(&program, &result.env).unwrap();
        let state = TestState::new();

        let roll_result = RollResult {
            expr: DiceExpr {
                count: 1,
                sides: 20,
                filter: None,
                modifier: 5,
            },
            dice: vec![15],
            kept: vec![15],
            modifier: 5,
            total: 20,
            unmodified: 15,
        };
        let mut handler =
            ScriptedHandler::with_responses(vec![Response::Rolled(roll_result.clone())]);

        let val = interp
            .evaluate_mechanic(&state, &mut handler, "attack_roll", vec![Value::Int(5)])
            .unwrap();
        assert_eq!(val, Value::RollResult(roll_result));

        // Should have emitted RollDice
        assert!(matches!(&handler.log[0], Effect::RollDice { .. }));
    }

    // ── Response-validity matrix: invalid response → RuntimeError ──

    #[test]
    fn e2e_roll_dice_vetoed_is_error() {
        let source = r#"
system "test" {
    mechanic roll_it() -> RollResult {
        roll(1d6)
    }
}
"#;
        let (program, result) = setup(source);
        let interp = Interpreter::new(&program, &result.env).unwrap();
        let state = TestState::new();
        // Send Vetoed for RollDice — invalid, should produce RuntimeError
        let mut handler = ScriptedHandler::with_responses(vec![Response::Vetoed]);

        let err = interp
            .evaluate_mechanic(&state, &mut handler, "roll_it", vec![])
            .unwrap_err();
        assert!(
            err.message.contains("protocol error"),
            "expected protocol error, got: {}",
            err.message
        );
    }

    #[test]
    fn e2e_action_started_override_is_error() {
        let source = r#"
system "test" {
    entity Character {
        HP: int
    }
    action Noop on actor: Character () {
        resolve { 0 }
    }
}
"#;
        let (program, result) = setup(source);
        let interp = Interpreter::new(&program, &result.env).unwrap();
        let mut state = TestState::new();
        state.fields.insert((1, "HP".into()), Value::Int(10));
        state.conditions.insert(1, vec![]);

        // Send Override for ActionStarted — invalid
        let mut handler =
            ScriptedHandler::with_responses(vec![Response::Override(Value::Bool(true))]);

        let err = interp
            .execute_action(&state, &mut handler, "Noop", EntityRef(1), vec![])
            .unwrap_err();
        assert!(
            err.message.contains("protocol error"),
            "expected protocol error, got: {}",
            err.message
        );
    }

    #[test]
    fn e2e_deduct_cost_wrong_type_override_is_error() {
        let source = r#"
system "test" {
    entity Character {
        HP: int
    }
    action CostAction on actor: Character () {
        cost { action }
        resolve { 0 }
    }
}
"#;
        let (program, result) = setup(source);
        let interp = Interpreter::new(&program, &result.env).unwrap();
        let mut state = TestState::new();
        state.fields.insert((1, "HP".into()), Value::Int(10));
        state.conditions.insert(1, vec![]);

        // ActionStarted → Acknowledged, DeductCost → Override(Int) — wrong type
        let mut handler = ScriptedHandler::with_responses(vec![
            Response::Acknowledged,
            Response::Override(Value::Int(42)),
        ]);

        let err = interp
            .execute_action(&state, &mut handler, "CostAction", EntityRef(1), vec![])
            .unwrap_err();
        assert!(
            err.message.contains("protocol error"),
            "expected protocol error, got: {}",
            err.message
        );
    }

    // ── Undefined names produce errors ──

    #[test]
    fn e2e_undefined_action_errors() {
        let source = r#"
system "test" {
    entity Character { HP: int }
}
"#;
        let (program, result) = setup(source);
        let interp = Interpreter::new(&program, &result.env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();

        let err = interp
            .execute_action(&state, &mut handler, "Nonexistent", EntityRef(1), vec![])
            .unwrap_err();
        assert!(err.message.contains("undefined action"));
    }

    #[test]
    fn e2e_undefined_derive_errors() {
        let source = r#"
system "test" {
    entity Character { HP: int }
}
"#;
        let (program, result) = setup(source);
        let interp = Interpreter::new(&program, &result.env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();

        let err = interp
            .evaluate_derive(&state, &mut handler, "nonexistent", vec![])
            .unwrap_err();
        assert!(err.message.contains("undefined derive"));
    }

    #[test]
    fn e2e_undefined_mechanic_errors() {
        let source = r#"
system "test" {
    entity Character { HP: int }
}
"#;
        let (program, result) = setup(source);
        let interp = Interpreter::new(&program, &result.env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();

        let err = interp
            .evaluate_mechanic(&state, &mut handler, "nonexistent", vec![])
            .unwrap_err();
        assert!(err.message.contains("undefined mechanic"));
    }

    #[test]
    fn e2e_undefined_reaction_errors() {
        let source = r#"
system "test" {
    entity Character { HP: int }
}
"#;
        let (program, result) = setup(source);
        let interp = Interpreter::new(&program, &result.env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();

        let err = interp
            .execute_reaction(&state, &mut handler, "Nonexistent", EntityRef(1), Value::None)
            .unwrap_err();
        assert!(err.message.contains("undefined reaction"));
    }

    #[test]
    fn e2e_undefined_event_errors() {
        let source = r#"
system "test" {
    entity Character { HP: int }
}
"#;
        let (program, result) = setup(source);
        let interp = Interpreter::new(&program, &result.env).unwrap();
        let state = TestState::new();
        let payload = Value::Struct {
            name: "test".into(),
            fields: BTreeMap::new(),
        };

        let err = interp
            .what_triggers(&state, "nonexistent", payload, &[])
            .unwrap_err();
        assert!(err.message.contains("undefined event"));
    }

    // ── Integration with D&D 5e patterns ──

    #[test]
    fn e2e_d5e_attack_with_damage() {
        // Simplified D&D 5e attack pattern:
        // mechanic attack_roll → roll 1d20 + modifier
        // action Attack → call mechanic, apply damage on hit
        let source = r#"
system "test" {
    entity Character {
        HP: int
        AC: int
        attack_bonus: int
    }
    mechanic roll_attack(attacker: Character) -> RollResult {
        roll(1d20 + attacker.attack_bonus)
    }
    action Attack on attacker: Character (target: Character) {
        cost { action }
        resolve {
            let result = roll_attack(attacker)
            if result.total >= target.AC {
                target.HP -= 8
            }
        }
    }
}
"#;
        let (program, result) = setup(source);
        let interp = Interpreter::new(&program, &result.env).unwrap();
        let mut state = TestState::new();
        let attacker = EntityRef(1);
        let target = EntityRef(2);
        state.fields.insert((1, "HP".into()), Value::Int(30));
        state.fields.insert((1, "AC".into()), Value::Int(15));
        state.fields.insert((1, "attack_bonus".into()), Value::Int(5));
        state.fields.insert((2, "HP".into()), Value::Int(25));
        state.fields.insert((2, "AC".into()), Value::Int(12));
        state.fields.insert((2, "attack_bonus".into()), Value::Int(3));
        state.conditions.insert(1, vec![]);
        state.conditions.insert(2, vec![]);

        // Script: ActionStarted → Ack, RequiresCheck (none), DeductCost → Ack,
        // RollDice → roll 15+5=20 (hits AC 12)
        let roll_result = RollResult {
            expr: DiceExpr {
                count: 1,
                sides: 20,
                filter: None,
                modifier: 5,
            },
            dice: vec![15],
            kept: vec![15],
            modifier: 5,
            total: 20,
            unmodified: 15,
        };
        let mut handler = ScriptedHandler::with_responses(vec![
            Response::Acknowledged, // ActionStarted
            Response::Acknowledged, // DeductCost
            Response::Rolled(roll_result), // RollDice (from roll_attack)
        ]);

        let val = interp
            .execute_action(
                &state,
                &mut handler,
                "Attack",
                attacker,
                vec![Value::Entity(target)],
            )
            .unwrap();
        assert_eq!(val, Value::None); // resolve block ends with if-then (assignment)

        // Verify RollDice was emitted
        assert!(handler.log.iter().any(|e| matches!(e, Effect::RollDice { .. })));
        // Verify MutateField was emitted (HP damage)
        assert!(handler.log.iter().any(|e| matches!(e, Effect::MutateField { .. })));
    }

    #[test]
    fn e2e_d5e_attack_misses() {
        let source = r#"
system "test" {
    entity Character {
        HP: int
        AC: int
        attack_bonus: int
    }
    mechanic roll_attack(attacker: Character) -> RollResult {
        roll(1d20 + attacker.attack_bonus)
    }
    action Attack on attacker: Character (target: Character) {
        cost { action }
        resolve {
            let result = roll_attack(attacker)
            if result.total >= target.AC {
                target.HP -= 8
            }
        }
    }
}
"#;
        let (program, result) = setup(source);
        let interp = Interpreter::new(&program, &result.env).unwrap();
        let mut state = TestState::new();
        let attacker = EntityRef(1);
        let target = EntityRef(2);
        state.fields.insert((1, "HP".into()), Value::Int(30));
        state.fields.insert((1, "AC".into()), Value::Int(15));
        state.fields.insert((1, "attack_bonus".into()), Value::Int(5));
        state.fields.insert((2, "HP".into()), Value::Int(25));
        state.fields.insert((2, "AC".into()), Value::Int(18));
        state.fields.insert((2, "attack_bonus".into()), Value::Int(3));
        state.conditions.insert(1, vec![]);
        state.conditions.insert(2, vec![]);

        // Roll 3+5=8, misses AC 18
        let roll_result = RollResult {
            expr: DiceExpr {
                count: 1,
                sides: 20,
                filter: None,
                modifier: 5,
            },
            dice: vec![3],
            kept: vec![3],
            modifier: 5,
            total: 8,
            unmodified: 3,
        };
        let mut handler = ScriptedHandler::with_responses(vec![
            Response::Acknowledged,        // ActionStarted
            Response::Acknowledged,        // DeductCost
            Response::Rolled(roll_result), // RollDice — miss
        ]);

        interp
            .execute_action(
                &state,
                &mut handler,
                "Attack",
                attacker,
                vec![Value::Entity(target)],
            )
            .unwrap();

        // No MutateField — attack missed
        assert!(!handler.log.iter().any(|e| matches!(e, Effect::MutateField { .. })));
    }

    #[test]
    fn e2e_d5e_condition_suppresses_event() {
        // Test suppression: Stunned condition suppresses reactions
        let source = r#"
system "test" {
    entity Character {
        name: string
    }
    event flee(actor: Character) {}
    reaction Intercept on defender: Character (trigger: flee(actor: defender)) {
        cost { reaction }
        resolve { 0 }
    }
    condition Stunned on bearer: Character {
        suppress flee(actor: bearer)
    }
}
"#;
        let (program, result) = setup(source);
        let interp = Interpreter::new(&program, &result.env).unwrap();
        let mut state = TestState::new();
        let entity1 = EntityRef(1);
        state.fields.insert((1, "name".into()), Value::Str("Alice".into()));
        // Entity 1 has Stunned condition
        state.conditions.insert(
            1,
            vec![ActiveCondition {
                id: 1,
                name: "Stunned".into(),
                params: BTreeMap::new(),
                bearer: entity1,
                gained_at: 1,
                duration: Value::None,
            }],
        );

        let payload = Value::Struct {
            name: "__event_flee".into(),
            fields: {
                let mut f = BTreeMap::new();
                f.insert("actor".into(), Value::Entity(entity1));
                f
            },
        };

        let event_result = interp
            .what_triggers(&state, "flee", payload, &[entity1])
            .unwrap();

        // Entity 1 matches trigger but is suppressed by Stunned
        assert_eq!(event_result.triggerable.len(), 0);
        assert_eq!(event_result.suppressed.len(), 1);
        assert_eq!(event_result.suppressed[0].name, "Intercept");
    }

    // ── Move lowering integration ──

    #[test]
    fn e2e_move_lowered_and_executed() {
        let source = r#"
system "test" {
    entity Character {
        stat: int
    }
    move TestMove on actor: Character () {
        trigger: "make a test"
        roll: 2d6 + actor.stat
        on strong_hit {
            100
        }
        on weak_hit {
            50
        }
        on miss {
            0
        }
    }
}
"#;
        let (program, result) = setup(source);
        let interp = Interpreter::new(&program, &result.env).unwrap();
        let mut state = TestState::new();
        let actor = EntityRef(1);
        state.fields.insert((1, "stat".into()), Value::Int(2));
        state.conditions.insert(1, vec![]);

        // Script for action execution:
        // ActionStarted → Ack, DeductCost → Ack, RollDice → strong hit (total=12)
        let roll_result = RollResult {
            expr: DiceExpr {
                count: 2,
                sides: 6,
                filter: None,
                modifier: 2,
            },
            dice: vec![5, 5],
            kept: vec![5, 5],
            modifier: 2,
            total: 12,
            unmodified: 10,
        };
        let mut handler = ScriptedHandler::with_responses(vec![
            Response::Acknowledged,        // ActionStarted
            Response::Acknowledged,        // DeductCost
            Response::Rolled(roll_result), // RollDice
        ]);

        let val = interp
            .execute_action(&state, &mut handler, "TestMove", actor, vec![])
            .unwrap();
        // Strong hit (total 12 >= 10) → 100
        assert_eq!(val, Value::Int(100));
    }

    // ── End-to-end: struct spread (..base) ──

    #[test]
    fn e2e_struct_spread_override() {
        let source = r#"
system "test" {
    struct Point {
        x: int
        y: int
        z: int
    }
    derive shifted(p: Point) -> Point {
        Point { x: p.x + 10, ..p }
    }
}
"#;
        let (program, result) = setup(source);
        let interp = Interpreter::new(&program, &result.env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();

        let base = Value::Struct {
            name: "Point".into(),
            fields: {
                let mut m = BTreeMap::new();
                m.insert("x".into(), Value::Int(1));
                m.insert("y".into(), Value::Int(2));
                m.insert("z".into(), Value::Int(3));
                m
            },
        };

        let val = interp
            .evaluate_derive(&state, &mut handler, "shifted", vec![base])
            .unwrap();
        match &val {
            Value::Struct { name, fields } => {
                assert_eq!(name, "Point");
                assert_eq!(fields.get("x"), Some(&Value::Int(11)), "x overridden to p.x + 10");
                assert_eq!(fields.get("y"), Some(&Value::Int(2)), "y from base");
                assert_eq!(fields.get("z"), Some(&Value::Int(3)), "z from base");
            }
            _ => panic!("expected Struct, got {:?}", val),
        }
    }

    #[test]
    fn e2e_struct_spread_clone() {
        let source = r#"
system "test" {
    struct Point {
        x: int
        y: int
    }
    derive clone_point(p: Point) -> Point {
        Point { ..p }
    }
}
"#;
        let (program, result) = setup(source);
        let interp = Interpreter::new(&program, &result.env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();

        let base = Value::Struct {
            name: "Point".into(),
            fields: {
                let mut m = BTreeMap::new();
                m.insert("x".into(), Value::Int(5));
                m.insert("y".into(), Value::Int(7));
                m
            },
        };

        let val = interp
            .evaluate_derive(&state, &mut handler, "clone_point", vec![base.clone()])
            .unwrap();
        assert_eq!(val, base);
    }
}
