use std::collections::HashSet;

use ttrpg_ast::ast::ConditionClause;
use ttrpg_checker::ty::Ty;

use crate::Env;
use crate::RuntimeError;
use crate::effect::{EffectHandler, Response, Effect};
use crate::eval::{eval_expr, value_eq};
use crate::state::{EntityRef, StateProvider};
use crate::value::Value;
use crate::Interpreter;

// ── Result types ────────────────────────────────────────────────

/// Result of firing an event: which reactions are triggerable vs suppressed.
#[derive(Debug, Clone)]
pub struct EventResult {
    pub suppressed: Vec<ReactionInfo>,
    pub triggerable: Vec<ReactionInfo>,
}

/// A matched reaction with its reactor entity.
#[derive(Debug, Clone)]
pub struct ReactionInfo {
    pub name: String,
    pub reactor: EntityRef,
}

// ── Event firing ────────────────────────────────────────────────

/// Fire an event and determine which reactions are triggered.
///
/// This is a **pure query** — no effects are emitted. Binding expressions
/// are evaluated during matching and must be side-effect-free (enforced
/// by the checker via `BlockKind::TriggerBinding`).
///
/// The host provides `candidates` — the set of entities to consider as
/// potential reactors. This keeps entity enumeration in the host's hands.
///
/// `payload` should be a `Value::Struct` with fields for the event's params
/// and computed fields. The host constructs this when firing the event.
pub fn fire_event(
    interp: &Interpreter,
    state: &dyn StateProvider,
    event_name: &str,
    payload: &Value,
    candidates: &[EntityRef],
) -> Result<EventResult, RuntimeError> {
    // Look up event info for param/field type information
    let event_info = match interp.type_env.events.get(event_name) {
        Some(info) => info.clone(),
        None => {
            return Err(RuntimeError::new(format!(
                "undefined event '{}'",
                event_name
            )));
        }
    };

    // Extract payload fields
    let payload_fields = match payload {
        Value::Struct { fields, .. } => fields,
        _ => {
            return Err(RuntimeError::new(
                "event payload must be a Struct value",
            ));
        }
    };

    // Use a no-op handler since fire_event is a pure query.
    // The checker guarantees no effectful calls in trigger binding expressions.
    let mut noop_handler = NoopHandler;
    let mut env = Env::new(state, &mut noop_handler, interp);

    let mut suppressed = Vec::new();
    let mut triggerable = Vec::new();

    // Scan all reactions whose trigger event name matches
    for (reaction_name, reaction_decl) in &interp.index.reactions {
        if reaction_decl.trigger.event_name != event_name {
            continue;
        }

        // For each candidate entity, try to match trigger bindings
        for candidate in candidates {
            if !match_trigger_bindings(
                &mut env,
                &reaction_decl.trigger.bindings,
                &reaction_decl.receiver_name,
                *candidate,
                &event_info.params,
                &event_info.fields,
                payload_fields,
            )? {
                continue;
            }

            let info = ReactionInfo {
                name: reaction_name.to_string(),
                reactor: *candidate,
            };

            // Check suppression
            if is_suppressed(
                &mut env,
                event_name,
                &event_info.params,
                &event_info.fields,
                payload_fields,
            )? {
                suppressed.push(info);
            } else {
                triggerable.push(info);
            }
        }
    }

    Ok(EventResult {
        suppressed,
        triggerable,
    })
}

// ── Trigger matching ────────────────────────────────────────────

/// Match a reaction's trigger bindings against event payload.
///
/// Uses **fill-the-gaps** semantics:
/// 1. Named bindings claim their slots first (params first, then fields)
/// 2. Positional bindings fill remaining unclaimed param slots left-to-right
///
/// Returns true if all bindings match.
fn match_trigger_bindings(
    env: &mut Env,
    bindings: &[ttrpg_ast::ast::TriggerBinding],
    receiver_name: &str,
    candidate: EntityRef,
    event_params: &[ttrpg_checker::env::ParamInfo],
    event_fields: &[(String, Ty)],
    payload_fields: &std::collections::BTreeMap<String, Value>,
) -> Result<bool, RuntimeError> {
    // Push scope with candidate bound as receiver
    env.push_scope();
    env.bind(receiver_name.to_string(), Value::Entity(candidate));

    let result = match_bindings_inner(
        env,
        bindings,
        event_params,
        event_fields,
        payload_fields,
    );

    env.pop_scope();

    result
}

/// Inner binding match logic (separated for scope cleanup safety).
fn match_bindings_inner(
    env: &mut Env,
    bindings: &[ttrpg_ast::ast::TriggerBinding],
    event_params: &[ttrpg_checker::env::ParamInfo],
    event_fields: &[(String, Ty)],
    payload_fields: &std::collections::BTreeMap<String, Value>,
) -> Result<bool, RuntimeError> {
    // Track which param slots are claimed by named bindings
    let mut claimed_params: HashSet<usize> = HashSet::new();

    // First pass: identify named bindings and claim their slots
    for binding in bindings {
        if let Some(ref name) = binding.name {
            // Look up in event params first
            if let Some(pos) = event_params.iter().position(|p| p.name == *name) {
                claimed_params.insert(pos);
            }
            // Named bindings referencing fields don't claim param slots
        }
    }

    // Second pass: evaluate all bindings and check matches
    let mut pos_iter = (0..event_params.len()).filter(|i| !claimed_params.contains(i));

    for binding in bindings {
        // Evaluate the binding expression
        let binding_val = eval_expr(env, &binding.value)?;

        if let Some(ref name) = binding.name {
            // Named binding: look up name in event params first, then fields
            let actual_val = if let Some(param_info) =
                event_params.iter().find(|p| p.name == *name)
            {
                payload_fields.get(&param_info.name)
            } else if event_fields.iter().any(|(n, _)| n == name) {
                payload_fields.get(name)
            } else {
                // Unknown binding name — no match
                return Ok(false);
            };

            match actual_val {
                Some(val) => {
                    if !value_eq(env.state, val, &binding_val) {
                        return Ok(false);
                    }
                }
                None => return Ok(false),
            }
        } else {
            // Positional binding: fill next unclaimed param slot
            let slot_idx = match pos_iter.next() {
                Some(idx) => idx,
                None => return Ok(false), // more positional bindings than unclaimed params
            };

            let param_name = &event_params[slot_idx].name;
            match payload_fields.get(param_name) {
                Some(val) => {
                    if !value_eq(env.state, val, &binding_val) {
                        return Ok(false);
                    }
                }
                None => return Ok(false),
            }
        }
    }

    Ok(true)
}

// ── Suppression checking ────────────────────────────────────────

/// Check if any condition on any entity-typed event param/field suppresses
/// the reaction for this event.
fn is_suppressed(
    env: &mut Env,
    event_name: &str,
    event_params: &[ttrpg_checker::env::ParamInfo],
    event_fields: &[(String, Ty)],
    payload_fields: &std::collections::BTreeMap<String, Value>,
) -> Result<bool, RuntimeError> {
    // Collect all entity-typed values from event params and fields
    let mut entity_values: Vec<(&str, EntityRef)> = Vec::new();

    for param_info in event_params {
        if matches!(param_info.ty, Ty::Entity(_)) {
            if let Some(Value::Entity(e)) = payload_fields.get(&param_info.name) {
                entity_values.push((&param_info.name, *e));
            }
        }
    }

    for (field_name, field_ty) in event_fields {
        if matches!(field_ty, Ty::Entity(_)) {
            if let Some(Value::Entity(e)) = payload_fields.get(field_name) {
                entity_values.push((field_name, *e));
            }
        }
    }

    // For each entity, check its conditions for suppress clauses
    let mut seen_condition_ids: HashSet<u64> = HashSet::new();

    for (_param_name, entity_ref) in &entity_values {
        let conditions = match env.state.read_conditions(entity_ref) {
            Some(c) => c,
            None => continue,
        };

        for condition in &conditions {
            if !seen_condition_ids.insert(condition.id) {
                continue;
            }

            let cond_decl = match env.interp.index.conditions.get(condition.name.as_str()) {
                Some(decl) => *decl,
                None => continue,
            };

            for clause_item in &cond_decl.clauses {
                let suppress = match clause_item {
                    ConditionClause::Suppress(s) => s,
                    ConditionClause::Modify(_) => continue,
                };

                if suppress.event_name != event_name {
                    continue;
                }

                // Check suppress bindings
                if check_suppress_bindings(
                    env,
                    &suppress.bindings,
                    &cond_decl.receiver_name,
                    &Value::Entity(condition.bearer),
                    event_params,
                    event_fields,
                    payload_fields,
                )? {
                    return Ok(true);
                }
            }
        }
    }

    Ok(false)
}

/// Check if suppress clause bindings match the event payload.
///
/// Suppress bindings reference event params or fields (same lookup as trigger
/// bindings — params first, then fields). The binding expression is evaluated
/// in a scope with the condition's receiver bound.
fn check_suppress_bindings(
    env: &mut Env,
    bindings: &[ttrpg_ast::ast::ModifyBinding],
    receiver_name: &str,
    bearer: &Value,
    event_params: &[ttrpg_checker::env::ParamInfo],
    event_fields: &[(String, Ty)],
    payload_fields: &std::collections::BTreeMap<String, Value>,
) -> Result<bool, RuntimeError> {
    env.push_scope();
    env.bind(receiver_name.to_string(), bearer.clone());

    let result = check_suppress_bindings_inner(
        env,
        bindings,
        event_params,
        event_fields,
        payload_fields,
    );

    env.pop_scope();

    result
}

fn check_suppress_bindings_inner(
    env: &mut Env,
    bindings: &[ttrpg_ast::ast::ModifyBinding],
    event_params: &[ttrpg_checker::env::ParamInfo],
    event_fields: &[(String, Ty)],
    payload_fields: &std::collections::BTreeMap<String, Value>,
) -> Result<bool, RuntimeError> {
    for binding in bindings {
        let binding_val = eval_expr(env, &binding.value)?;

        // Look up binding name in event params first, then fields
        let actual_val = if let Some(param_info) =
            event_params.iter().find(|p| p.name == binding.name)
        {
            payload_fields.get(&param_info.name)
        } else if event_fields.iter().any(|(n, _)| *n == binding.name) {
            payload_fields.get(&binding.name)
        } else {
            return Ok(false);
        };

        match actual_val {
            Some(val) => {
                if !value_eq(env.state, val, &binding_val) {
                    return Ok(false);
                }
            }
            None => return Ok(false),
        }
    }

    Ok(true)
}

// ── No-op handler ───────────────────────────────────────────────

/// A no-op effect handler for pure query operations (fire_event).
///
/// The checker guarantees that trigger and suppress binding expressions
/// are side-effect-free (via BlockKind::TriggerBinding), so no effects
/// should be emitted during event firing. If one somehow is, we return
/// Acknowledged as a safe default.
struct NoopHandler;

impl EffectHandler for NoopHandler {
    fn handle(&mut self, _effect: Effect) -> Response {
        Response::Acknowledged
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::{BTreeMap, HashMap};

    use ttrpg_ast::{Span, Spanned};
    use ttrpg_ast::ast::*;
    use ttrpg_checker::env::{
        ConditionInfo, EventInfo, ParamInfo, TypeEnv,
    };
    use ttrpg_checker::ty::Ty;

    use crate::state::ActiveCondition;
    use crate::value::Value;

    // ── Test infrastructure ────────────────────────────────────

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

    /// Build a program with a single system block containing the given declarations.
    fn program_with_decls(decls: Vec<DeclKind>) -> Program {
        Program {
            items: vec![spanned(TopLevel::System(SystemBlock {
                name: "Test".into(),
                decls: decls.into_iter().map(|d| spanned(d)).collect(),
            }))],
        }
    }

    /// Build a payload struct value from a list of (name, value) pairs.
    fn make_payload(fields: Vec<(&str, Value)>) -> Value {
        let mut map = BTreeMap::new();
        for (name, val) in fields {
            map.insert(name.to_string(), val);
        }
        Value::Struct {
            name: "EventPayload".into(),
            fields: map,
        }
    }

    // ── Test 7: Trigger matching with named bindings ─────────

    #[test]
    fn trigger_matching_named_bindings() {
        // event Attacked(target: Character, attacker: Character)
        // reaction Parry on defender: Character {
        //   trigger Attacked(target: defender)
        //   resolve { ... }
        // }
        // Fire Attacked with target=entity(1), attacker=entity(2).
        // Candidate entity(1) should match (defender=entity(1), target: defender matches).
        // Candidate entity(2) should NOT match (target != entity(2)).

        let program = program_with_decls(vec![
            DeclKind::Event(EventDecl {
                name: "Attacked".into(),
                params: vec![
                    Param {
                        name: "target".into(),
                        ty: spanned(TypeExpr::Named("Character".into())),
                        default: None,
                        span: dummy_span(),
                    },
                    Param {
                        name: "attacker".into(),
                        ty: spanned(TypeExpr::Named("Character".into())),
                        default: None,
                        span: dummy_span(),
                    },
                ],
                fields: vec![],
            }),
            DeclKind::Reaction(ReactionDecl {
                name: "Parry".into(),
                receiver_name: "defender".into(),
                receiver_type: spanned(TypeExpr::Named("Character".into())),
                trigger: TriggerExpr {
                    event_name: "Attacked".into(),
                    bindings: vec![TriggerBinding {
                        name: Some("target".into()),
                        value: spanned(ExprKind::Ident("defender".into())),
                        span: dummy_span(),
                    }],
                    span: dummy_span(),
                },
                cost: None,
                resolve: spanned(vec![spanned(StmtKind::Expr(spanned(
                    ExprKind::IntLit(0),
                )))]),
            }),
        ]);

        let mut type_env = TypeEnv::new();
        type_env.events.insert(
            "Attacked".into(),
            EventInfo {
                name: "Attacked".into(),
                params: vec![
                    ParamInfo {
                        name: "target".into(),
                        ty: Ty::Entity("Character".into()),
                        has_default: false,
                    },
                    ParamInfo {
                        name: "attacker".into(),
                        ty: Ty::Entity("Character".into()),
                        has_default: false,
                    },
                ],
                fields: vec![],
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();

        let payload = make_payload(vec![
            ("target", Value::Entity(EntityRef(1))),
            ("attacker", Value::Entity(EntityRef(2))),
        ]);

        let candidates = vec![EntityRef(1), EntityRef(2)];

        let result = fire_event(&interp, &state, "Attacked", &payload, &candidates).unwrap();

        // entity(1) should match (defender=entity(1), target: defender -> entity(1) == target)
        assert_eq!(result.triggerable.len(), 1);
        assert_eq!(result.triggerable[0].name, "Parry");
        assert_eq!(result.triggerable[0].reactor, EntityRef(1));

        // entity(2) should not match
        assert_eq!(result.suppressed.len(), 0);
    }

    // ── Test 8: Trigger matching with positional bindings ────

    #[test]
    fn trigger_matching_positional_bindings() {
        // event Attacked(target: Character, attacker: Character)
        // reaction CounterStrike on fighter: Character {
        //   trigger Attacked(fighter)
        //   // positional: fills first unclaimed param slot (target)
        //   resolve { ... }
        // }

        let program = program_with_decls(vec![
            DeclKind::Event(EventDecl {
                name: "Attacked".into(),
                params: vec![
                    Param {
                        name: "target".into(),
                        ty: spanned(TypeExpr::Named("Character".into())),
                        default: None,
                        span: dummy_span(),
                    },
                    Param {
                        name: "attacker".into(),
                        ty: spanned(TypeExpr::Named("Character".into())),
                        default: None,
                        span: dummy_span(),
                    },
                ],
                fields: vec![],
            }),
            DeclKind::Reaction(ReactionDecl {
                name: "CounterStrike".into(),
                receiver_name: "fighter".into(),
                receiver_type: spanned(TypeExpr::Named("Character".into())),
                trigger: TriggerExpr {
                    event_name: "Attacked".into(),
                    bindings: vec![TriggerBinding {
                        name: None, // positional
                        value: spanned(ExprKind::Ident("fighter".into())),
                        span: dummy_span(),
                    }],
                    span: dummy_span(),
                },
                cost: None,
                resolve: spanned(vec![spanned(StmtKind::Expr(spanned(
                    ExprKind::IntLit(0),
                )))]),
            }),
        ]);

        let mut type_env = TypeEnv::new();
        type_env.events.insert(
            "Attacked".into(),
            EventInfo {
                name: "Attacked".into(),
                params: vec![
                    ParamInfo {
                        name: "target".into(),
                        ty: Ty::Entity("Character".into()),
                        has_default: false,
                    },
                    ParamInfo {
                        name: "attacker".into(),
                        ty: Ty::Entity("Character".into()),
                        has_default: false,
                    },
                ],
                fields: vec![],
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();

        let payload = make_payload(vec![
            ("target", Value::Entity(EntityRef(1))),
            ("attacker", Value::Entity(EntityRef(2))),
        ]);

        let candidates = vec![EntityRef(1), EntityRef(2), EntityRef(3)];

        let result = fire_event(&interp, &state, "Attacked", &payload, &candidates).unwrap();

        // Positional fills first param slot ("target").
        // entity(1) matches because fighter=entity(1) and target=entity(1).
        assert_eq!(result.triggerable.len(), 1);
        assert_eq!(result.triggerable[0].name, "CounterStrike");
        assert_eq!(result.triggerable[0].reactor, EntityRef(1));
    }

    // ── Test 9: Fill-the-gaps semantics ──────────────────────

    #[test]
    fn trigger_fill_the_gaps_semantics() {
        // event Combat(attacker: Character, target: Character, weapon: Character)
        // reaction Dodge on me: Character {
        //   trigger Combat(target: me, me)
        //   // Named: target -> slot 1 (claimed)
        //   // Positional: me -> fills first unclaimed slot 0 (attacker)
        //   resolve { ... }
        // }
        // Fire Combat(attacker=entity(1), target=entity(1), weapon=entity(2))
        // Candidate entity(1): named "target: me" matches (target=entity(1)==me),
        //   positional "me" fills slot 0 (attacker=entity(1)==me) -> MATCH
        // Candidate entity(2): named "target: me" -> target=entity(1)!=entity(2) -> NO MATCH

        let program = program_with_decls(vec![
            DeclKind::Event(EventDecl {
                name: "Combat".into(),
                params: vec![
                    Param {
                        name: "attacker".into(),
                        ty: spanned(TypeExpr::Named("Character".into())),
                        default: None,
                        span: dummy_span(),
                    },
                    Param {
                        name: "target".into(),
                        ty: spanned(TypeExpr::Named("Character".into())),
                        default: None,
                        span: dummy_span(),
                    },
                    Param {
                        name: "weapon".into(),
                        ty: spanned(TypeExpr::Named("Character".into())),
                        default: None,
                        span: dummy_span(),
                    },
                ],
                fields: vec![],
            }),
            DeclKind::Reaction(ReactionDecl {
                name: "Dodge".into(),
                receiver_name: "me".into(),
                receiver_type: spanned(TypeExpr::Named("Character".into())),
                trigger: TriggerExpr {
                    event_name: "Combat".into(),
                    bindings: vec![
                        TriggerBinding {
                            name: Some("target".into()), // named: claims slot 1
                            value: spanned(ExprKind::Ident("me".into())),
                            span: dummy_span(),
                        },
                        TriggerBinding {
                            name: None, // positional: fills first unclaimed (slot 0 = attacker)
                            value: spanned(ExprKind::Ident("me".into())),
                            span: dummy_span(),
                        },
                    ],
                    span: dummy_span(),
                },
                cost: None,
                resolve: spanned(vec![spanned(StmtKind::Expr(spanned(
                    ExprKind::IntLit(0),
                )))]),
            }),
        ]);

        let mut type_env = TypeEnv::new();
        type_env.events.insert(
            "Combat".into(),
            EventInfo {
                name: "Combat".into(),
                params: vec![
                    ParamInfo {
                        name: "attacker".into(),
                        ty: Ty::Entity("Character".into()),
                        has_default: false,
                    },
                    ParamInfo {
                        name: "target".into(),
                        ty: Ty::Entity("Character".into()),
                        has_default: false,
                    },
                    ParamInfo {
                        name: "weapon".into(),
                        ty: Ty::Entity("Character".into()),
                        has_default: false,
                    },
                ],
                fields: vec![],
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();

        let payload = make_payload(vec![
            ("attacker", Value::Entity(EntityRef(1))),
            ("target", Value::Entity(EntityRef(1))),
            ("weapon", Value::Entity(EntityRef(2))),
        ]);

        let candidates = vec![EntityRef(1), EntityRef(2)];

        let result = fire_event(&interp, &state, "Combat", &payload, &candidates).unwrap();

        // entity(1): target=entity(1)==me, attacker=entity(1)==me -> MATCH
        assert_eq!(result.triggerable.len(), 1);
        assert_eq!(result.triggerable[0].name, "Dodge");
        assert_eq!(result.triggerable[0].reactor, EntityRef(1));

        // entity(2): target=entity(1)!=entity(2) -> no match
        // (not in triggerable or suppressed)
    }

    // ── Test 10: Trigger matching with candidate iteration ──

    #[test]
    fn trigger_matching_candidate_iteration() {
        // event Blast(target: Character)
        // reaction Shield on defender: Character {
        //   trigger Blast(target: defender)
        //   resolve { ... }
        // }
        // Fire Blast(target=entity(2)).
        // Candidates: entity(1), entity(2), entity(3).
        // Only entity(2) should match.

        let program = program_with_decls(vec![
            DeclKind::Event(EventDecl {
                name: "Blast".into(),
                params: vec![Param {
                    name: "target".into(),
                    ty: spanned(TypeExpr::Named("Character".into())),
                    default: None,
                    span: dummy_span(),
                }],
                fields: vec![],
            }),
            DeclKind::Reaction(ReactionDecl {
                name: "Shield".into(),
                receiver_name: "defender".into(),
                receiver_type: spanned(TypeExpr::Named("Character".into())),
                trigger: TriggerExpr {
                    event_name: "Blast".into(),
                    bindings: vec![TriggerBinding {
                        name: Some("target".into()),
                        value: spanned(ExprKind::Ident("defender".into())),
                        span: dummy_span(),
                    }],
                    span: dummy_span(),
                },
                cost: None,
                resolve: spanned(vec![spanned(StmtKind::Expr(spanned(
                    ExprKind::IntLit(0),
                )))]),
            }),
        ]);

        let mut type_env = TypeEnv::new();
        type_env.events.insert(
            "Blast".into(),
            EventInfo {
                name: "Blast".into(),
                params: vec![ParamInfo {
                    name: "target".into(),
                    ty: Ty::Entity("Character".into()),
                    has_default: false,
                }],
                fields: vec![],
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();

        let payload = make_payload(vec![("target", Value::Entity(EntityRef(2)))]);

        let candidates = vec![EntityRef(1), EntityRef(2), EntityRef(3)];

        let result = fire_event(&interp, &state, "Blast", &payload, &candidates).unwrap();

        // Only entity(2) matches
        assert_eq!(result.triggerable.len(), 1);
        assert_eq!(result.triggerable[0].name, "Shield");
        assert_eq!(result.triggerable[0].reactor, EntityRef(2));

        // No suppressed reactions
        assert_eq!(result.suppressed.len(), 0);
    }

    // ── Test 11: Suppression blocks reaction ─────────────────

    #[test]
    fn suppress_clause_blocks_reaction() {
        // event Attacked(target: Character, attacker: Character)
        // reaction Parry on defender: Character {
        //   trigger Attacked(target: defender)
        //   resolve { ... }
        // }
        // condition Stunned on bearer: Character {
        //   suppress Attacked(target: bearer)
        // }
        // Entity 1 has Stunned condition.
        // Fire Attacked(target=entity(1), attacker=entity(2)).
        // Candidate entity(1) matches trigger, but Stunned suppresses -> suppressed list.

        let program = program_with_decls(vec![
            DeclKind::Event(EventDecl {
                name: "Attacked".into(),
                params: vec![
                    Param {
                        name: "target".into(),
                        ty: spanned(TypeExpr::Named("Character".into())),
                        default: None,
                        span: dummy_span(),
                    },
                    Param {
                        name: "attacker".into(),
                        ty: spanned(TypeExpr::Named("Character".into())),
                        default: None,
                        span: dummy_span(),
                    },
                ],
                fields: vec![],
            }),
            DeclKind::Reaction(ReactionDecl {
                name: "Parry".into(),
                receiver_name: "defender".into(),
                receiver_type: spanned(TypeExpr::Named("Character".into())),
                trigger: TriggerExpr {
                    event_name: "Attacked".into(),
                    bindings: vec![TriggerBinding {
                        name: Some("target".into()),
                        value: spanned(ExprKind::Ident("defender".into())),
                        span: dummy_span(),
                    }],
                    span: dummy_span(),
                },
                cost: None,
                resolve: spanned(vec![spanned(StmtKind::Expr(spanned(
                    ExprKind::IntLit(0),
                )))]),
            }),
            DeclKind::Condition(ConditionDecl {
                name: "Stunned".into(),
                receiver_name: "bearer".into(),
                receiver_type: spanned(TypeExpr::Named("Character".into())),
                clauses: vec![ConditionClause::Suppress(SuppressClause {
                    event_name: "Attacked".into(),
                    bindings: vec![ModifyBinding {
                        name: "target".into(),
                        value: spanned(ExprKind::Ident("bearer".into())),
                        span: dummy_span(),
                    }],
                    span: dummy_span(),
                })],
            }),
        ]);

        let mut type_env = TypeEnv::new();
        type_env.events.insert(
            "Attacked".into(),
            EventInfo {
                name: "Attacked".into(),
                params: vec![
                    ParamInfo {
                        name: "target".into(),
                        ty: Ty::Entity("Character".into()),
                        has_default: false,
                    },
                    ParamInfo {
                        name: "attacker".into(),
                        ty: Ty::Entity("Character".into()),
                        has_default: false,
                    },
                ],
                fields: vec![],
            },
        );
        type_env.conditions.insert(
            "Stunned".into(),
            ConditionInfo {
                name: "Stunned".into(),
                receiver_name: "bearer".into(),
                receiver_type: Ty::Entity("Character".into()),
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let mut state = TestState::new();
        // Entity 1 has Stunned condition
        state.conditions.insert(
            1,
            vec![ActiveCondition {
                id: 500,
                name: "Stunned".into(),
                bearer: EntityRef(1),
                gained_at: 1,
                duration: Value::None,
            }],
        );

        let payload = make_payload(vec![
            ("target", Value::Entity(EntityRef(1))),
            ("attacker", Value::Entity(EntityRef(2))),
        ]);

        let candidates = vec![EntityRef(1)];

        let result = fire_event(&interp, &state, "Attacked", &payload, &candidates).unwrap();

        // Entity(1) matches the trigger but is suppressed by Stunned
        assert_eq!(result.triggerable.len(), 0);
        assert_eq!(result.suppressed.len(), 1);
        assert_eq!(result.suppressed[0].name, "Parry");
        assert_eq!(result.suppressed[0].reactor, EntityRef(1));
    }

    // ── Test 12: Non-matching suppress passes through ────────

    #[test]
    fn non_matching_suppress_passes_through() {
        // event Attacked(target: Character, attacker: Character)
        // event Healed(target: Character)
        // reaction Parry on defender: Character {
        //   trigger Attacked(target: defender)
        //   resolve { ... }
        // }
        // condition Silenced on bearer: Character {
        //   suppress Healed(target: bearer)  // suppresses a DIFFERENT event
        // }
        // Entity 1 has Silenced condition.
        // Fire Attacked(target=entity(1), attacker=entity(2)).
        // Candidate entity(1) matches trigger, Silenced suppress doesn't apply to Attacked.
        // Result: entity(1) should be in triggerable list.

        let program = program_with_decls(vec![
            DeclKind::Event(EventDecl {
                name: "Attacked".into(),
                params: vec![
                    Param {
                        name: "target".into(),
                        ty: spanned(TypeExpr::Named("Character".into())),
                        default: None,
                        span: dummy_span(),
                    },
                    Param {
                        name: "attacker".into(),
                        ty: spanned(TypeExpr::Named("Character".into())),
                        default: None,
                        span: dummy_span(),
                    },
                ],
                fields: vec![],
            }),
            DeclKind::Event(EventDecl {
                name: "Healed".into(),
                params: vec![Param {
                    name: "target".into(),
                    ty: spanned(TypeExpr::Named("Character".into())),
                    default: None,
                    span: dummy_span(),
                }],
                fields: vec![],
            }),
            DeclKind::Reaction(ReactionDecl {
                name: "Parry".into(),
                receiver_name: "defender".into(),
                receiver_type: spanned(TypeExpr::Named("Character".into())),
                trigger: TriggerExpr {
                    event_name: "Attacked".into(),
                    bindings: vec![TriggerBinding {
                        name: Some("target".into()),
                        value: spanned(ExprKind::Ident("defender".into())),
                        span: dummy_span(),
                    }],
                    span: dummy_span(),
                },
                cost: None,
                resolve: spanned(vec![spanned(StmtKind::Expr(spanned(
                    ExprKind::IntLit(0),
                )))]),
            }),
            DeclKind::Condition(ConditionDecl {
                name: "Silenced".into(),
                receiver_name: "bearer".into(),
                receiver_type: spanned(TypeExpr::Named("Character".into())),
                clauses: vec![ConditionClause::Suppress(SuppressClause {
                    event_name: "Healed".into(), // different event
                    bindings: vec![ModifyBinding {
                        name: "target".into(),
                        value: spanned(ExprKind::Ident("bearer".into())),
                        span: dummy_span(),
                    }],
                    span: dummy_span(),
                })],
            }),
        ]);

        let mut type_env = TypeEnv::new();
        type_env.events.insert(
            "Attacked".into(),
            EventInfo {
                name: "Attacked".into(),
                params: vec![
                    ParamInfo {
                        name: "target".into(),
                        ty: Ty::Entity("Character".into()),
                        has_default: false,
                    },
                    ParamInfo {
                        name: "attacker".into(),
                        ty: Ty::Entity("Character".into()),
                        has_default: false,
                    },
                ],
                fields: vec![],
            },
        );
        type_env.events.insert(
            "Healed".into(),
            EventInfo {
                name: "Healed".into(),
                params: vec![ParamInfo {
                    name: "target".into(),
                    ty: Ty::Entity("Character".into()),
                    has_default: false,
                }],
                fields: vec![],
            },
        );
        type_env.conditions.insert(
            "Silenced".into(),
            ConditionInfo {
                name: "Silenced".into(),
                receiver_name: "bearer".into(),
                receiver_type: Ty::Entity("Character".into()),
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let mut state = TestState::new();
        // Entity 1 has Silenced condition (suppresses Healed, not Attacked)
        state.conditions.insert(
            1,
            vec![ActiveCondition {
                id: 600,
                name: "Silenced".into(),
                bearer: EntityRef(1),
                gained_at: 1,
                duration: Value::None,
            }],
        );

        let payload = make_payload(vec![
            ("target", Value::Entity(EntityRef(1))),
            ("attacker", Value::Entity(EntityRef(2))),
        ]);

        let candidates = vec![EntityRef(1)];

        let result = fire_event(&interp, &state, "Attacked", &payload, &candidates).unwrap();

        // Entity(1) matches the trigger, Silenced doesn't suppress Attacked -> triggerable
        assert_eq!(result.triggerable.len(), 1);
        assert_eq!(result.triggerable[0].name, "Parry");
        assert_eq!(result.triggerable[0].reactor, EntityRef(1));

        // Nothing suppressed
        assert_eq!(result.suppressed.len(), 0);
    }
}
