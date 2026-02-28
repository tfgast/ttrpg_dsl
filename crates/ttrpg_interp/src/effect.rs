use std::collections::BTreeMap;
use ttrpg_ast::ast::AssignOp;
use ttrpg_ast::Name;

use crate::state::{EntityRef, InvocationId};
use crate::value::{DiceExpr, RollResult, Value};

// ── Supporting types ────────────────────────────────────────────

/// A segment of a field path for mutation targeting.
///
/// A simple field access like `target.HP` is `[Field("HP")]`.
/// A nested access like `target.stats[STR]` is `[Field("stats"), Index(Value::Str("STR"))]`.
#[derive(Debug, Clone, PartialEq)]
pub enum FieldPathSegment {
    Field(Name),
    Index(Value),
}

/// Distinguishes action vs reaction context.
#[derive(Debug, Clone)]
pub enum ActionKind {
    Action,
    Reaction { event: Name, trigger: Value },
    Hook { event: Name, trigger: Value },
}

/// Identifies the source of a modifier.
#[derive(Debug, Clone)]
pub enum ModifySource {
    Condition(Name),
    Option(Name),
}

/// Which phase of the modify pipeline produced a change.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Phase {
    Phase1,
    Phase2,
}

/// A single field change recorded by the modify pipeline.
#[derive(Debug, Clone)]
pub struct FieldChange {
    pub name: Name,
    pub old: Value,
    pub new: Value,
}

/// Outcome of an action execution, reported in `ActionCompleted`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ActionOutcome {
    /// Body completed without error.
    Succeeded,
    /// Host vetoed the action at the gate.
    Vetoed,
    /// Body returned RuntimeError, or host returned unexpected response.
    Failed,
}

// ── Effect enum ─────────────────────────────────────────────────

/// An effect yielded by the interpreter to the host.
///
/// Effects fall into five categories:
/// - **Value effects**: interpreter needs a value back (`RollDice`, `ResolvePrompt`)
/// - **Mutation effects**: state changes (`MutateField`, `ApplyCondition`, `RemoveCondition`, `MutateTurnField`)
/// - **Decision effects**: always passed through (`DeductCost`)
/// - **Gate effects**: host can alter control flow (`ActionStarted`, `RequiresCheck`)
/// - **Informational effects**: fire-and-forget (`ActionCompleted`, `ModifyApplied`)
#[derive(Debug, Clone)]
pub enum Effect {
    // ── Value effects ───────────────────────────────────────
    RollDice {
        expr: DiceExpr,
    },
    ResolvePrompt {
        name: Name,
        params: Vec<Value>,
        hint: Option<String>,
        suggest: Option<Value>,
    },

    // ── Mutation effects ────────────────────────────────────
    MutateField {
        entity: EntityRef,
        path: Vec<FieldPathSegment>,
        op: AssignOp,
        value: Value,
        bounds: Option<(Value, Value)>,
    },
    ApplyCondition {
        target: EntityRef,
        condition: Name,
        params: BTreeMap<Name, Value>,
        duration: Value,
        invocation: Option<InvocationId>,
    },
    RemoveCondition {
        target: EntityRef,
        condition: Name,
        /// `None` = remove all matching the name. `Some(params)` = remove only matching params.
        params: Option<BTreeMap<Name, Value>>,
    },
    MutateTurnField {
        actor: EntityRef,
        field: Name,
        op: AssignOp,
        value: Value,
    },
    GrantGroup {
        entity: EntityRef,
        group_name: Name,
        fields: Value,
    },
    RevokeGroup {
        entity: EntityRef,
        group_name: Name,
    },

    // ── Decision effects ────────────────────────────────────
    DeductCost {
        actor: EntityRef,
        token: Name,
        budget_field: Name,
    },

    // ── Gate effects ────────────────────────────────────────
    ActionStarted {
        name: Name,
        kind: ActionKind,
        actor: EntityRef,
        params: Vec<Value>,
    },
    RequiresCheck {
        action: Name,
        passed: bool,
        reason: Option<String>,
    },

    // ── Informational effects ───────────────────────────────
    ActionCompleted {
        name: Name,
        actor: EntityRef,
        outcome: ActionOutcome,
        invocation: Option<InvocationId>,
    },
    RevokeInvocation {
        invocation: InvocationId,
    },
    ModifyApplied {
        source: ModifySource,
        target_fn: Name,
        phase: Phase,
        changes: Vec<FieldChange>,
    },
}

// ── Response enum ───────────────────────────────────────────────

/// A response from the host to an effect.
#[derive(Debug, Clone)]
pub enum Response {
    /// Dice result (expected response for `RollDice`).
    Rolled(RollResult),
    /// Human decision (expected response for `ResolvePrompt`).
    PromptResult(Value),
    /// Host accepts the effect.
    Acknowledged,
    /// GM substitutes a different value.
    Override(Value),
    /// GM blocks the effect.
    Vetoed,
}

// ── Step enum ───────────────────────────────────────────────────

/// Represents a single step in the execution pipeline.
/// Used for pull-based iteration (future extension).
#[derive(Debug, Clone)]
pub enum Step {
    /// The interpreter has yielded an effect and needs a response.
    Yielded(Box<Effect>),
    /// The interpreter has completed execution.
    Done(Value),
}

// ── EffectHandler trait ─────────────────────────────────────────

/// The host implements this trait to handle effects from the interpreter.
///
/// The interpreter calls `handle` synchronously whenever an effect is
/// produced. The host processes the effect and returns a response.
/// If the host needs async behavior (e.g., waiting for UI input),
/// it blocks inside `handle`.
pub trait EffectHandler {
    fn handle(&mut self, effect: Effect) -> Response;
}

// ── EffectKind discriminant ─────────────────────────────────────

/// A fieldless enum mirroring `Effect` variant names.
///
/// Used by `StateAdapter::pass_through` to configure which mutation
/// effects are forwarded to the inner handler vs. intercepted locally.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum EffectKind {
    RollDice,
    ResolvePrompt,
    MutateField,
    ApplyCondition,
    RemoveCondition,
    MutateTurnField,
    GrantGroup,
    RevokeGroup,
    DeductCost,
    ActionStarted,
    RequiresCheck,
    ActionCompleted,
    RevokeInvocation,
    ModifyApplied,
}

impl EffectKind {
    /// Returns the `EffectKind` discriminant for a given `Effect`.
    pub fn of(effect: &Effect) -> Self {
        match effect {
            Effect::RollDice { .. } => EffectKind::RollDice,
            Effect::ResolvePrompt { .. } => EffectKind::ResolvePrompt,
            Effect::MutateField { .. } => EffectKind::MutateField,
            Effect::ApplyCondition { .. } => EffectKind::ApplyCondition,
            Effect::RemoveCondition { .. } => EffectKind::RemoveCondition,
            Effect::MutateTurnField { .. } => EffectKind::MutateTurnField,
            Effect::GrantGroup { .. } => EffectKind::GrantGroup,
            Effect::RevokeGroup { .. } => EffectKind::RevokeGroup,
            Effect::DeductCost { .. } => EffectKind::DeductCost,
            Effect::ActionStarted { .. } => EffectKind::ActionStarted,
            Effect::RequiresCheck { .. } => EffectKind::RequiresCheck,
            Effect::ActionCompleted { .. } => EffectKind::ActionCompleted,
            Effect::RevokeInvocation { .. } => EffectKind::RevokeInvocation,
            Effect::ModifyApplied { .. } => EffectKind::ModifyApplied,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn effect_kind_of() {
        let effect = Effect::RollDice {
            expr: DiceExpr::single(1, 20, None, 0),
        };
        assert_eq!(EffectKind::of(&effect), EffectKind::RollDice);

        let effect = Effect::ActionCompleted {
            name: "Attack".into(),
            actor: EntityRef(1),
            outcome: ActionOutcome::Succeeded,
            invocation: None,
        };
        assert_eq!(EffectKind::of(&effect), EffectKind::ActionCompleted);
    }

    #[test]
    fn effect_construction_roll_dice() {
        let effect = Effect::RollDice {
            expr: DiceExpr::single(2, 6, None, 3),
        };
        if let Effect::RollDice { expr } = &effect {
            assert_eq!(expr.groups[0].count, 2);
            assert_eq!(expr.groups[0].sides, 6);
            assert_eq!(expr.modifier, 3);
        } else {
            panic!("wrong variant");
        }
    }

    #[test]
    fn effect_construction_mutate_field() {
        let effect = Effect::MutateField {
            entity: EntityRef(1),
            path: vec![FieldPathSegment::Field("HP".into())],
            op: AssignOp::MinusEq,
            value: Value::Int(15),
            bounds: Some((Value::Int(0), Value::Int(100))),
        };
        if let Effect::MutateField {
            entity,
            path,
            op,
            value,
            bounds,
        } = &effect
        {
            assert_eq!(entity.0, 1);
            assert_eq!(path.len(), 1);
            assert!(matches!(op, AssignOp::MinusEq));
            assert_eq!(*value, Value::Int(15));
            assert!(bounds.is_some());
        } else {
            panic!("wrong variant");
        }
    }

    #[test]
    fn effect_construction_action_started() {
        let effect = Effect::ActionStarted {
            name: "Attack".into(),
            kind: ActionKind::Action,
            actor: EntityRef(1),
            params: vec![Value::Entity(EntityRef(2))],
        };
        if let Effect::ActionStarted {
            name, kind, actor, ..
        } = &effect
        {
            assert_eq!(name, "Attack");
            assert!(matches!(kind, ActionKind::Action));
            assert_eq!(actor.0, 1);
        } else {
            panic!("wrong variant");
        }
    }

    #[test]
    fn effect_construction_reaction_started() {
        let effect = Effect::ActionStarted {
            name: "OpportunityAttack".into(),
            kind: ActionKind::Reaction {
                event: "entity_leaves_reach".into(),
                trigger: Value::Str("moved away".into()),
            },
            actor: EntityRef(3),
            params: vec![],
        };
        if let Effect::ActionStarted { kind, .. } = &effect {
            if let ActionKind::Reaction { event, .. } = kind {
                assert_eq!(event, "entity_leaves_reach");
            } else {
                panic!("expected Reaction kind");
            }
        } else {
            panic!("wrong variant");
        }
    }

    #[test]
    fn response_construction() {
        let rolled = Response::Rolled(RollResult {
            expr: DiceExpr::single(1, 20, None, 5),
            dice: vec![15],
            kept: vec![15],
            modifier: 5,
            total: 20,
            unmodified: 15,
        });
        assert!(matches!(rolled, Response::Rolled(_)));
        assert!(matches!(Response::Acknowledged, Response::Acknowledged));
        assert!(matches!(Response::Vetoed, Response::Vetoed));
        assert!(matches!(
            Response::Override(Value::Int(10)),
            Response::Override(_)
        ));
        assert!(matches!(
            Response::PromptResult(Value::Str("yes".into())),
            Response::PromptResult(_)
        ));
    }

    #[test]
    fn effect_construction_deduct_cost() {
        let effect = Effect::DeductCost {
            actor: EntityRef(1),
            token: "action".into(),
            budget_field: "actions".into(),
        };
        if let Effect::DeductCost {
            actor,
            token,
            budget_field,
        } = &effect
        {
            assert_eq!(actor.0, 1);
            assert_eq!(token, "action");
            assert_eq!(budget_field, "actions");
        } else {
            panic!("wrong variant");
        }
    }

    #[test]
    fn effect_construction_modify_applied() {
        let effect = Effect::ModifyApplied {
            source: ModifySource::Condition("Prone".into()),
            target_fn: "attack_roll".into(),
            phase: Phase::Phase1,
            changes: vec![FieldChange {
                name: "mode".into(),
                old: Value::Str("normal".into()),
                new: Value::Str("disadvantage".into()),
            }],
        };
        if let Effect::ModifyApplied {
            source,
            phase,
            changes,
            ..
        } = &effect
        {
            assert!(matches!(source, ModifySource::Condition(n) if n == "Prone"));
            assert_eq!(*phase, Phase::Phase1);
            assert_eq!(changes.len(), 1);
        } else {
            panic!("wrong variant");
        }
    }

    #[test]
    fn effect_kind_is_hashable() {
        use std::collections::HashSet;
        let mut set = HashSet::new();
        set.insert(EffectKind::MutateField);
        set.insert(EffectKind::ApplyCondition);
        set.insert(EffectKind::MutateField); // duplicate
        assert_eq!(set.len(), 2);
    }
}
