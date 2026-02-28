use std::collections::HashSet;

use crate::env::{FnInfo, FnKind, ParamInfo};
use crate::ty::Ty;

fn param(name: &str, ty: Ty) -> ParamInfo {
    ParamInfo {
        name: name.into(),
        ty,
        has_default: false,
        with_groups: vec![],
    }
}

fn builtin(name: &str, params: Vec<ParamInfo>, return_type: Ty) -> FnInfo {
    FnInfo {
        name: name.into(),
        kind: FnKind::Builtin,
        params,
        return_type,
        receiver: None,
        tags: HashSet::new(),
        synthetic: false,
    }
}

/// Register all built-in function signatures.
pub fn register_builtins() -> Vec<FnInfo> {
    vec![
        // Available everywhere
        builtin("floor", vec![param("x", Ty::Float)], Ty::Int),
        builtin("ceil", vec![param("x", Ty::Float)], Ty::Int),
        builtin(
            "max",
            vec![param("a", Ty::Int), param("b", Ty::Int)],
            Ty::Int,
        ),
        builtin(
            "min",
            vec![param("a", Ty::Int), param("b", Ty::Int)],
            Ty::Int,
        ),
        builtin(
            "distance",
            vec![param("a", Ty::Position), param("b", Ty::Position)],
            Ty::Int,
        ),
        builtin(
            "dice",
            vec![param("count", Ty::Int), param("sides", Ty::Int)],
            Ty::DiceExpr,
        ),
        builtin(
            "multiply_dice",
            vec![param("expr", Ty::DiceExpr), param("factor", Ty::Int)],
            Ty::DiceExpr,
        ),
        builtin("error", vec![param("message", Ty::String)], Ty::Error),
        // Available in rolling blocks
        builtin("roll", vec![param("expr", Ty::DiceExpr)], Ty::RollResult),
        // Available in mutation blocks
        builtin(
            "apply_condition",
            vec![
                param("target", Ty::AnyEntity),
                param("cond", Ty::Condition),
                param("duration", Ty::Duration),
            ],
            Ty::Unit,
        ),
        builtin(
            "remove_condition",
            vec![param("target", Ty::AnyEntity), param("cond", Ty::Condition)],
            Ty::Unit,
        ),
        // Available in action/reaction/hook blocks
        builtin("invocation", vec![], Ty::Invocation),
        builtin("revoke", vec![param("inv", Ty::Invocation)], Ty::Unit),
    ]
}
