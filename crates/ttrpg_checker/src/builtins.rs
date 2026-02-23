use crate::env::{FnInfo, FnKind, ParamInfo};
use crate::ty::Ty;

/// Register all built-in function signatures.
pub fn register_builtins() -> Vec<FnInfo> {
    vec![
        // Available everywhere
        FnInfo {
            name: "floor".into(),
            kind: FnKind::Builtin,
            params: vec![ParamInfo {
                name: "x".into(),
                ty: Ty::Float,
                has_default: false,
                with_groups: vec![],
            }],
            return_type: Ty::Int,
            receiver: None,
        },
        FnInfo {
            name: "ceil".into(),
            kind: FnKind::Builtin,
            params: vec![ParamInfo {
                name: "x".into(),
                ty: Ty::Float,
                has_default: false,
                with_groups: vec![],
            }],
            return_type: Ty::Int,
            receiver: None,
        },
        FnInfo {
            name: "max".into(),
            kind: FnKind::Builtin,
            params: vec![
                ParamInfo {
                    name: "a".into(),
                    ty: Ty::Int,
                    has_default: false,
                    with_groups: vec![],
                },
                ParamInfo {
                    name: "b".into(),
                    ty: Ty::Int,
                    has_default: false,
                    with_groups: vec![],
                },
            ],
            return_type: Ty::Int,
            receiver: None,
        },
        FnInfo {
            name: "min".into(),
            kind: FnKind::Builtin,
            params: vec![
                ParamInfo {
                    name: "a".into(),
                    ty: Ty::Int,
                    has_default: false,
                    with_groups: vec![],
                },
                ParamInfo {
                    name: "b".into(),
                    ty: Ty::Int,
                    has_default: false,
                    with_groups: vec![],
                },
            ],
            return_type: Ty::Int,
            receiver: None,
        },
        FnInfo {
            name: "distance".into(),
            kind: FnKind::Builtin,
            params: vec![
                ParamInfo {
                    name: "a".into(),
                    ty: Ty::Position,
                    has_default: false,
                    with_groups: vec![],
                },
                ParamInfo {
                    name: "b".into(),
                    ty: Ty::Position,
                    has_default: false,
                    with_groups: vec![],
                },
            ],
            return_type: Ty::Int,
            receiver: None,
        },
        FnInfo {
            name: "multiply_dice".into(),
            kind: FnKind::Builtin,
            params: vec![
                ParamInfo {
                    name: "expr".into(),
                    ty: Ty::DiceExpr,
                    has_default: false,
                    with_groups: vec![],
                },
                ParamInfo {
                    name: "factor".into(),
                    ty: Ty::Int,
                    has_default: false,
                    with_groups: vec![],
                },
            ],
            return_type: Ty::DiceExpr,
            receiver: None,
        },
        // Available in rolling blocks
        FnInfo {
            name: "roll".into(),
            kind: FnKind::Builtin,
            params: vec![ParamInfo {
                name: "expr".into(),
                ty: Ty::DiceExpr,
                has_default: false,
                with_groups: vec![],
            }],
            return_type: Ty::RollResult,
            receiver: None,
        },
        // Available in mutation blocks
        FnInfo {
            name: "apply_condition".into(),
            kind: FnKind::Builtin,
            params: vec![
                ParamInfo {
                    name: "target".into(),
                    ty: Ty::AnyEntity,
                    has_default: false,
                    with_groups: vec![],
                },
                ParamInfo {
                    name: "cond".into(),
                    ty: Ty::Condition,
                    has_default: false,
                    with_groups: vec![],
                },
                ParamInfo {
                    name: "duration".into(),
                    ty: Ty::Duration,
                    has_default: false,
                    with_groups: vec![],
                },
            ],
            return_type: Ty::Unit,
            receiver: None,
        },
        FnInfo {
            name: "remove_condition".into(),
            kind: FnKind::Builtin,
            params: vec![
                ParamInfo {
                    name: "target".into(),
                    ty: Ty::AnyEntity,
                    has_default: false,
                    with_groups: vec![],
                },
                ParamInfo {
                    name: "cond".into(),
                    ty: Ty::Condition,
                    has_default: false,
                    with_groups: vec![],
                },
            ],
            return_type: Ty::Unit,
            receiver: None,
        },
    ]
}
