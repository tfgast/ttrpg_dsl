//! Manual `Arbitrary` implementations for recursive AST types.
//!
//! These types cannot use `#[derive(Arbitrary)]` because they are self-recursive
//! through `Box<Spanned<T>>`. We use `u.len()` (remaining fuzzer bytes) as a
//! natural depth budget: when bytes are scarce, only leaf variants are generated.

use arbitrary::{Arbitrary, Result, Unstructured};

use crate::ast::*;
use crate::span::Spanned;
use crate::DiceFilter;

/// Minimum remaining bytes to allow recursive variant generation.
const RECURSION_BUDGET: usize = 64;

// ── Helper ───────────────────────────────────────────────────────

fn arb_spanned<'a, T: Arbitrary<'a>>(u: &mut Unstructured<'a>) -> Result<Spanned<T>> {
    Ok(Spanned {
        node: u.arbitrary()?,
        span: u.arbitrary()?,
    })
}

fn arb_spanned_expr<'a>(u: &mut Unstructured<'a>) -> Result<Spanned<ExprKind>> {
    Ok(Spanned {
        node: ExprKind::arbitrary(u)?,
        span: u.arbitrary()?,
    })
}

fn arb_boxed_expr<'a>(u: &mut Unstructured<'a>) -> Result<Box<Spanned<ExprKind>>> {
    Ok(Box::new(arb_spanned_expr(u)?))
}

fn arb_spanned_pattern<'a>(u: &mut Unstructured<'a>) -> Result<Spanned<PatternKind>> {
    Ok(Spanned {
        node: PatternKind::arbitrary(u)?,
        span: u.arbitrary()?,
    })
}

fn arb_block<'a>(u: &mut Unstructured<'a>) -> Result<Block> {
    // Generate a small block (0-3 statements) to limit size.
    let len = u.int_in_range(0..=3)?;
    let mut stmts = Vec::with_capacity(len);
    for _ in 0..len {
        stmts.push(arb_spanned(u)?);
    }
    Ok(Spanned {
        node: stmts,
        span: u.arbitrary()?,
    })
}

// ── ExprKind ─────────────────────────────────────────────────────

impl<'a> Arbitrary<'a> for ExprKind {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        if u.len() < RECURSION_BUDGET {
            // Leaf-only variants when bytes are scarce
            let choice = u.int_in_range(0..=6)?;
            return Ok(match choice {
                0 => ExprKind::IntLit(u.arbitrary()?),
                1 => ExprKind::StringLit(u.arbitrary()?),
                2 => ExprKind::BoolLit(u.arbitrary()?),
                3 => ExprKind::NoneLit,
                4 => ExprKind::DiceLit {
                    count: u.arbitrary()?,
                    sides: u.arbitrary()?,
                    filter: u.arbitrary::<Option<DiceFilter>>()?,
                },
                5 => ExprKind::UnitLit {
                    value: u.arbitrary()?,
                    suffix: u.arbitrary()?,
                },
                _ => ExprKind::Ident(u.arbitrary()?),
            });
        }

        let choice = u.int_in_range(0..=22)?;
        Ok(match choice {
            0 => ExprKind::IntLit(u.arbitrary()?),
            1 => ExprKind::StringLit(u.arbitrary()?),
            2 => ExprKind::BoolLit(u.arbitrary()?),
            3 => ExprKind::NoneLit,
            4 => ExprKind::DiceLit {
                count: u.arbitrary()?,
                sides: u.arbitrary()?,
                filter: u.arbitrary()?,
            },
            5 => ExprKind::UnitLit {
                value: u.arbitrary()?,
                suffix: u.arbitrary()?,
            },
            6 => ExprKind::Ident(u.arbitrary()?),
            7 => ExprKind::BinOp {
                op: u.arbitrary()?,
                lhs: arb_boxed_expr(u)?,
                rhs: arb_boxed_expr(u)?,
            },
            8 => ExprKind::UnaryOp {
                op: u.arbitrary()?,
                operand: arb_boxed_expr(u)?,
            },
            9 => ExprKind::FieldAccess {
                object: arb_boxed_expr(u)?,
                field: u.arbitrary()?,
            },
            10 => ExprKind::Index {
                object: arb_boxed_expr(u)?,
                index: arb_boxed_expr(u)?,
            },
            11 => {
                let len = u.int_in_range(0..=3)?;
                let mut args = Vec::with_capacity(len);
                for _ in 0..len {
                    args.push(u.arbitrary()?);
                }
                ExprKind::Call {
                    callee: arb_boxed_expr(u)?,
                    args,
                }
            }
            12 => {
                let len = u.int_in_range(0..=3)?;
                let mut fields = Vec::with_capacity(len);
                for _ in 0..len {
                    fields.push(u.arbitrary()?);
                }
                ExprKind::StructLit {
                    name: u.arbitrary()?,
                    fields,
                    base: if u.arbitrary()? {
                        Some(arb_boxed_expr(u)?)
                    } else {
                        None
                    },
                }
            }
            13 => {
                let len = u.int_in_range(0..=3)?;
                let mut elems = Vec::with_capacity(len);
                for _ in 0..len {
                    elems.push(arb_spanned_expr(u)?);
                }
                ExprKind::ListLit(elems)
            }
            14 => {
                let len = u.int_in_range(0..=2)?;
                let mut entries = Vec::with_capacity(len);
                for _ in 0..len {
                    entries.push((arb_spanned_expr(u)?, arb_spanned_expr(u)?));
                }
                ExprKind::MapLit(entries)
            }
            15 => ExprKind::Paren(arb_boxed_expr(u)?),
            16 => ExprKind::If {
                condition: arb_boxed_expr(u)?,
                then_block: arb_block(u)?,
                else_branch: u.arbitrary()?,
            },
            17 => ExprKind::IfLet {
                pattern: Box::new(arb_spanned_pattern(u)?),
                scrutinee: arb_boxed_expr(u)?,
                then_block: arb_block(u)?,
                else_branch: u.arbitrary()?,
            },
            18 => {
                let len = u.int_in_range(0..=3)?;
                let mut arms = Vec::with_capacity(len);
                for _ in 0..len {
                    arms.push(u.arbitrary()?);
                }
                ExprKind::PatternMatch {
                    scrutinee: arb_boxed_expr(u)?,
                    arms,
                }
            }
            19 => {
                let len = u.int_in_range(0..=3)?;
                let mut arms = Vec::with_capacity(len);
                for _ in 0..len {
                    arms.push(u.arbitrary()?);
                }
                ExprKind::GuardMatch { arms }
            }
            20 => ExprKind::For {
                pattern: Box::new(arb_spanned_pattern(u)?),
                iterable: u.arbitrary()?,
                body: arb_block(u)?,
            },
            21 => ExprKind::ListComprehension {
                element: arb_boxed_expr(u)?,
                pattern: Box::new(arb_spanned_pattern(u)?),
                iterable: u.arbitrary()?,
                filter: if u.arbitrary()? {
                    Some(arb_boxed_expr(u)?)
                } else {
                    None
                },
            },
            22 => ExprKind::Has {
                entity: arb_boxed_expr(u)?,
                group_name: u.arbitrary()?,
                alias: u.arbitrary()?,
            },
            _ => ExprKind::Is {
                entity: arb_boxed_expr(u)?,
                entity_type: u.arbitrary()?,
            },
        })
    }
}

// ── TypeExpr ─────────────────────────────────────────────────────

impl<'a> Arbitrary<'a> for TypeExpr {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        if u.len() < RECURSION_BUDGET {
            let choice = u.int_in_range(0..=14)?;
            return Ok(match choice {
                0 => TypeExpr::Int,
                1 => TypeExpr::Bool,
                2 => TypeExpr::String,
                3 => TypeExpr::Float,
                4 => TypeExpr::DiceExpr,
                5 => TypeExpr::RollResult,
                6 => TypeExpr::TurnBudget,
                7 => TypeExpr::Duration,
                8 => TypeExpr::Position,
                9 => TypeExpr::Condition,
                10 => TypeExpr::ActiveCondition,
                11 => TypeExpr::Invocation,
                12 => TypeExpr::Unit,
                13 => TypeExpr::Named(u.arbitrary()?),
                _ => TypeExpr::Qualified {
                    qualifier: u.arbitrary()?,
                    name: u.arbitrary()?,
                },
            });
        }

        let choice = u.int_in_range(0..=19)?;
        Ok(match choice {
            0 => TypeExpr::Int,
            1 => TypeExpr::Bool,
            2 => TypeExpr::String,
            3 => TypeExpr::Float,
            4 => TypeExpr::DiceExpr,
            5 => TypeExpr::RollResult,
            6 => TypeExpr::TurnBudget,
            7 => TypeExpr::Duration,
            8 => TypeExpr::Position,
            9 => TypeExpr::Condition,
            10 => TypeExpr::ActiveCondition,
            11 => TypeExpr::Invocation,
            12 => TypeExpr::Unit,
            13 => TypeExpr::Named(u.arbitrary()?),
            14 => TypeExpr::Qualified {
                qualifier: u.arbitrary()?,
                name: u.arbitrary()?,
            },
            14 => {
                let k: Spanned<TypeExpr> = arb_spanned(u)?;
                let v: Spanned<TypeExpr> = arb_spanned(u)?;
                TypeExpr::Map(Box::new(k), Box::new(v))
            }
            15 => {
                let inner: Spanned<TypeExpr> = arb_spanned(u)?;
                TypeExpr::List(Box::new(inner))
            }
            16 => {
                let inner: Spanned<TypeExpr> = arb_spanned(u)?;
                TypeExpr::Set(Box::new(inner))
            }
            17 => {
                let inner: Spanned<TypeExpr> = arb_spanned(u)?;
                TypeExpr::OptionType(Box::new(inner))
            }
            _ => TypeExpr::Resource(arb_boxed_expr(u)?, arb_boxed_expr(u)?),
        })
    }
}

// ── PatternKind ──────────────────────────────────────────────────

impl<'a> Arbitrary<'a> for PatternKind {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        if u.len() < RECURSION_BUDGET {
            let choice = u.int_in_range(0..=6)?;
            return Ok(match choice {
                0 => PatternKind::Wildcard,
                1 => PatternKind::IntLit(u.arbitrary()?),
                2 => PatternKind::StringLit(u.arbitrary()?),
                3 => PatternKind::BoolLit(u.arbitrary()?),
                4 => PatternKind::Ident(u.arbitrary()?),
                5 => PatternKind::NoneLit,
                _ => PatternKind::QualifiedVariant {
                    ty: u.arbitrary()?,
                    variant: u.arbitrary()?,
                },
            });
        }

        let choice = u.int_in_range(0..=9)?;
        Ok(match choice {
            0 => PatternKind::Wildcard,
            1 => PatternKind::IntLit(u.arbitrary()?),
            2 => PatternKind::StringLit(u.arbitrary()?),
            3 => PatternKind::BoolLit(u.arbitrary()?),
            4 => PatternKind::Ident(u.arbitrary()?),
            5 => PatternKind::QualifiedVariant {
                ty: u.arbitrary()?,
                variant: u.arbitrary()?,
            },
            6 => {
                let len = u.int_in_range(0..=3)?;
                let mut fields = Vec::with_capacity(len);
                for _ in 0..len {
                    fields.push(arb_spanned_pattern(u)?);
                }
                PatternKind::QualifiedDestructure {
                    ty: u.arbitrary()?,
                    variant: u.arbitrary()?,
                    fields,
                }
            }
            7 => {
                let len = u.int_in_range(0..=3)?;
                let mut fields = Vec::with_capacity(len);
                for _ in 0..len {
                    fields.push(arb_spanned_pattern(u)?);
                }
                PatternKind::BareDestructure {
                    name: u.arbitrary()?,
                    fields,
                }
            }
            8 => PatternKind::NoneLit,
            _ => PatternKind::Some(Box::new(arb_spanned_pattern(u)?)),
        })
    }
}

// ── ModifyStmt ───────────────────────────────────────────────────

impl<'a> Arbitrary<'a> for ModifyStmt {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        if u.len() < RECURSION_BUDGET {
            // Non-recursive variants only
            let choice = u.int_in_range(0..=3)?;
            return Ok(match choice {
                0 => ModifyStmt::Let {
                    name: u.arbitrary()?,
                    ty: if u.arbitrary()? {
                        Some(arb_spanned(u)?)
                    } else {
                        None
                    },
                    value: arb_spanned_expr(u)?,
                    span: u.arbitrary()?,
                },
                1 => ModifyStmt::ParamOverride {
                    name: u.arbitrary()?,
                    value: arb_spanned_expr(u)?,
                    span: u.arbitrary()?,
                },
                2 => ModifyStmt::ResultOverride {
                    field: u.arbitrary()?,
                    value: arb_spanned_expr(u)?,
                    span: u.arbitrary()?,
                },
                _ => ModifyStmt::CostOverride {
                    tokens: {
                        let len = u.int_in_range(0..=2)?;
                        let mut v = Vec::with_capacity(len);
                        for _ in 0..len {
                            v.push(arb_spanned(u)?);
                        }
                        v
                    },
                    free: u.arbitrary()?,
                    span: u.arbitrary()?,
                },
            });
        }

        let choice = u.int_in_range(0..=4)?;
        Ok(match choice {
            0 => ModifyStmt::Let {
                name: u.arbitrary()?,
                ty: if u.arbitrary()? {
                    Some(arb_spanned(u)?)
                } else {
                    None
                },
                value: arb_spanned_expr(u)?,
                span: u.arbitrary()?,
            },
            1 => ModifyStmt::ParamOverride {
                name: u.arbitrary()?,
                value: arb_spanned_expr(u)?,
                span: u.arbitrary()?,
            },
            2 => ModifyStmt::ResultOverride {
                field: u.arbitrary()?,
                value: arb_spanned_expr(u)?,
                span: u.arbitrary()?,
            },
            3 => {
                let then_len = u.int_in_range(0..=2)?;
                let mut then_body = Vec::with_capacity(then_len);
                for _ in 0..then_len {
                    then_body.push(ModifyStmt::arbitrary(u)?);
                }
                let else_body = if u.arbitrary()? {
                    let else_len = u.int_in_range(0..=2)?;
                    let mut v = Vec::with_capacity(else_len);
                    for _ in 0..else_len {
                        v.push(ModifyStmt::arbitrary(u)?);
                    }
                    Some(v)
                } else {
                    None
                };
                ModifyStmt::If {
                    condition: arb_spanned_expr(u)?,
                    then_body,
                    else_body,
                    span: u.arbitrary()?,
                }
            }
            _ => ModifyStmt::CostOverride {
                tokens: {
                    let len = u.int_in_range(0..=2)?;
                    let mut v = Vec::with_capacity(len);
                    for _ in 0..len {
                        v.push(arb_spanned(u)?);
                    }
                    v
                },
                free: u.arbitrary()?,
                span: u.arbitrary()?,
            },
        })
    }
}

// ── Program ──────────────────────────────────────────────────────

impl<'a> Arbitrary<'a> for Program {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        let len = u.int_in_range(0..=4)?;
        let mut items = Vec::with_capacity(len);
        for _ in 0..len {
            items.push(arb_spanned(u)?);
        }
        let mut program = Program {
            items,
            ..Default::default()
        };
        program.build_index();
        Ok(program)
    }
}
