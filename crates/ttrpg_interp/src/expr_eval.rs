//! Step-based expression evaluator (ExprEval frame).
//!
//! Compiles trivially-pure expressions (literals, arithmetic, field access,
//! index) into a flat work sequence that can be advanced without recursion
//! or bridging to the recursive `Env`-based evaluator.
//!
//! Phase 1: handles literal-only expression trees (no identifiers,
//! no calls, no control flow).
//! Phase 2: adds identifier resolution, list/map literals, and call dispatch
//! (named calls only; method calls deferred to Phase 3).

#![allow(dead_code)]

use std::collections::BTreeMap;

use rustc_hash::FxHashMap;
use ttrpg_ast::ast::{
    ArmBody, BinOp, ElseBranch, ExprKind, ForIterable, GuardKind, PatternKind, StmtKind, TypeExpr,
    UnaryOp,
};
use ttrpg_ast::{Name, Span, Spanned};
use ttrpg_checker::env::{DeclInfo, FnKind, TypeEnv};

use crate::RuntimeError;
use crate::effect::{Effect, EffectHandler, Response};
use crate::eval::{
    apply_binop_values, apply_unary_values, field_access_on_value, index_on_value, match_pattern,
};
use crate::execution::{Advance, ExecEnv, Frame};
use crate::runtime_core::RuntimeCore;
use crate::state::StateProvider;
use crate::value::{DiceExpr, Value};

// ── Micro-instruction set ───────────────────────────────────────

/// Metadata for a call argument (value is on the operand stack).
#[derive(Debug, Clone)]
pub(crate) struct ArgMeta {
    /// Named argument label, if present.
    pub name: Option<Name>,
    /// Original span for error reporting.
    pub span: Span,
}

/// Micro-instruction for the ExprEval frame.
///
/// Note: Does not derive Debug because `TypeExpr` (used in `Is`) does not implement Debug.
#[derive(Clone)]
pub(crate) enum ExprWork {
    /// Push a literal value onto the operand stack.
    Literal(Value, Span),
    /// Binary op: pop 2, push 1.
    BinOp(BinOp, Span),
    /// Unary op: pop 1, push 1.
    UnaryOp(UnaryOp, Span),
    /// Field access: pop object, push field value.
    Field(Name, Span),
    /// Index access: pop index + object, push result.
    Index(Span),
    /// Pop and discard top of stack.
    Pop,

    // ── Phase 2 variants ────────────────────────────────────────
    /// Resolve an identifier. Handles scope lookup, cached const,
    /// lazy const eval (pushes child ExprEval), bare enum variants,
    /// condition names, fn refs, enum namespaces, module aliases, turn.
    Ident(Name, Span),

    /// After a lazy const child frame completes: peek the evaluated
    /// value from the operand stack, write it to RuntimeCore::consts,
    /// and continue. If the value is Void, circular reference detected.
    ConstWriteback(Name, Span),

    /// Call where the callee is a simple identifier. Args are on
    /// the operand stack. Dispatches through full call resolution.
    CallNamed {
        callee: Name,
        arg_meta: Vec<ArgMeta>,
        span: Span,
    },

    /// List literal: pop N elements, push list.
    MakeList(usize, Span),
    /// Map literal: pop N*2 (key, value pairs), push map.
    MakeMap(usize, Span),

    /// `entity has GroupName` — pop entity, push bool.
    Has { group: Name, span: Span },
    /// `expr is Type` — pop value, push bool.
    Is {
        target_type: Spanned<TypeExpr>,
        span: Span,
    },

    // ── Phase 3 variants ────────────────────────────────────────
    /// Field-access call: `receiver.method(args)`. Receiver is on operand
    /// stack below the args.
    CallMethod {
        method: Name,
        arg_meta: Vec<ArgMeta>,
        span: Span,
    },

    /// Callable-value call: `callee_value(args)` where callee_value is on
    /// operand stack below args. Used for FnRef calls.
    CallValue { arg_meta: Vec<ArgMeta>, span: Span },

    // ── Phase 4 variants ────────────────────────────────────────
    /// Short-circuit: LHS on stack. Check bool, maybe skip RHS.
    ShortCircuit {
        op: BinOp,
        skip_to: usize,
        span: Span,
    },

    /// Conditional branch: pop condition, jump to then_pc or else_pc.
    Branch {
        then_pc: usize,
        else_pc: usize,
        span: Span,
    },
    /// Unconditional jump.
    Jump(usize),
    /// Push a Block child frame for a branch body. Result → operand stack.
    PushBlock(Vec<Spanned<StmtKind>>, Span),

    /// Construct a struct value: pop N field values, push struct.
    /// Fields are (name, _) pairs; values are on the operand stack in order.
    MakeStruct {
        name: Name,
        field_names: Vec<Name>,
        span: Span,
    },

    // ── Phase 5 variants ────────────────────────────────────────
    /// `if let` pattern test: pop scrutinee value, try to match against
    /// pattern. On match: push a new scope, bind pattern variables, jump
    /// to `then_pc`. On mismatch: jump to `else_pc`.
    IfLetTest {
        pattern: Box<Spanned<PatternKind>>,
        then_pc: usize,
        else_pc: usize,
        span: Span,
    },
    /// Pop the innermost scope pushed by `IfLetTest`.
    PopScope,

    // ── Phase 6 variants ────────────────────────────────────────
    /// Duplicate the top of the operand stack.
    Dup,
    /// No pattern arm matched in a `match` expression — emit runtime error.
    MatchFail(Span),

    // ── Phase 7 variants ────────────────────────────────────────
    /// For loop: pop iterable (collection or range start+end), materialize,
    /// push ForLoop child frame.
    PushForLoop {
        pattern: Box<Spanned<PatternKind>>,
        body: Vec<Spanned<StmtKind>>,
        body_span: Span,
        range: bool,
        inclusive: bool,
        span: Span,
    },
    /// List comprehension: pop iterable, materialize, push ListComp child frame.
    PushListComp {
        pattern: Box<Spanned<PatternKind>>,
        element: Box<Spanned<ExprKind>>,
        filter: Option<Box<Spanned<ExprKind>>>,
        range: bool,
        inclusive: bool,
        span: Span,
    },

    // ── Phase 8 variants ────────────────────────────────────────
    /// Entity construction: pop field + group field values from the operand
    /// stack, build a `Frame::SpawnEntity` child frame and push it.
    /// After the child frame completes the entity ref sits on the operand
    /// stack for any subsequent with-condition calls.
    PushSpawnEntity {
        entity_type: Name,
        /// Base field names (values on operand stack in this order).
        field_names: Vec<Name>,
        /// Each entry is (group_name, [field_names]). Values on the operand
        /// stack follow the base fields, groups in order.
        group_specs: Vec<(Name, Vec<Name>)>,
        span: Span,
    },
}

// ── Compilation ─────────────────────────────────────────────────

/// Try to compile an expression into a work sequence for ExprEval.
///
/// Returns `None` if the expression contains non-trivial sub-expressions
/// that cannot yet be compiled (control flow, struct literals, etc.).
pub(crate) fn compile_expr(
    expr: &Spanned<ExprKind>,
    type_env: &TypeEnv,
    program: &ttrpg_ast::ast::Program,
) -> Option<Vec<ExprWork>> {
    let mut work = Vec::new();
    compile_inner(expr, type_env, program, &mut work)?;
    Some(work)
}

fn compile_inner(
    expr: &Spanned<ExprKind>,
    type_env: &TypeEnv,
    program: &ttrpg_ast::ast::Program,
    work: &mut Vec<ExprWork>,
) -> Option<()> {
    let span = expr.span;
    match &expr.node {
        ExprKind::IntLit(n) => {
            work.push(ExprWork::Literal(Value::Int(*n), span));
        }
        ExprKind::StringLit(s) => {
            work.push(ExprWork::Literal(Value::Str(s.clone()), span));
        }
        ExprKind::BoolLit(b) => {
            work.push(ExprWork::Literal(Value::Bool(*b), span));
        }
        ExprKind::NoneLit => {
            work.push(ExprWork::Literal(Value::Void, span));
        }
        ExprKind::DiceLit {
            count,
            sides,
            filter,
        } => {
            work.push(ExprWork::Literal(
                Value::DiceExpr(DiceExpr::single(*count, *sides, *filter, 0)),
                span,
            ));
        }
        ExprKind::UnitLit { value, suffix } => {
            // Look up the unit type name from the suffix
            let unit_name = type_env.suffix_to_unit.get(suffix.as_str())?.clone();
            // Look up the field name from the unit type declaration
            let field_name = match type_env.types.get(unit_name.as_str())? {
                DeclInfo::Unit(info) => info.fields.first()?.name.clone(),
                _ => return None,
            };
            let mut fields = BTreeMap::new();
            fields.insert(field_name, Value::Int(*value));
            work.push(ExprWork::Literal(
                Value::Struct {
                    name: unit_name,
                    fields,
                },
                span,
            ));
        }
        ExprKind::Paren(inner) => {
            compile_inner(inner, type_env, program, work)?;
        }
        ExprKind::BinOp { op, lhs, rhs } => {
            match op {
                BinOp::And | BinOp::Or => {
                    compile_inner(lhs, type_env, program, work)?;
                    let sc_idx = work.len();
                    work.push(ExprWork::ShortCircuit {
                        op: *op,
                        skip_to: 0,
                        span,
                    }); // placeholder
                    compile_inner(rhs, type_env, program, work)?;
                    // Patch skip_to to point past the RHS
                    let end = work.len();
                    if let ExprWork::ShortCircuit { skip_to, .. } = &mut work[sc_idx] {
                        *skip_to = end;
                    }
                }
                _ => {
                    compile_inner(lhs, type_env, program, work)?;
                    compile_inner(rhs, type_env, program, work)?;
                    work.push(ExprWork::BinOp(*op, span));
                }
            }
        }
        ExprKind::UnaryOp { op, operand } => {
            compile_inner(operand, type_env, program, work)?;
            work.push(ExprWork::UnaryOp(*op, span));
        }
        ExprKind::FieldAccess { object, field } => {
            compile_inner(object, type_env, program, work)?;
            work.push(ExprWork::Field(field.clone(), span));
        }
        ExprKind::Index { object, index } => {
            compile_inner(object, type_env, program, work)?;
            compile_inner(index, type_env, program, work)?;
            work.push(ExprWork::Index(span));
        }

        // ── Phase 2 cases ───────────────────────────────────────
        ExprKind::Ident(name) => {
            work.push(ExprWork::Ident(name.clone(), span));
            // If it's a const, emit ConstWriteback right after
            if program.consts.contains_key(name.as_str()) {
                work.push(ExprWork::ConstWriteback(name.clone(), span));
            }
        }

        ExprKind::Call { callee, args } => {
            match &callee.node {
                ExprKind::Ident(name) => {
                    // Compile each arg value expression
                    let mut meta = Vec::with_capacity(args.len());
                    for arg in args {
                        compile_inner(&arg.value, type_env, program, work)?;
                        meta.push(ArgMeta {
                            name: arg.name.clone(),
                            span: arg.span,
                        });
                    }
                    work.push(ExprWork::CallNamed {
                        callee: name.clone(),
                        arg_meta: meta,
                        span,
                    });
                }
                // ── Phase 3: FieldAccess callee = method or qualified call ──
                ExprKind::FieldAccess { object, field } => {
                    // Compile receiver (pushes receiver value onto operand stack)
                    compile_inner(object, type_env, program, work)?;
                    // Compile each arg
                    let mut meta = Vec::with_capacity(args.len());
                    for arg in args {
                        compile_inner(&arg.value, type_env, program, work)?;
                        meta.push(ArgMeta {
                            name: arg.name.clone(),
                            span: arg.span,
                        });
                    }
                    work.push(ExprWork::CallMethod {
                        method: field.clone(),
                        arg_meta: meta,
                        span,
                    });
                }
                // ── Phase 3: General callee expression (e.g., a FnRef value) ──
                _ => {
                    compile_inner(callee, type_env, program, work)?;
                    let mut meta = Vec::with_capacity(args.len());
                    for arg in args {
                        compile_inner(&arg.value, type_env, program, work)?;
                        meta.push(ArgMeta {
                            name: arg.name.clone(),
                            span: arg.span,
                        });
                    }
                    work.push(ExprWork::CallValue {
                        arg_meta: meta,
                        span,
                    });
                }
            }
        }

        ExprKind::ListLit(elements) => {
            for elem in elements {
                compile_inner(elem, type_env, program, work)?;
            }
            work.push(ExprWork::MakeList(elements.len(), span));
        }

        ExprKind::MapLit(entries) => {
            for (key, val) in entries {
                compile_inner(key, type_env, program, work)?;
                compile_inner(val, type_env, program, work)?;
            }
            work.push(ExprWork::MakeMap(entries.len(), span));
        }

        ExprKind::Has {
            entity,
            group_name,
            alias: _,
        } => {
            compile_inner(entity, type_env, program, work)?;
            work.push(ExprWork::Has {
                group: group_name.clone(),
                span,
            });
        }

        ExprKind::Is {
            expr: inner,
            target_type,
        } => {
            compile_inner(inner, type_env, program, work)?;
            work.push(ExprWork::Is {
                target_type: target_type.clone(),
                span,
            });
        }

        // ── Phase 4 cases ───────────────────────────────────────
        ExprKind::If {
            condition,
            then_block,
            else_branch,
        } => {
            compile_inner(condition, type_env, program, work)?;
            let branch_idx = work.len();
            work.push(ExprWork::Branch {
                then_pc: 0,
                else_pc: 0,
                span,
            }); // placeholder

            // Then branch
            let then_pc = work.len();
            work.push(ExprWork::PushBlock(then_block.node.clone(), span));
            let jump_idx = work.len();
            work.push(ExprWork::Jump(0)); // placeholder

            // Else branch
            let else_pc = work.len();
            match else_branch {
                Some(ElseBranch::Block(block)) => {
                    work.push(ExprWork::PushBlock(block.node.clone(), span));
                }
                Some(ElseBranch::If(if_expr)) => {
                    // Recursively compile the else-if chain
                    compile_inner(if_expr, type_env, program, work)?;
                }
                None => {
                    work.push(ExprWork::Literal(Value::Void, span));
                }
            }
            let end_pc = work.len();

            // Patch
            if let ExprWork::Branch {
                then_pc: tp,
                else_pc: ep,
                ..
            } = &mut work[branch_idx]
            {
                *tp = then_pc;
                *ep = else_pc;
            }
            if let ExprWork::Jump(target) = &mut work[jump_idx] {
                *target = end_pc;
            }
        }

        ExprKind::GuardMatch { arms } => {
            let mut jump_patches = Vec::new();
            for arm in arms {
                match &arm.guard {
                    GuardKind::Wildcard => {
                        work.push(ExprWork::Literal(Value::Bool(true), arm.span));
                    }
                    GuardKind::Expr(expr) => {
                        compile_inner(expr, type_env, program, work)?;
                    }
                }
                let branch_idx = work.len();
                work.push(ExprWork::Branch {
                    then_pc: 0,
                    else_pc: 0,
                    span: arm.span,
                });
                let then_pc = work.len();
                match &arm.body {
                    ArmBody::Block(block) => {
                        work.push(ExprWork::PushBlock(block.node.clone(), arm.span));
                    }
                    ArmBody::Expr(expr) => {
                        compile_inner(expr, type_env, program, work)?;
                    }
                }
                jump_patches.push(work.len());
                work.push(ExprWork::Jump(0)); // placeholder
                let else_pc = work.len();
                if let ExprWork::Branch {
                    then_pc: tp,
                    else_pc: ep,
                    ..
                } = &mut work[branch_idx]
                {
                    *tp = then_pc;
                    *ep = else_pc;
                }
            }
            // Patch all jumps to end
            let end_pc = work.len();
            for idx in jump_patches {
                if let ExprWork::Jump(target) = &mut work[idx] {
                    *target = end_pc;
                }
            }
        }

        ExprKind::IfLet {
            pattern,
            scrutinee,
            then_block,
            else_branch,
        } => {
            // Evaluate scrutinee → value on operand stack
            compile_inner(scrutinee, type_env, program, work)?;

            // IfLetTest: pop scrutinee, pattern match, branch
            let test_idx = work.len();
            work.push(ExprWork::IfLetTest {
                pattern: pattern.clone(),
                then_pc: 0,
                else_pc: 0,
                span,
            }); // placeholder targets

            // Then branch (runs in the scope pushed by IfLetTest)
            let then_pc = work.len();
            work.push(ExprWork::PushBlock(then_block.node.clone(), span));
            work.push(ExprWork::PopScope);
            let jump_idx = work.len();
            work.push(ExprWork::Jump(0)); // placeholder

            // Else branch
            let else_pc = work.len();
            match else_branch {
                Some(ElseBranch::Block(block)) => {
                    work.push(ExprWork::PushBlock(block.node.clone(), span));
                }
                Some(ElseBranch::If(if_expr)) => {
                    compile_inner(if_expr, type_env, program, work)?;
                }
                None => {
                    work.push(ExprWork::Literal(Value::Void, span));
                }
            }
            let end_pc = work.len();

            // Patch jump targets
            if let ExprWork::IfLetTest {
                then_pc: tp,
                else_pc: ep,
                ..
            } = &mut work[test_idx]
            {
                *tp = then_pc;
                *ep = else_pc;
            }
            if let ExprWork::Jump(target) = &mut work[jump_idx] {
                *target = end_pc;
            }
        }

        ExprKind::StructLit {
            name,
            fields,
            groups,
            base,
            with_conditions,
        } => {
            let is_entity = matches!(type_env.types.get(name.as_str()), Some(DeclInfo::Entity(_)));

            if is_entity {
                // ..base spread not yet supported for entity construction
                if base.is_some() {
                    return None;
                }
                compile_entity_struct_lit(
                    name,
                    fields,
                    groups,
                    with_conditions,
                    span,
                    type_env,
                    program,
                    work,
                )?;
            } else {
                // Non-entity: groups/base/with_conditions → fall back
                if !groups.is_empty() || base.is_some() || !with_conditions.is_empty() {
                    return None;
                }
                // Plain struct: compile each field
                let mut field_names = Vec::with_capacity(fields.len());
                for field in fields {
                    compile_inner(&field.value, type_env, program, work)?;
                    field_names.push(field.name.clone());
                }
                work.push(ExprWork::MakeStruct {
                    name: name.clone(),
                    field_names,
                    span,
                });
            }
        }

        // ── Phase 7: For loop ──────────────────────────────────
        ExprKind::For {
            pattern,
            iterable,
            body,
        } => {
            let (range, inclusive) = match iterable {
                ForIterable::Collection(expr) => {
                    compile_inner(expr, type_env, program, work)?;
                    (false, false)
                }
                ForIterable::Range {
                    start,
                    end,
                    inclusive,
                } => {
                    compile_inner(start, type_env, program, work)?;
                    compile_inner(end, type_env, program, work)?;
                    (true, *inclusive)
                }
            };
            work.push(ExprWork::PushForLoop {
                pattern: pattern.clone(),
                body: body.node.clone(),
                body_span: body.span,
                range,
                inclusive,
                span,
            });
        }

        // ── Phase 7: List comprehension ─────────────────────────
        ExprKind::ListComprehension {
            element,
            pattern,
            iterable,
            filter,
        } => {
            let (range, inclusive) = match iterable {
                ForIterable::Collection(expr) => {
                    compile_inner(expr, type_env, program, work)?;
                    (false, false)
                }
                ForIterable::Range {
                    start,
                    end,
                    inclusive,
                } => {
                    compile_inner(start, type_env, program, work)?;
                    compile_inner(end, type_env, program, work)?;
                    (true, *inclusive)
                }
            };
            work.push(ExprWork::PushListComp {
                pattern: pattern.clone(),
                element: element.clone(),
                filter: filter.clone(),
                range,
                inclusive,
                span,
            });
        }

        // ── Phase 6: PatternMatch ──────────────────────────────
        ExprKind::PatternMatch { scrutinee, arms } => {
            // Compile scrutinee — its value stays on the stack as long as
            // we keep testing arms, removed by Pop once we commit to a body.
            compile_inner(scrutinee, type_env, program, work)?;

            let mut jump_patches = Vec::new(); // Jump-to-end after each arm body

            for arm in arms {
                // Dup scrutinee for this arm's pattern test
                work.push(ExprWork::Dup);
                let test_idx = work.len();
                work.push(ExprWork::IfLetTest {
                    pattern: Box::new(arm.pattern.clone()),
                    then_pc: 0,
                    else_pc: 0,
                    span: arm.span,
                });

                // ── Match succeeded: remove original scrutinee, run body ──
                let then_pc = work.len();
                work.push(ExprWork::Pop); // pop original scrutinee
                match &arm.body {
                    ArmBody::Block(block) => {
                        work.push(ExprWork::PushBlock(block.node.clone(), arm.span));
                    }
                    ArmBody::Expr(expr) => {
                        compile_inner(expr, type_env, program, work)?;
                    }
                }
                work.push(ExprWork::PopScope);
                jump_patches.push(work.len());
                work.push(ExprWork::Jump(0)); // placeholder: jump to end

                // Patch IfLetTest targets
                let else_pc = work.len();
                if let ExprWork::IfLetTest {
                    then_pc: tp,
                    else_pc: ep,
                    ..
                } = &mut work[test_idx]
                {
                    *tp = then_pc;
                    *ep = else_pc;
                }
            }

            // No arm matched: pop scrutinee and error
            work.push(ExprWork::Pop);
            work.push(ExprWork::MatchFail(span));

            // Patch all arm-end jumps to skip past the error
            let end_pc = work.len();
            for idx in jump_patches {
                if let ExprWork::Jump(target) = &mut work[idx] {
                    *target = end_pc;
                }
            }
        }

        // Safety fallback for future ExprKind variants.
        #[allow(unreachable_patterns)]
        _ => return None,
    }
    Some(())
}

// ── Entity StructLit compilation ─────────────────────────────────

/// Compile an entity construction expression into ExprWork instructions.
///
/// Layout: evaluate base fields (explicit + defaults), then group fields
/// (explicit + defaults per group), emit PushSpawnEntity, then with_condition
/// calls.
fn compile_entity_struct_lit(
    entity_name: &Name,
    fields: &[ttrpg_ast::ast::StructFieldInit],
    groups: &[ttrpg_ast::ast::GroupInit],
    with_conditions: &[Spanned<ExprKind>],
    span: Span,
    type_env: &TypeEnv,
    program: &ttrpg_ast::ast::Program,
    work: &mut Vec<ExprWork>,
) -> Option<()> {
    let entity_decl = find_entity_decl(program, entity_name.as_str())?;

    // ── Base fields: explicit values + defaults for omitted fields ──
    let explicit_names: std::collections::HashSet<&Name> = fields.iter().map(|f| &f.name).collect();
    let mut field_names: Vec<Name> = Vec::new();

    // Compile explicit field expressions
    for field in fields {
        compile_inner(&field.value, type_env, program, work)?;
        field_names.push(field.name.clone());
    }

    // Compile default expressions for omitted base fields
    for fd in &entity_decl.fields {
        if explicit_names.contains(&fd.name) {
            continue;
        }
        if let Some(default_expr) = &fd.default {
            compile_inner(default_expr, type_env, program, work)?;
            field_names.push(fd.name.clone());
        }
    }

    // ── Groups: inline groups + required groups with defaults ──
    let provided_groups: std::collections::HashSet<&Name> =
        groups.iter().map(|g| &g.name).collect();

    let mut group_specs: Vec<(Name, Vec<Name>)> = Vec::new();

    // Inline groups from the construction expression
    for group in groups {
        let explicit_group_names: std::collections::HashSet<&Name> =
            group.fields.iter().map(|f| &f.name).collect();
        let mut gfield_names = Vec::new();

        // Compile explicit group field expressions
        for f in &group.fields {
            compile_inner(&f.value, type_env, program, work)?;
            gfield_names.push(f.name.clone());
        }

        // Compile defaults for omitted group fields
        if let Some(group_fields) = find_group_fields(program, entity_decl, &group.name) {
            for fd in group_fields {
                if explicit_group_names.contains(&fd.name) {
                    continue;
                }
                if let Some(default_expr) = &fd.default {
                    compile_inner(default_expr, type_env, program, work)?;
                    gfield_names.push(fd.name.clone());
                }
            }
        }

        group_specs.push((group.name.clone(), gfield_names));
    }

    // Auto-materialize required (include) groups not already provided
    for og in &entity_decl.optional_groups {
        if !og.is_required || provided_groups.contains(&og.name) {
            continue;
        }
        let mut gfield_names = Vec::new();
        let group_fields = if og.is_external_ref {
            find_external_group_fields(program, &og.name)
        } else {
            Some(og.fields.as_slice())
        };
        if let Some(gfields) = group_fields {
            for fd in gfields {
                if let Some(default_expr) = &fd.default {
                    compile_inner(default_expr, type_env, program, work)?;
                    gfield_names.push(fd.name.clone());
                }
            }
        }
        group_specs.push((og.name.clone(), gfield_names));
    }

    // ── Emit PushSpawnEntity ──
    work.push(ExprWork::PushSpawnEntity {
        entity_type: entity_name.clone(),
        field_names,
        group_specs,
        span,
    });

    // ── With-conditions: Dup entity, eval cond, push Indefinite, call apply_condition, Pop ──
    for cond_expr in with_conditions {
        work.push(ExprWork::Dup);
        compile_inner(cond_expr, type_env, program, work)?;
        work.push(ExprWork::Literal(
            crate::value::duration_variant("Indefinite"),
            cond_expr.span,
        ));
        work.push(ExprWork::CallNamed {
            callee: Name::from("apply_condition"),
            arg_meta: vec![
                ArgMeta {
                    name: None,
                    span: cond_expr.span,
                },
                ArgMeta {
                    name: None,
                    span: cond_expr.span,
                },
                ArgMeta {
                    name: None,
                    span: cond_expr.span,
                },
            ],
            span: cond_expr.span,
        });
        work.push(ExprWork::Pop); // discard apply_condition return value
    }

    Some(())
}

/// Find an entity declaration by name in the program AST.
fn find_entity_decl<'a>(
    program: &'a ttrpg_ast::ast::Program,
    name: &str,
) -> Option<&'a ttrpg_ast::ast::EntityDecl> {
    use ttrpg_ast::ast::{DeclKind, TopLevel};
    for item in &program.items {
        if let TopLevel::System(system) = &item.node {
            for decl in &system.decls {
                if let DeclKind::Entity(e) = &decl.node
                    && e.name == name
                {
                    return Some(e);
                }
            }
        }
    }
    None
}

/// Find group field definitions for an entity's optional group.
/// Handles both inline and external group references.
fn find_group_fields<'a>(
    program: &'a ttrpg_ast::ast::Program,
    entity_decl: &'a ttrpg_ast::ast::EntityDecl,
    group_name: &Name,
) -> Option<&'a [ttrpg_ast::ast::FieldDef]> {
    for group in &entity_decl.optional_groups {
        if &group.name == group_name {
            return if group.is_external_ref {
                find_external_group_fields(program, group_name)
            } else {
                Some(group.fields.as_slice())
            };
        }
    }
    None
}

/// Find field definitions for a standalone group declaration.
fn find_external_group_fields<'a>(
    program: &'a ttrpg_ast::ast::Program,
    group_name: &Name,
) -> Option<&'a [ttrpg_ast::ast::FieldDef]> {
    use ttrpg_ast::ast::{DeclKind, TopLevel};
    for item in &program.items {
        if let TopLevel::System(system) = &item.node {
            for decl in &system.decls {
                if let DeclKind::Group(g) = &decl.node
                    && g.name == *group_name
                {
                    return Some(g.fields.as_slice());
                }
            }
        }
    }
    None
}

// ── Advance loop ────────────────────────────────────────────────

/// Execute ExprEval micro-instructions in a tight loop.
///
/// This is a free function (not a method on Frame) so it can be called
/// from `advance_action` with the ExprEval fields destructured.
pub(crate) fn advance_expr_eval(
    work: &[ExprWork],
    operands: &mut Vec<Value>,
    pc: &mut usize,
    child_result: &mut Option<Result<Value, RuntimeError>>,
    scope_depth: &mut usize,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    sp: &dyn StateProvider,
    eh: &mut dyn EffectHandler,
) -> Advance {
    // Handle child frame result (const eval, function call, etc.).
    if let Some(result) = child_result.take() {
        match result {
            Ok(val) => {
                operands.push(val);
                return Advance::Continue;
            }
            Err(e) => {
                // Clean up any scopes pushed by IfLetTest before propagating.
                for _ in 0..*scope_depth {
                    env.pop_scope();
                }
                *scope_depth = 0;
                return Advance::Error(e);
            }
        }
    }

    loop {
        if *pc >= work.len() {
            return Advance::Pop(operands.pop().unwrap_or(Value::Void));
        }
        match &work[*pc] {
            ExprWork::Literal(val, _) => {
                operands.push(val.clone());
                *pc += 1;
            }
            ExprWork::BinOp(op, span) => {
                let rhs = operands.pop().unwrap();
                let lhs = operands.pop().unwrap();
                match apply_binop_values(*op, lhs, rhs, *span, &core.type_env, sp) {
                    Ok(val) => {
                        operands.push(val);
                        *pc += 1;
                    }
                    Err(e) => return Advance::Error(e),
                }
            }
            ExprWork::UnaryOp(op, span) => {
                let val = operands.pop().unwrap();
                match apply_unary_values(*op, &val, *span, &core.type_env) {
                    Ok(result) => {
                        operands.push(result);
                        *pc += 1;
                    }
                    Err(e) => return Advance::Error(e),
                }
            }
            ExprWork::Field(field, span) => {
                let object = operands.pop().unwrap();
                match field_access_on_value(&object, field, *span, &core.type_env, sp) {
                    Ok(val) => {
                        operands.push(val);
                        *pc += 1;
                    }
                    Err(e) => return Advance::Error(e),
                }
            }
            ExprWork::Index(span) => {
                let index = operands.pop().unwrap();
                let object = operands.pop().unwrap();
                match index_on_value(&object, &index, *span, sp) {
                    Ok(val) => {
                        operands.push(val);
                        *pc += 1;
                    }
                    Err(e) => return Advance::Error(e),
                }
            }
            ExprWork::Pop => {
                operands.pop();
                *pc += 1;
            }

            // ── Phase 2: Identifier resolution ──────────────────
            ExprWork::Ident(name, span) => {
                return advance_ident(name, *span, work, operands, pc, core, env, sp, eh);
            }

            ExprWork::ConstWriteback(name, span) => {
                // Child frame completed with const value on operand stack
                let val = operands.last().cloned().unwrap_or(Value::Void);
                if matches!(val, Value::Void) {
                    return Advance::Error(RuntimeError::with_span(
                        format!("circular const reference: '{name}'"),
                        *span,
                    ));
                }
                core.consts.borrow_mut().insert(name.clone(), val);
                *pc += 1;
                // Value stays on operand stack — continue tight loop
            }

            // ── Phase 2: Call dispatch ───────────────────────────
            ExprWork::CallNamed {
                callee,
                arg_meta,
                span,
            } => {
                return advance_call_named(
                    callee, arg_meta, *span, operands, pc, core, env, sp, eh,
                );
            }

            // ── Phase 2: Collection constructors ────────────────
            ExprWork::MakeList(count, _) => {
                let start = operands.len().saturating_sub(*count);
                let elements = operands.split_off(start);
                operands.push(Value::List(elements));
                *pc += 1;
            }
            ExprWork::MakeMap(count, _) => {
                let start = operands.len().saturating_sub(*count * 2);
                let pairs = operands.split_off(start);
                let mut map = BTreeMap::new();
                for chunk in pairs.chunks_exact(2) {
                    map.insert(chunk[0].clone(), chunk[1].clone());
                }
                operands.push(Value::Map(map));
                *pc += 1;
            }

            // ── Phase 2: Has / Is ───────────────────────────────
            ExprWork::Has { group, span } => {
                let entity = operands.pop().unwrap();
                match &entity {
                    Value::Entity(eref) => {
                        let has = sp.read_field(eref, group).is_some();
                        operands.push(Value::Bool(has));
                        *pc += 1;
                    }
                    _ => {
                        return Advance::Error(RuntimeError::with_span(
                            "has: expected entity value",
                            *span,
                        ));
                    }
                }
            }
            ExprWork::Is { target_type, span } => {
                let val = operands.pop().unwrap();
                let result = eval_is_check(&val, target_type, *span, core, sp);
                operands.push(Value::Bool(result));
                *pc += 1;
            }

            // ── Phase 3: Method call ───────────────────────────
            ExprWork::CallMethod {
                method,
                arg_meta,
                span,
            } => {
                let start = operands.len().saturating_sub(arg_meta.len());
                let arg_values = operands.split_off(start);
                let receiver = operands.pop().unwrap();
                *pc += 1;

                match resolve_call_method(
                    receiver,
                    method,
                    arg_meta,
                    &arg_values,
                    *span,
                    core,
                    env,
                    sp,
                    eh,
                ) {
                    Ok(CallResult::Value(val)) => {
                        operands.push(val);
                        // stay in loop
                    }
                    Ok(CallResult::PushChild(frame)) => {
                        return Advance::Push(frame);
                    }
                    Err(e) => return Advance::Error(e),
                }
            }

            // ── Phase 3: Callable-value call ───────────────────
            ExprWork::CallValue { arg_meta, span } => {
                let start = operands.len().saturating_sub(arg_meta.len());
                let arg_values = operands.split_off(start);
                let callee_val = operands.pop().unwrap();
                *pc += 1;

                match callee_val {
                    Value::FnRef(fn_name) => {
                        match dispatch_fn_ref_step(
                            &fn_name,
                            arg_meta,
                            &arg_values,
                            *span,
                            core,
                            env,
                            sp,
                            eh,
                        ) {
                            Ok(CallResult::Value(val)) => {
                                operands.push(val);
                            }
                            Ok(CallResult::PushChild(frame)) => {
                                return Advance::Push(frame);
                            }
                            Err(e) => return Advance::Error(e),
                        }
                    }
                    other => {
                        return Advance::Error(RuntimeError::with_span(
                            format!(
                                "expression of type {} is not callable",
                                crate::value::value_type_display(&other)
                            ),
                            *span,
                        ));
                    }
                }
            }

            // ── Phase 4: Short-circuit And/Or ─────────────────
            ExprWork::ShortCircuit { op, skip_to, span } => {
                let val = operands.last().unwrap();
                match (op, val) {
                    (BinOp::And, Value::Bool(false)) => {
                        // LHS is false, short-circuit: skip RHS, keep false on stack
                        *pc = *skip_to;
                    }
                    (BinOp::And, Value::Bool(true)) => {
                        // LHS is true, pop it, evaluate RHS
                        operands.pop();
                        *pc += 1;
                    }
                    (BinOp::Or, Value::Bool(true)) => {
                        // LHS is true, short-circuit: skip RHS, keep true on stack
                        *pc = *skip_to;
                    }
                    (BinOp::Or, Value::Bool(false)) => {
                        // LHS is false, pop it, evaluate RHS
                        operands.pop();
                        *pc += 1;
                    }
                    _ => {
                        let op_str = if *op == BinOp::And { "&&" } else { "||" };
                        return Advance::Error(RuntimeError::with_span(
                            format!("{op_str} requires Bool operands"),
                            *span,
                        ));
                    }
                }
            }

            // ── Phase 4: If / GuardMatch control flow ─────────
            ExprWork::Branch {
                then_pc,
                else_pc,
                span,
            } => {
                let cond = operands.pop().unwrap();
                match cond {
                    Value::Bool(true) => *pc = *then_pc,
                    Value::Bool(false) => *pc = *else_pc,
                    _ => {
                        return Advance::Error(RuntimeError::with_span(
                            "condition must be a boolean",
                            *span,
                        ));
                    }
                }
            }
            ExprWork::Jump(target) => {
                *pc = *target;
            }
            ExprWork::PushBlock(stmts, _span) => {
                *pc += 1;
                return Advance::Push(Frame::Block {
                    stmts: stmts.clone(),
                    index: 0,
                    result: Value::Void,
                    expr_cache: Vec::new(),
                    awaiting_fn: None,
                    awaiting_error: None,
                });
            }

            // ── Phase 4: Struct literal ───────────────────────
            ExprWork::MakeStruct {
                name,
                field_names,
                span: _,
            } => {
                let values = operands.split_off(operands.len() - field_names.len());
                let mut fields = BTreeMap::new();
                for (fname, val) in field_names.iter().zip(values) {
                    fields.insert(fname.clone(), val);
                }
                operands.push(Value::Struct {
                    name: name.clone(),
                    fields,
                });
                *pc += 1;
            }

            // ── Phase 5: IfLet pattern matching ─────────────
            ExprWork::IfLetTest {
                pattern,
                then_pc,
                else_pc,
                span: _,
            } => {
                let scrutinee = operands.pop().unwrap();
                let mut bindings = FxHashMap::default();
                if match_pattern(&core.type_env, pattern, &scrutinee, &mut bindings) {
                    env.push_scope();
                    *scope_depth += 1;
                    for (name, val) in bindings {
                        env.bind(name, val);
                    }
                    *pc = *then_pc;
                } else {
                    *pc = *else_pc;
                }
            }
            ExprWork::PopScope => {
                env.pop_scope();
                *scope_depth -= 1;
                *pc += 1;
            }

            // ── Phase 6: PatternMatch support ───────────────
            ExprWork::Dup => {
                let val = operands.last().unwrap().clone();
                operands.push(val);
                *pc += 1;
            }
            ExprWork::MatchFail(span) => {
                for _ in 0..*scope_depth {
                    env.pop_scope();
                }
                *scope_depth = 0;
                return Advance::Error(RuntimeError::with_span(
                    "no pattern matched in match expression",
                    *span,
                ));
            }

            // ── Phase 7: For loop / List comprehension ──────
            ExprWork::PushForLoop {
                pattern,
                body,
                body_span,
                range,
                inclusive,
                span,
            } => {
                let items = match materialize_iterable(operands, *range, *inclusive, *span) {
                    Ok(v) => v,
                    Err(e) => return Advance::Error(e),
                };
                *pc += 1;
                return Advance::Push(Frame::ForLoop {
                    items,
                    index: 0,
                    pattern: pattern.clone(),
                    body: body.clone(),
                    body_span: *body_span,
                    child_result: None,
                });
            }
            ExprWork::PushListComp {
                pattern,
                element,
                filter,
                range,
                inclusive,
                span,
            } => {
                let items = match materialize_iterable(operands, *range, *inclusive, *span) {
                    Ok(v) => v,
                    Err(e) => return Advance::Error(e),
                };
                *pc += 1;
                return Advance::Push(Frame::ListComp {
                    items,
                    index: 0,
                    pattern: pattern.clone(),
                    element: element.clone(),
                    filter: filter.clone(),
                    collected: Vec::new(),
                    phase: crate::execution::ListCompPhase::TryMatch,
                    span: *span,
                    child_result: None,
                });
            }

            // ── Phase 8: Entity construction ─────────────────────
            ExprWork::PushSpawnEntity {
                entity_type,
                field_names,
                group_specs,
                span,
            } => {
                // Pop base field values from operand stack (reverse order)
                let total_group_fields: usize =
                    group_specs.iter().map(|(_, names)| names.len()).sum();
                let base_count = field_names.len();
                let total = base_count + total_group_fields;
                let start = operands.len().saturating_sub(total);
                let all_values = operands.split_off(start);
                let mut vals = all_values.into_iter();

                // Build base fields
                let base_fields: Vec<(Name, Value)> = field_names
                    .iter()
                    .map(|name| (name.clone(), vals.next().unwrap()))
                    .collect();

                // Build groups
                let groups: Vec<crate::execution::GroupInit> = group_specs
                    .iter()
                    .map(|(group_name, gfield_names)| {
                        let mut fields = BTreeMap::new();
                        for fname in gfield_names {
                            fields.insert(fname.clone(), vals.next().unwrap());
                        }
                        crate::execution::GroupInit {
                            group_name: group_name.clone(),
                            fields,
                        }
                    })
                    .collect();

                *pc += 1;
                return Advance::Push(Frame::SpawnEntity {
                    entity_type: entity_type.clone(),
                    base_fields,
                    groups,
                    phase: crate::execution::SpawnPhase::Defaults,
                    pending: None,
                    entity_ref: None,
                    span: *span,
                });
            }
        }
    }
}

/// Pop iterable value(s) from the operand stack and materialize into Vec<Value>.
fn materialize_iterable(
    operands: &mut Vec<Value>,
    range: bool,
    inclusive: bool,
    span: Span,
) -> Result<Vec<Value>, RuntimeError> {
    if range {
        let end_val = operands.pop().unwrap();
        let start_val = operands.pop().unwrap();
        let s = match start_val {
            Value::Int(n) => n,
            other => {
                return Err(RuntimeError::with_span(
                    format!(
                        "range start must be int, got {}",
                        crate::value::value_type_display(&other)
                    ),
                    span,
                ));
            }
        };
        let e = match end_val {
            Value::Int(n) => n,
            other => {
                return Err(RuntimeError::with_span(
                    format!(
                        "range end must be int, got {}",
                        crate::value::value_type_display(&other)
                    ),
                    span,
                ));
            }
        };
        crate::eval::collect_range(s, e, inclusive, span)
    } else {
        let collection = operands.pop().unwrap();
        match collection {
            Value::List(items) => Ok(items),
            Value::Set(items) => Ok(items.into_iter().collect()),
            other => Err(RuntimeError::with_span(
                format!(
                    "expected list or set, got {}",
                    crate::value::value_type_display(&other)
                ),
                span,
            )),
        }
    }
}

// ── Ident resolution ────────────────────────────────────────────

/// Helper to skip ConstWriteback if it's the next instruction.
fn skip_const_writeback(work: &[ExprWork], pc: &mut usize) {
    if matches!(work.get(*pc), Some(ExprWork::ConstWriteback(..))) {
        *pc += 1;
    }
}

fn advance_ident(
    name: &Name,
    span: Span,
    work: &[ExprWork],
    operands: &mut Vec<Value>,
    pc: &mut usize,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    sp: &dyn StateProvider,
    eh: &mut dyn EffectHandler,
) -> Advance {
    // 1. Check local scopes
    if let Some(val) = env.lookup(name) {
        operands.push(val.clone());
        *pc += 1;
        skip_const_writeback(work, pc);
        return Advance::Continue;
    }

    // 2. Check cached const
    if let Some(val) = core.consts.borrow().get(name).cloned() {
        if val == Value::Void {
            return Advance::Error(RuntimeError::new(format!(
                "circular const reference: '{name}'"
            )));
        }
        operands.push(val);
        *pc += 1;
        skip_const_writeback(work, pc);
        return Advance::Continue;
    }

    // 3. Uncached const — need child frame to evaluate
    if let Some(const_decl) = core.program.consts.get(name.as_str()) {
        core.consts
            .borrow_mut()
            .insert(Name::from(name.as_str()), Value::Void);
        *pc += 1; // advance to ConstWriteback
        // Compile the const expression and push child ExprEval
        if let Some(child_work) = compile_expr(&const_decl.value, &core.type_env, &core.program) {
            return Advance::Push(Frame::ExprEval {
                work: child_work,
                operands: Vec::new(),
                pc: 0,
                child_result: None,
                scope_depth: 0,
            });
        }
        // Fallback removed (Phase 7) — compile_expr should handle all const expressions.
        panic!(
            "compile_expr failed for const at {span:?} — ResumableBridge fallback removed (Phase 7)",
        );
    }

    // 4. Bare enum variant (fieldless)
    let resolved_variant = core
        .type_env
        .resolved_variants
        .get(&span)
        .cloned()
        .or_else(|| core.type_env.unique_variant_owner(name).cloned());
    if let Some(enum_name) = resolved_variant
        && let Some(DeclInfo::Enum(enum_info)) = core.type_env.types.get(enum_name.as_str())
        && let Some(variant) = enum_info.variants.iter().find(|v| v.name == *name)
        && variant.fields.is_empty()
    {
        operands.push(Value::EnumVariant {
            enum_name: enum_name.clone(),
            variant: name.clone(),
            fields: BTreeMap::new(),
        });
        *pc += 1;
        skip_const_writeback(work, pc);
        return Advance::Continue;
    }

    // 5. Bare condition name (materialize with defaults)
    if let Some(cond_decl) = core.program.conditions.get(name.as_str()) {
        let cond_decl = cond_decl.clone();
        let mut args = BTreeMap::new();
        // Evaluate default expressions for all params
        for param in &cond_decl.params {
            if let Some(ref default_expr) = param.default {
                match eval_expr_step(core, env, sp, eh, default_expr) {
                    Ok(val) => {
                        args.insert(param.name.clone(), val);
                    }
                    Err(e) => return Advance::Error(e),
                }
            }
        }
        operands.push(Value::Condition {
            name: name.clone(),
            args,
        });
        *pc += 1;
        skip_const_writeback(work, pc);
        return Advance::Continue;
    }

    // 6. Function reference
    if core.type_env.resolved_fn_refs.contains_key(&span) {
        operands.push(Value::FnRef(name.clone()));
        *pc += 1;
        skip_const_writeback(work, pc);
        return Advance::Continue;
    }
    if let Some(fn_info) = core.type_env.lookup_fn(name)
        && fn_info.kind == FnKind::Function
        && fn_info.params.iter().all(|p| p.with_groups.is_empty())
    {
        operands.push(Value::FnRef(name.clone()));
        *pc += 1;
        skip_const_writeback(work, pc);
        return Advance::Continue;
    }

    // 7. Enum namespace
    if let Some(DeclInfo::Enum(_)) = core.type_env.types.get(name.as_str()) {
        operands.push(Value::EnumNamespace(name.clone()));
        *pc += 1;
        skip_const_writeback(work, pc);
        return Advance::Continue;
    }

    // 8. Module alias
    if core
        .type_env
        .system_aliases
        .values()
        .any(|aliases| aliases.contains_key(name.as_str()))
    {
        operands.push(Value::ModuleAlias(name.clone()));
        *pc += 1;
        skip_const_writeback(work, pc);
        return Advance::Continue;
    }

    // 9. turn keyword
    if name == "turn" {
        let actor = match env.turn_actor {
            Some(a) => a,
            None => {
                return Advance::Error(RuntimeError::with_span(
                    "cannot access `turn` outside of turn context",
                    span,
                ));
            }
        };
        let budget = match sp.read_turn_budget(&actor) {
            Some(b) => b,
            None => {
                return Advance::Error(RuntimeError::with_span(
                    "no turn budget provisioned for actor",
                    span,
                ));
            }
        };
        operands.push(Value::Struct {
            name: Name::from("TurnBudget"),
            fields: budget,
        });
        *pc += 1;
        skip_const_writeback(work, pc);
        return Advance::Continue;
    }

    Advance::Error(RuntimeError::with_span(
        format!("undefined variable '{name}'"),
        span,
    ))
}

// ── Call dispatch ────────────────────────────────────────────────

/// Result of a call resolution: either an immediate value or a child frame to push.
#[allow(clippy::large_enum_variant)]
enum CallResult {
    Value(Value),
    PushChild(Frame),
}

fn advance_call_named(
    callee: &Name,
    arg_meta: &[ArgMeta],
    span: Span,
    operands: &mut Vec<Value>,
    pc: &mut usize,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    sp: &dyn StateProvider,
    eh: &mut dyn EffectHandler,
) -> Advance {
    // Pop arg values from operand stack
    let start = operands.len().saturating_sub(arg_meta.len());
    let arg_values = operands.split_off(start);

    match resolve_call_named(callee, arg_meta, &arg_values, span, core, env, sp, eh) {
        Ok(CallResult::Value(val)) => {
            operands.push(val);
            *pc += 1;
            Advance::Continue
        }
        Ok(CallResult::PushChild(frame)) => {
            *pc += 1;
            Advance::Push(frame)
        }
        Err(e) => Advance::Error(e),
    }
}

fn resolve_call_named(
    callee: &Name,
    arg_meta: &[ArgMeta],
    arg_values: &[Value],
    span: Span,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    sp: &dyn StateProvider,
    eh: &mut dyn EffectHandler,
) -> Result<CallResult, RuntimeError> {
    // 0. Check if callee is a local binding holding a fn ref
    if let Some(Value::FnRef(fn_name)) = env.lookup(callee) {
        let fn_name = fn_name.clone();
        return dispatch_fn_ref_step(&fn_name, arg_meta, arg_values, span, core, env, sp, eh);
    }

    // 1. Condition constructor
    if let Some(cond_decl) = core.program.conditions.get(callee.as_str()) {
        let cond_decl = cond_decl.clone();
        let param_infos = core
            .type_env
            .conditions
            .get(callee.as_str())
            .map(|ci| ci.params.clone())
            .unwrap_or_default();
        let bound = bind_args_from_values(
            &param_infos,
            arg_meta,
            arg_values,
            Some(&cond_decl.params),
            core,
            env,
            sp,
            eh,
            span,
        )?;
        let cond_args: BTreeMap<Name, Value> = bound.into_iter().collect();
        return Ok(CallResult::Value(Value::Condition {
            name: callee.clone(),
            args: cond_args,
        }));
    }

    // 2. Ordinal builtins
    if callee == "ordinal" {
        return eval_ordinal_step(arg_values, span, core).map(CallResult::Value);
    }
    if callee == "from_ordinal" {
        return eval_from_ordinal_step(arg_values, span, core).map(CallResult::Value);
    }
    if callee == "try_from_ordinal" {
        return eval_try_from_ordinal_step(arg_values, span, core).map(CallResult::Value);
    }

    // 3. Collection builtins
    match callee.as_str() {
        "len" => return eval_len_values(arg_values, span).map(CallResult::Value),
        "keys" => return eval_keys_values(arg_values, span).map(CallResult::Value),
        "values" => return eval_values_values(arg_values, span).map(CallResult::Value),
        "first" => return eval_first_values(arg_values, span).map(CallResult::Value),
        "last" => return eval_last_values(arg_values, span).map(CallResult::Value),
        "append" => return eval_append_values(arg_values, span).map(CallResult::Value),
        "concat" => return eval_concat_values(arg_values, span).map(CallResult::Value),
        "reverse" => return eval_reverse_values(arg_values, span).map(CallResult::Value),
        "sum" => return eval_sum_values(arg_values, span).map(CallResult::Value),
        "any" => return eval_any_values(arg_values, span).map(CallResult::Value),
        "all" => return eval_all_values(arg_values, span).map(CallResult::Value),
        "sort" => return eval_sort_values(arg_values, span).map(CallResult::Value),
        "take" => return eval_take_values(arg_values, span).map(CallResult::Value),
        "some" => return eval_some_values(arg_values, span).map(CallResult::Value),
        "max" => return eval_max_values(arg_values, span).map(CallResult::Value),
        "min" => return eval_min_values(arg_values, span).map(CallResult::Value),
        "to_any" => {
            if arg_values.len() != 1 {
                return Err(RuntimeError::with_span(
                    format!("to_any: expected 1 argument, got {}", arg_values.len()),
                    span,
                ));
            }
            return Ok(CallResult::Value(arg_values[0].clone()));
        }
        "conditions" if arg_values.len() == 2 => {
            return call_builtin_step("conditions", arg_values, span, core, sp)
                .map(CallResult::Value);
        }
        "has_condition" => {
            return call_builtin_step("has_condition", arg_values, span, core, sp)
                .map(CallResult::Value);
        }
        _ => {}
    }

    // 4. Enum variant constructor (via resolution table or unique owner)
    let resolved = core
        .type_env
        .resolved_variants
        .get(&span)
        .cloned()
        .or_else(|| core.type_env.unique_variant_owner(callee).cloned());
    if let Some(enum_name) = resolved {
        return construct_enum_variant_step(
            &enum_name, callee, arg_meta, arg_values, span, core, env, sp, eh,
        )
        .map(CallResult::Value);
    }

    // 5. Function (user-defined or builtin)
    if let Some(fn_info) = core.type_env.lookup_fn(callee) {
        let fn_info = fn_info.clone();
        // Record coverage entry for user-defined functions/derives/mechanics.
        if let Some(ref cov) = core.coverage {
            cov.borrow_mut().hit_functions.insert(callee.to_string());
        }
        return dispatch_fn_step(&fn_info, arg_meta, arg_values, span, core, env, sp, eh);
    }

    Err(RuntimeError::with_span(
        format!("undefined function '{callee}'"),
        span,
    ))
}

/// Dispatch a call through a function reference (FnRef).
fn dispatch_fn_ref_step(
    fn_name: &str,
    arg_meta: &[ArgMeta],
    arg_values: &[Value],
    span: Span,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    sp: &dyn StateProvider,
    eh: &mut dyn EffectHandler,
) -> Result<CallResult, RuntimeError> {
    if let Some(fn_info) = core.type_env.lookup_fn(fn_name) {
        let fn_info = fn_info.clone();
        if fn_info.kind == FnKind::Function {
            return dispatch_function_step(
                &fn_info.name,
                arg_meta,
                arg_values,
                span,
                core,
                env,
                sp,
                eh,
            );
        }
        return Err(RuntimeError::with_span(
            format!(
                "cannot call through reference to {} `{fn_name}`",
                match fn_info.kind {
                    FnKind::Derive => "derive",
                    FnKind::Mechanic => "mechanic",
                    FnKind::Action => "action",
                    FnKind::Table => "table",
                    FnKind::Builtin => "builtin",
                    _ => "non-function",
                }
            ),
            span,
        ));
    }
    Err(RuntimeError::with_span(
        format!("function reference points to undefined function '{fn_name}'"),
        span,
    ))
}

// ── Method call dispatch (Phase 3) ──────────────────────────────

fn resolve_call_method(
    receiver: Value,
    method: &Name,
    arg_meta: &[ArgMeta],
    arg_values: &[Value],
    span: Span,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    sp: &dyn StateProvider,
    eh: &mut dyn EffectHandler,
) -> Result<CallResult, RuntimeError> {
    // 1. Enum namespace: construct enum variant (e.g., Duration.Rounds(3))
    if let Value::EnumNamespace(ref enum_name) = receiver {
        return construct_enum_variant_step(
            enum_name, method, arg_meta, arg_values, span, core, env, sp, eh,
        )
        .map(CallResult::Value);
    }

    // 2. Module alias: dispatch alias-qualified call
    if let Value::ModuleAlias(ref alias_name) = receiver {
        return dispatch_alias_call_step(
            alias_name, method, arg_meta, arg_values, span, core, env, sp, eh,
        );
    }

    // 3. Action method call: entity.ActionName(args)
    if let Value::Entity(_) = &receiver
        && let Some(fn_info) = core.type_env.lookup_fn(method)
        && fn_info.kind == FnKind::Action
    {
        return dispatch_action_method_step(
            &receiver, method, arg_meta, arg_values, span, core, env, sp, eh,
        );
    }

    // 4. Struct field holding a fn ref: entry.resolve(args)
    if let Value::Struct { ref fields, .. } = receiver
        && let Some(Value::FnRef(fn_name)) = fields.get(method.as_str())
    {
        let fn_name = fn_name.clone();
        return dispatch_fn_ref_step(&fn_name, arg_meta, arg_values, span, core, env, sp, eh);
    }

    // 5. Value methods (type-specific dispatch)
    dispatch_method_step(receiver, method, arg_values, span, core, sp)
}

/// Dispatch value-level method calls with pre-evaluated args.
fn dispatch_method_step(
    receiver: Value,
    method: &Name,
    arg_values: &[Value],
    span: Span,
    _core: &RuntimeCore,
    _sp: &dyn StateProvider,
) -> Result<CallResult, RuntimeError> {
    match &receiver {
        Value::Option(_) | Value::Void => {
            step_option_method(receiver, method, arg_values, span).map(CallResult::Value)
        }
        Value::List(_) => {
            step_list_method(receiver, method, arg_values, span).map(CallResult::Value)
        }
        Value::Set(_) => step_set_method(receiver, method, arg_values, span).map(CallResult::Value),
        Value::Map(_) => step_map_method(receiver, method, span).map(CallResult::Value),
        Value::DiceExpr(_) => step_dice_method(receiver, method, arg_values, span),
        Value::Str(_) => {
            step_string_method(receiver, method, arg_values, span).map(CallResult::Value)
        }
        _ => Err(RuntimeError::with_span(
            format!("type {} has no methods", type_name(&receiver)),
            span,
        )),
    }
}

fn step_option_method(
    value: Value,
    method: &str,
    args: &[Value],
    span: Span,
) -> Result<Value, RuntimeError> {
    match method {
        "unwrap" => match value {
            Value::Option(Some(inner)) => Ok(*inner),
            Value::Option(None) | Value::Void => Err(RuntimeError::with_span(
                "called unwrap() on a none value",
                span,
            )),
            _ => unreachable!(),
        },
        "unwrap_or" => {
            if args.is_empty() {
                return Err(RuntimeError::with_span(
                    "unwrap_or() requires 1 argument",
                    span,
                ));
            }
            match value {
                Value::Option(Some(inner)) => Ok(*inner),
                Value::Option(None) | Value::Void => Ok(args[0].clone()),
                _ => unreachable!(),
            }
        }
        "is_some" => match value {
            Value::Option(Some(_)) => Ok(Value::Bool(true)),
            Value::Option(None) | Value::Void => Ok(Value::Bool(false)),
            _ => unreachable!(),
        },
        "is_none" => match value {
            Value::Option(None) | Value::Void => Ok(Value::Bool(true)),
            Value::Option(Some(_)) => Ok(Value::Bool(false)),
            _ => unreachable!(),
        },
        _ => Err(RuntimeError::with_span(
            format!(
                "option type has no method `{method}`; available methods: unwrap, unwrap_or, is_some, is_none"
            ),
            span,
        )),
    }
}

fn step_list_method(
    object: Value,
    method: &str,
    args: &[Value],
    span: Span,
) -> Result<Value, RuntimeError> {
    let Value::List(list) = object else {
        unreachable!()
    };
    match method {
        "len" => Ok(Value::Int(list.len() as i64)),
        "first" => Ok(list
            .into_iter()
            .next()
            .map_or(Value::Option(None), |v| Value::Option(Some(Box::new(v))))),
        "last" => Ok(list
            .into_iter()
            .next_back()
            .map_or(Value::Option(None), |v| Value::Option(Some(Box::new(v))))),
        "reverse" => {
            let mut v = list;
            v.reverse();
            Ok(Value::List(v))
        }
        "append" => {
            if args.is_empty() {
                return Err(RuntimeError::with_span(
                    "append() requires 1 argument",
                    span,
                ));
            }
            let mut v = list;
            v.push(args[0].clone());
            Ok(Value::List(v))
        }
        "concat" => {
            if args.is_empty() {
                return Err(RuntimeError::with_span(
                    "concat() requires 1 argument",
                    span,
                ));
            }
            match &args[0] {
                Value::List(b) => {
                    let mut v = list;
                    v.extend(b.iter().cloned());
                    Ok(Value::List(v))
                }
                other => Err(RuntimeError::with_span(
                    format!("concat() argument must be a list, got {}", type_name(other)),
                    span,
                )),
            }
        }
        "sum" => {
            if list.is_empty() {
                return Ok(Value::Int(0));
            }
            let mut int_sum: i64 = 0;
            let mut float_sum: f64 = 0.0;
            let mut is_float = false;
            for item in &list {
                match item {
                    Value::Int(n) => {
                        if is_float {
                            float_sum += *n as f64;
                        } else {
                            int_sum = int_sum.checked_add(*n).ok_or_else(|| {
                                RuntimeError::with_span("integer overflow in sum()", span)
                            })?;
                        }
                    }
                    Value::Float(f) => {
                        if !is_float {
                            is_float = true;
                            float_sum = int_sum as f64;
                        }
                        float_sum += f;
                    }
                    _ => {
                        return Err(RuntimeError::with_span(
                            format!(
                                "sum() requires list of int or float, got {}",
                                type_name(item)
                            ),
                            span,
                        ));
                    }
                }
            }
            if is_float {
                Ok(Value::Float(float_sum))
            } else {
                Ok(Value::Int(int_sum))
            }
        }
        "any" => {
            for item in &list {
                match item {
                    Value::Bool(true) => return Ok(Value::Bool(true)),
                    Value::Bool(false) => {}
                    _ => {
                        return Err(RuntimeError::with_span(
                            format!("any() requires list of bool, got {}", type_name(item)),
                            span,
                        ));
                    }
                }
            }
            Ok(Value::Bool(false))
        }
        "all" => {
            for item in &list {
                match item {
                    Value::Bool(false) => return Ok(Value::Bool(false)),
                    Value::Bool(true) => {}
                    _ => {
                        return Err(RuntimeError::with_span(
                            format!("all() requires list of bool, got {}", type_name(item)),
                            span,
                        ));
                    }
                }
            }
            Ok(Value::Bool(true))
        }
        "sort" => {
            let mut v = list;
            v.sort();
            Ok(Value::List(v))
        }
        "take" => {
            if args.is_empty() {
                return Err(RuntimeError::with_span("take() requires 1 argument", span));
            }
            let n = match &args[0] {
                Value::Int(i) => (*i).max(0) as usize,
                other => {
                    return Err(RuntimeError::with_span(
                        format!("take() expects int argument, got {}", type_name(other)),
                        span,
                    ));
                }
            };
            let n = n.min(list.len());
            Ok(Value::List(list.into_iter().take(n).collect()))
        }
        "to_set" => Ok(Value::Set(list.into_iter().collect())),
        "contains" => {
            if args.is_empty() {
                return Err(RuntimeError::with_span(
                    "contains() requires 1 argument",
                    span,
                ));
            }
            Ok(Value::Bool(list.contains(&args[0])))
        }
        "remove_first" => {
            if args.is_empty() {
                return Err(RuntimeError::with_span(
                    "remove_first() requires 1 argument",
                    span,
                ));
            }
            let mut v = list;
            if let Some(pos) = v.iter().position(|x| x == &args[0]) {
                v.remove(pos);
            }
            Ok(Value::List(v))
        }
        _ => Err(RuntimeError::with_span(
            format!(
                "list type has no method `{method}`; available methods: len, first, last, reverse, append, concat, sum, any, all, sort, take, to_set, contains, remove_first"
            ),
            span,
        )),
    }
}

fn step_set_method(
    object: Value,
    method: &str,
    args: &[Value],
    span: Span,
) -> Result<Value, RuntimeError> {
    let Value::Set(set) = object else {
        unreachable!()
    };
    match method {
        "len" => Ok(Value::Int(set.len() as i64)),
        "add" => {
            if args.is_empty() {
                return Err(RuntimeError::with_span("add() requires 1 argument", span));
            }
            let mut new_set = set;
            new_set.insert(args[0].clone());
            Ok(Value::Set(new_set))
        }
        "remove" => {
            if args.is_empty() {
                return Err(RuntimeError::with_span(
                    "remove() requires 1 argument",
                    span,
                ));
            }
            let mut new_set = set;
            new_set.remove(&args[0]);
            Ok(Value::Set(new_set))
        }
        "union" => {
            if args.is_empty() {
                return Err(RuntimeError::with_span("union() requires 1 argument", span));
            }
            match &args[0] {
                Value::Set(b) => {
                    let mut new_set = set;
                    new_set.extend(b.iter().cloned());
                    Ok(Value::Set(new_set))
                }
                other => Err(RuntimeError::with_span(
                    format!("union() argument must be a set, got {}", type_name(other)),
                    span,
                )),
            }
        }
        "intersection" => {
            if args.is_empty() {
                return Err(RuntimeError::with_span(
                    "intersection() requires 1 argument",
                    span,
                ));
            }
            match &args[0] {
                Value::Set(b) => {
                    let result = set.intersection(b).cloned().collect();
                    Ok(Value::Set(result))
                }
                other => Err(RuntimeError::with_span(
                    format!(
                        "intersection() argument must be a set, got {}",
                        type_name(other)
                    ),
                    span,
                )),
            }
        }
        "difference" => {
            if args.is_empty() {
                return Err(RuntimeError::with_span(
                    "difference() requires 1 argument",
                    span,
                ));
            }
            match &args[0] {
                Value::Set(b) => {
                    let result = set.difference(b).cloned().collect();
                    Ok(Value::Set(result))
                }
                other => Err(RuntimeError::with_span(
                    format!(
                        "difference() argument must be a set, got {}",
                        type_name(other)
                    ),
                    span,
                )),
            }
        }
        "to_list" => Ok(Value::List(set.into_iter().collect())),
        "contains" => {
            if args.is_empty() {
                return Err(RuntimeError::with_span(
                    "contains() requires 1 argument",
                    span,
                ));
            }
            Ok(Value::Bool(set.contains(&args[0])))
        }
        _ => Err(RuntimeError::with_span(
            format!(
                "set type has no method `{method}`; available methods: len, add, remove, union, intersection, difference, to_list, contains"
            ),
            span,
        )),
    }
}

fn step_map_method(object: Value, method: &str, span: Span) -> Result<Value, RuntimeError> {
    let Value::Map(map) = object else {
        unreachable!()
    };
    match method {
        "len" => Ok(Value::Int(map.len() as i64)),
        "keys" => Ok(Value::List(map.into_keys().collect())),
        "values" => Ok(Value::List(map.into_values().collect())),
        _ => Err(RuntimeError::with_span(
            format!("map type has no method `{method}`; available methods: len, keys, values"),
            span,
        )),
    }
}

fn step_dice_method(
    object: Value,
    method: &str,
    args: &[Value],
    span: Span,
) -> Result<CallResult, RuntimeError> {
    let Value::DiceExpr(expr) = object else {
        unreachable!()
    };
    match method {
        "multiply" => {
            if args.is_empty() {
                return Err(RuntimeError::with_span(
                    "multiply() requires 1 argument",
                    span,
                ));
            }
            match &args[0] {
                Value::Int(factor) => {
                    if *factor <= 0 {
                        return Err(RuntimeError::with_span(
                            format!("multiply() factor must be positive, got {factor}"),
                            span,
                        ));
                    }
                    let mut new_groups = Vec::with_capacity(expr.groups.len());
                    for g in &expr.groups {
                        let new_count = (g.count as i64)
                            .checked_mul(*factor)
                            .and_then(|n| u32::try_from(n).ok())
                            .ok_or_else(|| {
                                RuntimeError::with_span("dice count overflow in multiply()", span)
                            })?;
                        new_groups.push(crate::value::DiceGroup {
                            count: new_count,
                            sides: g.sides,
                            filter: g.filter,
                        });
                    }
                    Ok(CallResult::Value(Value::DiceExpr(DiceExpr {
                        groups: new_groups,
                        modifier: expr.modifier,
                    })))
                }
                other => Err(RuntimeError::with_span(
                    format!("multiply() factor must be int, got {}", type_name(other)),
                    span,
                )),
            }
        }
        "roll" => {
            // Effectful: push RollDiceWaiting frame
            Ok(CallResult::PushChild(Frame::RollDiceWaiting {
                dice_expr: expr,
                span,
                pending: None,
            }))
        }
        _ => Err(RuntimeError::with_span(
            format!("DiceExpr type has no method `{method}`; available methods: multiply, roll"),
            span,
        )),
    }
}

fn step_string_method(
    object: Value,
    method: &str,
    args: &[Value],
    span: Span,
) -> Result<Value, RuntimeError> {
    let Value::Str(s) = object else {
        unreachable!()
    };
    match method {
        "len" => Ok(Value::Int(s.len() as i64)),
        "contains" | "starts_with" | "ends_with" => {
            if args.is_empty() {
                return Err(RuntimeError::with_span(
                    format!("{method}() requires 1 argument"),
                    span,
                ));
            }
            let Value::Str(ref substr) = args[0] else {
                return Err(RuntimeError::with_span(
                    format!(
                        "{}() argument must be string, got {}",
                        method,
                        type_name(&args[0])
                    ),
                    span,
                ));
            };
            let result = match method {
                "contains" => s.contains(substr.as_str()),
                "starts_with" => s.starts_with(substr.as_str()),
                "ends_with" => s.ends_with(substr.as_str()),
                _ => unreachable!(),
            };
            Ok(Value::Bool(result))
        }
        _ => Err(RuntimeError::with_span(
            format!(
                "string type has no method `{method}`; available methods: len, contains, starts_with, ends_with"
            ),
            span,
        )),
    }
}

/// Dispatch a module alias-qualified call: Alias.name(args).
fn dispatch_alias_call_step(
    alias_name: &str,
    name: &Name,
    arg_meta: &[ArgMeta],
    arg_values: &[Value],
    span: Span,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    sp: &dyn StateProvider,
    eh: &mut dyn EffectHandler,
) -> Result<CallResult, RuntimeError> {
    // 1. Condition call (e.g., Core.Frightened(source: attacker))
    if let Some(cond_decl) = core.program.conditions.get(name.as_str()) {
        let cond_decl = cond_decl.clone();
        let param_infos = core
            .type_env
            .conditions
            .get(name.as_str())
            .map(|ci| ci.params.clone())
            .unwrap_or_default();
        let bound = bind_args_from_values(
            &param_infos,
            arg_meta,
            arg_values,
            Some(&cond_decl.params),
            core,
            env,
            sp,
            eh,
            span,
        )?;
        let cond_args: BTreeMap<Name, Value> = bound.into_iter().collect();
        return Ok(CallResult::Value(Value::Condition {
            name: name.clone(),
            args: cond_args,
        }));
    }

    // 2. Function call (e.g., Core.modifier(10))
    if let Some(fn_info) = core.type_env.lookup_fn(name) {
        let fn_info = fn_info.clone();
        return dispatch_fn_step(&fn_info, arg_meta, arg_values, span, core, env, sp, eh);
    }

    // 3. Variant constructor — use system-scoped lookup via alias
    let resolved_enum = {
        let target = core
            .type_env
            .system_aliases
            .values()
            .find_map(|aliases| aliases.get(alias_name))
            .cloned();
        target.and_then(|target_sys| {
            let owners = core.type_env.variant_to_enums.get(name.as_str())?;
            let matching: Vec<_> = owners
                .iter()
                .filter(|e| core.type_env.type_owner.get(e.as_str()) == Some(&target_sys))
                .collect();
            (matching.len() == 1).then(|| matching[0].clone())
        })
    };
    if let Some(enum_name) = resolved_enum {
        return construct_enum_variant_step(
            &enum_name, name, arg_meta, arg_values, span, core, env, sp, eh,
        )
        .map(CallResult::Value);
    }

    Err(RuntimeError::with_span(
        format!("no function, condition, or variant '{name}' in module alias"),
        span,
    ))
}

/// Dispatch an action method call natively by building an ActionLifecycle frame.
fn dispatch_action_method_step(
    receiver: &Value,
    method: &Name,
    arg_meta: &[ArgMeta],
    arg_values: &[Value],
    span: Span,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    sp: &dyn StateProvider,
    _eh: &mut dyn EffectHandler,
) -> Result<CallResult, RuntimeError> {
    let actor = match receiver {
        Value::Entity(eref) => *eref,
        other => {
            return Err(RuntimeError::with_span(
                format!("action '{method}' receiver must be an entity, got {other:?}"),
                span,
            ));
        }
    };

    build_action_lifecycle(method, actor, arg_meta, arg_values, span, core, env, sp)
}

/// Dispatch by FnKind.
fn dispatch_fn_step(
    fn_info: &ttrpg_checker::env::FnInfo,
    arg_meta: &[ArgMeta],
    arg_values: &[Value],
    span: Span,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    sp: &dyn StateProvider,
    eh: &mut dyn EffectHandler,
) -> Result<CallResult, RuntimeError> {
    match fn_info.kind {
        FnKind::Function => {
            dispatch_function_step(&fn_info.name, arg_meta, arg_values, span, core, env, sp, eh)
        }
        FnKind::Derive | FnKind::Mechanic => {
            dispatch_derive_step(&fn_info.name, arg_meta, arg_values, span, core, env, sp, eh)
        }
        FnKind::Builtin => {
            // Builtins have no defaults — bind positional/named args
            let bound = bind_args_from_values(
                &fn_info.params,
                arg_meta,
                arg_values,
                None,
                core,
                env,
                sp,
                eh,
                span,
            )?;
            let vals: Vec<Value> = bound.into_iter().map(|(_, v)| v).collect();
            call_builtin_step_full(&fn_info.name, vals, span, core, env, sp, eh)
        }
        FnKind::Table => dispatch_table_step(
            &fn_info.name,
            &fn_info.params,
            arg_meta,
            arg_values,
            span,
            core,
            env,
            sp,
            eh,
        ),
        FnKind::Prompt => {
            dispatch_prompt_step(&fn_info.name, arg_meta, arg_values, span, core, env, sp, eh)
        }
        FnKind::Action => {
            dispatch_action_named_step(&fn_info.name, arg_meta, arg_values, span, core, env, sp)
        }
        FnKind::Reaction | FnKind::Hook => Err(RuntimeError::with_span(
            "internal error: reactions and hooks cannot be called directly",
            span,
        )),
    }
}

// ── Function dispatch (no modify pipeline) ──────────────────────

fn dispatch_function_step(
    name: &str,
    arg_meta: &[ArgMeta],
    arg_values: &[Value],
    span: Span,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    sp: &dyn StateProvider,
    eh: &mut dyn EffectHandler,
) -> Result<CallResult, RuntimeError> {
    let fn_decl = core.program.functions.get(name).ok_or_else(|| {
        RuntimeError::with_span(
            format!("internal error: no declaration found for function '{name}'"),
            span,
        )
    })?;
    let ast_params = fn_decl.params.clone();
    let body = fn_decl.body.clone();

    let fn_info = core
        .type_env
        .lookup_fn(name)
        .ok_or_else(|| {
            RuntimeError::with_span(
                format!("internal error: no type info for function '{name}'"),
                span,
            )
        })?
        .clone();

    let bound = bind_args_from_values(
        &fn_info.params,
        arg_meta,
        arg_values,
        Some(&ast_params),
        core,
        env,
        sp,
        eh,
        span,
    )?;

    // All args (including defaults) are already evaluated by bind_args_from_values.
    // Push FunctionEval with all args bound and no remaining defaults.
    Ok(CallResult::PushChild(Frame::FunctionEval {
        name: Name::from(name),
        args: bound,
        default_params: Vec::new(),
        body: Some(body),
        defaults_done: true,
        child_result: None,
    }))
}

// ── Derive/Mechanic dispatch ────────────────────────────────────

fn dispatch_derive_step(
    name: &str,
    arg_meta: &[ArgMeta],
    arg_values: &[Value],
    span: Span,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    sp: &dyn StateProvider,
    eh: &mut dyn EffectHandler,
) -> Result<CallResult, RuntimeError> {
    // For derive/mechanic, we use the DeriveEval frame which handles
    // the full modifier pipeline natively.
    let fn_decl = core
        .program
        .derives
        .get(name)
        .or_else(|| core.program.mechanics.get(name))
        .ok_or_else(|| {
            RuntimeError::with_span(format!("undefined derive/mechanic '{name}'"), span)
        })?;
    let body = fn_decl.body.clone();

    let fn_info = core
        .type_env
        .lookup_fn(name)
        .ok_or_else(|| {
            RuntimeError::with_span(format!("internal error: no type info for '{name}'"), span)
        })?
        .clone();

    let bound = bind_args_from_values(
        &fn_info.params,
        arg_meta,
        arg_values,
        Some(&fn_decl.params),
        core,
        env,
        sp,
        eh,
        span,
    )?;

    // Convert bound to positional Vec<Value> for DeriveEval
    let bound_values: Vec<Value> = bound.iter().map(|(_, v)| v.clone()).collect();

    Ok(CallResult::PushChild(Frame::DeriveEval {
        name: Name::from(name),
        args: bound_values,
        is_table: false,
        base_value: None,
        modify_hooks: Vec::new(),
        hook_index: 0,
        expr_cache: Vec::new(),
        phase: crate::execution::DeriveEvalPhase::Init,
        bound_args: Some(bound),
        modifiers: Vec::new(),
        body: Some(body),
        pending_modify_effect: None,
        pending: None,
        phase1_params: None,
        phase2_result: None,
        fn_info_cache: Some(fn_info),
        modify_hooks_result: None,
    }))
}

// ── Table dispatch ──────────────────────────────────────────────

fn dispatch_table_step(
    name: &str,
    _params: &[ttrpg_checker::env::ParamInfo],
    arg_meta: &[ArgMeta],
    arg_values: &[Value],
    span: Span,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    sp: &dyn StateProvider,
    eh: &mut dyn EffectHandler,
) -> Result<CallResult, RuntimeError> {
    let fn_info = core
        .type_env
        .lookup_fn(name)
        .ok_or_else(|| {
            RuntimeError::with_span(
                format!("internal error: no type info for table '{name}'"),
                span,
            )
        })?
        .clone();

    let table_decl = core.program.tables.get(name).ok_or_else(|| {
        RuntimeError::with_span(
            format!("internal error: no declaration found for table '{name}'"),
            span,
        )
    })?;

    let bound = bind_args_from_values(
        &fn_info.params,
        arg_meta,
        arg_values,
        Some(&table_decl.params),
        core,
        env,
        sp,
        eh,
        span,
    )?;
    let bound_values: Vec<Value> = bound.iter().map(|(_, v)| v.clone()).collect();

    Ok(CallResult::PushChild(Frame::DeriveEval {
        name: Name::from(name),
        args: bound_values,
        is_table: true,
        base_value: None,
        modify_hooks: Vec::new(),
        hook_index: 0,
        expr_cache: Vec::new(),
        phase: crate::execution::DeriveEvalPhase::Init,
        bound_args: Some(bound),
        modifiers: Vec::new(),
        body: None,
        pending_modify_effect: None,
        pending: None,
        phase1_params: None,
        phase2_result: None,
        fn_info_cache: Some(fn_info),
        modify_hooks_result: None,
    }))
}

// ── Prompt dispatch ─────────────────────────────────────────────

fn dispatch_prompt_step(
    name: &str,
    arg_meta: &[ArgMeta],
    arg_values: &[Value],
    span: Span,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    sp: &dyn StateProvider,
    eh: &mut dyn EffectHandler,
) -> Result<CallResult, RuntimeError> {
    let prompt_decl = core.program.prompts.get(name).ok_or_else(|| {
        RuntimeError::with_span(
            format!("internal error: no declaration found for prompt '{name}'"),
            span,
        )
    })?;

    let hint = prompt_decl.hint.clone();
    let suggest_expr = prompt_decl.suggest.clone();
    let default_block = prompt_decl.default.clone();

    let fn_info = core
        .type_env
        .lookup_fn(name)
        .ok_or_else(|| {
            RuntimeError::with_span(
                format!("internal error: no type info for prompt '{name}'"),
                span,
            )
        })?
        .clone();

    let bound = bind_args_from_values(
        &fn_info.params,
        arg_meta,
        arg_values,
        Some(&prompt_decl.params),
        core,
        env,
        sp,
        eh,
        span,
    )?;

    // Evaluate suggest expression if present
    let suggest = match &suggest_expr {
        Some(expr) => {
            env.push_scope();
            for (pn, pv) in &bound {
                env.bind(pn.clone(), pv.clone());
            }
            let result = eval_expr_step(core, env, sp, eh, expr);
            env.pop_scope();
            Some(result?)
        }
        None => None,
    };

    Ok(CallResult::PushChild(Frame::PromptWaiting {
        prompt_name: Name::from(name),
        params: bound,
        return_type: fn_info.return_type.clone(),
        hint,
        suggest,
        default_block,
        span,
        pending: None,
        result: None,
    }))
}

// ── Native action dispatch ──────────────────────────────────────

/// Dispatch a named action call (e.g., `MeleeAttack(actor, target)`) by
/// building an ActionLifecycle frame. The first positional arg (or named arg
/// matching the receiver name) is the receiver entity.
fn dispatch_action_named_step(
    name: &str,
    arg_meta: &[ArgMeta],
    arg_values: &[Value],
    span: Span,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    sp: &dyn StateProvider,
) -> Result<CallResult, RuntimeError> {
    // Get receiver info from type env
    let fn_info = core.type_env.lookup_fn(name).ok_or_else(|| {
        RuntimeError::with_span(
            format!("internal error: no type info for action '{name}'"),
            span,
        )
    })?;
    let receiver_info = fn_info.receiver.as_ref().ok_or_else(|| {
        RuntimeError::with_span(
            format!("internal error: action '{name}' has no receiver info"),
            span,
        )
    })?;
    let receiver_param_name = receiver_info.name.clone();

    // Find receiver: first positional arg, or named arg matching receiver name
    let (receiver_idx, receiver_val) = arg_meta
        .iter()
        .zip(arg_values.iter())
        .enumerate()
        .find(|(_, (meta, _))| meta.name.is_none())
        .or_else(|| {
            arg_meta
                .iter()
                .zip(arg_values.iter())
                .enumerate()
                .find(|(_, (meta, _))| meta.name.as_ref() == Some(&receiver_param_name))
        })
        .map(|(i, (_, val))| (i, val.clone()))
        .ok_or_else(|| {
            RuntimeError::with_span(
                format!("action '{name}' requires a receiver argument"),
                span,
            )
        })?;

    let actor = match &receiver_val {
        Value::Entity(eref) => *eref,
        other => {
            return Err(RuntimeError::with_span(
                format!("action '{name}' receiver must be an entity, got {other:?}"),
                span,
            ));
        }
    };

    // Remaining args (excluding receiver)
    let remaining_meta: Vec<_> = arg_meta
        .iter()
        .enumerate()
        .filter(|(i, _)| *i != receiver_idx)
        .map(|(_, m)| m.clone())
        .collect();
    let remaining_values: Vec<_> = arg_values
        .iter()
        .enumerate()
        .filter(|(i, _)| *i != receiver_idx)
        .map(|(_, v)| v.clone())
        .collect();

    build_action_lifecycle(
        name,
        actor,
        &remaining_meta,
        &remaining_values,
        span,
        core,
        env,
        sp,
    )
}

/// Build an ActionLifecycle frame for an action dispatch.
///
/// Handles overload resolution, argument binding, and default parameter
/// collection. Returns `CallResult::PushChild` with the lifecycle frame.
fn build_action_lifecycle(
    name: &str,
    actor: crate::state::EntityRef,
    arg_meta: &[ArgMeta],
    arg_values: &[Value],
    span: Span,
    core: &RuntimeCore,
    _env: &mut ExecEnv,
    sp: &dyn StateProvider,
) -> Result<CallResult, RuntimeError> {
    use crate::effect::ActionKind;
    use crate::execution::ActionStep;
    use crate::state::InvocationId;
    use ttrpg_checker::ty::Ty;

    // Resolve overload based on entity type
    let entity_type = sp.entity_type_name(&actor);
    let overloads = core.program.actions.get(name).ok_or_else(|| {
        RuntimeError::with_span(
            format!("internal error: no declaration found for action '{name}'"),
            span,
        )
    })?;
    let action_decl = crate::select_action_overload(overloads, entity_type.as_ref())
        .cloned()
        .ok_or_else(|| {
            RuntimeError::with_span(
                format!(
                    "no matching overload for action '{}' on entity type '{}'",
                    name,
                    entity_type.as_ref().map_or("unknown", |n| n.as_str())
                ),
                span,
            )
        })?;

    // Get correct overload's FnInfo for param types
    let recv_ty = entity_type.map_or(Ty::AnyEntity, Ty::Entity);
    let correct_fn_info = core
        .type_env
        .lookup_action_overload(name, &recv_ty)
        .ok_or_else(|| {
            RuntimeError::with_span(
                format!(
                    "no matching overload for action '{}' on type '{}'",
                    name,
                    recv_ty.display()
                ),
                span,
            )
        })?
        .clone();

    // Map positional and named args to param slots
    let mut bindings: Vec<(Name, Value)> = Vec::new();
    let mut bound_indices = vec![false; correct_fn_info.params.len()];
    let mut next_positional = 0usize;

    for (meta, val) in arg_meta.iter().zip(arg_values.iter()) {
        if let Some(ref param_name) = meta.name {
            // Named arg: find matching param
            let pos = correct_fn_info
                .params
                .iter()
                .position(|p| p.name == *param_name)
                .ok_or_else(|| {
                    RuntimeError::with_span(format!("unknown parameter '{param_name}'"), meta.span)
                })?;
            bound_indices[pos] = true;
            bindings.push((param_name.clone(), val.clone()));
        } else {
            // Positional arg: skip to next unbound param
            while next_positional < correct_fn_info.params.len() && bound_indices[next_positional] {
                next_positional += 1;
            }
            if next_positional >= correct_fn_info.params.len() {
                return Err(RuntimeError::with_span(
                    "too many positional arguments",
                    meta.span,
                ));
            }
            bound_indices[next_positional] = true;
            bindings.push((
                correct_fn_info.params[next_positional].name.clone(),
                val.clone(),
            ));
            next_positional += 1;
        }
    }

    // Collect default expressions for any unbound optional params
    let mut default_params = Vec::new();
    for (i, param) in correct_fn_info.params.iter().enumerate() {
        if !bound_indices[i] {
            if param.has_default {
                if let Some(ast_param) = action_decl.params.get(i)
                    && let Some(ref default_expr) = ast_param.default
                {
                    default_params.push((param.name.clone(), default_expr.clone()));
                }
            } else {
                return Err(RuntimeError::with_span(
                    format!("missing required argument '{}'", param.name),
                    span,
                ));
            }
        }
    }

    let inv_id = InvocationId(core.alloc_invocation_id()?);

    Ok(CallResult::PushChild(Frame::ActionLifecycle {
        name: action_decl.name.clone(),
        actor,
        action_kind: ActionKind::Action,
        call_span: span,
        has_return_type: action_decl.return_type.is_some(),
        inv_id,
        requires: action_decl.requires.clone(),
        cost: action_decl.cost.clone(),
        resolve: action_decl.resolve.clone(),
        receiver_name: action_decl.receiver_name.clone(),
        bindings,
        default_params,
        step: ActionStep::EmitStarted,
        pending: None,
        body_result: None,
        saved_turn_actor: None,
        saved_invocation: None,
    }))
}

/// Convert a Value back to an ExprKind for synthetic expressions.
/// Only needs to handle values that can appear as call arguments.
fn value_to_expr(val: &Value) -> ExprKind {
    match val {
        Value::Int(n) => ExprKind::IntLit(*n),
        Value::Bool(b) => ExprKind::BoolLit(*b),
        Value::Str(s) => ExprKind::StringLit(s.clone()),
        Value::Void => ExprKind::NoneLit,
        _ => ExprKind::NoneLit, // fallback — should be unreachable in practice
    }
}

// ── Argument binding (value-level) ──────────────────────────────

/// Bind pre-evaluated argument values to parameters.
///
/// Handles positional and named args, fills defaults via bridge evaluation.
fn bind_args_from_values(
    params: &[ttrpg_checker::env::ParamInfo],
    arg_meta: &[ArgMeta],
    arg_values: &[Value],
    ast_params: Option<&[ttrpg_ast::ast::Param]>,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    sp: &dyn StateProvider,
    eh: &mut dyn EffectHandler,
    call_span: Span,
) -> Result<Vec<(Name, Value)>, RuntimeError> {
    let mut result: Vec<Option<Value>> = vec![None; params.len()];

    // Map positional + named args to param slots
    let mut next_positional = 0usize;
    for (meta, val) in arg_meta.iter().zip(arg_values.iter()) {
        if let Some(ref name) = meta.name {
            let pos = params.iter().position(|p| p.name == *name).ok_or_else(|| {
                RuntimeError::with_span(format!("unknown parameter '{name}'"), meta.span)
            })?;
            if result[pos].is_some() {
                return Err(RuntimeError::with_span(
                    format!("duplicate argument for parameter '{name}'"),
                    meta.span,
                ));
            }
            result[pos] = Some(val.clone());
        } else {
            if next_positional >= params.len() {
                return Err(RuntimeError::with_span(
                    "too many positional arguments",
                    meta.span,
                ));
            }
            result[next_positional] = Some(val.clone());
            next_positional += 1;
        }
    }

    // Fill defaults for unbound optional params
    let needs_defaults = params
        .iter()
        .enumerate()
        .any(|(i, p)| result[i].is_none() && p.has_default);

    if needs_defaults {
        // Push a temporary scope so default expressions can reference earlier params
        env.push_scope();
        for (i, param) in params.iter().enumerate() {
            if let Some(ref val) = result[i] {
                env.bind(param.name.clone(), val.clone());
            }
        }
    }

    let outcome = fill_defaults_step(
        params,
        &mut result,
        ast_params,
        core,
        env,
        sp,
        eh,
        call_span,
    );

    if needs_defaults {
        env.pop_scope();
    }

    outcome
}

fn fill_defaults_step(
    params: &[ttrpg_checker::env::ParamInfo],
    result: &mut [Option<Value>],
    ast_params: Option<&[ttrpg_ast::ast::Param]>,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    sp: &dyn StateProvider,
    eh: &mut dyn EffectHandler,
    call_span: Span,
) -> Result<Vec<(Name, Value)>, RuntimeError> {
    let mut bound = Vec::with_capacity(params.len());
    for (i, param) in params.iter().enumerate() {
        match result[i].take() {
            Some(val) => bound.push((param.name.clone(), val)),
            None => {
                if param.has_default {
                    let default_val = if let Some(ast_ps) = ast_params {
                        if let Some(ast_param) = ast_ps.get(i) {
                            if let Some(ref default_expr) = ast_param.default {
                                let val = eval_expr_step(core, env, sp, eh, default_expr)?;
                                // Bind into scope so later defaults can see it
                                env.bind(param.name.clone(), val.clone());
                                val
                            } else {
                                return Err(RuntimeError::with_span(
                                    format!(
                                        "internal error: parameter '{}' has_default but no default expression",
                                        param.name
                                    ),
                                    call_span,
                                ));
                            }
                        } else {
                            return Err(RuntimeError::with_span(
                                format!(
                                    "internal error: parameter index {} out of range for '{}'",
                                    i, param.name
                                ),
                                call_span,
                            ));
                        }
                    } else {
                        // Builtin or enum constructor: no AST defaults available.
                        continue;
                    };
                    bound.push((param.name.clone(), default_val));
                } else {
                    return Err(RuntimeError::with_span(
                        format!("missing required argument '{}'", param.name),
                        call_span,
                    ));
                }
            }
        }
    }
    Ok(bound)
}

// ── Collection builtins (value-level) ───────────────────────────

fn type_name(val: &Value) -> &'static str {
    crate::eval::type_name(val)
}

fn eval_len_values(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    if args.len() != 1 {
        return Err(RuntimeError::with_span(
            format!("len() requires 1 argument, got {}", args.len()),
            span,
        ));
    }
    match &args[0] {
        Value::List(v) => Ok(Value::Int(v.len() as i64)),
        Value::Set(s) => Ok(Value::Int(s.len() as i64)),
        Value::Map(m) => Ok(Value::Int(m.len() as i64)),
        _ => Err(RuntimeError::with_span(
            format!(
                "len() expects a list, set, or map, got {}",
                type_name(&args[0])
            ),
            span,
        )),
    }
}

fn eval_keys_values(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    if args.len() != 1 {
        return Err(RuntimeError::with_span(
            format!("keys() requires 1 argument, got {}", args.len()),
            span,
        ));
    }
    match &args[0] {
        Value::Map(m) => Ok(Value::List(m.keys().cloned().collect())),
        _ => Err(RuntimeError::with_span(
            format!("keys() expects a map, got {}", type_name(&args[0])),
            span,
        )),
    }
}

fn eval_values_values(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    if args.len() != 1 {
        return Err(RuntimeError::with_span(
            format!("values() requires 1 argument, got {}", args.len()),
            span,
        ));
    }
    match &args[0] {
        Value::Map(m) => Ok(Value::List(m.values().cloned().collect())),
        _ => Err(RuntimeError::with_span(
            format!("values() expects a map, got {}", type_name(&args[0])),
            span,
        )),
    }
}

fn eval_first_values(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    if args.len() != 1 {
        return Err(RuntimeError::with_span(
            format!("first() requires 1 argument, got {}", args.len()),
            span,
        ));
    }
    match &args[0] {
        Value::List(v) => Ok(v.first().map_or(Value::Option(None), |v| {
            Value::Option(Some(Box::new(v.clone())))
        })),
        _ => Err(RuntimeError::with_span(
            format!("first() expects a list, got {}", type_name(&args[0])),
            span,
        )),
    }
}

fn eval_last_values(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    if args.len() != 1 {
        return Err(RuntimeError::with_span(
            format!("last() requires 1 argument, got {}", args.len()),
            span,
        ));
    }
    match &args[0] {
        Value::List(v) => Ok(v.last().map_or(Value::Option(None), |v| {
            Value::Option(Some(Box::new(v.clone())))
        })),
        _ => Err(RuntimeError::with_span(
            format!("last() expects a list, got {}", type_name(&args[0])),
            span,
        )),
    }
}

fn eval_append_values(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    if args.len() != 2 {
        return Err(RuntimeError::with_span(
            format!("append() requires 2 arguments, got {}", args.len()),
            span,
        ));
    }
    match &args[0] {
        Value::List(v) => {
            let mut v = v.clone();
            v.push(args[1].clone());
            Ok(Value::List(v))
        }
        _ => Err(RuntimeError::with_span(
            format!(
                "append() first argument must be a list, got {}",
                type_name(&args[0])
            ),
            span,
        )),
    }
}

fn eval_concat_values(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    if args.len() != 2 {
        return Err(RuntimeError::with_span(
            format!("concat() requires 2 arguments, got {}", args.len()),
            span,
        ));
    }
    match (&args[0], &args[1]) {
        (Value::List(a), Value::List(b)) => {
            let mut result = a.clone();
            result.extend(b.iter().cloned());
            Ok(Value::List(result))
        }
        (Value::List(_), _) => Err(RuntimeError::with_span(
            format!(
                "concat() second argument must be a list, got {}",
                type_name(&args[1])
            ),
            span,
        )),
        _ => Err(RuntimeError::with_span(
            format!(
                "concat() expects two lists, got {} and {}",
                type_name(&args[0]),
                type_name(&args[1])
            ),
            span,
        )),
    }
}

fn eval_reverse_values(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    if args.len() != 1 {
        return Err(RuntimeError::with_span(
            format!("reverse() requires 1 argument, got {}", args.len()),
            span,
        ));
    }
    match &args[0] {
        Value::List(v) => {
            let mut v = v.clone();
            v.reverse();
            Ok(Value::List(v))
        }
        _ => Err(RuntimeError::with_span(
            format!("reverse() expects a list, got {}", type_name(&args[0])),
            span,
        )),
    }
}

fn eval_sum_values(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    if args.len() != 1 {
        return Err(RuntimeError::with_span(
            format!("sum() requires 1 argument, got {}", args.len()),
            span,
        ));
    }
    match &args[0] {
        Value::List(v) => {
            if v.is_empty() {
                return Ok(Value::Int(0));
            }
            let mut int_sum: i64 = 0;
            let mut float_sum: f64 = 0.0;
            let mut is_float = false;
            for item in v {
                match item {
                    Value::Int(n) => {
                        if is_float {
                            float_sum += *n as f64;
                        } else {
                            int_sum = int_sum.checked_add(*n).ok_or_else(|| {
                                RuntimeError::with_span("integer overflow in sum()", span)
                            })?;
                        }
                    }
                    Value::Float(f) => {
                        if !is_float {
                            is_float = true;
                            float_sum = int_sum as f64;
                        }
                        float_sum += f;
                    }
                    _ => {
                        return Err(RuntimeError::with_span(
                            format!(
                                "sum() requires list of int or float, got {}",
                                type_name(item)
                            ),
                            span,
                        ));
                    }
                }
            }
            if is_float {
                Ok(Value::Float(float_sum))
            } else {
                Ok(Value::Int(int_sum))
            }
        }
        _ => Err(RuntimeError::with_span(
            format!("sum() expects a list, got {}", type_name(&args[0])),
            span,
        )),
    }
}

fn eval_any_values(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    if args.len() != 1 {
        return Err(RuntimeError::with_span(
            format!("any() requires 1 argument, got {}", args.len()),
            span,
        ));
    }
    match &args[0] {
        Value::List(v) => {
            for item in v {
                match item {
                    Value::Bool(true) => return Ok(Value::Bool(true)),
                    Value::Bool(false) => {}
                    _ => {
                        return Err(RuntimeError::with_span(
                            format!("any() requires list of bool, got {}", type_name(item)),
                            span,
                        ));
                    }
                }
            }
            Ok(Value::Bool(false))
        }
        _ => Err(RuntimeError::with_span(
            format!("any() expects a list, got {}", type_name(&args[0])),
            span,
        )),
    }
}

fn eval_all_values(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    if args.len() != 1 {
        return Err(RuntimeError::with_span(
            format!("all() requires 1 argument, got {}", args.len()),
            span,
        ));
    }
    match &args[0] {
        Value::List(v) => {
            for item in v {
                match item {
                    Value::Bool(false) => return Ok(Value::Bool(false)),
                    Value::Bool(true) => {}
                    _ => {
                        return Err(RuntimeError::with_span(
                            format!("all() requires list of bool, got {}", type_name(item)),
                            span,
                        ));
                    }
                }
            }
            Ok(Value::Bool(true))
        }
        _ => Err(RuntimeError::with_span(
            format!("all() expects a list, got {}", type_name(&args[0])),
            span,
        )),
    }
}

fn eval_sort_values(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    if args.len() != 1 {
        return Err(RuntimeError::with_span(
            format!("sort() requires 1 argument, got {}", args.len()),
            span,
        ));
    }
    match &args[0] {
        Value::List(v) => {
            let mut v = v.clone();
            v.sort();
            Ok(Value::List(v))
        }
        _ => Err(RuntimeError::with_span(
            format!("sort() expects a list, got {}", type_name(&args[0])),
            span,
        )),
    }
}

fn eval_take_values(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    if args.len() != 2 {
        return Err(RuntimeError::with_span(
            format!("take() requires 2 arguments, got {}", args.len()),
            span,
        ));
    }
    let n = match &args[1] {
        Value::Int(i) => *i,
        _ => {
            return Err(RuntimeError::with_span(
                format!(
                    "take() expects an int as second argument, got {}",
                    type_name(&args[1])
                ),
                span,
            ));
        }
    };
    match &args[0] {
        Value::List(v) => {
            let n = (n.max(0) as usize).min(v.len());
            Ok(Value::List(v[..n].to_vec()))
        }
        _ => Err(RuntimeError::with_span(
            format!(
                "take() expects a list as first argument, got {}",
                type_name(&args[0])
            ),
            span,
        )),
    }
}

fn eval_some_values(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    if args.len() != 1 {
        return Err(RuntimeError::with_span(
            format!("some() requires 1 argument, got {}", args.len()),
            span,
        ));
    }
    Ok(Value::Option(Some(Box::new(args[0].clone()))))
}

fn eval_max_values(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    eval_min_max_values(args, span, "max", |a, b| a.max(b))
}

fn eval_min_values(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    eval_min_max_values(args, span, "min", |a, b| a.min(b))
}

fn eval_min_max_values(
    args: &[Value],
    span: Span,
    name: &str,
    combine: fn(i64, i64) -> i64,
) -> Result<Value, RuntimeError> {
    match args.len() {
        2 => match (&args[0], &args[1]) {
            (Value::Int(x), Value::Int(y)) => Ok(Value::Int(combine(*x, *y))),
            _ => Err(RuntimeError::with_span(
                format!(
                    "{name}() expects (int, int) or (list<int>), got ({}, {})",
                    type_name(&args[0]),
                    type_name(&args[1])
                ),
                span,
            )),
        },
        1 => match &args[0] {
            Value::List(items) => {
                let mut iter = items.iter();
                let first = match iter.next() {
                    Some(Value::Int(n)) => *n,
                    Some(other) => {
                        return Err(RuntimeError::with_span(
                            format!("{name}() list contains non-int: {}", type_name(other)),
                            span,
                        ));
                    }
                    None => {
                        return Err(RuntimeError::with_span(
                            format!("{name}() called on empty list"),
                            span,
                        ));
                    }
                };
                let mut result = first;
                for item in iter {
                    match item {
                        Value::Int(n) => result = combine(result, *n),
                        other => {
                            return Err(RuntimeError::with_span(
                                format!("{name}() list contains non-int: {}", type_name(other)),
                                span,
                            ));
                        }
                    }
                }
                Ok(Value::Int(result))
            }
            _ => Err(RuntimeError::with_span(
                format!(
                    "{name}() expects (int, int) or (list<int>), got ({})",
                    type_name(&args[0])
                ),
                span,
            )),
        },
        _ => Err(RuntimeError::with_span(
            format!("{name}() requires 1 or 2 arguments, got {}", args.len()),
            span,
        )),
    }
}

// ── Ordinal builtins (value-level) ──────────────────────────────

fn eval_ordinal_step(
    args: &[Value],
    span: Span,
    core: &RuntimeCore,
) -> Result<Value, RuntimeError> {
    if args.is_empty() {
        return Err(RuntimeError::with_span(
            "ordinal() requires 1 argument",
            span,
        ));
    }
    match &args[0] {
        Value::EnumVariant {
            enum_name, variant, ..
        } => {
            let ordinal = crate::eval::variant_ordinal(&core.type_env, enum_name, variant)
                .ok_or_else(|| {
                    RuntimeError::with_span(
                        format!("unknown variant `{variant}` of enum `{enum_name}`"),
                        span,
                    )
                })?;
            Ok(Value::Int(ordinal as i64))
        }
        _ => Err(RuntimeError::with_span(
            format!(
                "ordinal() expects an enum variant, got {}",
                type_name(&args[0])
            ),
            span,
        )),
    }
}

fn eval_from_ordinal_step(
    args: &[Value],
    span: Span,
    core: &RuntimeCore,
) -> Result<Value, RuntimeError> {
    if args.len() < 2 {
        return Err(RuntimeError::with_span(
            "from_ordinal() requires 2 arguments",
            span,
        ));
    }
    let enum_name = match &args[0] {
        Value::EnumNamespace(name) => name.clone(),
        _ => {
            return Err(RuntimeError::with_span(
                format!(
                    "from_ordinal() first argument must be an enum type, got {}",
                    type_name(&args[0])
                ),
                span,
            ));
        }
    };
    let idx = match &args[1] {
        Value::Int(n) => *n,
        _ => {
            return Err(RuntimeError::with_span(
                format!(
                    "from_ordinal() second argument must be int, got {}",
                    type_name(&args[1])
                ),
                span,
            ));
        }
    };
    if idx < 0 {
        return Err(RuntimeError::with_span(
            format!("from_ordinal() index must be non-negative, got {idx}"),
            span,
        ));
    }
    let info = match core.type_env.types.get(enum_name.as_str()) {
        Some(DeclInfo::Enum(info)) => info,
        _ => {
            return Err(RuntimeError::with_span(
                format!("unknown enum `{enum_name}`"),
                span,
            ));
        }
    };
    let idx_usize = idx as usize;
    if idx_usize >= info.variants.len() {
        return Err(RuntimeError::with_span(
            format!(
                "from_ordinal() index {} out of range for enum `{}` (0..{})",
                idx,
                enum_name,
                info.variants.len()
            ),
            span,
        ));
    }
    let variant = &info.variants[idx_usize];
    if !variant.fields.is_empty() {
        return Err(RuntimeError::with_span(
            format!(
                "from_ordinal() cannot construct variant `{}` of `{}` — it has payload fields",
                variant.name, enum_name
            ),
            span,
        ));
    }
    Ok(Value::EnumVariant {
        enum_name,
        variant: variant.name.clone(),
        fields: BTreeMap::new(),
    })
}

fn eval_try_from_ordinal_step(
    args: &[Value],
    span: Span,
    core: &RuntimeCore,
) -> Result<Value, RuntimeError> {
    if args.len() < 2 {
        return Err(RuntimeError::with_span(
            "try_from_ordinal() requires 2 arguments",
            span,
        ));
    }
    let enum_name = match &args[0] {
        Value::EnumNamespace(name) => name.clone(),
        _ => {
            return Err(RuntimeError::with_span(
                format!(
                    "try_from_ordinal() first argument must be an enum type, got {}",
                    type_name(&args[0])
                ),
                span,
            ));
        }
    };
    let idx = match &args[1] {
        Value::Int(n) => *n,
        _ => {
            return Err(RuntimeError::with_span(
                format!(
                    "try_from_ordinal() second argument must be int, got {}",
                    type_name(&args[1])
                ),
                span,
            ));
        }
    };
    if idx < 0 {
        return Ok(Value::Option(None));
    }
    let info = match core.type_env.types.get(enum_name.as_str()) {
        Some(DeclInfo::Enum(info)) => info,
        _ => {
            return Err(RuntimeError::with_span(
                format!("unknown enum `{enum_name}`"),
                span,
            ));
        }
    };
    let idx_usize = idx as usize;
    if idx_usize >= info.variants.len() {
        return Ok(Value::Option(None));
    }
    let variant = &info.variants[idx_usize];
    if !variant.fields.is_empty() {
        return Ok(Value::Option(None));
    }
    Ok(Value::EnumVariant {
        enum_name,
        variant: variant.name.clone(),
        fields: BTreeMap::new(),
    })
}

// ── Enum variant construction (value-level) ─────────────────────

fn construct_enum_variant_step(
    enum_name: &str,
    variant_name: &str,
    arg_meta: &[ArgMeta],
    arg_values: &[Value],
    span: Span,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    sp: &dyn StateProvider,
    eh: &mut dyn EffectHandler,
) -> Result<Value, RuntimeError> {
    let enum_info = match core.type_env.types.get(enum_name) {
        Some(DeclInfo::Enum(info)) => info.clone(),
        _ => {
            return Err(RuntimeError::with_span(
                format!("internal error: '{enum_name}' is not an enum"),
                span,
            ));
        }
    };

    let variant_info = enum_info
        .variants
        .iter()
        .find(|v| v.name == variant_name)
        .ok_or_else(|| {
            RuntimeError::with_span(
                format!("enum '{enum_name}' has no variant '{variant_name}'"),
                span,
            )
        })?;

    if variant_info.fields.is_empty() && arg_values.is_empty() {
        return Ok(Value::EnumVariant {
            enum_name: Name::from(enum_name),
            variant: Name::from(variant_name),
            fields: BTreeMap::new(),
        });
    }

    let has_any_default = variant_info.has_defaults.iter().any(|d| *d);

    // Build ParamInfo from variant fields
    let param_infos: Vec<ttrpg_checker::env::ParamInfo> = variant_info
        .fields
        .iter()
        .enumerate()
        .map(|(i, (name, ty))| ttrpg_checker::env::ParamInfo {
            name: name.clone(),
            ty: ty.clone(),
            has_default: variant_info.has_defaults.get(i).copied().unwrap_or(false),
            with_groups: vec![],
            with_disjunctive: false,
        })
        .collect();

    // If any field has a default, look up the AST to get default expressions
    let ast_params = if has_any_default {
        Some(find_variant_ast_fields(
            &core.program,
            enum_name,
            variant_name,
        ))
    } else {
        None
    };

    let bound = bind_args_from_values(
        &param_infos,
        arg_meta,
        arg_values,
        ast_params.as_deref(),
        core,
        env,
        sp,
        eh,
        span,
    )?;

    let mut fields = BTreeMap::new();
    for (name, val) in bound {
        fields.insert(name, val);
    }

    Ok(Value::EnumVariant {
        enum_name: Name::from(enum_name),
        variant: Name::from(variant_name),
        fields,
    })
}

/// Find the AST field entries for an enum variant, used to evaluate defaults.
fn find_variant_ast_fields(
    program: &ttrpg_ast::ast::Program,
    enum_name: &str,
    variant_name: &str,
) -> Vec<ttrpg_ast::ast::Param> {
    use ttrpg_ast::ast::{DeclKind, TopLevel, WithClause};

    for item in &program.items {
        if let TopLevel::System(system) = &item.node {
            for decl in &system.decls {
                if let DeclKind::Enum(e) = &decl.node
                    && e.name == enum_name
                {
                    for v in &e.variants {
                        if v.name == variant_name {
                            if let Some(ref fields) = v.fields {
                                return fields
                                    .iter()
                                    .map(|f| ttrpg_ast::ast::Param {
                                        name: f.name.clone(),
                                        ty: f.ty.clone(),
                                        default: f.default.clone(),
                                        with_groups: WithClause::default(),
                                        span: f.span,
                                    })
                                    .collect();
                            }
                            return Vec::new();
                        }
                    }
                }
            }
        }
    }
    Vec::new()
}

// ── Builtin dispatch (value-level) ──────────────────────────────

/// Dispatch a pure/state-reading builtin with pre-evaluated args.
/// For effectful builtins (roll, apply_condition, etc.), delegates to
/// `call_builtin_step_full` which can return PushChild.
fn call_builtin_step(
    name: &str,
    args: &[Value],
    span: Span,
    _core: &RuntimeCore,
    sp: &dyn StateProvider,
) -> Result<Value, RuntimeError> {
    match name {
        "floor" => builtin_floor_step(args, span),
        "ceil" => builtin_ceil_step(args, span),
        "distance" => builtin_distance_step(args, span, sp),
        "conditions" => builtin_conditions_step(args, span, sp),
        "has_condition" => builtin_has_condition_step(args, span, sp),
        "dice" => builtin_dice_step(args, span),
        "multiply_dice" => builtin_multiply_dice_step(args, span),
        "max_value" => builtin_max_value_step(args, span),
        "dice_count" => builtin_dice_count_step(args, span),
        "dice_sides" => builtin_dice_sides_step(args, span),
        "dice_modifier" => builtin_dice_modifier_step(args, span),
        "error" => builtin_error_step(args, span),
        "game_time" => builtin_game_time_step(args, span, sp),
        "budget_of" => builtin_budget_of_step(args, span, sp),
        "is_suspended" => builtin_is_suspended_step(args, span, sp),
        "is_off_board" => builtin_is_off_board_step(args, span, sp),
        "are_turns_frozen" => builtin_are_turns_frozen_step(args, span, sp),
        "are_durations_frozen" => builtin_are_durations_frozen_step(args, span, sp),
        "invocation" => {
            // invocation() is env-dependent; we need to handle it specially
            Err(RuntimeError::with_span(
                format!("builtin '{name}' not available in step evaluator"),
                span,
            ))
        }
        _ => Err(RuntimeError::with_span(
            format!("unknown builtin function '{name}'"),
            span,
        )),
    }
}

/// Full builtin dispatch including effectful builtins.
/// Returns CallResult to allow pushing child frames for effects.
fn call_builtin_step_full(
    name: &str,
    args: Vec<Value>,
    span: Span,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    sp: &dyn StateProvider,
    eh: &mut dyn EffectHandler,
) -> Result<CallResult, RuntimeError> {
    match name {
        // Effectful builtins that need child frames
        "roll" => match args.first() {
            Some(Value::DiceExpr(expr)) => Ok(CallResult::PushChild(Frame::RollDiceWaiting {
                dice_expr: expr.clone(),
                span,
                pending: None,
            })),
            Some(other) => Err(RuntimeError::with_span(
                format!("roll() expects DiceExpr, got {}", type_name(other)),
                span,
            )),
            None => Err(RuntimeError::with_span("roll() requires 1 argument", span)),
        },
        // Env-context builtins: implemented natively using ExecEnv + EffectHandler
        "invocation" => builtin_invocation_step(env, &args, span).map(CallResult::Value),
        "condition_token" => builtin_condition_token_step(env, &args, span).map(CallResult::Value),
        "advance_time" => builtin_advance_time_step(env, &args, span, eh).map(CallResult::Value),
        "despawn" => builtin_despawn_step(&args, span, eh).map(CallResult::Value),
        "suspend" => builtin_suspend_step(env, &args, span, eh).map(CallResult::Value),
        "suspend_with_source" => {
            builtin_suspend_with_source_step(&args, span, eh).map(CallResult::Value)
        }
        "remove_suspension_source" => {
            builtin_remove_suspension_source_step(&args, span, eh).map(CallResult::Value)
        }
        "transfer_conditions" => {
            builtin_transfer_conditions_step(env, &args, span, core, eh).map(CallResult::Value)
        }
        // Complex lifecycle builtins — run via frame-based execution
        "apply_condition" | "remove_condition" | "revoke" => {
            run_builtin_via_frame(name, args, span, core, env, sp, eh).map(CallResult::Value)
        }
        // Pure/state-reading builtins
        _ => call_builtin_step(name, &args, span, core, sp).map(CallResult::Value),
    }
}

// ── Individual builtin implementations ──────────────────────────

fn builtin_floor_step(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    match args.first() {
        Some(Value::Float(f)) => {
            if f.is_nan() {
                return Err(RuntimeError::with_span("floor() received NaN", span));
            }
            if f.is_infinite() {
                return Err(RuntimeError::with_span("floor() received infinity", span));
            }
            let floored = f.floor();
            if floored < (i64::MIN as f64) || floored > (i64::MAX as f64) {
                return Err(RuntimeError::with_span(
                    format!("floor({f}) overflows integer range"),
                    span,
                ));
            }
            Ok(Value::Int(floored as i64))
        }
        Some(other) => Err(RuntimeError::with_span(
            format!("floor() expects Float, got {}", type_name(other)),
            span,
        )),
        None => Err(RuntimeError::with_span("floor() requires 1 argument", span)),
    }
}

fn builtin_ceil_step(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    match args.first() {
        Some(Value::Float(f)) => {
            if f.is_nan() {
                return Err(RuntimeError::with_span("ceil() received NaN", span));
            }
            if f.is_infinite() {
                return Err(RuntimeError::with_span("ceil() received infinity", span));
            }
            let ceiled = f.ceil();
            if ceiled < (i64::MIN as f64) || ceiled > (i64::MAX as f64) {
                return Err(RuntimeError::with_span(
                    format!("ceil({f}) overflows integer range"),
                    span,
                ));
            }
            Ok(Value::Int(ceiled as i64))
        }
        Some(other) => Err(RuntimeError::with_span(
            format!("ceil() expects Float, got {}", type_name(other)),
            span,
        )),
        None => Err(RuntimeError::with_span("ceil() requires 1 argument", span)),
    }
}

fn builtin_distance_step(
    args: &[Value],
    span: Span,
    sp: &dyn StateProvider,
) -> Result<Value, RuntimeError> {
    match (args.first(), args.get(1)) {
        (Some(Value::Position(pa)), Some(Value::Position(pb))) => {
            sp.distance(pa.0, pb.0).map(Value::Int).ok_or_else(|| {
                RuntimeError::with_span("distance() received invalid position values", span)
            })
        }
        (Some(a), Some(b)) => Err(RuntimeError::with_span(
            format!(
                "distance() expects (Position, Position), got ({}, {})",
                type_name(a),
                type_name(b)
            ),
            span,
        )),
        _ => Err(RuntimeError::with_span(
            "distance() requires 2 arguments",
            span,
        )),
    }
}

fn builtin_conditions_step(
    args: &[Value],
    span: Span,
    sp: &dyn StateProvider,
) -> Result<Value, RuntimeError> {
    let entity = match args.first() {
        Some(Value::Entity(entity)) => entity,
        Some(other) => {
            return Err(RuntimeError::with_span(
                format!("conditions() expects Entity, got {}", type_name(other)),
                span,
            ));
        }
        None => {
            return Err(RuntimeError::with_span(
                "conditions() requires at least 1 argument",
                span,
            ));
        }
    };
    let conditions = match sp.read_conditions(entity) {
        Some(c) => c,
        None => {
            return Err(RuntimeError::with_span(
                format!("conditions() called on unknown entity: {entity:?}"),
                span,
            ));
        }
    };
    if let Some(Value::Condition {
        name: cond_name, ..
    }) = args.get(1)
    {
        let values = conditions
            .iter()
            .filter(|c| c.name == *cond_name)
            .map(|c| c.to_value())
            .collect();
        return Ok(Value::List(values));
    }
    let values = conditions.iter().map(|c| c.to_value()).collect();
    Ok(Value::List(values))
}

fn builtin_has_condition_step(
    args: &[Value],
    span: Span,
    sp: &dyn StateProvider,
) -> Result<Value, RuntimeError> {
    match (args.first(), args.get(1)) {
        (
            Some(Value::Entity(entity)),
            Some(Value::Condition {
                name: cond_name, ..
            }),
        ) => match sp.read_conditions(entity) {
            Some(conditions) => {
                let has_it = conditions.iter().any(|c| c.name == *cond_name);
                Ok(Value::Bool(has_it))
            }
            None => Err(RuntimeError::with_span(
                format!("has_condition() called on unknown entity: {entity:?}"),
                span,
            )),
        },
        (Some(Value::Entity(_)), Some(other)) => Err(RuntimeError::with_span(
            format!(
                "has_condition() expects Condition as second argument, got {}",
                type_name(other)
            ),
            span,
        )),
        (Some(other), _) => Err(RuntimeError::with_span(
            format!(
                "has_condition() expects Entity as first argument, got {}",
                type_name(other)
            ),
            span,
        )),
        _ => Err(RuntimeError::with_span(
            "has_condition() requires 2 arguments",
            span,
        )),
    }
}

fn builtin_dice_step(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    match (args.first(), args.get(1)) {
        (Some(Value::Int(count)), Some(Value::Int(sides))) => {
            if *count < 0 {
                return Err(RuntimeError::with_span(
                    format!("dice() count must be non-negative, got {count}"),
                    span,
                ));
            }
            if *sides < 1 {
                return Err(RuntimeError::with_span(
                    format!("dice() sides must be at least 1, got {sides}"),
                    span,
                ));
            }
            let count_u32 = u32::try_from(*count).map_err(|_| {
                RuntimeError::with_span(format!("dice() count {count} overflows u32"), span)
            })?;
            let sides_u32 = u32::try_from(*sides).map_err(|_| {
                RuntimeError::with_span(format!("dice() sides {sides} overflows u32"), span)
            })?;
            Ok(Value::DiceExpr(DiceExpr::single(
                count_u32, sides_u32, None, 0,
            )))
        }
        (Some(a), Some(b)) => Err(RuntimeError::with_span(
            format!(
                "dice() expects (Int, Int), got ({}, {})",
                type_name(a),
                type_name(b)
            ),
            span,
        )),
        _ => Err(RuntimeError::with_span("dice() requires 2 arguments", span)),
    }
}

fn builtin_multiply_dice_step(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    match (args.first(), args.get(1)) {
        (Some(Value::DiceExpr(expr)), Some(Value::Int(factor))) => {
            if *factor <= 0 {
                return Err(RuntimeError::with_span(
                    format!("multiply_dice() factor must be positive, got {factor}"),
                    span,
                ));
            }
            let mut new_groups = Vec::with_capacity(expr.groups.len());
            for g in &expr.groups {
                let new_count = (g.count as i64)
                    .checked_mul(*factor)
                    .and_then(|n| u32::try_from(n).ok())
                    .ok_or_else(|| {
                        RuntimeError::with_span("dice count overflow in multiply_dice()", span)
                    })?;
                new_groups.push(crate::value::DiceGroup {
                    count: new_count,
                    sides: g.sides,
                    filter: g.filter,
                });
            }
            Ok(Value::DiceExpr(DiceExpr {
                groups: new_groups,
                modifier: expr.modifier,
            }))
        }
        (Some(a), Some(b)) => Err(RuntimeError::with_span(
            format!(
                "multiply_dice() expects (DiceExpr, Int), got ({}, {})",
                type_name(a),
                type_name(b)
            ),
            span,
        )),
        _ => Err(RuntimeError::with_span(
            "multiply_dice() requires 2 arguments",
            span,
        )),
    }
}

fn builtin_max_value_step(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    match args.first() {
        Some(Value::DiceExpr(expr)) => {
            let max_dice: i64 = expr
                .groups
                .iter()
                .map(|g| {
                    let effective = match g.filter {
                        Some(
                            ttrpg_ast::DiceFilter::KeepHighest(n)
                            | ttrpg_ast::DiceFilter::KeepLowest(n),
                        ) => n,
                        Some(
                            ttrpg_ast::DiceFilter::DropHighest(n)
                            | ttrpg_ast::DiceFilter::DropLowest(n),
                        ) => g.count.saturating_sub(n),
                        None => g.count,
                    };
                    (effective as i64) * (g.sides as i64)
                })
                .sum();
            Ok(Value::Int(max_dice + expr.modifier))
        }
        Some(other) => Err(RuntimeError::with_span(
            format!("max_value() expects DiceExpr, got {}", type_name(other)),
            span,
        )),
        None => Err(RuntimeError::with_span(
            "max_value() requires 1 argument",
            span,
        )),
    }
}

fn builtin_dice_count_step(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    match args.first() {
        Some(Value::DiceExpr(expr)) => Ok(Value::Int(expr.total_dice_count() as i64)),
        Some(other) => Err(RuntimeError::with_span(
            format!("dice_count() expects DiceExpr, got {}", type_name(other)),
            span,
        )),
        None => Err(RuntimeError::with_span(
            "dice_count() requires 1 argument",
            span,
        )),
    }
}

fn builtin_dice_sides_step(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    match args.first() {
        Some(Value::DiceExpr(expr)) => {
            if expr.groups.is_empty() {
                return Err(RuntimeError::with_span(
                    "dice_sides() called on dice expression with no dice groups",
                    span,
                ));
            }
            let sides = expr.groups[0].sides;
            for g in &expr.groups[1..] {
                if g.sides != sides {
                    return Err(RuntimeError::with_span(
                        format!(
                            "dice_sides() requires uniform die size, got d{} and d{}",
                            sides, g.sides
                        ),
                        span,
                    ));
                }
            }
            Ok(Value::Int(sides as i64))
        }
        Some(other) => Err(RuntimeError::with_span(
            format!("dice_sides() expects DiceExpr, got {}", type_name(other)),
            span,
        )),
        None => Err(RuntimeError::with_span(
            "dice_sides() requires 1 argument",
            span,
        )),
    }
}

fn builtin_dice_modifier_step(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    match args.first() {
        Some(Value::DiceExpr(expr)) => Ok(Value::Int(expr.modifier)),
        Some(other) => Err(RuntimeError::with_span(
            format!("dice_modifier() expects DiceExpr, got {}", type_name(other)),
            span,
        )),
        None => Err(RuntimeError::with_span(
            "dice_modifier() requires 1 argument",
            span,
        )),
    }
}

fn builtin_error_step(args: &[Value], span: Span) -> Result<Value, RuntimeError> {
    match args.first() {
        Some(Value::Str(message)) => Err(RuntimeError::with_span(message.clone(), span)),
        Some(other) => Err(RuntimeError::with_span(
            format!("error() expects String, got {}", type_name(other)),
            span,
        )),
        None => Err(RuntimeError::with_span("error() requires 1 argument", span)),
    }
}

fn builtin_game_time_step(
    args: &[Value],
    span: Span,
    sp: &dyn StateProvider,
) -> Result<Value, RuntimeError> {
    if !args.is_empty() {
        return Err(RuntimeError::with_span(
            format!("game_time() requires 0 arguments, got {}", args.len()),
            span,
        ));
    }
    Ok(Value::Int(sp.read_game_time() as i64))
}

fn builtin_budget_of_step(
    args: &[Value],
    span: Span,
    sp: &dyn StateProvider,
) -> Result<Value, RuntimeError> {
    match args.first() {
        Some(Value::Entity(eref)) => {
            let budget = sp.read_turn_budget(eref).ok_or_else(|| {
                RuntimeError::with_span(
                    format!("budget_of() called on unknown entity: {eref:?}"),
                    span,
                )
            })?;
            Ok(Value::Struct {
                name: Name::from("TurnBudget"),
                fields: budget,
            })
        }
        Some(other) => Err(RuntimeError::with_span(
            format!("budget_of() expects Entity, got {}", type_name(other)),
            span,
        )),
        None => Err(RuntimeError::with_span(
            "budget_of() requires 1 argument",
            span,
        )),
    }
}

fn builtin_is_suspended_step(
    args: &[Value],
    span: Span,
    sp: &dyn StateProvider,
) -> Result<Value, RuntimeError> {
    match args.first() {
        Some(Value::Entity(eref)) => Ok(Value::Bool(sp.is_suspended(eref))),
        Some(other) => Err(RuntimeError::with_span(
            format!("is_suspended() expects Entity, got {}", type_name(other)),
            span,
        )),
        None => Err(RuntimeError::with_span(
            "is_suspended() requires 1 argument",
            span,
        )),
    }
}

fn builtin_is_off_board_step(
    args: &[Value],
    span: Span,
    sp: &dyn StateProvider,
) -> Result<Value, RuntimeError> {
    match args.first() {
        Some(Value::Entity(eref)) => Ok(Value::Bool(sp.is_off_board(eref))),
        Some(other) => Err(RuntimeError::with_span(
            format!("is_off_board() expects Entity, got {}", type_name(other)),
            span,
        )),
        None => Err(RuntimeError::with_span(
            "is_off_board() requires 1 argument",
            span,
        )),
    }
}

fn builtin_are_turns_frozen_step(
    args: &[Value],
    span: Span,
    sp: &dyn StateProvider,
) -> Result<Value, RuntimeError> {
    match args.first() {
        Some(Value::Entity(eref)) => Ok(Value::Bool(sp.are_turns_frozen(eref))),
        Some(other) => Err(RuntimeError::with_span(
            format!(
                "are_turns_frozen() expects Entity, got {}",
                type_name(other)
            ),
            span,
        )),
        None => Err(RuntimeError::with_span(
            "are_turns_frozen() requires 1 argument",
            span,
        )),
    }
}

fn builtin_are_durations_frozen_step(
    args: &[Value],
    span: Span,
    sp: &dyn StateProvider,
) -> Result<Value, RuntimeError> {
    match args.first() {
        Some(Value::Entity(eref)) => Ok(Value::Bool(sp.are_durations_frozen(eref))),
        Some(other) => Err(RuntimeError::with_span(
            format!(
                "are_durations_frozen() expects Entity, got {}",
                type_name(other)
            ),
            span,
        )),
        None => Err(RuntimeError::with_span(
            "are_durations_frozen() requires 1 argument",
            span,
        )),
    }
}

// ── Effectful builtins (native implementations) ─────────────────

fn builtin_invocation_step(
    env: &ExecEnv,
    args: &[Value],
    span: Span,
) -> Result<Value, RuntimeError> {
    if !args.is_empty() {
        return Err(RuntimeError::with_span(
            "invocation() takes no arguments",
            span,
        ));
    }
    match env.current_invocation_id {
        Some(id) => Ok(Value::Invocation(id)),
        None => Err(RuntimeError::with_span(
            "invocation() called outside of action/reaction/hook scope",
            span,
        )),
    }
}

fn builtin_condition_token_step(
    env: &ExecEnv,
    args: &[Value],
    span: Span,
) -> Result<Value, RuntimeError> {
    if !args.is_empty() {
        return Err(RuntimeError::with_span(
            "condition_token() takes no arguments",
            span,
        ));
    }
    match env.current_condition_token {
        Some(token) => Ok(Value::Int(token.0 as i64)),
        None => Err(RuntimeError::with_span(
            "condition_token() requires an active condition token (only valid in lifecycle blocks)",
            span,
        )),
    }
}

fn builtin_advance_time_step(
    env: &ExecEnv,
    args: &[Value],
    span: Span,
    eh: &mut dyn EffectHandler,
) -> Result<Value, RuntimeError> {
    if env.current_invocation_id.is_some() {
        return Err(RuntimeError::with_span(
            "advance_time() cannot be called during action/reaction/hook execution",
            span,
        ));
    }
    match args.first() {
        Some(Value::Int(amount)) if *amount > 0 => {
            let effect = Effect::AdvanceTime {
                amount: *amount as u64,
            };
            validate_mutation_response(eh.handle(effect), "AdvanceTime", span)?;
            Ok(Value::Void)
        }
        Some(Value::Int(0)) => Err(RuntimeError::with_span(
            "advance_time() amount must be positive, got 0",
            span,
        )),
        Some(Value::Int(amount)) => Err(RuntimeError::with_span(
            format!("advance_time() amount must be positive, got {amount}"),
            span,
        )),
        Some(other) => Err(RuntimeError::with_span(
            format!("advance_time() expects Int, got {}", type_name(other)),
            span,
        )),
        None => Err(RuntimeError::with_span(
            "advance_time() requires 1 argument",
            span,
        )),
    }
}

fn builtin_despawn_step(
    args: &[Value],
    span: Span,
    eh: &mut dyn EffectHandler,
) -> Result<Value, RuntimeError> {
    match args.first() {
        Some(Value::Entity(entity)) => {
            let effect = Effect::RemoveEntity { entity: *entity };
            validate_mutation_response(eh.handle(effect), "RemoveEntity", span)?;
            Ok(Value::Void)
        }
        Some(other) => Err(RuntimeError::with_span(
            format!("despawn() expects entity, got {}", type_name(other)),
            span,
        )),
        None => Err(RuntimeError::with_span(
            "despawn() requires 1 argument",
            span,
        )),
    }
}

fn parse_presence_step(val: &Value, span: Span) -> Result<crate::state::Presence, RuntimeError> {
    match val {
        Value::EnumVariant {
            enum_name, variant, ..
        } if enum_name == "Presence" => match variant.as_str() {
            "OnMap" => Ok(crate::state::Presence::OnMap),
            "OffBoard" => Ok(crate::state::Presence::OffBoard),
            _ => Err(RuntimeError::with_span(
                format!("unknown Presence variant '{variant}'"),
                span,
            )),
        },
        _ => Err(RuntimeError::with_span(
            format!("expected Presence enum, got {}", type_name(val)),
            span,
        )),
    }
}

fn builtin_suspend_step(
    env: &ExecEnv,
    args: &[Value],
    span: Span,
    eh: &mut dyn EffectHandler,
) -> Result<Value, RuntimeError> {
    if env.in_lifecycle_block == 0 {
        return Err(RuntimeError::with_span(
            "suspend() can only be called inside on_apply/on_remove blocks. \
             Use suspend_with_source() for explicit source keying outside lifecycle blocks.",
            span,
        ));
    }
    let token = env.current_condition_token.ok_or_else(|| {
        RuntimeError::with_span(
            "suspend() requires a condition token (no condition being applied/removed)",
            span,
        )
    })?;
    match (args.first(), args.get(1), args.get(2), args.get(3)) {
        (
            Some(Value::Entity(entity)),
            Some(presence_val),
            Some(Value::Bool(freeze_turns)),
            Some(Value::Bool(freeze_durations)),
        ) => {
            let presence = parse_presence_step(presence_val, span)?;
            let effect = Effect::AddSuspension {
                entity: *entity,
                source_id: token.0,
                presence,
                freeze_turns: *freeze_turns,
                freeze_durations: *freeze_durations,
            };
            validate_mutation_response(eh.handle(effect), "AddSuspension", span)?;
            Ok(Value::Void)
        }
        _ => Err(RuntimeError::with_span(
            "suspend() requires 4 arguments: (entity, Presence, bool, bool)",
            span,
        )),
    }
}

fn builtin_suspend_with_source_step(
    args: &[Value],
    span: Span,
    eh: &mut dyn EffectHandler,
) -> Result<Value, RuntimeError> {
    match (
        args.first(),
        args.get(1),
        args.get(2),
        args.get(3),
        args.get(4),
    ) {
        (
            Some(Value::Entity(entity)),
            Some(Value::Int(source_id)),
            Some(presence_val),
            Some(Value::Bool(freeze_turns)),
            Some(Value::Bool(freeze_durations)),
        ) if *source_id >= 0 => {
            let presence = parse_presence_step(presence_val, span)?;
            let effect = Effect::AddSuspension {
                entity: *entity,
                source_id: *source_id as u64,
                presence,
                freeze_turns: *freeze_turns,
                freeze_durations: *freeze_durations,
            };
            validate_mutation_response(eh.handle(effect), "AddSuspension", span)?;
            Ok(Value::Void)
        }
        _ => Err(RuntimeError::with_span(
            "suspend_with_source() requires 5 arguments: (entity, int, Presence, bool, bool)",
            span,
        )),
    }
}

fn builtin_remove_suspension_source_step(
    args: &[Value],
    span: Span,
    eh: &mut dyn EffectHandler,
) -> Result<Value, RuntimeError> {
    match (args.first(), args.get(1)) {
        (Some(Value::Entity(entity)), Some(Value::Int(source_id))) if *source_id >= 0 => {
            let effect = Effect::RemoveSuspensionSource {
                entity: *entity,
                source_id: *source_id as u64,
            };
            validate_mutation_response(eh.handle(effect), "RemoveSuspensionSource", span)?;
            Ok(Value::Void)
        }
        _ => Err(RuntimeError::with_span(
            "remove_suspension_source() requires 2 arguments: (entity, int)",
            span,
        )),
    }
}

fn builtin_transfer_conditions_step(
    env: &ExecEnv,
    args: &[Value],
    span: Span,
    core: &RuntimeCore,
    eh: &mut dyn EffectHandler,
) -> Result<Value, RuntimeError> {
    let (from, to, tag) = match (args.first(), args.get(1), args.get(2)) {
        (Some(Value::Entity(from)), Some(Value::Entity(to)), Some(Value::Str(tag))) => {
            (*from, *to, tag.clone())
        }
        _ => {
            return Err(RuntimeError::with_span(
                "transfer_conditions() requires (entity, entity, string)",
                span,
            ));
        }
    };

    if !core.program.tags.contains(tag.as_str()) {
        return Err(RuntimeError::with_span(
            format!(
                "transfer_conditions: unknown tag `{tag}` — \
                 no `tag {tag}` declaration found in the program"
            ),
            span,
        ));
    }

    let exclude_instance = env.lifecycle_condition_stack.last().copied();
    let effect = Effect::TransferConditions {
        from,
        to,
        tag: Name::from(tag.as_str()),
        exclude_instance,
    };
    validate_mutation_response(eh.handle(effect), "TransferConditions", span)?;
    Ok(Value::Void)
}

/// Validate a response to a mutation effect.
fn validate_mutation_response(
    response: Response,
    effect_name: &str,
    span: Span,
) -> Result<(), RuntimeError> {
    match response {
        Response::Acknowledged | Response::Override(_) | Response::Vetoed => Ok(()),
        _ => Err(RuntimeError::with_span(
            format!("protocol error: unsupported response for {effect_name}: {response:?}"),
            span,
        )),
    }
}

/// Run a complex lifecycle builtin (apply_condition, remove_condition, revoke)
/// by constructing a synthetic call expression and evaluating it via a
/// ResumableBridge frame. This avoids a direct bridge_call_builtin call from
/// expr_eval.rs while preserving full lifecycle semantics.
fn run_builtin_via_frame(
    name: &str,
    args: Vec<Value>,
    span: Span,
    core: &RuntimeCore,
    env: &mut ExecEnv,
    sp: &dyn StateProvider,
    eh: &mut dyn EffectHandler,
) -> Result<Value, RuntimeError> {
    use ttrpg_ast::ast::Arg;

    // Build synthetic literal arguments from pre-evaluated values
    let ast_args: Vec<Arg> = args
        .iter()
        .map(|val| Arg {
            name: None,
            value: Spanned {
                node: value_to_expr(val),
                span,
            },
            span,
        })
        .collect();

    let callee_expr = Spanned {
        node: ExprKind::Ident(Name::from(name)),
        span,
    };
    let call_expr = Spanned {
        node: ExprKind::Call {
            callee: Box::new(callee_expr),
            args: ast_args,
        },
        span,
    };

    let work = compile_expr(&call_expr, &core.type_env, &core.program)
        .unwrap_or_else(|| panic!(
            "compile_expr failed for builtin '{name}' at {span:?} — ResumableBridge fallback removed (Phase 7)",
        ));
    let frame = Frame::ExprEval {
        work,
        operands: Vec::new(),
        pc: 0,
        child_result: None,
        scope_depth: 0,
    };
    crate::execution::run_frame_to_completion_sync(frame, core, env, sp, eh)
}

// ── Is-check implementation ─────────────────────────────────────

fn eval_is_check(
    val: &Value,
    target_type: &Spanned<TypeExpr>,
    _span: Span,
    _core: &RuntimeCore,
    sp: &dyn StateProvider,
) -> bool {
    value_matches_type_step(val, &target_type.node, sp)
}

/// Step-compatible version of `value_matches_type` from dispatch.rs.
fn value_matches_type_step(val: &Value, ty: &TypeExpr, sp: &dyn StateProvider) -> bool {
    match (val, ty) {
        // Primitives
        (Value::Int(_), TypeExpr::Int) => true,
        (Value::Float(_), TypeExpr::Float) => true,
        (Value::Bool(_), TypeExpr::Bool) => true,
        (Value::Str(_), TypeExpr::String) => true,
        // Dice
        (Value::DiceExpr(_), TypeExpr::DiceExpr) => true,
        (Value::RollResult(_), TypeExpr::RollResult) => true,
        // Entity types
        (Value::Entity(eref), TypeExpr::Named(name)) => {
            if name == "entity" {
                true
            } else {
                sp.entity_type_name(eref)
                    .is_some_and(|actual| actual.as_ref() == name.as_ref())
            }
        }
        // Structs
        (Value::Struct { name: sname, .. }, TypeExpr::Named(name)) => {
            sname.as_ref() == name.as_ref()
        }
        // Enums
        (Value::EnumVariant { enum_name, .. }, TypeExpr::Named(name)) => {
            enum_name.as_ref() == name.as_ref()
        }
        // Containers with element type checking
        (Value::List(items), TypeExpr::List(inner)) => items
            .iter()
            .all(|item| value_matches_type_step(item, &inner.node, sp)),
        (Value::Set(items), TypeExpr::Set(inner)) => items
            .iter()
            .all(|item| value_matches_type_step(item, &inner.node, sp)),
        (Value::Map(entries), TypeExpr::Map(kt, vt)) => entries.iter().all(|(k, v)| {
            value_matches_type_step(k, &kt.node, sp) && value_matches_type_step(v, &vt.node, sp)
        }),
        (Value::Option(inner), TypeExpr::OptionType(inner_ty)) => match inner {
            Some(v) => value_matches_type_step(v, &inner_ty.node, sp),
            None => true,
        },
        (Value::Void, TypeExpr::OptionType(_)) => true,
        // Opaque built-in types
        (Value::Condition { .. }, TypeExpr::Condition) => true,
        (
            Value::Struct {
                name: sname,
                fields,
            },
            TypeExpr::TypedActiveCondition(cond_name),
        ) if sname.as_ref() == "ActiveCondition" => {
            matches!(fields.get(&Name::from("name")), Some(Value::Str(n)) if n == cond_name.as_ref())
        }
        (Value::Position(_), TypeExpr::Position) => true,
        (Value::Direction(_), TypeExpr::Direction) => true,
        (Value::Invocation(_), TypeExpr::Invocation) => true,
        _ => false,
    }
}

// ── Inline step evaluator ──────────────────────────────────────

/// Evaluate an expression using the step-based ExprEval machinery.
///
/// Tries to compile the expression into ExprWork instructions and run them
/// inline. If the expression can't be compiled, falls back to a
/// ResumableBridge frame. Child frames (DeriveEval, FunctionEval, etc.)
/// and host effects (dice rolls, prompts) are handled by running the
/// frame to completion synchronously via `run_frame_to_completion_sync`.
pub(crate) fn eval_expr_step(
    core: &RuntimeCore,
    env: &mut ExecEnv,
    sp: &dyn StateProvider,
    eh: &mut dyn EffectHandler,
    expr: &Spanned<ExprKind>,
) -> Result<Value, RuntimeError> {
    // Try fast inline path first: compile + step without frame overhead
    if let Some(ref work) = compile_expr(expr, &core.type_env, &core.program) {
        let mut operands = Vec::new();
        let mut pc = 0;
        let mut child_result = None;
        let mut scope_depth = 0;
        loop {
            match advance_expr_eval(
                work,
                &mut operands,
                &mut pc,
                &mut child_result,
                &mut scope_depth,
                core,
                env,
                sp,
                eh,
            ) {
                Advance::Pop(val) => return Ok(val),
                Advance::Continue => {}
                Advance::Error(e) => return Err(e),
                Advance::Push(child_frame) => {
                    // Run the child frame synchronously, then feed result back
                    match crate::execution::run_frame_to_completion_sync(
                        child_frame,
                        core,
                        env,
                        sp,
                        eh,
                    ) {
                        Ok(val) => {
                            child_result = Some(Ok(val));
                        }
                        Err(e) => {
                            child_result = Some(Err(e));
                        }
                    }
                }
                Advance::Yield(effect) => {
                    // Forward the effect to the handler (e.g., dice roll, mutation)
                    let _response = eh.handle(effect);
                    // ExprEval itself doesn't yield — this shouldn't occur.
                    // If it does, it means a work item emitted a yield directly,
                    // which is a bug. Continue and let the next step handle it.
                }
            }
        }
    }
    // Fallback removed (Phase 7) — compile_expr should handle all expressions.
    panic!(
        "compile_expr failed at {:?} — ResumableBridge fallback removed (Phase 7)",
        expr.span,
    )
}
