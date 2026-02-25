//! Move lowering: transforms `MoveDecl` nodes into canonical
//! `FnDecl` (mechanic) + `ActionDecl` pairs.
//!
//! Runs after parsing but **before** type-checking. The synthesized
//! declarations are validated by the checker naturally.

use std::collections::HashSet;

use ttrpg_ast::ast::*;
use ttrpg_ast::diagnostic::Diagnostic;
use ttrpg_ast::name::Name;
use ttrpg_ast::Span;
use ttrpg_ast::Spanned;

const VALID_OUTCOMES: &[&str] = &["strong_hit", "weak_hit", "miss"];

/// Lower all `MoveDecl` nodes in a program into mechanic + action pairs.
///
/// Malformed moves are skipped (left as `DeclKind::Move` for the checker
/// to catch). Lowering errors are accumulated into `diags`.
pub fn lower_moves(mut program: Program, diags: &mut Vec<Diagnostic>) -> Program {
    for item in &mut program.items {
        if let TopLevel::System(system) = &mut item.node {
            lower_system_moves(system, diags);
        }
    }
    program.build_index();
    program
}

fn lower_system_moves(system: &mut SystemBlock, diags: &mut Vec<Diagnostic>) {
    // Collect synthetic names used by moves in this block to detect collisions.
    let mut synthetic_names: HashSet<Name> = HashSet::new();

    // Also collect existing declaration names to check for collisions.
    let existing_names: HashSet<Name> = system
        .decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Derive(f) | DeclKind::Mechanic(f) => Some(f.name.clone()),
            DeclKind::Action(a) => Some(a.name.clone()),
            DeclKind::Reaction(r) => Some(r.name.clone()),
            DeclKind::Prompt(p) => Some(p.name.clone()),
            DeclKind::Table(t) => Some(t.name.clone()),
            DeclKind::Hook(h) => Some(h.name.clone()),
            _ => None,
        })
        .collect();

    let mut new_decls: Vec<Spanned<DeclKind>> = Vec::with_capacity(system.decls.len());

    for decl in std::mem::take(&mut system.decls) {
        if let DeclKind::Move(ref m) = decl.node {
            let span = decl.span;
            match lower_one_move(m, span, &existing_names, &mut synthetic_names, diags) {
                Some((mechanic_decl, action_decl)) => {
                    new_decls.push(Spanned::new(DeclKind::Mechanic(mechanic_decl), span));
                    new_decls.push(Spanned::new(DeclKind::Action(action_decl), span));
                }
                None => {
                    // Malformed move — leave as DeclKind::Move for the checker to catch
                    new_decls.push(decl);
                }
            }
        } else {
            new_decls.push(decl);
        }
    }

    system.decls = new_decls;
}

/// Convert a move name to its synthetic mechanic name: `__{snake_case}_roll`.
fn synthetic_mechanic_name(move_name: &str) -> Name {
    let mut snake = String::new();
    for (i, ch) in move_name.chars().enumerate() {
        if ch.is_uppercase() && i > 0 {
            snake.push('_');
        }
        snake.push(ch.to_lowercase().next().unwrap_or(ch));
    }
    Name::from(format!("__{}_roll", snake))
}

fn lower_one_move(
    m: &MoveDecl,
    span: Span,
    existing_names: &HashSet<Name>,
    synthetic_names: &mut HashSet<Name>,
    diags: &mut Vec<Diagnostic>,
) -> Option<(FnDecl, ActionDecl)> {
    // 1. Validate outcomes: must be exactly {strong_hit, weak_hit, miss}
    let outcome_names: Vec<&str> = m.outcomes.iter().map(|o| o.name.as_str()).collect();
    let mut seen = HashSet::new();
    let mut has_error = false;

    for outcome in &m.outcomes {
        if !VALID_OUTCOMES.contains(&outcome.name.as_str()) {
            diags.push(Diagnostic::error(
                format!(
                    "move `{}` has invalid outcome `{}`; expected one of: strong_hit, weak_hit, miss",
                    m.name, outcome.name
                ),
                outcome.span,
            ));
            has_error = true;
        }
        if !seen.insert(outcome.name.as_str()) {
            diags.push(Diagnostic::error(
                format!(
                    "move `{}` has duplicate outcome `{}`",
                    m.name, outcome.name
                ),
                outcome.span,
            ));
            has_error = true;
        }
    }

    for &expected in VALID_OUTCOMES {
        if !outcome_names.contains(&expected) {
            diags.push(Diagnostic::error(
                format!(
                    "move `{}` is missing required outcome `{}`",
                    m.name, expected
                ),
                span,
            ));
            has_error = true;
        }
    }

    if has_error {
        return None;
    }

    // 2. Check for parameter names that conflict with synthesized names
    const RESERVED_NAMES: &[&str] = &["roll", "result"];
    for reserved in RESERVED_NAMES {
        if m.receiver_name == *reserved {
            diags.push(Diagnostic::error(
                format!(
                    "move `{}` receiver '{}' conflicts with synthesized name used in lowering",
                    m.name, reserved
                ),
                span,
            ));
            return None;
        }
        for p in &m.params {
            if p.name == *reserved {
                diags.push(Diagnostic::error(
                    format!(
                        "move `{}` parameter '{}' conflicts with synthesized name used in lowering",
                        m.name, reserved
                    ),
                    span,
                ),
                );
                return None;
            }
        }
    }

    // 3. Check for synthetic name collision
    let mechanic_name = synthetic_mechanic_name(&m.name);
    if existing_names.contains(&mechanic_name) {
        diags.push(Diagnostic::error(
            format!(
                "move `{}` generates synthetic mechanic `{}` which collides with an existing declaration",
                m.name, mechanic_name
            ),
            span,
        ));
        return None;
    }
    if !synthetic_names.insert(mechanic_name.clone()) {
        diags.push(Diagnostic::error(
            format!(
                "move `{}` generates synthetic mechanic `{}` which collides with another move's synthetic name",
                m.name, mechanic_name
            ),
            span,
        ));
        return None;
    }

    // 4. Synthesize mechanic FnDecl
    // Parameters: receiver + all move params
    let mut mechanic_params = vec![Param {
        name: m.receiver_name.clone(),
        ty: m.receiver_type.clone(),
        default: None,
        with_groups: vec![],
        span,
    }];
    mechanic_params.extend(m.params.iter().cloned());

    // Body: roll(m.roll_expr)
    let roll_call = Spanned::new(
        ExprKind::Call {
            callee: Box::new(Spanned::new(ExprKind::Ident("roll".into()), span)),
            args: vec![Arg {
                name: None,
                value: m.roll_expr.clone(),
                span,
            }],
        },
        span,
    );

    let mechanic_body: Block = Spanned::new(
        vec![Spanned::new(StmtKind::Expr(roll_call), span)],
        span,
    );

    let mechanic = FnDecl {
        name: mechanic_name.clone(),
        params: mechanic_params,
        return_type: Spanned::new(TypeExpr::RollResult, span),
        body: mechanic_body,
        synthetic: true,
    };

    // 5. Synthesize action
    // Build the resolve block:
    //   let result = __move_roll(receiver, param1, param2, ...)
    //   match {
    //     result >= 10 => { strong_hit body },
    //     result >= 7  => { weak_hit body },
    //     _            => { miss body },
    //   }

    // Build call args: receiver + all move params, forwarding by name
    let mut call_args = vec![Arg {
        name: None,
        value: Spanned::new(ExprKind::Ident(m.receiver_name.clone()), span),
        span,
    }];
    for p in &m.params {
        call_args.push(Arg {
            name: None,
            value: Spanned::new(ExprKind::Ident(p.name.clone()), span),
            span,
        });
    }

    let mechanic_call = Spanned::new(
        ExprKind::Call {
            callee: Box::new(Spanned::new(ExprKind::Ident(mechanic_name), span)),
            args: call_args,
        },
        span,
    );

    let let_result = Spanned::new(
        StmtKind::Let {
            name: "result".into(),
            ty: None,
            value: mechanic_call,
        },
        span,
    );

    // Find outcome bodies by name (validated above; `?` is defensive)
    let strong_hit_body = m
        .outcomes
        .iter()
        .find(|o| o.name == "strong_hit")?
        .body
        .clone();
    let weak_hit_body = m
        .outcomes
        .iter()
        .find(|o| o.name == "weak_hit")?
        .body
        .clone();
    let miss_body = m
        .outcomes
        .iter()
        .find(|o| o.name == "miss")?
        .body
        .clone();

    // Build guard match arms:
    //   result >= 10 => { strong_hit },
    //   result >= 7  => { weak_hit },
    //   _            => { miss },
    let result_ident = || Spanned::new(ExprKind::Ident("result".into()), span);

    let guard_arm = |threshold: i64, body: Block| -> GuardArm {
        GuardArm {
            guard: GuardKind::Expr(Spanned::new(
                ExprKind::BinOp {
                    op: BinOp::GtEq,
                    lhs: Box::new(result_ident()),
                    rhs: Box::new(Spanned::new(ExprKind::IntLit(threshold), span)),
                },
                span,
            )),
            body: ArmBody::Block(body),
            span,
        }
    };

    let miss_arm = GuardArm {
        guard: GuardKind::Wildcard,
        body: ArmBody::Block(miss_body),
        span,
    };

    let guard_match = Spanned::new(
        ExprKind::GuardMatch {
            arms: vec![
                guard_arm(10, strong_hit_body),
                guard_arm(7, weak_hit_body),
                miss_arm,
            ],
        },
        span,
    );

    let guard_match_stmt = Spanned::new(StmtKind::Expr(guard_match), span);

    let resolve: Block = Spanned::new(vec![let_result, guard_match_stmt], span);

    // Cost: { action }
    let cost = CostClause {
        tokens: vec![Spanned::new("action".into(), span)],
        span,
    };

    let action = ActionDecl {
        name: m.name.clone(),
        receiver_name: m.receiver_name.clone(),
        receiver_type: m.receiver_type.clone(),
        receiver_with_groups: vec![],
        params: m.params.clone(),
        cost: Some(cost),
        requires: None,
        resolve,
        trigger_text: Some(m.trigger_text.clone()),
        synthetic: true,
    };

    Some((mechanic, action))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_synthetic_mechanic_name() {
        assert_eq!(synthetic_mechanic_name("GoAggro"), "__go_aggro_roll");
        assert_eq!(synthetic_mechanic_name("Attack"), "__attack_roll");
        assert_eq!(synthetic_mechanic_name("HackAndSlash"), "__hack_and_slash_roll");
    }

    // ── Regression: tdsl-t4c — synthetic mechanic collision includes table/hook ──

    #[test]
    fn existing_names_includes_tables_and_hooks() {
        use ttrpg_ast::ast::*;
        use ttrpg_ast::Spanned;

        let dummy_span = ttrpg_ast::Span::dummy();

        let table_decl = Spanned::new(
            DeclKind::Table(TableDecl {
                name: "__attack_roll".into(),
                params: vec![],
                return_type: Spanned::new(TypeExpr::Named("int".into()), dummy_span),
                entries: vec![],
            }),
            dummy_span,
        );

        let hook_decl = Spanned::new(
            DeclKind::Hook(HookDecl {
                name: "__defend_roll".into(),
                receiver_name: "e".into(),
                receiver_type: Spanned::new(TypeExpr::Named("Character".into()), dummy_span),
                receiver_with_groups: vec![],
                trigger: TriggerExpr {
                    event_name: "test".into(),
                    bindings: vec![],
                    span: dummy_span,
                },
                resolve: Spanned::new(vec![], dummy_span),
            }),
            dummy_span,
        );

        let system = SystemBlock {
            name: "test".into(),
            decls: vec![table_decl, hook_decl],
        };

        let existing: std::collections::HashSet<Name> = system
            .decls
            .iter()
            .filter_map(|d| match &d.node {
                DeclKind::Derive(f) | DeclKind::Mechanic(f) => Some(f.name.clone()),
                DeclKind::Action(a) => Some(a.name.clone()),
                DeclKind::Reaction(r) => Some(r.name.clone()),
                DeclKind::Prompt(p) => Some(p.name.clone()),
                DeclKind::Table(t) => Some(t.name.clone()),
                DeclKind::Hook(h) => Some(h.name.clone()),
                _ => None,
            })
            .collect();

        assert!(existing.contains("__attack_roll"), "table name should be in existing_names");
        assert!(existing.contains("__defend_roll"), "hook name should be in existing_names");
    }
}
