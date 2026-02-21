use std::collections::BTreeMap;

use ttrpg_ast::Span;
use ttrpg_ast::Spanned;
use ttrpg_ast::ast::{Arg, ExprKind, Param};
use ttrpg_checker::env::{DeclInfo, FnKind, ParamInfo};

use crate::Env;
use crate::RuntimeError;
use crate::builtins::call_builtin;
use crate::effect::{Effect, Response};
use crate::eval::{eval_block, eval_expr};
use crate::value::Value;

// ── Call dispatch ───────────────────────────────────────────────

/// Evaluate a function call expression.
///
/// Resolves the callee syntactically (function names are not first-class),
/// dispatches based on `FnKind`, and handles enum variant construction.
pub(crate) fn eval_call(
    env: &mut Env,
    callee: &Spanned<ExprKind>,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    match &callee.node {
        // ── Simple identifier: function name or bare enum variant ──
        ExprKind::Ident(name) => {
            // 1. Check if it's a function (user-defined or builtin)
            if let Some(fn_info) = env.interp.type_env.lookup_fn(name) {
                let fn_info = fn_info.clone();
                return dispatch_fn(env, &fn_info, args, call_span);
            }

            // 2. Check if it's a bare enum variant with fields (via variant_to_enum)
            if let Some(enum_name) = env.interp.type_env.variant_to_enum.get(name.as_str()) {
                let enum_name = enum_name.clone();
                return construct_enum_variant(env, &enum_name, name, args, call_span);
            }

            Err(RuntimeError::with_span(
                format!("undefined function '{}'", name),
                call_span,
            ))
        }

        // ── Qualified access: enum constructor (e.g. Duration.rounds(3)) ──
        ExprKind::FieldAccess { object, field } => {
            if let ExprKind::Ident(type_name) = &object.node {
                if let Some(DeclInfo::Enum(_)) =
                    env.interp.type_env.types.get(type_name.as_str())
                {
                    return construct_enum_variant(
                        env, type_name, field, args, call_span,
                    );
                }
            }
            Err(RuntimeError::with_span(
                "invalid callee: only function names and enum constructors can be called",
                call_span,
            ))
        }

        _ => Err(RuntimeError::with_span(
            "invalid callee expression",
            call_span,
        )),
    }
}

// ── Function dispatch by kind ──────────────────────────────────

fn dispatch_fn(
    env: &mut Env,
    fn_info: &ttrpg_checker::env::FnInfo,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    match fn_info.kind {
        FnKind::Derive => dispatch_derive_or_mechanic(env, &fn_info.name, args, call_span),
        FnKind::Mechanic => dispatch_derive_or_mechanic(env, &fn_info.name, args, call_span),
        FnKind::Prompt => dispatch_prompt(env, &fn_info.name, args, call_span),
        FnKind::Builtin => {
            // Builtins have no defaults — all params are required
            let bound = bind_args(&fn_info.params, args, None, env, call_span)?;
            let arg_values: Vec<Value> = bound.into_iter().map(|(_, v)| v).collect();
            call_builtin(env, &fn_info.name, arg_values, call_span)
        }
        FnKind::Action => {
            // Action calls from DSL code: dispatched through execute_action (Phase 5).
            // For now, stub — real dispatch comes in Phase 5.
            Err(RuntimeError::with_span(
                "action calls are not yet implemented (Phase 5)",
                call_span,
            ))
        }
        FnKind::Reaction => {
            // The checker rejects direct reaction calls; this is unreachable.
            Err(RuntimeError::with_span(
                "internal error: reactions cannot be called directly",
                call_span,
            ))
        }
    }
}

// ── Derive / Mechanic dispatch ─────────────────────────────────

fn dispatch_derive_or_mechanic(
    env: &mut Env,
    name: &str,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    // Look up the declaration in DeclIndex
    let fn_decl = env
        .interp
        .index
        .derives
        .get(name)
        .or_else(|| env.interp.index.mechanics.get(name))
        .ok_or_else(|| {
            RuntimeError::with_span(
                format!("internal error: no declaration found for function '{}'", name),
                call_span,
            )
        })?;

    // Clone what we need from the declaration before mutably borrowing env
    let ast_params = fn_decl.params.clone();
    let body = fn_decl.body.clone();

    // Get the FnInfo for parameter type info
    let fn_info = env
        .interp
        .type_env
        .lookup_fn(name)
        .ok_or_else(|| {
            RuntimeError::with_span(
                format!("internal error: no type info for function '{}'", name),
                call_span,
            )
        })?
        .clone();

    // Bind arguments (with access to AST params for default expressions)
    let bound = bind_args(&fn_info.params, args, Some(&ast_params), env, call_span)?;

    // Push scope and bind parameters
    // Note: modify pipeline (Phase 6) will wrap Phase 1 / Phase 2 around body execution.
    // For now we execute the body directly.
    env.push_scope();
    for (param_name, param_val) in bound {
        env.bind(param_name, param_val);
    }

    let result = eval_block(env, &body);
    env.pop_scope();

    result
}

// ── Prompt dispatch ────────────────────────────────────────────

fn dispatch_prompt(
    env: &mut Env,
    name: &str,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    let prompt_decl = env
        .interp
        .index
        .prompts
        .get(name)
        .ok_or_else(|| {
            RuntimeError::with_span(
                format!("internal error: no declaration found for prompt '{}'", name),
                call_span,
            )
        })?;

    let hint = prompt_decl.hint.clone();
    let suggest_expr = prompt_decl.suggest.clone();
    let ast_params = prompt_decl.params.clone();

    // Get the FnInfo for parameter info
    let fn_info = env
        .interp
        .type_env
        .lookup_fn(name)
        .ok_or_else(|| {
            RuntimeError::with_span(
                format!("internal error: no type info for prompt '{}'", name),
                call_span,
            )
        })?
        .clone();

    // Bind arguments
    let bound = bind_args(&fn_info.params, args, Some(&ast_params), env, call_span)?;
    let param_values: Vec<Value> = bound.iter().map(|(_, v)| v.clone()).collect();

    // Evaluate suggest expression if present
    let suggest = match &suggest_expr {
        Some(expr) => {
            // Push scope with params for suggest evaluation
            env.push_scope();
            for (pn, pv) in &bound {
                env.bind(pn.clone(), pv.clone());
            }
            let val = eval_expr(env, expr)?;
            env.pop_scope();
            Some(val)
        }
        None => None,
    };

    // Emit ResolvePrompt effect
    let effect = Effect::ResolvePrompt {
        name: name.to_string(),
        params: param_values,
        hint,
        suggest,
    };
    let response = env.handler.handle(effect);

    match response {
        Response::PromptResult(val) => Ok(val),
        _ => Err(RuntimeError::with_span(
            format!(
                "protocol error: expected PromptResult response for ResolvePrompt, got {:?}",
                response
            ),
            call_span,
        )),
    }
}

// ── Enum variant construction ──────────────────────────────────

fn construct_enum_variant(
    env: &mut Env,
    enum_name: &str,
    variant_name: &str,
    args: &[Arg],
    call_span: Span,
) -> Result<Value, RuntimeError> {
    let enum_info = match env.interp.type_env.types.get(enum_name) {
        Some(DeclInfo::Enum(info)) => info.clone(),
        _ => {
            return Err(RuntimeError::with_span(
                format!("internal error: '{}' is not an enum", enum_name),
                call_span,
            ));
        }
    };

    let variant_info = enum_info
        .variants
        .iter()
        .find(|v| v.name == variant_name)
        .ok_or_else(|| {
            RuntimeError::with_span(
                format!("enum '{}' has no variant '{}'", enum_name, variant_name),
                call_span,
            )
        })?;

    if variant_info.fields.is_empty() && args.is_empty() {
        return Ok(Value::EnumVariant {
            enum_name: enum_name.to_string(),
            variant: variant_name.to_string(),
            fields: BTreeMap::new(),
        });
    }

    // Build ParamInfo from variant fields for bind_args (no defaults for enum fields)
    let param_infos: Vec<ParamInfo> = variant_info
        .fields
        .iter()
        .map(|(name, ty)| ParamInfo {
            name: name.clone(),
            ty: ty.clone(),
            has_default: false,
        })
        .collect();

    let bound = bind_args(&param_infos, args, None, env, call_span)?;

    let mut fields = BTreeMap::new();
    for (name, val) in bound {
        fields.insert(name, val);
    }

    Ok(Value::EnumVariant {
        enum_name: enum_name.to_string(),
        variant: variant_name.to_string(),
        fields,
    })
}

// ── Argument binding ───────────────────────────────────────────

/// Match call arguments to function parameters.
///
/// `ast_params` provides the AST parameter declarations (with default expressions)
/// when available. For builtins and enum constructors, this is `None`.
///
/// Returns a list of (param_name, value) pairs in parameter declaration order.
fn bind_args(
    params: &[ParamInfo],
    args: &[Arg],
    ast_params: Option<&[Param]>,
    env: &mut Env,
    call_span: Span,
) -> Result<Vec<(String, Value)>, RuntimeError> {
    let mut result: Vec<Option<Value>> = vec![None; params.len()];
    let mut used_positions = vec![false; params.len()];

    // Pass 1: Bind named arguments
    for arg in args {
        if let Some(ref name) = arg.name {
            let pos = params
                .iter()
                .position(|p| p.name == *name)
                .ok_or_else(|| {
                    RuntimeError::with_span(
                        format!("unknown parameter '{}'", name),
                        arg.span,
                    )
                })?;
            if result[pos].is_some() {
                return Err(RuntimeError::with_span(
                    format!("duplicate argument for parameter '{}'", name),
                    arg.span,
                ));
            }
            let val = eval_expr(env, &arg.value)?;
            result[pos] = Some(val);
            used_positions[pos] = true;
        }
    }

    // Pass 2: Bind positional arguments (fill unclaimed slots left-to-right)
    let mut pos_iter = (0..params.len()).filter(|i| !used_positions[*i]);
    for arg in args {
        if arg.name.is_none() {
            let pos = pos_iter.next().ok_or_else(|| {
                RuntimeError::with_span("too many positional arguments", arg.span)
            })?;
            let val = eval_expr(env, &arg.value)?;
            result[pos] = Some(val);
        }
    }

    // Pass 3: Fill defaults for unbound optional params
    let mut bound = Vec::with_capacity(params.len());
    for (i, param) in params.iter().enumerate() {
        match result[i].take() {
            Some(val) => bound.push((param.name.clone(), val)),
            None => {
                if param.has_default {
                    // Look up the default expression from the AST params
                    let default_val = if let Some(ast_ps) = ast_params {
                        if let Some(ast_param) = ast_ps.get(i) {
                            if let Some(ref default_expr) = ast_param.default {
                                eval_expr(env, default_expr)?
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
                        return Err(RuntimeError::with_span(
                            format!(
                                "internal error: no AST params available to evaluate default for '{}'",
                                param.name
                            ),
                            call_span,
                        ));
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

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::{BTreeMap, HashMap};

    use ttrpg_ast::Span;
    use ttrpg_ast::ast::*;
    use ttrpg_checker::env::{
        EnumInfo, FnInfo, FnKind, ParamInfo, TypeEnv, VariantInfo,
    };
    use ttrpg_checker::ty::Ty;

    use crate::effect::{Effect, EffectHandler, Response};
    use crate::state::{ActiveCondition, EntityRef, StateProvider};
    use crate::value::{DiceExpr, DurationValue, PositionValue, RollResult};
    use crate::Interpreter;

    // ── Test infrastructure ────────────────────────────────────

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
        fn position_eq(&self, a: &Value, b: &Value) -> bool {
            if let (Value::Position(pa), Value::Position(pb)) = (a, b) {
                if let (Some(a), Some(b)) = (
                    pa.0.downcast_ref::<(i64, i64)>(),
                    pb.0.downcast_ref::<(i64, i64)>(),
                ) {
                    return a == b;
                }
            }
            false
        }
        fn distance(&self, a: &Value, b: &Value) -> Option<i64> {
            if let (Value::Position(pa), Value::Position(pb)) = (a, b) {
                if let (Some(a), Some(b)) = (
                    pa.0.downcast_ref::<(i64, i64)>(),
                    pb.0.downcast_ref::<(i64, i64)>(),
                ) {
                    return Some(((a.0 - b.0).abs()).max((a.1 - b.1).abs()));
                }
            }
            None
        }
    }

    fn dummy_span() -> Span {
        Span::dummy()
    }

    fn spanned<T>(node: T) -> Spanned<T> {
        Spanned::new(node, dummy_span())
    }

    fn make_env<'a, 'p>(
        state: &'a TestState,
        handler: &'a mut ScriptedHandler,
        interp: &'a Interpreter<'p>,
    ) -> Env<'a, 'p> {
        Env::new(state, handler, interp)
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

    /// Build a type env with builtins registered.
    fn type_env_with_builtins() -> TypeEnv {
        let mut env = TypeEnv::new();
        for builtin in ttrpg_checker::builtins::register_builtins() {
            env.builtins.insert(builtin.name.clone(), builtin);
        }
        env
    }

    // ── Derive call tests ──────────────────────────────────────

    #[test]
    fn derive_call_arithmetic_body() {
        // derive add_bonus(base: Int, bonus: Int) -> Int { base + bonus }
        let program = program_with_decls(vec![DeclKind::Derive(FnDecl {
            name: "add_bonus".into(),
            params: vec![
                Param {
                    name: "base".into(),
                    ty: spanned(TypeExpr::Int),
                    default: None,
                    span: dummy_span(),
                },
                Param {
                    name: "bonus".into(),
                    ty: spanned(TypeExpr::Int),
                    default: None,
                    span: dummy_span(),
                },
            ],
            return_type: spanned(TypeExpr::Int),
            body: spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::BinOp {
                op: BinOp::Add,
                lhs: Box::new(spanned(ExprKind::Ident("base".into()))),
                rhs: Box::new(spanned(ExprKind::Ident("bonus".into()))),
            })))]),
            synthetic: false,
        })]);

        let mut type_env = TypeEnv::new();
        type_env.functions.insert(
            "add_bonus".into(),
            FnInfo {
                name: "add_bonus".into(),
                kind: FnKind::Derive,
                params: vec![
                    ParamInfo { name: "base".into(), ty: Ty::Int, has_default: false },
                    ParamInfo { name: "bonus".into(), ty: Ty::Int, has_default: false },
                ],
                return_type: Ty::Int,
                receiver: None,
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // Call: add_bonus(10, 5)
        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("add_bonus".into()))),
            args: vec![
                Arg { name: None, value: spanned(ExprKind::IntLit(10)), span: dummy_span() },
                Arg { name: None, value: spanned(ExprKind::IntLit(5)), span: dummy_span() },
            ],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        assert_eq!(result, Value::Int(15));
    }

    #[test]
    fn derive_call_with_named_args() {
        // derive add_bonus(base: Int, bonus: Int) -> Int { base + bonus }
        let program = program_with_decls(vec![DeclKind::Derive(FnDecl {
            name: "add_bonus".into(),
            params: vec![
                Param {
                    name: "base".into(),
                    ty: spanned(TypeExpr::Int),
                    default: None,
                    span: dummy_span(),
                },
                Param {
                    name: "bonus".into(),
                    ty: spanned(TypeExpr::Int),
                    default: None,
                    span: dummy_span(),
                },
            ],
            return_type: spanned(TypeExpr::Int),
            body: spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::BinOp {
                op: BinOp::Add,
                lhs: Box::new(spanned(ExprKind::Ident("base".into()))),
                rhs: Box::new(spanned(ExprKind::Ident("bonus".into()))),
            })))]),
            synthetic: false,
        })]);

        let mut type_env = TypeEnv::new();
        type_env.functions.insert(
            "add_bonus".into(),
            FnInfo {
                name: "add_bonus".into(),
                kind: FnKind::Derive,
                params: vec![
                    ParamInfo { name: "base".into(), ty: Ty::Int, has_default: false },
                    ParamInfo { name: "bonus".into(), ty: Ty::Int, has_default: false },
                ],
                return_type: Ty::Int,
                receiver: None,
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // Call: add_bonus(bonus: 3, base: 7) — reversed named args
        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("add_bonus".into()))),
            args: vec![
                Arg { name: Some("bonus".into()), value: spanned(ExprKind::IntLit(3)), span: dummy_span() },
                Arg { name: Some("base".into()), value: spanned(ExprKind::IntLit(7)), span: dummy_span() },
            ],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        assert_eq!(result, Value::Int(10));
    }

    #[test]
    fn derive_call_with_default_value() {
        // derive add_bonus(base: Int, bonus: Int = 5) -> Int { base + bonus }
        let program = program_with_decls(vec![DeclKind::Derive(FnDecl {
            name: "add_bonus".into(),
            params: vec![
                Param {
                    name: "base".into(),
                    ty: spanned(TypeExpr::Int),
                    default: None,
                    span: dummy_span(),
                },
                Param {
                    name: "bonus".into(),
                    ty: spanned(TypeExpr::Int),
                    default: Some(spanned(ExprKind::IntLit(5))),
                    span: dummy_span(),
                },
            ],
            return_type: spanned(TypeExpr::Int),
            body: spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::BinOp {
                op: BinOp::Add,
                lhs: Box::new(spanned(ExprKind::Ident("base".into()))),
                rhs: Box::new(spanned(ExprKind::Ident("bonus".into()))),
            })))]),
            synthetic: false,
        })]);

        let mut type_env = TypeEnv::new();
        type_env.functions.insert(
            "add_bonus".into(),
            FnInfo {
                name: "add_bonus".into(),
                kind: FnKind::Derive,
                params: vec![
                    ParamInfo { name: "base".into(), ty: Ty::Int, has_default: false },
                    ParamInfo { name: "bonus".into(), ty: Ty::Int, has_default: true },
                ],
                return_type: Ty::Int,
                receiver: None,
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // Call: add_bonus(10) — bonus defaults to 5
        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("add_bonus".into()))),
            args: vec![
                Arg { name: None, value: spanned(ExprKind::IntLit(10)), span: dummy_span() },
            ],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        assert_eq!(result, Value::Int(15));
    }

    // ── Mechanic call tests ────────────────────────────────────

    #[test]
    fn mechanic_call_with_roll_emits_roll_dice() {
        // mechanic attack_roll(bonus: Int) -> RollResult { roll(2d6 + bonus) }
        // We simulate this as: body = roll(2d6 + bonus)
        // Since roll is a builtin, the body calls roll(DiceExpr)
        // For simplicity, body is: roll(2d6 + bonus) which needs DiceLit + Add + roll
        // Let's simplify: body just calls roll on a dice literal

        let program = program_with_decls(vec![DeclKind::Mechanic(FnDecl {
            name: "attack_roll".into(),
            params: vec![],
            return_type: spanned(TypeExpr::RollResult),
            body: spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::Call {
                callee: Box::new(spanned(ExprKind::Ident("roll".into()))),
                args: vec![Arg {
                    name: None,
                    value: spanned(ExprKind::DiceLit {
                        count: 2,
                        sides: 6,
                        filter: None,
                    }),
                    span: dummy_span(),
                }],
            })))]),
            synthetic: false,
        })]);

        let mut type_env = type_env_with_builtins();
        type_env.functions.insert(
            "attack_roll".into(),
            FnInfo {
                name: "attack_roll".into(),
                kind: FnKind::Mechanic,
                params: vec![],
                return_type: Ty::RollResult,
                receiver: None,
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();

        let roll_result = RollResult {
            expr: DiceExpr { count: 2, sides: 6, filter: None, modifier: 0 },
            dice: vec![4, 5],
            kept: vec![4, 5],
            modifier: 0,
            total: 9,
            unmodified: 9,
        };
        let mut handler = ScriptedHandler::with_responses(vec![
            Response::Rolled(roll_result.clone()),
        ]);
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("attack_roll".into()))),
            args: vec![],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        assert_eq!(result, Value::RollResult(roll_result));

        // Verify that RollDice effect was emitted
        assert_eq!(handler.log.len(), 1);
        assert!(matches!(&handler.log[0], Effect::RollDice { expr } if expr.count == 2 && expr.sides == 6));
    }

    // ── Prompt call tests ──────────────────────────────────────

    #[test]
    fn prompt_call_emits_resolve_prompt() {
        let program = program_with_decls(vec![DeclKind::Prompt(PromptDecl {
            name: "ask_target".into(),
            params: vec![],
            return_type: spanned(TypeExpr::Int),
            hint: Some("Choose a target".into()),
            suggest: None,
        })]);

        let mut type_env = TypeEnv::new();
        type_env.functions.insert(
            "ask_target".into(),
            FnInfo {
                name: "ask_target".into(),
                kind: FnKind::Prompt,
                params: vec![],
                return_type: Ty::Int,
                receiver: None,
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::with_responses(vec![
            Response::PromptResult(Value::Int(42)),
        ]);
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("ask_target".into()))),
            args: vec![],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        assert_eq!(result, Value::Int(42));

        // Verify ResolvePrompt was emitted with hint
        assert_eq!(handler.log.len(), 1);
        match &handler.log[0] {
            Effect::ResolvePrompt { name, hint, .. } => {
                assert_eq!(name, "ask_target");
                assert_eq!(*hint, Some("Choose a target".to_string()));
            }
            _ => panic!("expected ResolvePrompt"),
        }
    }

    #[test]
    fn prompt_call_with_suggest() {
        // prompt pick_value(default: Int) -> Int { hint: "pick", suggest: default + 1 }
        let program = program_with_decls(vec![DeclKind::Prompt(PromptDecl {
            name: "pick_value".into(),
            params: vec![Param {
                name: "default_val".into(),
                ty: spanned(TypeExpr::Int),
                default: None,
                span: dummy_span(),
            }],
            return_type: spanned(TypeExpr::Int),
            hint: Some("pick".into()),
            suggest: Some(spanned(ExprKind::BinOp {
                op: BinOp::Add,
                lhs: Box::new(spanned(ExprKind::Ident("default_val".into()))),
                rhs: Box::new(spanned(ExprKind::IntLit(1))),
            })),
        })]);

        let mut type_env = TypeEnv::new();
        type_env.functions.insert(
            "pick_value".into(),
            FnInfo {
                name: "pick_value".into(),
                kind: FnKind::Prompt,
                params: vec![ParamInfo {
                    name: "default_val".into(),
                    ty: Ty::Int,
                    has_default: false,
                }],
                return_type: Ty::Int,
                receiver: None,
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::with_responses(vec![
            Response::PromptResult(Value::Int(100)),
        ]);
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("pick_value".into()))),
            args: vec![Arg {
                name: None,
                value: spanned(ExprKind::IntLit(10)),
                span: dummy_span(),
            }],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        assert_eq!(result, Value::Int(100));

        // Verify suggest was evaluated: default_val(10) + 1 = 11
        match &handler.log[0] {
            Effect::ResolvePrompt { suggest, params, .. } => {
                assert_eq!(*suggest, Some(Value::Int(11)));
                assert_eq!(params, &[Value::Int(10)]);
            }
            _ => panic!("expected ResolvePrompt"),
        }
    }

    // ── Builtin tests ──────────────────────────────────────────

    #[test]
    fn builtin_floor_test() {
        let program = program_with_decls(vec![]);
        let type_env = type_env_with_builtins();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("floor".into()))),
            args: vec![Arg {
                name: None,
                value: spanned(ExprKind::BinOp {
                    op: BinOp::Div,
                    lhs: Box::new(spanned(ExprKind::IntLit(7))),
                    rhs: Box::new(spanned(ExprKind::IntLit(2))),
                }),
                span: dummy_span(),
            }],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        assert_eq!(result, Value::Int(3)); // floor(3.5) = 3
    }

    #[test]
    fn builtin_ceil_test() {
        let program = program_with_decls(vec![]);
        let type_env = type_env_with_builtins();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("ceil".into()))),
            args: vec![Arg {
                name: None,
                value: spanned(ExprKind::BinOp {
                    op: BinOp::Div,
                    lhs: Box::new(spanned(ExprKind::IntLit(7))),
                    rhs: Box::new(spanned(ExprKind::IntLit(2))),
                }),
                span: dummy_span(),
            }],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        assert_eq!(result, Value::Int(4)); // ceil(3.5) = 4
    }

    #[test]
    fn builtin_min_max_test() {
        let program = program_with_decls(vec![]);
        let type_env = type_env_with_builtins();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // min(3, 7)
        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("min".into()))),
            args: vec![
                Arg { name: None, value: spanned(ExprKind::IntLit(3)), span: dummy_span() },
                Arg { name: None, value: spanned(ExprKind::IntLit(7)), span: dummy_span() },
            ],
        });
        assert_eq!(crate::eval::eval_expr(&mut env, &expr).unwrap(), Value::Int(3));

        // max(3, 7)
        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("max".into()))),
            args: vec![
                Arg { name: None, value: spanned(ExprKind::IntLit(3)), span: dummy_span() },
                Arg { name: None, value: spanned(ExprKind::IntLit(7)), span: dummy_span() },
            ],
        });
        assert_eq!(crate::eval::eval_expr(&mut env, &expr).unwrap(), Value::Int(7));
    }

    #[test]
    fn builtin_distance_test() {
        use std::sync::Arc;

        let program = program_with_decls(vec![]);
        let type_env = type_env_with_builtins();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        let pos_a = Value::Position(PositionValue(Arc::new((0i64, 0i64))));
        let pos_b = Value::Position(PositionValue(Arc::new((3i64, 4i64))));

        // Bind positions as local variables to pass to distance()
        env.bind("pos_a".into(), pos_a);
        env.bind("pos_b".into(), pos_b);

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("distance".into()))),
            args: vec![
                Arg { name: None, value: spanned(ExprKind::Ident("pos_a".into())), span: dummy_span() },
                Arg { name: None, value: spanned(ExprKind::Ident("pos_b".into())), span: dummy_span() },
            ],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        assert_eq!(result, Value::Int(4)); // Chebyshev distance: max(|3|, |4|) = 4
    }

    #[test]
    fn builtin_multiply_dice_test() {
        let program = program_with_decls(vec![]);
        let type_env = type_env_with_builtins();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // multiply_dice(2d6, 3) → 6d6
        env.bind("dice".into(), Value::DiceExpr(DiceExpr {
            count: 2, sides: 6, filter: None, modifier: 0,
        }));

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("multiply_dice".into()))),
            args: vec![
                Arg { name: None, value: spanned(ExprKind::Ident("dice".into())), span: dummy_span() },
                Arg { name: None, value: spanned(ExprKind::IntLit(3)), span: dummy_span() },
            ],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        match result {
            Value::DiceExpr(d) => {
                assert_eq!(d.count, 6);
                assert_eq!(d.sides, 6);
            }
            _ => panic!("expected DiceExpr"),
        }
    }

    #[test]
    fn builtin_multiply_dice_zero_factor_error() {
        let program = program_with_decls(vec![]);
        let type_env = type_env_with_builtins();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("dice".into(), Value::DiceExpr(DiceExpr {
            count: 2, sides: 6, filter: None, modifier: 0,
        }));

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("multiply_dice".into()))),
            args: vec![
                Arg { name: None, value: spanned(ExprKind::Ident("dice".into())), span: dummy_span() },
                Arg { name: None, value: spanned(ExprKind::IntLit(0)), span: dummy_span() },
            ],
        });
        let err = crate::eval::eval_expr(&mut env, &expr).unwrap_err();
        assert!(err.message.contains("positive"));
    }

    #[test]
    fn builtin_roll_test() {
        let program = program_with_decls(vec![]);
        let type_env = type_env_with_builtins();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();

        let roll_result = RollResult {
            expr: DiceExpr { count: 1, sides: 20, filter: None, modifier: 5 },
            dice: vec![15],
            kept: vec![15],
            modifier: 5,
            total: 20,
            unmodified: 15,
        };
        let mut handler = ScriptedHandler::with_responses(vec![
            Response::Rolled(roll_result.clone()),
        ]);
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("dice".into(), Value::DiceExpr(DiceExpr {
            count: 1, sides: 20, filter: None, modifier: 5,
        }));

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("roll".into()))),
            args: vec![Arg {
                name: None,
                value: spanned(ExprKind::Ident("dice".into())),
                span: dummy_span(),
            }],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        assert_eq!(result, Value::RollResult(roll_result));
    }

    #[test]
    fn builtin_roll_override_response() {
        let program = program_with_decls(vec![]);
        let type_env = type_env_with_builtins();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();

        let override_result = RollResult {
            expr: DiceExpr { count: 1, sides: 20, filter: None, modifier: 0 },
            dice: vec![20],
            kept: vec![20],
            modifier: 0,
            total: 20,
            unmodified: 20,
        };
        let mut handler = ScriptedHandler::with_responses(vec![
            Response::Override(Value::RollResult(override_result.clone())),
        ]);
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("dice".into(), Value::DiceExpr(DiceExpr {
            count: 1, sides: 20, filter: None, modifier: 0,
        }));

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("roll".into()))),
            args: vec![Arg {
                name: None,
                value: spanned(ExprKind::Ident("dice".into())),
                span: dummy_span(),
            }],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        assert_eq!(result, Value::RollResult(override_result));
    }

    #[test]
    fn builtin_apply_condition_emits_effect() {
        let program = program_with_decls(vec![]);
        let type_env = type_env_with_builtins();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("target".into(), Value::Entity(EntityRef(1)));
        env.bind("cond".into(), Value::Condition("Prone".into()));
        env.bind("dur".into(), Value::Duration(DurationValue::Rounds(3)));

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("apply_condition".into()))),
            args: vec![
                Arg { name: None, value: spanned(ExprKind::Ident("target".into())), span: dummy_span() },
                Arg { name: None, value: spanned(ExprKind::Ident("cond".into())), span: dummy_span() },
                Arg { name: None, value: spanned(ExprKind::Ident("dur".into())), span: dummy_span() },
            ],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        assert_eq!(result, Value::None);

        assert_eq!(handler.log.len(), 1);
        match &handler.log[0] {
            Effect::ApplyCondition { target, condition, .. } => {
                assert_eq!(target.0, 1);
                assert_eq!(condition, "Prone");
            }
            _ => panic!("expected ApplyCondition effect"),
        }
    }

    #[test]
    fn builtin_remove_condition_emits_effect() {
        let program = program_with_decls(vec![]);
        let type_env = type_env_with_builtins();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("target".into(), Value::Entity(EntityRef(2)));
        env.bind("cond".into(), Value::Condition("Stunned".into()));

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("remove_condition".into()))),
            args: vec![
                Arg { name: None, value: spanned(ExprKind::Ident("target".into())), span: dummy_span() },
                Arg { name: None, value: spanned(ExprKind::Ident("cond".into())), span: dummy_span() },
            ],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        assert_eq!(result, Value::None);

        assert_eq!(handler.log.len(), 1);
        match &handler.log[0] {
            Effect::RemoveCondition { target, condition } => {
                assert_eq!(target.0, 2);
                assert_eq!(condition, "Stunned");
            }
            _ => panic!("expected RemoveCondition effect"),
        }
    }

    // ── Enum variant construction tests ────────────────────────

    #[test]
    fn enum_variant_qualified_construction() {
        let program = program_with_decls(vec![]);
        let mut type_env = TypeEnv::new();
        type_env.types.insert(
            "Duration".into(),
            ttrpg_checker::env::DeclInfo::Enum(EnumInfo {
                name: "Duration".into(),
                variants: vec![
                    VariantInfo { name: "rounds".into(), fields: vec![("value".into(), Ty::Int)] },
                    VariantInfo { name: "indefinite".into(), fields: vec![] },
                ],
            }),
        );
        type_env.variant_to_enum.insert("rounds".into(), "Duration".into());
        type_env.variant_to_enum.insert("indefinite".into(), "Duration".into());

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // Duration.rounds(3)
        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::FieldAccess {
                object: Box::new(spanned(ExprKind::Ident("Duration".into()))),
                field: "rounds".into(),
            })),
            args: vec![Arg {
                name: None,
                value: spanned(ExprKind::IntLit(3)),
                span: dummy_span(),
            }],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        match result {
            Value::EnumVariant { enum_name, variant, fields } => {
                assert_eq!(enum_name, "Duration");
                assert_eq!(variant, "rounds");
                assert_eq!(fields.get("value"), Some(&Value::Int(3)));
            }
            _ => panic!("expected EnumVariant, got {:?}", result),
        }
    }

    #[test]
    fn enum_variant_bare_construction() {
        let program = program_with_decls(vec![]);
        let mut type_env = TypeEnv::new();
        type_env.types.insert(
            "Duration".into(),
            ttrpg_checker::env::DeclInfo::Enum(EnumInfo {
                name: "Duration".into(),
                variants: vec![
                    VariantInfo { name: "rounds".into(), fields: vec![("value".into(), Ty::Int)] },
                    VariantInfo { name: "indefinite".into(), fields: vec![] },
                ],
            }),
        );
        type_env.variant_to_enum.insert("rounds".into(), "Duration".into());
        type_env.variant_to_enum.insert("indefinite".into(), "Duration".into());

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // rounds(5) — bare enum variant call
        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("rounds".into()))),
            args: vec![Arg {
                name: None,
                value: spanned(ExprKind::IntLit(5)),
                span: dummy_span(),
            }],
        });
        let result = crate::eval::eval_expr(&mut env, &expr).unwrap();
        match result {
            Value::EnumVariant { enum_name, variant, fields } => {
                assert_eq!(enum_name, "Duration");
                assert_eq!(variant, "rounds");
                assert_eq!(fields.get("value"), Some(&Value::Int(5)));
            }
            _ => panic!("expected EnumVariant, got {:?}", result),
        }
    }

    // ── Error case tests ───────────────────────────────────────

    #[test]
    fn missing_required_arg_error() {
        let program = program_with_decls(vec![DeclKind::Derive(FnDecl {
            name: "identity".into(),
            params: vec![Param {
                name: "x".into(),
                ty: spanned(TypeExpr::Int),
                default: None,
                span: dummy_span(),
            }],
            return_type: spanned(TypeExpr::Int),
            body: spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::Ident("x".into()))))]),
            synthetic: false,
        })]);

        let mut type_env = TypeEnv::new();
        type_env.functions.insert(
            "identity".into(),
            FnInfo {
                name: "identity".into(),
                kind: FnKind::Derive,
                params: vec![ParamInfo { name: "x".into(), ty: Ty::Int, has_default: false }],
                return_type: Ty::Int,
                receiver: None,
            },
        );

        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // Call with no arguments
        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("identity".into()))),
            args: vec![],
        });
        let err = crate::eval::eval_expr(&mut env, &expr).unwrap_err();
        assert!(err.message.contains("missing required argument"));
    }

    #[test]
    fn multiply_dice_overflow_error() {
        let program = program_with_decls(vec![]);
        let type_env = type_env_with_builtins();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        env.bind("dice".into(), Value::DiceExpr(DiceExpr {
            count: u32::MAX, sides: 6, filter: None, modifier: 0,
        }));

        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::Ident("multiply_dice".into()))),
            args: vec![
                Arg { name: None, value: spanned(ExprKind::Ident("dice".into())), span: dummy_span() },
                Arg { name: None, value: spanned(ExprKind::IntLit(2)), span: dummy_span() },
            ],
        });
        let err = crate::eval::eval_expr(&mut env, &expr).unwrap_err();
        assert!(err.message.contains("overflow"));
    }

    #[test]
    fn invalid_callee_expression_error() {
        let program = program_with_decls(vec![]);
        let type_env = TypeEnv::new();
        let interp = Interpreter::new(&program, &type_env).unwrap();
        let state = TestState::new();
        let mut handler = ScriptedHandler::new();
        let mut env = make_env(&state, &mut handler, &interp);

        // Try to call a literal: 42()
        let expr = spanned(ExprKind::Call {
            callee: Box::new(spanned(ExprKind::IntLit(42))),
            args: vec![],
        });
        let err = crate::eval::eval_expr(&mut env, &expr).unwrap_err();
        assert!(err.message.contains("invalid callee"));
    }
}
