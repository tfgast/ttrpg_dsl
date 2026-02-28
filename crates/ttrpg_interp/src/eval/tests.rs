use super::*;
use super::compare::{int_float_cmp, int_float_eq, match_pattern};
use super::control::eval_stmt;
use std::collections::{BTreeMap, HashMap};
use std::sync::Arc;

use ttrpg_ast::ast::*;
use ttrpg_ast::{Name, Span, Spanned};
use ttrpg_checker::env::{DeclInfo, EnumInfo, TypeEnv, VariantInfo};

use crate::effect::{Effect, EffectHandler, FieldPathSegment, Response};
use crate::state::{ActiveCondition, EntityRef, StateProvider};
use crate::value::{default_turn_budget, DiceExpr, PositionValue, RollResult, Value};
use crate::{Env, Interpreter};

// ── Test infrastructure ────────────────────────────────────

/// Records effects and replays scripted responses.
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
}

impl EffectHandler for ScriptedHandler {
    fn handle(&mut self, effect: Effect) -> Response {
        self.log.push(effect);
        self.script.pop_front().unwrap_or(Response::Acknowledged)
    }
}

/// Minimal StateProvider for tests.
struct TestState {
    fields: HashMap<(u64, String), Value>,
    conditions: HashMap<u64, Vec<ActiveCondition>>,
    turn_budgets: HashMap<u64, BTreeMap<Name, Value>>,
    enabled_options: Vec<Name>,
    entity_type: Option<Name>,
}

impl TestState {
    fn new() -> Self {
        TestState {
            fields: HashMap::new(),
            conditions: HashMap::new(),
            turn_budgets: HashMap::new(),
            enabled_options: Vec::new(),
            entity_type: None,
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

    fn position_eq(&self, a: &Value, b: &Value) -> bool {
        // For testing: compare as (i64, i64) grid positions
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
                return Some(std::cmp::max((a.0 - b.0).abs(), (a.1 - b.1).abs()));
            }
        }
        None
    }

    fn entity_type_name(&self, _entity: &EntityRef) -> Option<Name> {
        self.entity_type.clone()
    }
}

// Helpers to build test environments

fn empty_program() -> Program {
    Program::default()
}

fn empty_type_env() -> TypeEnv {
    TypeEnv::new()
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

// ── Literal tests ──────────────────────────────────────────

#[test]
fn eval_int_lit() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let expr = spanned(ExprKind::IntLit(42));
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(42));
}

#[test]
fn eval_string_lit() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let expr = spanned(ExprKind::StringLit("hello".to_string()));
    assert_eq!(
        eval_expr(&mut env, &expr).unwrap(),
        Value::Str("hello".to_string())
    );
}

#[test]
fn eval_bool_lit() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let expr = spanned(ExprKind::BoolLit(true));
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));

    let expr = spanned(ExprKind::BoolLit(false));
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(false));
}

#[test]
fn eval_none_lit() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let expr = spanned(ExprKind::NoneLit);
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::None);
}

#[test]
fn eval_dice_lit() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let expr = spanned(ExprKind::DiceLit {
        count: 2,
        sides: 6,
        filter: None,
    });
    let result = eval_expr(&mut env, &expr).unwrap();
    match result {
        Value::DiceExpr(de) => {
            assert_eq!(de.groups[0].count, 2);
            assert_eq!(de.groups[0].sides, 6);
            assert_eq!(de.modifier, 0);
            assert!(de.groups[0].filter.is_none());
        }
        _ => panic!("expected DiceExpr, got {:?}", result),
    }
}

#[test]
fn eval_paren() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let expr = spanned(ExprKind::Paren(Box::new(spanned(ExprKind::IntLit(99)))));
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(99));
}

// ── Ident tests ────────────────────────────────────────────

#[test]
fn eval_ident_from_scope() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(Name::from("x"), Value::Int(10));

    let expr = spanned(ExprKind::Ident("x".into()));
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(10));
}

#[test]
fn eval_ident_undefined() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let expr = spanned(ExprKind::Ident("unknown".into()));
    let err = eval_expr(&mut env, &expr).unwrap_err();
    assert!(err.message.contains("undefined variable 'unknown'"));
}

// ── Unary operator tests ───────────────────────────────────

#[test]
fn eval_unary_neg_int() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let expr = spanned(ExprKind::UnaryOp {
        op: UnaryOp::Neg,
        operand: Box::new(spanned(ExprKind::IntLit(5))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(-5));
}

#[test]
fn eval_unary_neg_float() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let expr = spanned(ExprKind::UnaryOp {
        op: UnaryOp::Neg,
        operand: Box::new(spanned(ExprKind::IntLit(0))),
    });
    // Test that -0 works for int
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(0));
}

#[test]
fn eval_unary_not() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let expr = spanned(ExprKind::UnaryOp {
        op: UnaryOp::Not,
        operand: Box::new(spanned(ExprKind::BoolLit(true))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(false));
}

// ── Arithmetic tests ───────────────────────────────────────

#[test]
fn eval_add_int() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let expr = spanned(ExprKind::BinOp {
        op: BinOp::Add,
        lhs: Box::new(spanned(ExprKind::IntLit(3))),
        rhs: Box::new(spanned(ExprKind::IntLit(4))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(7));
}

#[test]
fn eval_sub_int() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let expr = spanned(ExprKind::BinOp {
        op: BinOp::Sub,
        lhs: Box::new(spanned(ExprKind::IntLit(10))),
        rhs: Box::new(spanned(ExprKind::IntLit(3))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(7));
}

#[test]
fn eval_mul_int() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let expr = spanned(ExprKind::BinOp {
        op: BinOp::Mul,
        lhs: Box::new(spanned(ExprKind::IntLit(6))),
        rhs: Box::new(spanned(ExprKind::IntLit(7))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(42));
}

#[test]
fn eval_div_int_promotes_to_float() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let expr = spanned(ExprKind::BinOp {
        op: BinOp::Div,
        lhs: Box::new(spanned(ExprKind::IntLit(7))),
        rhs: Box::new(spanned(ExprKind::IntLit(2))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Float(3.5));
}

#[test]
fn eval_string_concatenation() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let expr = spanned(ExprKind::BinOp {
        op: BinOp::Add,
        lhs: Box::new(spanned(ExprKind::StringLit("hello".to_string()))),
        rhs: Box::new(spanned(ExprKind::StringLit(" world".to_string()))),
    });
    assert_eq!(
        eval_expr(&mut env, &expr).unwrap(),
        Value::Str("hello world".to_string())
    );
}

#[test]
fn eval_mixed_int_float_arithmetic() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    // Int + Float promotes to Float
    env.bind(Name::from("x"), Value::Int(3));
    env.bind(Name::from("y"), Value::Float(1.5));

    let expr = spanned(ExprKind::BinOp {
        op: BinOp::Add,
        lhs: Box::new(spanned(ExprKind::Ident("x".into()))),
        rhs: Box::new(spanned(ExprKind::Ident("y".into()))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Float(4.5));
}

// ── Overflow tests ─────────────────────────────────────────

#[test]
fn eval_integer_overflow_add() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let expr = spanned(ExprKind::BinOp {
        op: BinOp::Add,
        lhs: Box::new(spanned(ExprKind::IntLit(i64::MAX))),
        rhs: Box::new(spanned(ExprKind::IntLit(1))),
    });
    let err = eval_expr(&mut env, &expr).unwrap_err();
    assert!(err.message.contains("overflow"));
}

#[test]
fn eval_integer_overflow_mul() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let expr = spanned(ExprKind::BinOp {
        op: BinOp::Mul,
        lhs: Box::new(spanned(ExprKind::IntLit(i64::MAX))),
        rhs: Box::new(spanned(ExprKind::IntLit(2))),
    });
    let err = eval_expr(&mut env, &expr).unwrap_err();
    assert!(err.message.contains("overflow"));
}

#[test]
fn eval_integer_overflow_sub() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let expr = spanned(ExprKind::BinOp {
        op: BinOp::Sub,
        lhs: Box::new(spanned(ExprKind::IntLit(i64::MIN))),
        rhs: Box::new(spanned(ExprKind::IntLit(1))),
    });
    let err = eval_expr(&mut env, &expr).unwrap_err();
    assert!(err.message.contains("overflow"));
}

#[test]
fn eval_integer_overflow_neg() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let expr = spanned(ExprKind::UnaryOp {
        op: UnaryOp::Neg,
        operand: Box::new(spanned(ExprKind::IntLit(i64::MIN))),
    });
    let err = eval_expr(&mut env, &expr).unwrap_err();
    assert!(err.message.contains("overflow"));
}

// ── Division by zero tests ─────────────────────────────────

#[test]
fn eval_div_by_zero_int() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let expr = spanned(ExprKind::BinOp {
        op: BinOp::Div,
        lhs: Box::new(spanned(ExprKind::IntLit(10))),
        rhs: Box::new(spanned(ExprKind::IntLit(0))),
    });
    let err = eval_expr(&mut env, &expr).unwrap_err();
    assert!(err.message.contains("division by zero"));
}

// ── Comparison tests ───────────────────────────────────────

#[test]
fn eval_comparisons() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    // 3 < 5 = true
    let expr = spanned(ExprKind::BinOp {
        op: BinOp::Lt,
        lhs: Box::new(spanned(ExprKind::IntLit(3))),
        rhs: Box::new(spanned(ExprKind::IntLit(5))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));

    // 5 <= 5 = true
    let expr = spanned(ExprKind::BinOp {
        op: BinOp::LtEq,
        lhs: Box::new(spanned(ExprKind::IntLit(5))),
        rhs: Box::new(spanned(ExprKind::IntLit(5))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));

    // 5 > 3 = true
    let expr = spanned(ExprKind::BinOp {
        op: BinOp::Gt,
        lhs: Box::new(spanned(ExprKind::IntLit(5))),
        rhs: Box::new(spanned(ExprKind::IntLit(3))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));

    // 3 >= 5 = false
    let expr = spanned(ExprKind::BinOp {
        op: BinOp::GtEq,
        lhs: Box::new(spanned(ExprKind::IntLit(3))),
        rhs: Box::new(spanned(ExprKind::IntLit(5))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(false));
}

// ── Equality tests ─────────────────────────────────────────

#[test]
fn eval_equality_int() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let expr = spanned(ExprKind::BinOp {
        op: BinOp::Eq,
        lhs: Box::new(spanned(ExprKind::IntLit(5))),
        rhs: Box::new(spanned(ExprKind::IntLit(5))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));

    let expr = spanned(ExprKind::BinOp {
        op: BinOp::NotEq,
        lhs: Box::new(spanned(ExprKind::IntLit(5))),
        rhs: Box::new(spanned(ExprKind::IntLit(3))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));
}

#[test]
fn eval_equality_float_neg_zero() {
    // Semantic equality: -0.0 == +0.0 (standard f64)
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(Name::from("a"), Value::Float(-0.0));
    env.bind(Name::from("b"), Value::Float(0.0));

    let expr = spanned(ExprKind::BinOp {
        op: BinOp::Eq,
        lhs: Box::new(spanned(ExprKind::Ident("a".into()))),
        rhs: Box::new(spanned(ExprKind::Ident("b".into()))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));
}

#[test]
fn eval_equality_position_delegation() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    // Two different Arc allocations with same logical position
    let pos1 = Value::Position(PositionValue(Arc::new((1i64, 2i64))));
    let pos2 = Value::Position(PositionValue(Arc::new((1i64, 2i64))));

    env.bind(Name::from("p1"), pos1);
    env.bind(Name::from("p2"), pos2);

    let expr = spanned(ExprKind::BinOp {
        op: BinOp::Eq,
        lhs: Box::new(spanned(ExprKind::Ident("p1".into()))),
        rhs: Box::new(spanned(ExprKind::Ident("p2".into()))),
    });
    // TestState's position_eq compares the underlying (i64, i64)
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));
}

// ── Logical operator tests ─────────────────────────────────

#[test]
fn eval_logical_and_short_circuit() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    // false && (error) should short-circuit — never evaluate RHS
    let expr = spanned(ExprKind::BinOp {
        op: BinOp::And,
        lhs: Box::new(spanned(ExprKind::BoolLit(false))),
        rhs: Box::new(spanned(ExprKind::Ident("undefined_var".into()))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(false));
}

#[test]
fn eval_logical_or_short_circuit() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    // true || (error) should short-circuit
    let expr = spanned(ExprKind::BinOp {
        op: BinOp::Or,
        lhs: Box::new(spanned(ExprKind::BoolLit(true))),
        rhs: Box::new(spanned(ExprKind::Ident("undefined_var".into()))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));
}

#[test]
fn eval_logical_and_both_true() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let expr = spanned(ExprKind::BinOp {
        op: BinOp::And,
        lhs: Box::new(spanned(ExprKind::BoolLit(true))),
        rhs: Box::new(spanned(ExprKind::BoolLit(true))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));
}

// ── In operator tests ──────────────────────────────────────

#[test]
fn eval_in_list() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(
        "items".into(),
        Value::List(vec![Value::Int(1), Value::Int(2), Value::Int(3)]),
    );

    // 2 in items => true
    let expr = spanned(ExprKind::BinOp {
        op: BinOp::In,
        lhs: Box::new(spanned(ExprKind::IntLit(2))),
        rhs: Box::new(spanned(ExprKind::Ident("items".into()))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));

    // 5 in items => false
    let expr = spanned(ExprKind::BinOp {
        op: BinOp::In,
        lhs: Box::new(spanned(ExprKind::IntLit(5))),
        rhs: Box::new(spanned(ExprKind::Ident("items".into()))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(false));
}

#[test]
fn eval_in_set() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let mut s = std::collections::BTreeSet::new();
    s.insert(Value::Str("a".into()));
    s.insert(Value::Str("b".into()));
    env.bind(Name::from("my_set"), Value::Set(s));

    let expr = spanned(ExprKind::BinOp {
        op: BinOp::In,
        lhs: Box::new(spanned(ExprKind::StringLit("a".to_string()))),
        rhs: Box::new(spanned(ExprKind::Ident("my_set".into()))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));
}

#[test]
fn eval_in_map() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let mut m = BTreeMap::new();
    m.insert(Value::Str("key".into()), Value::Int(1));
    env.bind(Name::from("my_map"), Value::Map(m));

    // "key" in my_map => true
    let expr = spanned(ExprKind::BinOp {
        op: BinOp::In,
        lhs: Box::new(spanned(ExprKind::StringLit("key".to_string()))),
        rhs: Box::new(spanned(ExprKind::Ident("my_map".into()))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));
}

// ── RollResult coercion tests ──────────────────────────────

#[test]
fn eval_roll_result_coercion_in_arithmetic() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let rr = Value::RollResult(RollResult {
        expr: DiceExpr::single(1, 20, None, 5),
        dice: vec![15],
        kept: vec![15],
        modifier: 5,
        total: 20,
        unmodified: 15,
    });
    env.bind(Name::from("roll"), rr);

    // roll + 2 should coerce RollResult to 20, then add 2
    let expr = spanned(ExprKind::BinOp {
        op: BinOp::Add,
        lhs: Box::new(spanned(ExprKind::Ident("roll".into()))),
        rhs: Box::new(spanned(ExprKind::IntLit(2))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(22));
}

#[test]
fn eval_roll_result_coercion_in_comparison() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let rr = Value::RollResult(RollResult {
        expr: DiceExpr::single(1, 20, None, 5),
        dice: vec![15],
        kept: vec![15],
        modifier: 5,
        total: 20,
        unmodified: 15,
    });
    env.bind(Name::from("roll"), rr);

    // roll >= 10 should be true (20 >= 10)
    let expr = spanned(ExprKind::BinOp {
        op: BinOp::GtEq,
        lhs: Box::new(spanned(ExprKind::Ident("roll".into()))),
        rhs: Box::new(spanned(ExprKind::IntLit(10))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));
}

// ── Field access tests ─────────────────────────────────────

#[test]
fn eval_field_access_entity() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let mut state = TestState::new();
    state.fields.insert((1, "HP".into()), Value::Int(30));

    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(Name::from("target"), Value::Entity(EntityRef(1)));

    let expr = spanned(ExprKind::FieldAccess {
        object: Box::new(spanned(ExprKind::Ident("target".into()))),
        field: "HP".into(),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(30));
}

#[test]
fn eval_field_access_struct() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let mut fields = BTreeMap::new();
    fields.insert("x".into(), Value::Int(10));
    fields.insert("y".into(), Value::Int(20));
    env.bind(
        "point".into(),
        Value::Struct {
            name: "Point".into(),
            fields,
        },
    );

    let expr = spanned(ExprKind::FieldAccess {
        object: Box::new(spanned(ExprKind::Ident("point".into()))),
        field: "x".into(),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(10));
}

#[test]
fn eval_field_access_roll_result() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let rr = Value::RollResult(RollResult {
        expr: DiceExpr::single(2, 6, None, 3),
        dice: vec![4, 5],
        kept: vec![4, 5],
        modifier: 3,
        total: 12,
        unmodified: 9,
    });
    env.bind(Name::from("result"), rr);

    // .total
    let expr = spanned(ExprKind::FieldAccess {
        object: Box::new(spanned(ExprKind::Ident("result".into()))),
        field: "total".into(),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(12));

    // .unmodified
    let expr = spanned(ExprKind::FieldAccess {
        object: Box::new(spanned(ExprKind::Ident("result".into()))),
        field: "unmodified".into(),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(9));

    // .dice
    let expr = spanned(ExprKind::FieldAccess {
        object: Box::new(spanned(ExprKind::Ident("result".into()))),
        field: "dice".into(),
    });
    assert_eq!(
        eval_expr(&mut env, &expr).unwrap(),
        Value::List(vec![Value::Int(4), Value::Int(5)])
    );
}

#[test]
fn eval_field_access_turn_budget() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(Name::from("budget"), default_turn_budget());

    let expr = spanned(ExprKind::FieldAccess {
        object: Box::new(spanned(ExprKind::Ident("budget".into()))),
        field: "actions".into(),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(1));
}

// ── Index tests ────────────────────────────────────────────

#[test]
fn eval_index_list() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(
        "items".into(),
        Value::List(vec![Value::Int(10), Value::Int(20), Value::Int(30)]),
    );

    let expr = spanned(ExprKind::Index {
        object: Box::new(spanned(ExprKind::Ident("items".into()))),
        index: Box::new(spanned(ExprKind::IntLit(1))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(20));
}

#[test]
fn eval_index_list_out_of_bounds() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(Name::from("items"), Value::List(vec![Value::Int(10)]));

    let expr = spanned(ExprKind::Index {
        object: Box::new(spanned(ExprKind::Ident("items".into()))),
        index: Box::new(spanned(ExprKind::IntLit(5))),
    });
    let err = eval_expr(&mut env, &expr).unwrap_err();
    assert!(err.message.contains("out of bounds"));
}

#[test]
fn eval_index_map() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let mut m = BTreeMap::new();
    m.insert(Value::Str("STR".into()), Value::Int(18));
    env.bind(Name::from("stats"), Value::Map(m));

    let expr = spanned(ExprKind::Index {
        object: Box::new(spanned(ExprKind::Ident("stats".into()))),
        index: Box::new(spanned(ExprKind::StringLit("STR".to_string()))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(18));
}

#[test]
fn eval_index_map_missing_key() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let m = BTreeMap::new();
    env.bind(Name::from("stats"), Value::Map(m));

    let expr = spanned(ExprKind::Index {
        object: Box::new(spanned(ExprKind::Ident("stats".into()))),
        index: Box::new(spanned(ExprKind::StringLit("DEX".to_string()))),
    });
    let err = eval_expr(&mut env, &expr).unwrap_err();
    assert!(err.message.contains("not found"));
}

// ── List literal tests ─────────────────────────────────────

#[test]
fn eval_list_lit() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let expr = spanned(ExprKind::ListLit(vec![
        spanned(ExprKind::IntLit(1)),
        spanned(ExprKind::IntLit(2)),
        spanned(ExprKind::IntLit(3)),
    ]));
    assert_eq!(
        eval_expr(&mut env, &expr).unwrap(),
        Value::List(vec![Value::Int(1), Value::Int(2), Value::Int(3)])
    );
}

// ── Struct literal tests ───────────────────────────────────

#[test]
fn eval_struct_lit() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let expr = spanned(ExprKind::StructLit {
        name: "Point".into(),
        fields: vec![
            StructFieldInit {
                name: "x".into(),
                value: spanned(ExprKind::IntLit(10)),
                span: dummy_span(),
            },
            StructFieldInit {
                name: "y".into(),
                value: spanned(ExprKind::IntLit(20)),
                span: dummy_span(),
            },
        ],
        base: None,
    });
    let result = eval_expr(&mut env, &expr).unwrap();
    match &result {
        Value::Struct { name, fields } => {
            assert_eq!(name, "Point");
            assert_eq!(fields.get("x"), Some(&Value::Int(10)));
            assert_eq!(fields.get("y"), Some(&Value::Int(20)));
        }
        _ => panic!("expected Struct, got {:?}", result),
    }
}

#[test]
fn eval_struct_lit_fills_defaults() {
    let mut program = Program {
        items: vec![spanned(TopLevel::System(SystemBlock {
            name: "test".into(),
            decls: vec![spanned(DeclKind::Struct(StructDecl {
                name: "Config".into(),
                fields: vec![
                    FieldDef {
                        name: "x".into(),
                        ty: spanned(TypeExpr::Int),
                        default: None,
                        span: dummy_span(),
                    },
                    FieldDef {
                        name: "y".into(),
                        ty: spanned(TypeExpr::Int),
                        default: Some(spanned(ExprKind::IntLit(42))),
                        span: dummy_span(),
                    },
                    FieldDef {
                        name: "z".into(),
                        ty: spanned(TypeExpr::Int),
                        default: Some(spanned(ExprKind::IntLit(99))),
                        span: dummy_span(),
                    },
                ],
            }))],
        }))],
        ..Default::default()
    };
    program.build_index();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    // Provide only x and z — y should get its default of 42
    let expr = spanned(ExprKind::StructLit {
        name: "Config".into(),
        fields: vec![
            StructFieldInit {
                name: "x".into(),
                value: spanned(ExprKind::IntLit(1)),
                span: dummy_span(),
            },
            StructFieldInit {
                name: "z".into(),
                value: spanned(ExprKind::IntLit(7)),
                span: dummy_span(),
            },
        ],
        base: None,
    });
    let result = eval_expr(&mut env, &expr).unwrap();
    match &result {
        Value::Struct { name, fields } => {
            assert_eq!(name, "Config");
            assert_eq!(fields.get("x"), Some(&Value::Int(1)));
            assert_eq!(
                fields.get("y"),
                Some(&Value::Int(42)),
                "default should be filled"
            );
            assert_eq!(fields.get("z"), Some(&Value::Int(7)));
        }
        _ => panic!("expected Struct, got {:?}", result),
    }
}

// ── Struct spread (..base) tests ─────────────────────────────

#[test]
fn eval_struct_spread_override_one_field() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    // Bind a base struct value: Point { x: 1, y: 2 }
    env.bind(
        "base".into(),
        Value::Struct {
            name: "Point".into(),
            fields: {
                let mut m = BTreeMap::new();
                m.insert("x".into(), Value::Int(1));
                m.insert("y".into(), Value::Int(2));
                m
            },
        },
    );

    // Point { x: 99, ..base } — override x, keep y from base
    let expr = spanned(ExprKind::StructLit {
        name: "Point".into(),
        fields: vec![StructFieldInit {
            name: "x".into(),
            value: spanned(ExprKind::IntLit(99)),
            span: dummy_span(),
        }],
        base: Some(Box::new(spanned(ExprKind::Ident("base".into())))),
    });
    let result = eval_expr(&mut env, &expr).unwrap();
    match &result {
        Value::Struct { name, fields } => {
            assert_eq!(name, "Point");
            assert_eq!(
                fields.get("x"),
                Some(&Value::Int(99)),
                "explicit field overrides base"
            );
            assert_eq!(
                fields.get("y"),
                Some(&Value::Int(2)),
                "base field preserved"
            );
        }
        _ => panic!("expected Struct, got {:?}", result),
    }
}

#[test]
fn eval_struct_spread_base_only() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    // Bind a base struct value: Point { x: 10, y: 20 }
    env.bind(
        "p".into(),
        Value::Struct {
            name: "Point".into(),
            fields: {
                let mut m = BTreeMap::new();
                m.insert("x".into(), Value::Int(10));
                m.insert("y".into(), Value::Int(20));
                m
            },
        },
    );

    // Point { ..p } — clone via spread with no explicit fields
    let expr = spanned(ExprKind::StructLit {
        name: "Point".into(),
        fields: vec![],
        base: Some(Box::new(spanned(ExprKind::Ident("p".into())))),
    });
    let result = eval_expr(&mut env, &expr).unwrap();
    match &result {
        Value::Struct { name, fields } => {
            assert_eq!(name, "Point");
            assert_eq!(fields.get("x"), Some(&Value::Int(10)));
            assert_eq!(fields.get("y"), Some(&Value::Int(20)));
        }
        _ => panic!("expected Struct, got {:?}", result),
    }
}

// ── If expression tests ────────────────────────────────────

#[test]
fn eval_if_true_branch() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let expr = spanned(ExprKind::If {
        condition: Box::new(spanned(ExprKind::BoolLit(true))),
        then_block: spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::IntLit(1))))]),
        else_branch: Some(ElseBranch::Block(spanned(vec![spanned(StmtKind::Expr(
            spanned(ExprKind::IntLit(2)),
        ))]))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(1));
}

#[test]
fn eval_if_false_branch() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let expr = spanned(ExprKind::If {
        condition: Box::new(spanned(ExprKind::BoolLit(false))),
        then_block: spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::IntLit(1))))]),
        else_branch: Some(ElseBranch::Block(spanned(vec![spanned(StmtKind::Expr(
            spanned(ExprKind::IntLit(2)),
        ))]))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(2));
}

#[test]
fn eval_if_no_else_returns_none() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let expr = spanned(ExprKind::If {
        condition: Box::new(spanned(ExprKind::BoolLit(false))),
        then_block: spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::IntLit(1))))]),
        else_branch: None,
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::None);
}

// ── Guard match tests ──────────────────────────────────────

#[test]
fn eval_guard_match_first_matching() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(Name::from("x"), Value::Int(15));

    let expr = spanned(ExprKind::GuardMatch {
        arms: vec![
            GuardArm {
                guard: GuardKind::Expr(spanned(ExprKind::BinOp {
                    op: BinOp::GtEq,
                    lhs: Box::new(spanned(ExprKind::Ident("x".into()))),
                    rhs: Box::new(spanned(ExprKind::IntLit(10))),
                })),
                body: ArmBody::Expr(spanned(ExprKind::StringLit("high".to_string()))),
                span: dummy_span(),
            },
            GuardArm {
                guard: GuardKind::Expr(spanned(ExprKind::BinOp {
                    op: BinOp::GtEq,
                    lhs: Box::new(spanned(ExprKind::Ident("x".into()))),
                    rhs: Box::new(spanned(ExprKind::IntLit(7))),
                })),
                body: ArmBody::Expr(spanned(ExprKind::StringLit("medium".to_string()))),
                span: dummy_span(),
            },
            GuardArm {
                guard: GuardKind::Wildcard,
                body: ArmBody::Expr(spanned(ExprKind::StringLit("low".to_string()))),
                span: dummy_span(),
            },
        ],
    });
    assert_eq!(
        eval_expr(&mut env, &expr).unwrap(),
        Value::Str("high".to_string())
    );
}

#[test]
fn eval_guard_match_wildcard_fallthrough() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(Name::from("x"), Value::Int(3));

    let expr = spanned(ExprKind::GuardMatch {
        arms: vec![
            GuardArm {
                guard: GuardKind::Expr(spanned(ExprKind::BinOp {
                    op: BinOp::GtEq,
                    lhs: Box::new(spanned(ExprKind::Ident("x".into()))),
                    rhs: Box::new(spanned(ExprKind::IntLit(10))),
                })),
                body: ArmBody::Expr(spanned(ExprKind::StringLit("high".to_string()))),
                span: dummy_span(),
            },
            GuardArm {
                guard: GuardKind::Wildcard,
                body: ArmBody::Expr(spanned(ExprKind::StringLit("low".to_string()))),
                span: dummy_span(),
            },
        ],
    });
    assert_eq!(
        eval_expr(&mut env, &expr).unwrap(),
        Value::Str("low".to_string())
    );
}

// ── Pattern match tests ────────────────────────────────────

#[test]
fn eval_pattern_match_int() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let expr = spanned(ExprKind::PatternMatch {
        scrutinee: Box::new(spanned(ExprKind::IntLit(2))),
        arms: vec![
            PatternArm {
                pattern: spanned(PatternKind::IntLit(1)),
                body: ArmBody::Expr(spanned(ExprKind::StringLit("one".to_string()))),
                span: dummy_span(),
            },
            PatternArm {
                pattern: spanned(PatternKind::IntLit(2)),
                body: ArmBody::Expr(spanned(ExprKind::StringLit("two".to_string()))),
                span: dummy_span(),
            },
            PatternArm {
                pattern: spanned(PatternKind::Wildcard),
                body: ArmBody::Expr(spanned(ExprKind::StringLit("other".to_string()))),
                span: dummy_span(),
            },
        ],
    });
    assert_eq!(
        eval_expr(&mut env, &expr).unwrap(),
        Value::Str("two".to_string())
    );
}

#[test]
fn eval_pattern_match_binding() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    // match 42 { x => x + 1 }
    let expr = spanned(ExprKind::PatternMatch {
        scrutinee: Box::new(spanned(ExprKind::IntLit(42))),
        arms: vec![PatternArm {
            pattern: spanned(PatternKind::Ident("x".into())),
            body: ArmBody::Expr(spanned(ExprKind::BinOp {
                op: BinOp::Add,
                lhs: Box::new(spanned(ExprKind::Ident("x".into()))),
                rhs: Box::new(spanned(ExprKind::IntLit(1))),
            })),
            span: dummy_span(),
        }],
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(43));
}

#[test]
fn eval_pattern_match_wildcard() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let expr = spanned(ExprKind::PatternMatch {
        scrutinee: Box::new(spanned(ExprKind::IntLit(999))),
        arms: vec![PatternArm {
            pattern: spanned(PatternKind::Wildcard),
            body: ArmBody::Expr(spanned(ExprKind::StringLit("caught".to_string()))),
            span: dummy_span(),
        }],
    });
    assert_eq!(
        eval_expr(&mut env, &expr).unwrap(),
        Value::Str("caught".to_string())
    );
}

#[test]
fn eval_pattern_match_qualified_variant() {
    let program = empty_program();
    let mut type_env = empty_type_env();

    // Register Duration enum with fieldless variants
    type_env.types.insert(
        "Duration".into(),
        DeclInfo::Enum(EnumInfo {
            name: "Duration".into(),
            ordered: false,
            variants: vec![
                VariantInfo {
                    name: "end_of_turn".into(),
                    fields: vec![],
                },
                VariantInfo {
                    name: "indefinite".into(),
                    fields: vec![],
                },
            ],
        }),
    );

    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let val = Value::EnumVariant {
        enum_name: "Duration".into(),
        variant: "end_of_turn".into(),
        fields: BTreeMap::new(),
    };
    env.bind(Name::from("dur"), val);

    let expr = spanned(ExprKind::PatternMatch {
        scrutinee: Box::new(spanned(ExprKind::Ident("dur".into()))),
        arms: vec![
            PatternArm {
                pattern: spanned(PatternKind::QualifiedVariant {
                    ty: "Duration".into(),
                    variant: "end_of_turn".into(),
                }),
                body: ArmBody::Expr(spanned(ExprKind::StringLit("eot".to_string()))),
                span: dummy_span(),
            },
            PatternArm {
                pattern: spanned(PatternKind::Wildcard),
                body: ArmBody::Expr(spanned(ExprKind::StringLit("other".to_string()))),
                span: dummy_span(),
            },
        ],
    });
    assert_eq!(
        eval_expr(&mut env, &expr).unwrap(),
        Value::Str("eot".to_string())
    );
}

#[test]
fn eval_pattern_match_qualified_destructure() {
    let program = empty_program();
    let mut type_env = empty_type_env();

    type_env.types.insert(
        "Duration".into(),
        DeclInfo::Enum(EnumInfo {
            name: "Duration".into(),
            ordered: false,
            variants: vec![VariantInfo {
                name: "rounds".into(),
                fields: vec![("n".into(), ttrpg_checker::ty::Ty::Int)],
            }],
        }),
    );

    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let mut fields = BTreeMap::new();
    fields.insert("n".into(), Value::Int(3));
    let val = Value::EnumVariant {
        enum_name: "Duration".into(),
        variant: "rounds".into(),
        fields,
    };
    env.bind(Name::from("dur"), val);

    // match dur { Duration.rounds(count) => count }
    let expr = spanned(ExprKind::PatternMatch {
        scrutinee: Box::new(spanned(ExprKind::Ident("dur".into()))),
        arms: vec![PatternArm {
            pattern: spanned(PatternKind::QualifiedDestructure {
                ty: "Duration".into(),
                variant: "rounds".into(),
                fields: vec![spanned(PatternKind::Ident("count".into()))],
            }),
            body: ArmBody::Expr(spanned(ExprKind::Ident("count".into()))),
            span: dummy_span(),
        }],
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(3));
}

// ── Let statement tests ────────────────────────────────────

#[test]
fn eval_let_binding() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    // Simulate: let x = 42; x + 1
    let block = spanned(vec![
        spanned(StmtKind::Let {
            name: "x".into(),
            ty: None,
            value: spanned(ExprKind::IntLit(42)),
        }),
        spanned(StmtKind::Expr(spanned(ExprKind::BinOp {
            op: BinOp::Add,
            lhs: Box::new(spanned(ExprKind::Ident("x".into()))),
            rhs: Box::new(spanned(ExprKind::IntLit(1))),
        }))),
    ]);
    assert_eq!(eval_block(&mut env, &block).unwrap(), Value::Int(43));
}

#[test]
fn eval_nested_scopes() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    // let x = 1; { let x = 2; x } + x should be 3
    // But we need to use two block evaluations to test scope isolation
    env.bind(Name::from("x"), Value::Int(1));
    let inner_block = spanned(vec![
        spanned(StmtKind::Let {
            name: "x".into(),
            ty: None,
            value: spanned(ExprKind::IntLit(2)),
        }),
        spanned(StmtKind::Expr(spanned(ExprKind::Ident("x".into())))),
    ]);
    let inner_result = eval_block(&mut env, &inner_block).unwrap();
    assert_eq!(inner_result, Value::Int(2));

    // After inner block, x should still be 1
    let outer_x = env.lookup("x").unwrap().clone();
    assert_eq!(outer_x, Value::Int(1));
}

// ── Call dispatch test ──────────────────────────────────────

#[test]
fn eval_call_undefined_function_error() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let expr = spanned(ExprKind::Call {
        callee: Box::new(spanned(ExprKind::Ident("foo".into()))),
        args: vec![],
    });
    let err = eval_expr(&mut env, &expr).unwrap_err();
    assert!(err.message.contains("undefined function"));
}

// ── value_eq unit tests ────────────────────────────────────

#[test]
fn value_eq_float_neg_zero() {
    let state = TestState::new();
    assert!(value_eq(&state, &Value::Float(-0.0), &Value::Float(0.0)));
}

#[test]
fn value_eq_float_nan() {
    let state = TestState::new();
    assert!(!value_eq(
        &state,
        &Value::Float(f64::NAN),
        &Value::Float(f64::NAN)
    ));
}

#[test]
fn value_eq_position_delegates() {
    let state = TestState::new();
    let p1 = Value::Position(PositionValue(Arc::new((5i64, 10i64))));
    let p2 = Value::Position(PositionValue(Arc::new((5i64, 10i64))));
    assert!(value_eq(&state, &p1, &p2)); // same logical position

    let p3 = Value::Position(PositionValue(Arc::new((5i64, 11i64))));
    assert!(!value_eq(&state, &p1, &p3)); // different position
}

#[test]
fn value_eq_composite_recursive() {
    let state = TestState::new();
    let a = Value::List(vec![Value::Float(-0.0), Value::Int(1)]);
    let b = Value::List(vec![Value::Float(0.0), Value::Int(1)]);
    assert!(value_eq(&state, &a, &b)); // -0.0 == +0.0 via value_eq
}

// ── Bare enum variant ident test ───────────────────────────

#[test]
fn eval_bare_fieldless_variant() {
    let program = empty_program();
    let mut type_env = empty_type_env();

    type_env.types.insert(
        "Color".into(),
        DeclInfo::Enum(EnumInfo {
            name: "Color".into(),
            ordered: false,
            variants: vec![
                VariantInfo {
                    name: "red".into(),
                    fields: vec![],
                },
                VariantInfo {
                    name: "blue".into(),
                    fields: vec![],
                },
            ],
        }),
    );
    type_env
        .variant_to_enums
        .entry("red".into())
        .or_default()
        .push("Color".into());
    type_env
        .variant_to_enums
        .entry("blue".into())
        .or_default()
        .push("Color".into());

    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let expr = spanned(ExprKind::Ident("red".into()));
    let result = eval_expr(&mut env, &expr).unwrap();
    assert_eq!(
        result,
        Value::EnumVariant {
            enum_name: "Color".into(),
            variant: "red".into(),
            fields: BTreeMap::new(),
        }
    );
}

// ── Qualified enum field access ────────────────────────────

#[test]
fn eval_qualified_enum_variant_via_field_access() {
    let program = empty_program();
    let mut type_env = empty_type_env();

    type_env.types.insert(
        "Color".into(),
        DeclInfo::Enum(EnumInfo {
            name: "Color".into(),
            ordered: false,
            variants: vec![VariantInfo {
                name: "red".into(),
                fields: vec![],
            }],
        }),
    );

    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    // Color.red
    let expr = spanned(ExprKind::FieldAccess {
        object: Box::new(spanned(ExprKind::Ident("Color".into()))),
        field: "red".into(),
    });
    assert_eq!(
        eval_expr(&mut env, &expr).unwrap(),
        Value::EnumVariant {
            enum_name: "Color".into(),
            variant: "red".into(),
            fields: BTreeMap::new(),
        }
    );
}

// ── Interpreter construction ───────────────────────────────

#[test]
fn interpreter_rejects_surviving_move() {
    use ttrpg_ast::ast::{MoveDecl, SystemBlock, TopLevel};

    let program = Program {
        items: vec![spanned(TopLevel::System(SystemBlock {
            name: "Test".into(),
            decls: vec![spanned(DeclKind::Move(MoveDecl {
                name: "TestMove".into(),
                receiver_name: "actor".into(),
                receiver_type: spanned(ttrpg_ast::ast::TypeExpr::Named("Character".into())),
                params: vec![],
                trigger_text: "test".into(),
                roll_expr: spanned(ExprKind::IntLit(0)),
                outcomes: vec![],
            }))],
        }))],
        ..Default::default()
    };
    let type_env = empty_type_env();
    match Interpreter::new(&program, &type_env) {
        Err(err) => assert!(err.message.contains("must be lowered")),
        Ok(_) => panic!("expected error for surviving Move decl"),
    }
}

// ── Enum variant field access ──────────────────────────────

#[test]
fn eval_field_access_enum_variant() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let mut fields = BTreeMap::new();
    fields.insert("n".into(), Value::Int(5));
    env.bind(
        "d".into(),
        Value::EnumVariant {
            enum_name: "Duration".into(),
            variant: "rounds".into(),
            fields,
        },
    );

    let expr = spanned(ExprKind::FieldAccess {
        object: Box::new(spanned(ExprKind::Ident("d".into()))),
        field: "n".into(),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(5));
}

// ── Dice literal with filter ───────────────────────────────

#[test]
fn eval_dice_lit_with_filter() {
    use ttrpg_ast::DiceFilter;

    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let expr = spanned(ExprKind::DiceLit {
        count: 4,
        sides: 6,
        filter: Some(DiceFilter::KeepHighest(3)),
    });
    let result = eval_expr(&mut env, &expr).unwrap();
    match result {
        Value::DiceExpr(de) => {
            assert_eq!(de.groups[0].count, 4);
            assert_eq!(de.groups[0].sides, 6);
            assert_eq!(de.groups[0].filter, Some(DiceFilter::KeepHighest(3)));
        }
        _ => panic!("expected DiceExpr"),
    }
}

// ── If with else-if chain ──────────────────────────────────

#[test]
fn eval_if_else_if_chain() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    // if false { 1 } else if true { 2 } else { 3 }
    // This is: If { cond: false, then: 1, else: If { cond: true, then: 2, else: 3 } }
    let expr = spanned(ExprKind::If {
        condition: Box::new(spanned(ExprKind::BoolLit(false))),
        then_block: spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::IntLit(1))))]),
        else_branch: Some(ElseBranch::If(Box::new(spanned(ExprKind::If {
            condition: Box::new(spanned(ExprKind::BoolLit(true))),
            then_block: spanned(vec![spanned(StmtKind::Expr(spanned(ExprKind::IntLit(2))))]),
            else_branch: Some(ElseBranch::Block(spanned(vec![spanned(StmtKind::Expr(
                spanned(ExprKind::IntLit(3)),
            ))]))),
        })))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(2));
}

// ── Bare enum variant pattern tests ────────────────────────

#[test]
fn eval_pattern_bare_variant_matches() {
    let program = empty_program();
    let mut type_env = empty_type_env();
    type_env.types.insert(
        "Color".into(),
        ttrpg_checker::env::DeclInfo::Enum(EnumInfo {
            name: "Color".into(),
            ordered: false,
            variants: vec![
                VariantInfo {
                    name: "red".into(),
                    fields: vec![],
                },
                VariantInfo {
                    name: "blue".into(),
                    fields: vec![],
                },
            ],
        }),
    );
    type_env
        .variant_to_enums
        .entry("red".into())
        .or_default()
        .push("Color".into());
    type_env
        .variant_to_enums
        .entry("blue".into())
        .or_default()
        .push("Color".into());

    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    // Pattern match with bare variant idents: match val { red => 1, blue => 2 }
    let val = Value::EnumVariant {
        enum_name: "Color".into(),
        variant: "blue".into(),
        fields: BTreeMap::new(),
    };
    env.bind(Name::from("val"), val);

    let expr = spanned(ExprKind::PatternMatch {
        scrutinee: Box::new(spanned(ExprKind::Ident("val".into()))),
        arms: vec![
            PatternArm {
                pattern: spanned(PatternKind::Ident("red".into())),
                body: ArmBody::Expr(spanned(ExprKind::IntLit(1))),
                span: dummy_span(),
            },
            PatternArm {
                pattern: spanned(PatternKind::Ident("blue".into())),
                body: ArmBody::Expr(spanned(ExprKind::IntLit(2))),
                span: dummy_span(),
            },
        ],
    });
    // `blue` should match the second arm, NOT the first (red should NOT act as a binding)
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(2));
}

#[test]
fn eval_pattern_bare_variant_no_match() {
    let program = empty_program();
    let mut type_env = empty_type_env();
    type_env.types.insert(
        "Color".into(),
        ttrpg_checker::env::DeclInfo::Enum(EnumInfo {
            name: "Color".into(),
            ordered: false,
            variants: vec![VariantInfo {
                name: "red".into(),
                fields: vec![],
            }],
        }),
    );
    type_env
        .variant_to_enums
        .entry("red".into())
        .or_default()
        .push("Color".into());

    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let env = make_env(&state, &mut handler, &interp);

    // Try to match `red` against an Int — should not match
    let mut bindings = HashMap::new();
    let result = match_pattern(
        &env,
        &PatternKind::Ident("red".into()),
        &Value::Int(42),
        &mut bindings,
    );
    assert!(!result);
    assert!(bindings.is_empty());
}

#[test]
fn eval_pattern_binding_still_works_for_non_variant() {
    let program = empty_program();
    let type_env = empty_type_env();
    // No variants registered — "x" is purely a binding
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let env = make_env(&state, &mut handler, &interp);

    let mut bindings = HashMap::new();
    let result = match_pattern(
        &env,
        &PatternKind::Ident("x".into()),
        &Value::Int(42),
        &mut bindings,
    );
    assert!(result);
    assert_eq!(bindings.get("x"), Some(&Value::Int(42)));
}

// ── DiceExpr arithmetic tests ──────────────────────────────

#[test]
fn eval_dice_add_int() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(
        "d".into(),
        Value::DiceExpr(DiceExpr::single(1, 20, None, 0)),
    );

    // d + 5
    let expr = spanned(ExprKind::BinOp {
        op: BinOp::Add,
        lhs: Box::new(spanned(ExprKind::Ident("d".into()))),
        rhs: Box::new(spanned(ExprKind::IntLit(5))),
    });
    match eval_expr(&mut env, &expr).unwrap() {
        Value::DiceExpr(de) => {
            assert_eq!(de.groups[0].count, 1);
            assert_eq!(de.groups[0].sides, 20);
            assert_eq!(de.modifier, 5);
        }
        other => panic!("expected DiceExpr, got {:?}", other),
    }
}

#[test]
fn eval_int_add_dice() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(
        "d".into(),
        Value::DiceExpr(DiceExpr::single(2, 6, None, 3)),
    );

    // 10 + d
    let expr = spanned(ExprKind::BinOp {
        op: BinOp::Add,
        lhs: Box::new(spanned(ExprKind::IntLit(10))),
        rhs: Box::new(spanned(ExprKind::Ident("d".into()))),
    });
    match eval_expr(&mut env, &expr).unwrap() {
        Value::DiceExpr(de) => {
            assert_eq!(de.groups[0].count, 2);
            assert_eq!(de.groups[0].sides, 6);
            assert_eq!(de.modifier, 13);
        }
        other => panic!("expected DiceExpr, got {:?}", other),
    }
}

#[test]
fn eval_dice_add_dice() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(
        "a".into(),
        Value::DiceExpr(DiceExpr::single(2, 6, None, 1)),
    );
    env.bind(
        "b".into(),
        Value::DiceExpr(DiceExpr::single(3, 6, None, 2)),
    );

    // a + b → 2 groups (2d6, 3d6) with modifier 3
    let expr = spanned(ExprKind::BinOp {
        op: BinOp::Add,
        lhs: Box::new(spanned(ExprKind::Ident("a".into()))),
        rhs: Box::new(spanned(ExprKind::Ident("b".into()))),
    });
    match eval_expr(&mut env, &expr).unwrap() {
        Value::DiceExpr(de) => {
            assert_eq!(de.groups.len(), 2);
            assert_eq!(de.groups[0].count, 2);
            assert_eq!(de.groups[0].sides, 6);
            assert_eq!(de.groups[1].count, 3);
            assert_eq!(de.groups[1].sides, 6);
            assert_eq!(de.modifier, 3);
        }
        other => panic!("expected DiceExpr, got {:?}", other),
    }
}

#[test]
fn eval_dice_sub_int() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(
        "d".into(),
        Value::DiceExpr(DiceExpr::single(1, 20, None, 5)),
    );

    // d - 3
    let expr = spanned(ExprKind::BinOp {
        op: BinOp::Sub,
        lhs: Box::new(spanned(ExprKind::Ident("d".into()))),
        rhs: Box::new(spanned(ExprKind::IntLit(3))),
    });
    match eval_expr(&mut env, &expr).unwrap() {
        Value::DiceExpr(de) => {
            assert_eq!(de.groups[0].count, 1);
            assert_eq!(de.groups[0].sides, 20);
            assert_eq!(de.modifier, 2);
        }
        other => panic!("expected DiceExpr, got {:?}", other),
    }
}

// ── GuardMatch non-bool guard error test ───────────────────

#[test]
fn eval_guard_match_non_bool_error() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    // match { 42 => ... } — guard evaluates to Int, not Bool
    let expr = spanned(ExprKind::GuardMatch {
        arms: vec![GuardArm {
            guard: GuardKind::Expr(spanned(ExprKind::IntLit(42))),
            body: ArmBody::Expr(spanned(ExprKind::IntLit(1))),
            span: dummy_span(),
        }],
    });
    let err = eval_expr(&mut env, &expr).unwrap_err();
    assert!(err.message.contains("guard expression must be Bool"));
}

// ── Scope cleanup on error test ────────────────────────────

#[test]
fn eval_block_error_cleans_scope() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let scope_depth_before = env.scopes.len();

    // Block that contains an error (undefined variable)
    let block: ttrpg_ast::ast::Block = spanned(vec![spanned(StmtKind::Expr(spanned(
        ExprKind::Ident("undefined_var".into()),
    )))]);
    let result = eval_block(&mut env, &block);
    assert!(result.is_err());

    // Scope stack should be restored to its pre-block state
    assert_eq!(env.scopes.len(), scope_depth_before);
}

#[test]
fn eval_pattern_match_error_in_arm_cleans_scope() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let scope_depth_before = env.scopes.len();

    // Pattern match where the matched arm body errors
    let expr = spanned(ExprKind::PatternMatch {
        scrutinee: Box::new(spanned(ExprKind::IntLit(1))),
        arms: vec![PatternArm {
            pattern: spanned(PatternKind::Wildcard),
            body: ArmBody::Expr(spanned(ExprKind::Ident("undefined_var".into()))),
            span: dummy_span(),
        }],
    });
    let result = eval_expr(&mut env, &expr);
    assert!(result.is_err());

    // Scope stack should be restored
    assert_eq!(env.scopes.len(), scope_depth_before);
}

// ── Issue fix: qualified enum access respects scoping ──────

#[test]
fn eval_qualified_enum_access_via_paren() {
    // (Color).red should work — parenthesized enum namespace access
    let program = empty_program();
    let mut type_env = empty_type_env();
    type_env.types.insert(
        "Color".into(),
        DeclInfo::Enum(EnumInfo {
            name: "Color".into(),
            ordered: false,
            variants: vec![VariantInfo {
                name: "red".into(),
                fields: vec![],
            }],
        }),
    );
    type_env
        .variant_to_enums
        .entry("red".into())
        .or_default()
        .push("Color".into());

    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    // (Color).red — parenthesized
    let expr = spanned(ExprKind::FieldAccess {
        object: Box::new(spanned(ExprKind::Paren(Box::new(spanned(
            ExprKind::Ident("Color".into()),
        ))))),
        field: "red".into(),
    });
    let result = eval_expr(&mut env, &expr).unwrap();
    assert_eq!(
        result,
        Value::EnumVariant {
            enum_name: "Color".into(),
            variant: "red".into(),
            fields: BTreeMap::new(),
        }
    );
}

#[test]
fn eval_qualified_enum_access_shadowed_by_local() {
    // If a local variable shadows an enum type name, field access
    // should resolve the local, not the enum namespace.
    let program = empty_program();
    let mut type_env = empty_type_env();
    type_env.types.insert(
        "Color".into(),
        DeclInfo::Enum(EnumInfo {
            name: "Color".into(),
            ordered: false,
            variants: vec![VariantInfo {
                name: "red".into(),
                fields: vec![],
            }],
        }),
    );
    type_env
        .variant_to_enums
        .entry("red".into())
        .or_default()
        .push("Color".into());

    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    // Bind "Color" as a local struct value
    let mut struct_fields = BTreeMap::new();
    struct_fields.insert("name".into(), Value::Str("my_color".to_string()));
    env.bind(
        "Color".into(),
        Value::Struct {
            name: "MyStruct".into(),
            fields: struct_fields,
        },
    );

    // Color.name should resolve local struct, not enum namespace
    let expr = spanned(ExprKind::FieldAccess {
        object: Box::new(spanned(ExprKind::Ident("Color".into()))),
        field: "name".into(),
    });
    let result = eval_expr(&mut env, &expr).unwrap();
    assert_eq!(result, Value::Str("my_color".to_string()));
}

#[test]
fn eval_enum_namespace_not_usable_as_value() {
    // Using an enum type name as a standalone expression (not in field access)
    // should produce an EnumNamespace value (which would fail in most contexts).
    let program = empty_program();
    let mut type_env = empty_type_env();
    type_env.types.insert(
        "Color".into(),
        DeclInfo::Enum(EnumInfo {
            name: "Color".into(),
            ordered: false,
            variants: vec![],
        }),
    );

    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let expr = spanned(ExprKind::Ident("Color".into()));
    let result = eval_expr(&mut env, &expr).unwrap();
    assert!(matches!(result, Value::EnumNamespace(ref s) if s == "Color"));
}

// ── Issue fix: RollResult coercion not applied to `in` ────

#[test]
fn eval_in_roll_result_no_coercion() {
    // `roll_result in list<RollResult>` should match structurally,
    // not coerce to Int first.
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let roll = Value::RollResult(RollResult {
        expr: DiceExpr::single(1, 20, None, 0),
        dice: vec![15],
        kept: vec![15],
        modifier: 0,
        total: 15,
        unmodified: 15,
    });

    env.bind(Name::from("r"), roll.clone());
    env.bind(Name::from("rolls"), Value::List(vec![roll]));

    let expr = spanned(ExprKind::BinOp {
        op: BinOp::In,
        lhs: Box::new(spanned(ExprKind::Ident("r".into()))),
        rhs: Box::new(spanned(ExprKind::Ident("rolls".into()))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));
}

#[test]
fn eval_in_roll_result_not_in_int_list() {
    // `roll_result in list<Int>` should be false (different types),
    // not coerced-true.
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let roll = Value::RollResult(RollResult {
        expr: DiceExpr::single(1, 20, None, 0),
        dice: vec![15],
        kept: vec![15],
        modifier: 0,
        total: 15,
        unmodified: 15,
    });

    env.bind(Name::from("r"), roll);
    // List contains Int(15) — same total but different type
    env.bind(Name::from("ints"), Value::List(vec![Value::Int(15)]));

    let expr = spanned(ExprKind::BinOp {
        op: BinOp::In,
        lhs: Box::new(spanned(ExprKind::Ident("r".into()))),
        rhs: Box::new(spanned(ExprKind::Ident("ints".into()))),
    });
    // Should be false — RollResult != Int even though total matches
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(false));
}

// ── Issue fix: dice arithmetic overflow and spec validation ──

#[test]
fn eval_dice_add_dice_different_sides_error() {
    // 2d6 + 3d8 should error — different dice specs
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(
        "a".into(),
        Value::DiceExpr(DiceExpr::single(2, 6, None, 0)),
    );
    env.bind(
        "b".into(),
        Value::DiceExpr(DiceExpr::single(3, 8, None, 0)),
    );

    let expr = spanned(ExprKind::BinOp {
        op: BinOp::Add,
        lhs: Box::new(spanned(ExprKind::Ident("a".into()))),
        rhs: Box::new(spanned(ExprKind::Ident("b".into()))),
    });
    // With component-based DiceExpr, different sides are allowed (creates 2 groups)
    match eval_expr(&mut env, &expr).unwrap() {
        Value::DiceExpr(de) => {
            assert_eq!(de.groups.len(), 2);
            assert_eq!(de.groups[0].count, 2);
            assert_eq!(de.groups[0].sides, 6);
            assert_eq!(de.groups[1].count, 3);
            assert_eq!(de.groups[1].sides, 8);
            assert_eq!(de.modifier, 0);
        }
        other => panic!("expected DiceExpr, got {:?}", other),
    }
}

#[test]
fn eval_dice_add_int_overflow() {
    // DiceExpr with modifier near i64::MAX + Int should overflow
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(
        "d".into(),
        Value::DiceExpr(DiceExpr::single(1, 20, None, i64::MAX)),
    );

    let expr = spanned(ExprKind::BinOp {
        op: BinOp::Add,
        lhs: Box::new(spanned(ExprKind::Ident("d".into()))),
        rhs: Box::new(spanned(ExprKind::IntLit(1))),
    });
    let result = eval_expr(&mut env, &expr);
    assert!(result.is_err());
    assert!(result.unwrap_err().message.contains("overflow"));
}

#[test]
fn eval_dice_sub_int_overflow() {
    // DiceExpr with modifier near i64::MIN - Int should overflow
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(
        "d".into(),
        Value::DiceExpr(DiceExpr::single(1, 20, None, i64::MIN)),
    );

    let expr = spanned(ExprKind::BinOp {
        op: BinOp::Sub,
        lhs: Box::new(spanned(ExprKind::Ident("d".into()))),
        rhs: Box::new(spanned(ExprKind::IntLit(1))),
    });
    let result = eval_expr(&mut env, &expr);
    assert!(result.is_err());
    assert!(result.unwrap_err().message.contains("overflow"));
}

#[test]
fn eval_dice_add_dice_modifier_overflow() {
    // Two DiceExpr with modifiers near i64::MAX should overflow on addition
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(
        "a".into(),
        Value::DiceExpr(DiceExpr::single(1, 6, None, i64::MAX)),
    );
    env.bind(
        "b".into(),
        Value::DiceExpr(DiceExpr::single(1, 6, None, 1)),
    );

    let expr = spanned(ExprKind::BinOp {
        op: BinOp::Add,
        lhs: Box::new(spanned(ExprKind::Ident("a".into()))),
        rhs: Box::new(spanned(ExprKind::Ident("b".into()))),
    });
    let result = eval_expr(&mut env, &expr);
    assert!(result.is_err());
    assert!(result.unwrap_err().message.contains("overflow"));
}

#[test]
fn eval_dice_add_dice_same_spec_succeeds() {
    // 2d6+1 + 3d6+2 → 2 groups with combined modifier 3
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(
        "a".into(),
        Value::DiceExpr(DiceExpr::single(2, 6, None, 1)),
    );
    env.bind(
        "b".into(),
        Value::DiceExpr(DiceExpr::single(3, 6, None, 2)),
    );

    let expr = spanned(ExprKind::BinOp {
        op: BinOp::Add,
        lhs: Box::new(spanned(ExprKind::Ident("a".into()))),
        rhs: Box::new(spanned(ExprKind::Ident("b".into()))),
    });
    match eval_expr(&mut env, &expr).unwrap() {
        Value::DiceExpr(de) => {
            assert_eq!(de.groups.len(), 2);
            assert_eq!(de.groups[0].count, 2);
            assert_eq!(de.groups[0].sides, 6);
            assert_eq!(de.groups[1].count, 3);
            assert_eq!(de.groups[1].sides, 6);
            assert_eq!(de.modifier, 3);
        }
        other => panic!("expected DiceExpr, got {:?}", other),
    }
}

// ── Issue 1: == / != coerce RollResult; Int↔Float equality ──

#[test]
fn eq_coerces_roll_result_to_int() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    // Bind `r` to a RollResult with total=10
    env.bind(
        "r".into(),
        Value::RollResult(RollResult {
            expr: DiceExpr::single(1, 20, None, 0),
            dice: vec![10],
            kept: vec![10],
            modifier: 0,
            total: 10,
            unmodified: 10,
        }),
    );

    // r == 10 should be true (coerced)
    let expr = spanned(ExprKind::BinOp {
        op: BinOp::Eq,
        lhs: Box::new(spanned(ExprKind::Ident("r".into()))),
        rhs: Box::new(spanned(ExprKind::IntLit(10))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));

    // r != 10 should be false
    let expr = spanned(ExprKind::BinOp {
        op: BinOp::NotEq,
        lhs: Box::new(spanned(ExprKind::Ident("r".into()))),
        rhs: Box::new(spanned(ExprKind::IntLit(10))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(false));

    // r == 99 should be false
    let expr = spanned(ExprKind::BinOp {
        op: BinOp::Eq,
        lhs: Box::new(spanned(ExprKind::Ident("r".into()))),
        rhs: Box::new(spanned(ExprKind::IntLit(99))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(false));
}

#[test]
fn value_eq_int_float_cross_type() {
    let state = TestState::new();
    assert!(value_eq(&state, &Value::Int(1), &Value::Float(1.0)));
    assert!(value_eq(&state, &Value::Float(1.0), &Value::Int(1)));
    assert!(!value_eq(&state, &Value::Int(1), &Value::Float(1.5)));
    assert!(!value_eq(&state, &Value::Float(1.5), &Value::Int(1)));
}

#[test]
fn value_eq_int_float_boundary() {
    let state = TestState::new();

    // i64::MAX as f64 rounds up to 2^63 — must NOT equal i64::MAX
    let max_f = i64::MAX as f64; // 9223372036854775808.0
    assert!(!value_eq(
        &state,
        &Value::Int(i64::MAX),
        &Value::Float(max_f)
    ));
    assert!(!value_eq(
        &state,
        &Value::Float(max_f),
        &Value::Int(i64::MAX)
    ));

    // i64::MIN as f64 is exactly -2^63 — SHOULD equal i64::MIN
    let min_f = i64::MIN as f64; // -9223372036854775808.0
    assert!(value_eq(
        &state,
        &Value::Int(i64::MIN),
        &Value::Float(min_f)
    ));
    assert!(value_eq(
        &state,
        &Value::Float(min_f),
        &Value::Int(i64::MIN)
    ));

    // Large float above i64 range
    assert!(!value_eq(
        &state,
        &Value::Int(i64::MAX),
        &Value::Float(1.0e19)
    ));
    assert!(!value_eq(
        &state,
        &Value::Int(i64::MIN),
        &Value::Float(-1.0e19)
    ));

    // Largest f64 below 2^63 (still in i64 range) should round-trip correctly
    let largest_below = 9223372036854774784.0_f64; // 2^63 - 1024
    assert!(value_eq(
        &state,
        &Value::Int(9223372036854774784),
        &Value::Float(largest_below),
    ));
    assert!(!value_eq(
        &state,
        &Value::Int(i64::MAX),
        &Value::Float(largest_below),
    ));
}

#[test]
fn int_float_cmp_boundary() {
    use std::cmp::Ordering;

    // i64::MAX < (i64::MAX as f64) because the float rounds up to 2^63
    assert_eq!(
        int_float_cmp(i64::MAX, i64::MAX as f64),
        Some(Ordering::Less)
    );

    // i64::MIN == (i64::MIN as f64) because -2^63 is exact
    assert_eq!(
        int_float_cmp(i64::MIN, i64::MIN as f64),
        Some(Ordering::Equal)
    );

    // i64::MAX vs very large float
    assert_eq!(int_float_cmp(i64::MAX, 1.0e19), Some(Ordering::Less));

    // i64::MIN vs very negative float
    assert_eq!(int_float_cmp(i64::MIN, -1.0e19), Some(Ordering::Greater));

    // NaN → None
    assert_eq!(int_float_cmp(0, f64::NAN), None);

    // Infinity
    assert_eq!(int_float_cmp(i64::MAX, f64::INFINITY), Some(Ordering::Less));
    assert_eq!(
        int_float_cmp(i64::MIN, f64::NEG_INFINITY),
        Some(Ordering::Greater)
    );

    // Largest f64 below 2^63
    let largest_below = 9223372036854774784.0_f64;
    assert_eq!(
        int_float_cmp(9223372036854774784, largest_below),
        Some(Ordering::Equal),
    );
    assert_eq!(
        int_float_cmp(i64::MAX, largest_below),
        Some(Ordering::Greater),
    );
}

#[test]
fn int_float_eq_helper_edge_cases() {
    // Basic exact matches
    assert!(int_float_eq(0, 0.0));
    assert!(int_float_eq(0, -0.0)); // -0.0 == +0.0
    assert!(int_float_eq(-1, -1.0));

    // Fractional → never equal
    assert!(!int_float_eq(1, 1.5));
    assert!(!int_float_eq(0, 0.1));

    // Non-finite → never equal
    assert!(!int_float_eq(0, f64::NAN));
    assert!(!int_float_eq(0, f64::INFINITY));
    assert!(!int_float_eq(0, f64::NEG_INFINITY));

    // 2^53 boundary (largest exact integer in f64)
    let two_53: i64 = 1 << 53;
    assert!(int_float_eq(two_53, two_53 as f64));
    assert!(!int_float_eq(two_53 + 1, (two_53 + 1) as f64));
}

// ── Issue 2: Enum ordering uses declaration order ───────────

#[test]
fn enum_ordering_uses_declaration_order() {
    let program = empty_program();
    let mut type_env = empty_type_env();

    // Declare enum Size { small, medium, large }
    // Declaration order: small=0, medium=1, large=2
    // Alphabetical would be: large < medium < small — opposite!
    type_env.types.insert(
        "Size".into(),
        DeclInfo::Enum(EnumInfo {
            name: "Size".into(),
            ordered: false,
            variants: vec![
                VariantInfo {
                    name: "small".into(),
                    fields: vec![],
                },
                VariantInfo {
                    name: "medium".into(),
                    fields: vec![],
                },
                VariantInfo {
                    name: "large".into(),
                    fields: vec![],
                },
            ],
        }),
    );
    type_env
        .variant_to_enums
        .entry("small".into())
        .or_default()
        .push("Size".into());
    type_env
        .variant_to_enums
        .entry("medium".into())
        .or_default()
        .push("Size".into());
    type_env
        .variant_to_enums
        .entry("large".into())
        .or_default()
        .push("Size".into());

    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(
        Name::from("a"),
        Value::EnumVariant {
            enum_name: "Size".into(),
            variant: "small".into(),
            fields: BTreeMap::new(),
        },
    );
    env.bind(
        Name::from("b"),
        Value::EnumVariant {
            enum_name: "Size".into(),
            variant: "large".into(),
            fields: BTreeMap::new(),
        },
    );

    // small < large should be true (declaration order: 0 < 2)
    let expr = spanned(ExprKind::BinOp {
        op: BinOp::Lt,
        lhs: Box::new(spanned(ExprKind::Ident("a".into()))),
        rhs: Box::new(spanned(ExprKind::Ident("b".into()))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));

    // large > small should be true
    let expr = spanned(ExprKind::BinOp {
        op: BinOp::Gt,
        lhs: Box::new(spanned(ExprKind::Ident("b".into()))),
        rhs: Box::new(spanned(ExprKind::Ident("a".into()))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));

    // small >= large should be false
    let expr = spanned(ExprKind::BinOp {
        op: BinOp::GtEq,
        lhs: Box::new(spanned(ExprKind::Ident("a".into()))),
        rhs: Box::new(spanned(ExprKind::Ident("b".into()))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(false));
}

// ── ordinal / from_ordinal ──────────────────────────────────

#[test]
fn ordinal_returns_declaration_index() {
    let program = empty_program();
    let mut type_env = empty_type_env();

    type_env.types.insert(
        "Size".into(),
        DeclInfo::Enum(EnumInfo {
            name: "Size".into(),
            ordered: true,
            variants: vec![
                VariantInfo {
                    name: "small".into(),
                    fields: vec![],
                },
                VariantInfo {
                    name: "medium".into(),
                    fields: vec![],
                },
                VariantInfo {
                    name: "large".into(),
                    fields: vec![],
                },
            ],
        }),
    );
    type_env
        .variant_to_enums
        .entry("small".into())
        .or_default()
        .push("Size".into());
    type_env
        .variant_to_enums
        .entry("medium".into())
        .or_default()
        .push("Size".into());
    type_env
        .variant_to_enums
        .entry("large".into())
        .or_default()
        .push("Size".into());

    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    // ordinal(small) == 0
    env.bind(
        Name::from("s"),
        Value::EnumVariant {
            enum_name: "Size".into(),
            variant: "small".into(),
            fields: BTreeMap::new(),
        },
    );
    let expr = spanned(ExprKind::Call {
        callee: Box::new(spanned(ExprKind::Ident("ordinal".into()))),
        args: vec![ttrpg_ast::ast::Arg {
            name: None,
            value: spanned(ExprKind::Ident("s".into())),
            span: dummy_span(),
        }],
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(0));

    // ordinal(large) == 2
    env.bind(
        Name::from("l"),
        Value::EnumVariant {
            enum_name: "Size".into(),
            variant: "large".into(),
            fields: BTreeMap::new(),
        },
    );
    let expr = spanned(ExprKind::Call {
        callee: Box::new(spanned(ExprKind::Ident("ordinal".into()))),
        args: vec![ttrpg_ast::ast::Arg {
            name: None,
            value: spanned(ExprKind::Ident("l".into())),
            span: dummy_span(),
        }],
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Int(2));
}

#[test]
fn from_ordinal_returns_correct_variant() {
    let program = empty_program();
    let mut type_env = empty_type_env();

    type_env.types.insert(
        "Size".into(),
        DeclInfo::Enum(EnumInfo {
            name: "Size".into(),
            ordered: true,
            variants: vec![
                VariantInfo {
                    name: "small".into(),
                    fields: vec![],
                },
                VariantInfo {
                    name: "medium".into(),
                    fields: vec![],
                },
                VariantInfo {
                    name: "large".into(),
                    fields: vec![],
                },
            ],
        }),
    );

    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(Name::from("ns"), Value::EnumNamespace("Size".into()));
    env.bind(Name::from("idx"), Value::Int(1));

    let expr = spanned(ExprKind::Call {
        callee: Box::new(spanned(ExprKind::Ident("from_ordinal".into()))),
        args: vec![
            ttrpg_ast::ast::Arg {
                name: None,
                value: spanned(ExprKind::Ident("ns".into())),
                span: dummy_span(),
            },
            ttrpg_ast::ast::Arg {
                name: None,
                value: spanned(ExprKind::Ident("idx".into())),
                span: dummy_span(),
            },
        ],
    });
    assert_eq!(
        eval_expr(&mut env, &expr).unwrap(),
        Value::EnumVariant {
            enum_name: "Size".into(),
            variant: "medium".into(),
            fields: BTreeMap::new(),
        }
    );
}

#[test]
fn from_ordinal_out_of_bounds_error() {
    let program = empty_program();
    let mut type_env = empty_type_env();

    type_env.types.insert(
        "Size".into(),
        DeclInfo::Enum(EnumInfo {
            name: "Size".into(),
            ordered: true,
            variants: vec![
                VariantInfo {
                    name: "small".into(),
                    fields: vec![],
                },
                VariantInfo {
                    name: "medium".into(),
                    fields: vec![],
                },
            ],
        }),
    );

    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(Name::from("ns"), Value::EnumNamespace("Size".into()));
    env.bind(Name::from("idx"), Value::Int(5));

    let expr = spanned(ExprKind::Call {
        callee: Box::new(spanned(ExprKind::Ident("from_ordinal".into()))),
        args: vec![
            ttrpg_ast::ast::Arg {
                name: None,
                value: spanned(ExprKind::Ident("ns".into())),
                span: dummy_span(),
            },
            ttrpg_ast::ast::Arg {
                name: None,
                value: spanned(ExprKind::Ident("idx".into())),
                span: dummy_span(),
            },
        ],
    });
    let err = eval_expr(&mut env, &expr).unwrap_err();
    assert!(err.message.contains("out of range"), "got: {}", err.message);
}

#[test]
fn from_ordinal_negative_index_error() {
    let program = empty_program();
    let mut type_env = empty_type_env();

    type_env.types.insert(
        "Size".into(),
        DeclInfo::Enum(EnumInfo {
            name: "Size".into(),
            ordered: true,
            variants: vec![VariantInfo {
                name: "small".into(),
                fields: vec![],
            }],
        }),
    );

    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(Name::from("ns"), Value::EnumNamespace("Size".into()));
    env.bind(Name::from("idx"), Value::Int(-1));

    let expr = spanned(ExprKind::Call {
        callee: Box::new(spanned(ExprKind::Ident("from_ordinal".into()))),
        args: vec![
            ttrpg_ast::ast::Arg {
                name: None,
                value: spanned(ExprKind::Ident("ns".into())),
                span: dummy_span(),
            },
            ttrpg_ast::ast::Arg {
                name: None,
                value: spanned(ExprKind::Ident("idx".into())),
                span: dummy_span(),
            },
        ],
    });
    let err = eval_expr(&mut env, &expr).unwrap_err();
    assert!(err.message.contains("non-negative"), "got: {}", err.message);
}

#[test]
fn try_from_ordinal_returns_some_on_valid_index() {
    let program = empty_program();
    let mut type_env = empty_type_env();

    type_env.types.insert(
        "Size".into(),
        DeclInfo::Enum(EnumInfo {
            name: "Size".into(),
            ordered: true,
            variants: vec![
                VariantInfo {
                    name: "small".into(),
                    fields: vec![],
                },
                VariantInfo {
                    name: "medium".into(),
                    fields: vec![],
                },
                VariantInfo {
                    name: "large".into(),
                    fields: vec![],
                },
            ],
        }),
    );

    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(Name::from("ns"), Value::EnumNamespace("Size".into()));
    env.bind(Name::from("idx"), Value::Int(2));

    let expr = spanned(ExprKind::Call {
        callee: Box::new(spanned(ExprKind::Ident("try_from_ordinal".into()))),
        args: vec![
            ttrpg_ast::ast::Arg {
                name: None,
                value: spanned(ExprKind::Ident("ns".into())),
                span: dummy_span(),
            },
            ttrpg_ast::ast::Arg {
                name: None,
                value: spanned(ExprKind::Ident("idx".into())),
                span: dummy_span(),
            },
        ],
    });
    assert_eq!(
        eval_expr(&mut env, &expr).unwrap(),
        Value::EnumVariant {
            enum_name: "Size".into(),
            variant: "large".into(),
            fields: BTreeMap::new(),
        }
    );
}

#[test]
fn try_from_ordinal_returns_none_on_out_of_bounds() {
    let program = empty_program();
    let mut type_env = empty_type_env();

    type_env.types.insert(
        "Size".into(),
        DeclInfo::Enum(EnumInfo {
            name: "Size".into(),
            ordered: true,
            variants: vec![VariantInfo {
                name: "small".into(),
                fields: vec![],
            }],
        }),
    );

    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(Name::from("ns"), Value::EnumNamespace("Size".into()));
    env.bind(Name::from("idx"), Value::Int(5));

    let expr = spanned(ExprKind::Call {
        callee: Box::new(spanned(ExprKind::Ident("try_from_ordinal".into()))),
        args: vec![
            ttrpg_ast::ast::Arg {
                name: None,
                value: spanned(ExprKind::Ident("ns".into())),
                span: dummy_span(),
            },
            ttrpg_ast::ast::Arg {
                name: None,
                value: spanned(ExprKind::Ident("idx".into())),
                span: dummy_span(),
            },
        ],
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::None);
}

#[test]
fn try_from_ordinal_returns_none_on_negative() {
    let program = empty_program();
    let mut type_env = empty_type_env();

    type_env.types.insert(
        "Size".into(),
        DeclInfo::Enum(EnumInfo {
            name: "Size".into(),
            ordered: true,
            variants: vec![VariantInfo {
                name: "small".into(),
                fields: vec![],
            }],
        }),
    );

    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(Name::from("ns"), Value::EnumNamespace("Size".into()));
    env.bind(Name::from("idx"), Value::Int(-1));

    let expr = spanned(ExprKind::Call {
        callee: Box::new(spanned(ExprKind::Ident("try_from_ordinal".into()))),
        args: vec![
            ttrpg_ast::ast::Arg {
                name: None,
                value: spanned(ExprKind::Ident("ns".into())),
                span: dummy_span(),
            },
            ttrpg_ast::ast::Arg {
                name: None,
                value: spanned(ExprKind::Ident("idx".into())),
                span: dummy_span(),
            },
        ],
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::None);
}

// ── Issue 3: none == Option(None) ───────────────────────────

#[test]
fn value_eq_none_vs_option_none() {
    let state = TestState::new();

    // Value::None == Value::Option(None)
    assert!(value_eq(&state, &Value::None, &Value::Option(None)));
    assert!(value_eq(&state, &Value::Option(None), &Value::None));

    // Value::None != Value::Option(Some(...))
    assert!(!value_eq(
        &state,
        &Value::None,
        &Value::Option(Some(Box::new(Value::Int(1))))
    ));
    assert!(!value_eq(
        &state,
        &Value::Option(Some(Box::new(Value::Int(1)))),
        &Value::None
    ));
}

#[test]
fn binop_eq_none_vs_option_none() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(Name::from("x"), Value::Option(None));

    // x == none should be true
    let expr = spanned(ExprKind::BinOp {
        op: BinOp::Eq,
        lhs: Box::new(spanned(ExprKind::Ident("x".into()))),
        rhs: Box::new(spanned(ExprKind::NoneLit)),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));

    // x != none should be false
    let expr = spanned(ExprKind::BinOp {
        op: BinOp::NotEq,
        lhs: Box::new(spanned(ExprKind::Ident("x".into()))),
        rhs: Box::new(spanned(ExprKind::NoneLit)),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(false));
}

// ── Condition identifier resolution ───────────────────────

#[test]
fn eval_ident_condition_name() {
    use ttrpg_ast::ast::{ConditionDecl, SystemBlock, TopLevel};

    let mut program = Program {
        items: vec![spanned(TopLevel::System(SystemBlock {
            name: "Test".into(),
            decls: vec![spanned(DeclKind::Condition(ConditionDecl {
                name: "Stunned".into(),
                params: vec![],
                extends: vec![],
                receiver_name: "bearer".into(),
                receiver_type: spanned(TypeExpr::Named("Character".into())),
                receiver_with_groups: WithClause::default(),
                clauses: vec![],
            }))],
        }))],
        ..Default::default()
    };
    program.build_index();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let expr = spanned(ExprKind::Ident("Stunned".into()));
    assert_eq!(
        eval_expr(&mut env, &expr).unwrap(),
        Value::Condition {
            name: "Stunned".into(),
            args: BTreeMap::new()
        }
    );
}

#[test]
fn eval_ident_condition_eq() {
    use ttrpg_ast::ast::{ConditionDecl, SystemBlock, TopLevel};

    let mut program = Program {
        items: vec![spanned(TopLevel::System(SystemBlock {
            name: "Test".into(),
            decls: vec![
                spanned(DeclKind::Condition(ConditionDecl {
                    name: "Stunned".into(),
                    params: vec![],

                    extends: vec![],
                    receiver_name: "bearer".into(),
                    receiver_type: spanned(TypeExpr::Named("Character".into())),
                    receiver_with_groups: WithClause::default(),
                    clauses: vec![],
                })),
                spanned(DeclKind::Condition(ConditionDecl {
                    name: "Prone".into(),
                    params: vec![],

                    extends: vec![],
                    receiver_name: "bearer".into(),
                    receiver_type: spanned(TypeExpr::Named("Character".into())),
                    receiver_with_groups: WithClause::default(),
                    clauses: vec![],
                })),
            ],
        }))],
        ..Default::default()
    };
    program.build_index();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    // Same condition == itself
    let expr = spanned(ExprKind::BinOp {
        op: BinOp::Eq,
        lhs: Box::new(spanned(ExprKind::Ident("Stunned".into()))),
        rhs: Box::new(spanned(ExprKind::Ident("Stunned".into()))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));

    // Different conditions != each other
    let expr = spanned(ExprKind::BinOp {
        op: BinOp::Eq,
        lhs: Box::new(spanned(ExprKind::Ident("Stunned".into()))),
        rhs: Box::new(spanned(ExprKind::Ident("Prone".into()))),
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(false));
}

// ── Phase 3: Statement Execution tests ─────────────────────

// Helper to build an LValue
fn make_lvalue(root: &str, segments: Vec<LValueSegment>) -> LValue {
    LValue {
        root: Name::from(root),
        segments,
        span: dummy_span(),
    }
}

// Helper to build an Assign statement
fn make_assign(target: LValue, op: AssignOp, value: Spanned<ExprKind>) -> Spanned<StmtKind> {
    spanned(StmtKind::Assign { target, op, value })
}

// Helper to build a Let statement
fn make_let(name: &str, value: Spanned<ExprKind>) -> Spanned<StmtKind> {
    spanned(StmtKind::Let {
        name: Name::from(name),
        ty: None,
        value,
    })
}

// ── Let binding tests ──────────────────────────────────────

#[test]
fn assign_let_bindings_visible_in_scope() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    // let x = 42
    let stmt = make_let("x", spanned(ExprKind::IntLit(42)));
    eval_stmt(&mut env, &stmt).unwrap();
    assert_eq!(env.lookup("x"), Some(&Value::Int(42)));
}

#[test]
fn assign_nested_scopes_shadowing_and_isolation() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    // Bind x = 10 in outer scope
    env.bind(Name::from("x"), Value::Int(10));

    // Enter a block: let x = 20 (shadows outer x)
    let block = spanned(vec![
        make_let("x", spanned(ExprKind::IntLit(20))),
        spanned(StmtKind::Expr(spanned(ExprKind::Ident("x".into())))),
    ]);
    let result = eval_block(&mut env, &block).unwrap();
    assert_eq!(result, Value::Int(20));

    // After block, outer x is still 10
    assert_eq!(env.lookup("x"), Some(&Value::Int(10)));
}

// ── Direct variable reassignment tests ─────────────────────

#[test]
fn assign_direct_variable_eq() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    // let x = 10; x = 20
    env.bind(Name::from("x"), Value::Int(10));
    let stmt = make_assign(
        make_lvalue("x", vec![]),
        AssignOp::Eq,
        spanned(ExprKind::IntLit(20)),
    );
    eval_stmt(&mut env, &stmt).unwrap();
    assert_eq!(env.lookup("x"), Some(&Value::Int(20)));
}

#[test]
fn assign_direct_variable_plus_eq() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(Name::from("x"), Value::Int(10));
    let stmt = make_assign(
        make_lvalue("x", vec![]),
        AssignOp::PlusEq,
        spanned(ExprKind::IntLit(5)),
    );
    eval_stmt(&mut env, &stmt).unwrap();
    assert_eq!(env.lookup("x"), Some(&Value::Int(15)));
}

#[test]
fn assign_direct_variable_minus_eq() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(Name::from("x"), Value::Int(10));
    let stmt = make_assign(
        make_lvalue("x", vec![]),
        AssignOp::MinusEq,
        spanned(ExprKind::IntLit(3)),
    );
    eval_stmt(&mut env, &stmt).unwrap();
    assert_eq!(env.lookup("x"), Some(&Value::Int(7)));
}

#[test]
fn assign_direct_undefined_variable_error() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let stmt = make_assign(
        make_lvalue("nonexistent", vec![]),
        AssignOp::Eq,
        spanned(ExprKind::IntLit(1)),
    );
    let err = eval_stmt(&mut env, &stmt).unwrap_err();
    assert!(
        err.message.contains("undefined variable"),
        "got: {}",
        err.message
    );
}

// ── Entity field assignment tests ──────────────────────────

#[test]
fn assign_entity_field_emits_mutate_field() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let entity_ref = EntityRef(1);
    env.bind(Name::from("target"), Value::Entity(entity_ref));

    // target.HP -= 5
    let stmt = make_assign(
        make_lvalue("target", vec![LValueSegment::Field("HP".into())]),
        AssignOp::MinusEq,
        spanned(ExprKind::IntLit(5)),
    );
    eval_stmt(&mut env, &stmt).unwrap();

    // Verify MutateField was emitted
    assert_eq!(handler.log.len(), 1);
    match &handler.log[0] {
        Effect::MutateField {
            entity,
            path,
            op,
            value,
            bounds,
        } => {
            assert_eq!(entity.0, 1);
            assert_eq!(path.len(), 1);
            match &path[0] {
                FieldPathSegment::Field(name) => assert_eq!(name, "HP"),
                _ => panic!("expected Field segment"),
            }
            assert_eq!(*op, AssignOp::MinusEq);
            assert_eq!(*value, Value::Int(5));
            assert!(bounds.is_none());
        }
        other => panic!("expected MutateField, got {:?}", other),
    }
}

#[test]
fn assign_entity_nested_path_emits_mutate_field() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let entity_ref = EntityRef(42);
    env.bind(Name::from("target"), Value::Entity(entity_ref));

    // target.stats[STR] = 18
    let stmt = make_assign(
        make_lvalue(
            "target",
            vec![
                LValueSegment::Field("stats".into()),
                LValueSegment::Index(spanned(ExprKind::StringLit("STR".to_string()))),
            ],
        ),
        AssignOp::Eq,
        spanned(ExprKind::IntLit(18)),
    );
    eval_stmt(&mut env, &stmt).unwrap();

    assert_eq!(handler.log.len(), 1);
    match &handler.log[0] {
        Effect::MutateField {
            entity,
            path,
            op,
            value,
            ..
        } => {
            assert_eq!(entity.0, 42);
            assert_eq!(path.len(), 2);
            match &path[0] {
                FieldPathSegment::Field(name) => assert_eq!(name, "stats"),
                _ => panic!("expected Field segment"),
            }
            match &path[1] {
                FieldPathSegment::Index(val) => assert_eq!(*val, Value::Str("STR".to_string())),
                _ => panic!("expected Index segment"),
            }
            assert_eq!(*op, AssignOp::Eq);
            assert_eq!(*value, Value::Int(18));
        }
        other => panic!("expected MutateField, got {:?}", other),
    }
}

#[test]
fn assign_entity_through_struct_emits_mutate_field() {
    // trigger.entity.HP -= 5 where trigger is a struct containing an entity
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let entity_ref = EntityRef(7);
    let trigger_struct = Value::Struct {
        name: "__event_Attack".into(),
        fields: {
            let mut f = BTreeMap::new();
            f.insert("entity".into(), Value::Entity(entity_ref));
            f
        },
    };
    env.bind(Name::from("trigger"), trigger_struct);

    // trigger.entity.HP -= 5
    let stmt = make_assign(
        make_lvalue(
            "trigger",
            vec![
                LValueSegment::Field("entity".into()),
                LValueSegment::Field("HP".into()),
            ],
        ),
        AssignOp::MinusEq,
        spanned(ExprKind::IntLit(5)),
    );
    eval_stmt(&mut env, &stmt).unwrap();

    // Should emit MutateField with entity=7, path=[Field("HP")]
    assert_eq!(handler.log.len(), 1);
    match &handler.log[0] {
        Effect::MutateField {
            entity,
            path,
            op,
            value,
            ..
        } => {
            assert_eq!(entity.0, 7);
            assert_eq!(path.len(), 1);
            match &path[0] {
                FieldPathSegment::Field(name) => assert_eq!(name, "HP"),
                _ => panic!("expected Field segment"),
            }
            assert_eq!(*op, AssignOp::MinusEq);
            assert_eq!(*value, Value::Int(5));
        }
        other => panic!("expected MutateField, got {:?}", other),
    }
}

// ── Turn budget mutation tests ─────────────────────────────

#[test]
fn assign_turn_field_emits_mutate_turn_field() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.turn_actor = Some(EntityRef(5));

    // turn.actions -= 1
    let stmt = make_assign(
        make_lvalue("turn", vec![LValueSegment::Field("actions".into())]),
        AssignOp::MinusEq,
        spanned(ExprKind::IntLit(1)),
    );
    eval_stmt(&mut env, &stmt).unwrap();

    assert_eq!(handler.log.len(), 1);
    match &handler.log[0] {
        Effect::MutateTurnField {
            actor,
            field,
            op,
            value,
        } => {
            assert_eq!(actor.0, 5);
            assert_eq!(field, "actions");
            assert_eq!(*op, AssignOp::MinusEq);
            assert_eq!(*value, Value::Int(1));
        }
        other => panic!("expected MutateTurnField, got {:?}", other),
    }
}

#[test]
fn assign_turn_without_actor_error() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    // No turn_actor set
    let stmt = make_assign(
        make_lvalue("turn", vec![LValueSegment::Field("actions".into())]),
        AssignOp::MinusEq,
        spanned(ExprKind::IntLit(1)),
    );
    let err = eval_stmt(&mut env, &stmt).unwrap_err();
    assert!(err.message.contains("turn"), "got: {}", err.message);
}

#[test]
fn assign_turn_no_segments_error() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.turn_actor = Some(EntityRef(1));

    // turn = 5 (no field segment)
    let stmt = make_assign(
        make_lvalue("turn", vec![]),
        AssignOp::Eq,
        spanned(ExprKind::IntLit(5)),
    );
    let err = eval_stmt(&mut env, &stmt).unwrap_err();
    assert!(err.message.contains("turn"), "got: {}", err.message);
}

// ── Local struct field mutation tests ──────────────────────

#[test]
fn assign_local_struct_field() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let my_struct = Value::Struct {
        name: "Point".into(),
        fields: {
            let mut f = BTreeMap::new();
            f.insert("x".into(), Value::Int(1));
            f.insert("y".into(), Value::Int(2));
            f
        },
    };
    env.bind(Name::from("p"), my_struct);

    // p.x = 10
    let stmt = make_assign(
        make_lvalue("p", vec![LValueSegment::Field("x".into())]),
        AssignOp::Eq,
        spanned(ExprKind::IntLit(10)),
    );
    eval_stmt(&mut env, &stmt).unwrap();

    match env.lookup("p") {
        Some(Value::Struct { fields, .. }) => {
            assert_eq!(fields.get("x"), Some(&Value::Int(10)));
            assert_eq!(fields.get("y"), Some(&Value::Int(2)));
        }
        other => panic!("expected Struct, got {:?}", other),
    }
}

#[test]
fn assign_local_struct_field_plus_eq() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let my_struct = Value::Struct {
        name: "Stats".into(),
        fields: {
            let mut f = BTreeMap::new();
            f.insert("strength".into(), Value::Int(10));
            f
        },
    };
    env.bind(Name::from("s"), my_struct);

    // s.strength += 5
    let stmt = make_assign(
        make_lvalue("s", vec![LValueSegment::Field("strength".into())]),
        AssignOp::PlusEq,
        spanned(ExprKind::IntLit(5)),
    );
    eval_stmt(&mut env, &stmt).unwrap();

    match env.lookup("s") {
        Some(Value::Struct { fields, .. }) => {
            assert_eq!(fields.get("strength"), Some(&Value::Int(15)));
        }
        other => panic!("expected Struct, got {:?}", other),
    }
}

#[test]
fn assign_local_struct_missing_field_error() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let my_struct = Value::Struct {
        name: "Point".into(),
        fields: {
            let mut f = BTreeMap::new();
            f.insert("x".into(), Value::Int(1));
            f
        },
    };
    env.bind(Name::from("p"), my_struct);

    // p.z = 10 (no field z)
    let stmt = make_assign(
        make_lvalue("p", vec![LValueSegment::Field("z".into())]),
        AssignOp::Eq,
        spanned(ExprKind::IntLit(10)),
    );
    let err = eval_stmt(&mut env, &stmt).unwrap_err();
    assert!(err.message.contains("no field"), "got: {}", err.message);
}

// ── Local list index mutation tests ────────────────────────

#[test]
fn assign_local_list_index() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(
        Name::from("nums"),
        Value::List(vec![Value::Int(10), Value::Int(20), Value::Int(30)]),
    );

    // nums[1] = 99
    let stmt = make_assign(
        make_lvalue(
            "nums",
            vec![LValueSegment::Index(spanned(ExprKind::IntLit(1)))],
        ),
        AssignOp::Eq,
        spanned(ExprKind::IntLit(99)),
    );
    eval_stmt(&mut env, &stmt).unwrap();

    match env.lookup("nums") {
        Some(Value::List(items)) => {
            assert_eq!(items, &vec![Value::Int(10), Value::Int(99), Value::Int(30)]);
        }
        other => panic!("expected List, got {:?}", other),
    }
}

#[test]
fn assign_local_list_negative_index() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(
        Name::from("nums"),
        Value::List(vec![Value::Int(1), Value::Int(2), Value::Int(3)]),
    );

    // nums[-1] = 99 (last element)
    let stmt = make_assign(
        make_lvalue(
            "nums",
            vec![LValueSegment::Index(spanned(ExprKind::IntLit(-1)))],
        ),
        AssignOp::Eq,
        spanned(ExprKind::IntLit(99)),
    );
    eval_stmt(&mut env, &stmt).unwrap();

    match env.lookup("nums") {
        Some(Value::List(items)) => {
            assert_eq!(items, &vec![Value::Int(1), Value::Int(2), Value::Int(99)]);
        }
        other => panic!("expected List, got {:?}", other),
    }
}

#[test]
fn assign_local_list_index_out_of_bounds_error() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(
        Name::from("nums"),
        Value::List(vec![Value::Int(1), Value::Int(2)]),
    );

    // nums[5] = 99 (out of bounds)
    let stmt = make_assign(
        make_lvalue(
            "nums",
            vec![LValueSegment::Index(spanned(ExprKind::IntLit(5)))],
        ),
        AssignOp::Eq,
        spanned(ExprKind::IntLit(99)),
    );
    let err = eval_stmt(&mut env, &stmt).unwrap_err();
    assert!(
        err.message.contains("out of bounds"),
        "got: {}",
        err.message
    );
}

#[test]
fn assign_local_list_index_plus_eq() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(
        Name::from("nums"),
        Value::List(vec![Value::Int(10), Value::Int(20)]),
    );

    // nums[0] += 5
    let stmt = make_assign(
        make_lvalue(
            "nums",
            vec![LValueSegment::Index(spanned(ExprKind::IntLit(0)))],
        ),
        AssignOp::PlusEq,
        spanned(ExprKind::IntLit(5)),
    );
    eval_stmt(&mut env, &stmt).unwrap();

    match env.lookup("nums") {
        Some(Value::List(items)) => {
            assert_eq!(items[0], Value::Int(15));
        }
        other => panic!("expected List, got {:?}", other),
    }
}

// ── Local map key mutation tests ───────────────────────────

#[test]
fn assign_local_map_key_insert() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let mut map = BTreeMap::new();
    map.insert(Value::Str("a".to_string()), Value::Int(1));
    env.bind(Name::from("m"), Value::Map(map));

    // m["b"] = 2 (insert new entry)
    let stmt = make_assign(
        make_lvalue(
            "m",
            vec![LValueSegment::Index(spanned(ExprKind::StringLit(
                "b".to_string(),
            )))],
        ),
        AssignOp::Eq,
        spanned(ExprKind::IntLit(2)),
    );
    eval_stmt(&mut env, &stmt).unwrap();

    match env.lookup("m") {
        Some(Value::Map(m)) => {
            assert_eq!(m.get(&Value::Str("a".to_string())), Some(&Value::Int(1)));
            assert_eq!(m.get(&Value::Str("b".to_string())), Some(&Value::Int(2)));
        }
        other => panic!("expected Map, got {:?}", other),
    }
}

#[test]
fn assign_local_map_key_update() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let mut map = BTreeMap::new();
    map.insert(Value::Str("a".to_string()), Value::Int(1));
    env.bind(Name::from("m"), Value::Map(map));

    // m["a"] = 99 (overwrite)
    let stmt = make_assign(
        make_lvalue(
            "m",
            vec![LValueSegment::Index(spanned(ExprKind::StringLit(
                "a".to_string(),
            )))],
        ),
        AssignOp::Eq,
        spanned(ExprKind::IntLit(99)),
    );
    eval_stmt(&mut env, &stmt).unwrap();

    match env.lookup("m") {
        Some(Value::Map(m)) => {
            assert_eq!(m.get(&Value::Str("a".to_string())), Some(&Value::Int(99)));
        }
        other => panic!("expected Map, got {:?}", other),
    }
}

#[test]
fn assign_local_map_key_plus_eq() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let mut map = BTreeMap::new();
    map.insert(Value::Str("score".to_string()), Value::Int(100));
    env.bind(Name::from("m"), Value::Map(map));

    // m["score"] += 50
    let stmt = make_assign(
        make_lvalue(
            "m",
            vec![LValueSegment::Index(spanned(ExprKind::StringLit(
                "score".to_string(),
            )))],
        ),
        AssignOp::PlusEq,
        spanned(ExprKind::IntLit(50)),
    );
    eval_stmt(&mut env, &stmt).unwrap();

    match env.lookup("m") {
        Some(Value::Map(m)) => {
            assert_eq!(
                m.get(&Value::Str("score".to_string())),
                Some(&Value::Int(150))
            );
        }
        other => panic!("expected Map, got {:?}", other),
    }
}

#[test]
fn assign_local_map_missing_key_plus_eq_error() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let map = BTreeMap::new();
    env.bind(Name::from("m"), Value::Map(map));

    // m["x"] += 1 (key doesn't exist)
    let stmt = make_assign(
        make_lvalue(
            "m",
            vec![LValueSegment::Index(spanned(ExprKind::StringLit(
                "x".to_string(),
            )))],
        ),
        AssignOp::PlusEq,
        spanned(ExprKind::IntLit(1)),
    );
    let err = eval_stmt(&mut env, &stmt).unwrap_err();
    assert!(
        err.message.contains("absent map key"),
        "got: {}",
        err.message
    );
}

#[test]
fn assign_local_map_missing_key_minus_eq_error() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let map = BTreeMap::new();
    env.bind(Name::from("m"), Value::Map(map));

    // m["x"] -= 1 (key doesn't exist)
    let stmt = make_assign(
        make_lvalue(
            "m",
            vec![LValueSegment::Index(spanned(ExprKind::StringLit(
                "x".to_string(),
            )))],
        ),
        AssignOp::MinusEq,
        spanned(ExprKind::IntLit(1)),
    );
    let err = eval_stmt(&mut env, &stmt).unwrap_err();
    assert!(
        err.message.contains("absent map key"),
        "got: {}",
        err.message
    );
}

// ── apply_assign_op error tests ────────────────────────────

#[test]
fn assign_plus_eq_incompatible_types_error() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(Name::from("x"), Value::Str("hello".to_string()));

    // x += 5 (string += int)
    let stmt = make_assign(
        make_lvalue("x", vec![]),
        AssignOp::PlusEq,
        spanned(ExprKind::IntLit(5)),
    );
    let err = eval_stmt(&mut env, &stmt).unwrap_err();
    assert!(
        err.message.contains("cannot apply +="),
        "got: {}",
        err.message
    );
}

#[test]
fn assign_integer_overflow_plus_eq_error() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(Name::from("x"), Value::Int(i64::MAX));

    let stmt = make_assign(
        make_lvalue("x", vec![]),
        AssignOp::PlusEq,
        spanned(ExprKind::IntLit(1)),
    );
    let err = eval_stmt(&mut env, &stmt).unwrap_err();
    assert!(err.message.contains("overflow"), "got: {}", err.message);
}

#[test]
fn assign_integer_overflow_minus_eq_error() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(Name::from("x"), Value::Int(i64::MIN));

    let stmt = make_assign(
        make_lvalue("x", vec![]),
        AssignOp::MinusEq,
        spanned(ExprKind::IntLit(1)),
    );
    let err = eval_stmt(&mut env, &stmt).unwrap_err();
    assert!(err.message.contains("overflow"), "got: {}", err.message);
}

// ── Float assignment tests ─────────────────────────────────

#[test]
fn assign_float_plus_eq() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(Name::from("x"), Value::Float(1.5));

    let block = spanned(vec![
        make_assign(
            make_lvalue("x", vec![]),
            AssignOp::PlusEq,
            spanned(ExprKind::IntLit(2)), // Int + Float works via mixed type
        ),
        spanned(StmtKind::Expr(spanned(ExprKind::Ident("x".into())))),
    ]);
    let result = eval_block(&mut env, &block).unwrap();
    assert_eq!(result, Value::Float(3.5));
}

#[test]
fn assign_float_minus_eq() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(Name::from("x"), Value::Float(10.0));

    let stmt = make_assign(
        make_lvalue("x", vec![]),
        AssignOp::MinusEq,
        spanned(ExprKind::IntLit(3)),
    );
    eval_stmt(&mut env, &stmt).unwrap();
    assert_eq!(env.lookup("x"), Some(&Value::Float(7.0)));
}

// ── Block returning value after assignment ─────────────────

#[test]
fn assign_returns_none_as_stmt_value() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(Name::from("x"), Value::Int(0));

    // Block: x = 42 (assign returns None as block value)
    let block = spanned(vec![make_assign(
        make_lvalue("x", vec![]),
        AssignOp::Eq,
        spanned(ExprKind::IntLit(42)),
    )]);
    let result = eval_block(&mut env, &block).unwrap();
    assert_eq!(result, Value::None);
    // But x was updated
    assert_eq!(env.lookup("x"), Some(&Value::Int(42)));
}

// ── RollResult coercion in assignment ──────────────────────

#[test]
fn assign_roll_result_coerced_in_plus_eq() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    // RollResult with total=7
    let rr = Value::RollResult(RollResult {
        expr: DiceExpr::single(2, 6, None, 0),
        dice: vec![3, 4],
        kept: vec![3, 4],
        modifier: 0,
        total: 7,
        unmodified: 7,
    });
    env.bind(Name::from("x"), rr);

    // x += 3 → RollResult coerced to Int(7), then 7 + 3 = 10
    let stmt = make_assign(
        make_lvalue("x", vec![]),
        AssignOp::PlusEq,
        spanned(ExprKind::IntLit(3)),
    );
    eval_stmt(&mut env, &stmt).unwrap();
    assert_eq!(env.lookup("x"), Some(&Value::Int(10)));
}

// ── No effects emitted for local mutations ─────────────────

#[test]
fn assign_local_mutation_emits_no_effects() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(Name::from("x"), Value::Int(10));

    // x += 5 → purely local, no effects
    let stmt = make_assign(
        make_lvalue("x", vec![]),
        AssignOp::PlusEq,
        spanned(ExprKind::IntLit(5)),
    );
    eval_stmt(&mut env, &stmt).unwrap();

    assert!(
        handler.log.is_empty(),
        "expected no effects for local mutation"
    );
}

// ── Regression: i64::MIN list index should not panic ────────

#[test]
fn assign_local_list_i64_min_index_error() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    env.bind(Name::from("nums"), Value::List(vec![Value::Int(1)]));

    // nums[i64::MIN] = 0 — should produce a RuntimeError, not panic
    let stmt = make_assign(
        make_lvalue(
            "nums",
            vec![LValueSegment::Index(spanned(ExprKind::IntLit(i64::MIN)))],
        ),
        AssignOp::Eq,
        spanned(ExprKind::IntLit(0)),
    );
    let err = eval_stmt(&mut env, &stmt).unwrap_err();
    assert!(
        err.message.contains("out of bounds"),
        "got: {}",
        err.message
    );
}

// ── Regression: map assignment uses semantic key equality ────

#[test]
fn assign_local_map_semantic_key_overwrite() {
    // Writing with Option(None) key should overwrite an existing None key
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let mut map = BTreeMap::new();
    map.insert(Value::None, Value::Int(1));
    env.bind(Name::from("m"), Value::Map(map));

    // m[option_none] = 99 — should overwrite the None entry, not create a duplicate
    let stmt = make_assign(
        make_lvalue("m", vec![LValueSegment::Index(spanned(ExprKind::NoneLit))]),
        AssignOp::Eq,
        spanned(ExprKind::IntLit(99)),
    );
    eval_stmt(&mut env, &stmt).unwrap();

    match env.lookup("m") {
        Some(Value::Map(m)) => {
            assert_eq!(
                m.len(),
                1,
                "should have 1 entry, not a duplicate; got {:?}",
                m
            );
            // The value should be updated regardless of which structural key remains
            let val = m.values().next().unwrap();
            assert_eq!(val, &Value::Int(99));
        }
        other => panic!("expected Map, got {:?}", other),
    }
}

#[test]
fn assign_local_map_semantic_key_plus_eq() {
    // Compound assignment should find an existing key via semantic equality
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);

    let mut map = BTreeMap::new();
    map.insert(Value::None, Value::Int(10));
    env.bind(Name::from("m"), Value::Map(map));

    // m[option_none] += 5 — should find the None key semantically
    let stmt = make_assign(
        make_lvalue("m", vec![LValueSegment::Index(spanned(ExprKind::NoneLit))]),
        AssignOp::PlusEq,
        spanned(ExprKind::IntLit(5)),
    );
    eval_stmt(&mut env, &stmt).unwrap();

    match env.lookup("m") {
        Some(Value::Map(m)) => {
            assert_eq!(m.len(), 1);
            let val = m.values().next().unwrap();
            assert_eq!(val, &Value::Int(15));
        }
        other => panic!("expected Map, got {:?}", other),
    }
}

// ── Has / Grant / Revoke tests ────────────────────────────

#[test]
fn has_returns_true_when_group_field_present() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let mut state = TestState::new();
    // Entity 1 has a "Spellcasting" field (simulating a granted group)
    state.fields.insert(
        (1, "Spellcasting".into()),
        Value::Struct {
            name: "Spellcasting".into(),
            fields: {
                let mut f = BTreeMap::new();
                f.insert("spell_slots".into(), Value::Int(3));
                f
            },
        },
    );
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);
    env.bind("actor".into(), Value::Entity(EntityRef(1)));

    let expr = spanned(ExprKind::Has {
        entity: Box::new(spanned(ExprKind::Ident("actor".into()))),
        group_name: "Spellcasting".into(),
        alias: None,
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(true));
}

#[test]
fn has_returns_false_when_group_field_absent() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new(); // Entity 1 has no fields
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);
    env.bind("actor".into(), Value::Entity(EntityRef(1)));

    let expr = spanned(ExprKind::Has {
        entity: Box::new(spanned(ExprKind::Ident("actor".into()))),
        group_name: "Spellcasting".into(),
        alias: None,
    });
    assert_eq!(eval_expr(&mut env, &expr).unwrap(), Value::Bool(false));
}

#[test]
fn has_on_non_entity_is_error() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);
    env.bind("x".into(), Value::Int(42));

    let expr = spanned(ExprKind::Has {
        entity: Box::new(spanned(ExprKind::Ident("x".into()))),
        group_name: "Spellcasting".into(),
        alias: None,
    });
    let err = eval_expr(&mut env, &expr).unwrap_err();
    assert!(
        err.message.contains("expected entity"),
        "got: {}",
        err.message
    );
}

#[test]
fn grant_emits_grant_group_effect_with_fields() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);
    env.bind("actor".into(), Value::Entity(EntityRef(1)));

    let stmt = spanned(StmtKind::Grant {
        entity: Box::new(spanned(ExprKind::Ident("actor".into()))),
        group_name: "Spellcasting".into(),
        fields: vec![
            StructFieldInit {
                name: "spell_slots".into(),
                value: spanned(ExprKind::IntLit(3)),
                span: dummy_span(),
            },
            StructFieldInit {
                name: "cantrips".into(),
                value: spanned(ExprKind::IntLit(2)),
                span: dummy_span(),
            },
        ],
    });
    eval_stmt(&mut env, &stmt).unwrap();

    // Should have emitted exactly one GrantGroup effect
    assert_eq!(handler.log.len(), 1);
    match &handler.log[0] {
        Effect::GrantGroup {
            entity,
            group_name,
            fields,
        } => {
            assert_eq!(entity.0, 1);
            assert_eq!(group_name, "Spellcasting");
            match fields {
                Value::Struct { name, fields } => {
                    assert_eq!(name, "Spellcasting");
                    assert_eq!(fields.get("spell_slots"), Some(&Value::Int(3)));
                    assert_eq!(fields.get("cantrips"), Some(&Value::Int(2)));
                }
                _ => panic!("expected Struct value, got {:?}", fields),
            }
        }
        _ => panic!("expected GrantGroup effect, got {:?}", handler.log[0]),
    }
}

#[test]
fn grant_with_no_fields_emits_empty_struct() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);
    env.bind("actor".into(), Value::Entity(EntityRef(1)));

    let stmt = spanned(StmtKind::Grant {
        entity: Box::new(spanned(ExprKind::Ident("actor".into()))),
        group_name: "Flight".into(),
        fields: vec![],
    });
    eval_stmt(&mut env, &stmt).unwrap();

    assert_eq!(handler.log.len(), 1);
    match &handler.log[0] {
        Effect::GrantGroup { fields, .. } => match fields {
            Value::Struct { fields, .. } => {
                assert!(fields.is_empty());
            }
            _ => panic!("expected Struct"),
        },
        _ => panic!("expected GrantGroup"),
    }
}

#[test]
fn grant_fills_defaults_from_entity_decl() {
    // Build a program with an entity that has an optional group with defaults
    let mut program = Program {
        items: vec![spanned(TopLevel::System(SystemBlock {
            name: "test".into(),
            decls: vec![spanned(DeclKind::Entity(EntityDecl {
                name: "Character".into(),
                fields: vec![],
                optional_groups: vec![OptionalGroup {
                    name: "Spellcasting".into(),
                    fields: vec![
                        FieldDef {
                            name: "spell_slots".into(),
                            ty: spanned(TypeExpr::Int),
                            default: None, // no default
                            span: dummy_span(),
                        },
                        FieldDef {
                            name: "cantrips".into(),
                            ty: spanned(TypeExpr::Int),
                            default: Some(spanned(ExprKind::IntLit(4))), // default = 4
                            span: dummy_span(),
                        },
                    ],
                    is_external_ref: false,
                    is_required: false,
                    span: dummy_span(),
                }],
            }))],
        }))],
        ..Default::default()
    };
    program.build_index();

    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let mut state = TestState::new();
    state.entity_type = Some("Character".into());
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);
    env.bind("actor".into(), Value::Entity(EntityRef(1)));

    // Grant with only spell_slots provided; cantrips should get default 4
    let stmt = spanned(StmtKind::Grant {
        entity: Box::new(spanned(ExprKind::Ident("actor".into()))),
        group_name: "Spellcasting".into(),
        fields: vec![StructFieldInit {
            name: "spell_slots".into(),
            value: spanned(ExprKind::IntLit(3)),
            span: dummy_span(),
        }],
    });
    eval_stmt(&mut env, &stmt).unwrap();

    assert_eq!(handler.log.len(), 1);
    match &handler.log[0] {
        Effect::GrantGroup { fields, .. } => match fields {
            Value::Struct { fields, .. } => {
                assert_eq!(fields.get("spell_slots"), Some(&Value::Int(3)));
                assert_eq!(fields.get("cantrips"), Some(&Value::Int(4)));
            }
            _ => panic!("expected Struct"),
        },
        _ => panic!("expected GrantGroup"),
    }
}

#[test]
fn grant_explicit_field_overrides_default() {
    // Build a program with an entity that has default=4 for cantrips
    let mut program = Program {
        items: vec![spanned(TopLevel::System(SystemBlock {
            name: "test".into(),
            decls: vec![spanned(DeclKind::Entity(EntityDecl {
                name: "Character".into(),
                fields: vec![],
                optional_groups: vec![OptionalGroup {
                    name: "Spellcasting".into(),
                    fields: vec![FieldDef {
                        name: "cantrips".into(),
                        ty: spanned(TypeExpr::Int),
                        default: Some(spanned(ExprKind::IntLit(4))),
                        span: dummy_span(),
                    }],
                    is_external_ref: false,
                    is_required: false,
                    span: dummy_span(),
                }],
            }))],
        }))],
        ..Default::default()
    };
    program.build_index();

    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let mut state = TestState::new();
    state.entity_type = Some("Character".into());
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);
    env.bind("actor".into(), Value::Entity(EntityRef(1)));

    // Grant with cantrips=10 — should override the default of 4
    let stmt = spanned(StmtKind::Grant {
        entity: Box::new(spanned(ExprKind::Ident("actor".into()))),
        group_name: "Spellcasting".into(),
        fields: vec![StructFieldInit {
            name: "cantrips".into(),
            value: spanned(ExprKind::IntLit(10)),
            span: dummy_span(),
        }],
    });
    eval_stmt(&mut env, &stmt).unwrap();

    match &handler.log[0] {
        Effect::GrantGroup { fields, .. } => match fields {
            Value::Struct { fields, .. } => {
                assert_eq!(fields.get("cantrips"), Some(&Value::Int(10)));
            }
            _ => panic!("expected Struct"),
        },
        _ => panic!("expected GrantGroup"),
    }
}

#[test]
fn grant_on_non_entity_is_error() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);
    env.bind("x".into(), Value::Int(42));

    let stmt = spanned(StmtKind::Grant {
        entity: Box::new(spanned(ExprKind::Ident("x".into()))),
        group_name: "Spellcasting".into(),
        fields: vec![],
    });
    let err = eval_stmt(&mut env, &stmt).unwrap_err();
    assert!(
        err.message.contains("expected entity"),
        "got: {}",
        err.message
    );
}

#[test]
fn grant_vetoed_by_host_is_error() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    handler.script.push_back(Response::Vetoed);
    let mut env = make_env(&state, &mut handler, &interp);
    env.bind("actor".into(), Value::Entity(EntityRef(1)));

    let stmt = spanned(StmtKind::Grant {
        entity: Box::new(spanned(ExprKind::Ident("actor".into()))),
        group_name: "Spellcasting".into(),
        fields: vec![],
    });
    let err = eval_stmt(&mut env, &stmt).unwrap_err();
    assert!(err.message.contains("vetoed"), "got: {}", err.message);
}

#[test]
fn revoke_emits_revoke_group_effect() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);
    env.bind("actor".into(), Value::Entity(EntityRef(1)));

    let stmt = spanned(StmtKind::Revoke {
        entity: Box::new(spanned(ExprKind::Ident("actor".into()))),
        group_name: "Spellcasting".into(),
    });
    eval_stmt(&mut env, &stmt).unwrap();

    assert_eq!(handler.log.len(), 1);
    match &handler.log[0] {
        Effect::RevokeGroup { entity, group_name } => {
            assert_eq!(entity.0, 1);
            assert_eq!(group_name, "Spellcasting");
        }
        _ => panic!("expected RevokeGroup effect, got {:?}", handler.log[0]),
    }
}

#[test]
fn revoke_on_non_entity_is_error() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);
    env.bind("x".into(), Value::Str("not entity".into()));

    let stmt = spanned(StmtKind::Revoke {
        entity: Box::new(spanned(ExprKind::Ident("x".into()))),
        group_name: "Spellcasting".into(),
    });
    let err = eval_stmt(&mut env, &stmt).unwrap_err();
    assert!(
        err.message.contains("expected entity"),
        "got: {}",
        err.message
    );
}

#[test]
fn revoke_vetoed_by_host_is_error() {
    let program = empty_program();
    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    handler.script.push_back(Response::Vetoed);
    let mut env = make_env(&state, &mut handler, &interp);
    env.bind("actor".into(), Value::Entity(EntityRef(1)));

    let stmt = spanned(StmtKind::Revoke {
        entity: Box::new(spanned(ExprKind::Ident("actor".into()))),
        group_name: "Spellcasting".into(),
    });
    let err = eval_stmt(&mut env, &stmt).unwrap_err();
    assert!(err.message.contains("vetoed"), "got: {}", err.message);
}

#[test]
fn grant_defaults_scoped_to_entity_type() {
    // Two entity types share the same optional group name but with different defaults.
    // When granting on a Monster, `spell_slots` should default to 1 (Monster's), not 3.
    let mut program = Program {
        items: vec![spanned(TopLevel::System(SystemBlock {
            name: "test".into(),
            decls: vec![
                spanned(DeclKind::Entity(EntityDecl {
                    name: "Character".into(),
                    fields: vec![FieldDef {
                        name: "HP".into(),
                        ty: spanned(TypeExpr::Int),
                        default: None,
                        span: dummy_span(),
                    }],
                    optional_groups: vec![OptionalGroup {
                        name: "Spellcasting".into(),
                        fields: vec![
                            FieldDef {
                                name: "spell_slots".into(),
                                ty: spanned(TypeExpr::Int),
                                default: Some(spanned(ExprKind::IntLit(3))),
                                span: dummy_span(),
                            },
                            FieldDef {
                                name: "dc".into(),
                                ty: spanned(TypeExpr::Int),
                                default: None,
                                span: dummy_span(),
                            },
                        ],
                        is_external_ref: false,
                        is_required: false,
                        span: dummy_span(),
                    }],
                })),
                spanned(DeclKind::Entity(EntityDecl {
                    name: "Monster".into(),
                    fields: vec![FieldDef {
                        name: "HP".into(),
                        ty: spanned(TypeExpr::Int),
                        default: None,
                        span: dummy_span(),
                    }],
                    optional_groups: vec![OptionalGroup {
                        name: "Spellcasting".into(),
                        fields: vec![
                            FieldDef {
                                name: "spell_slots".into(),
                                ty: spanned(TypeExpr::Int),
                                default: Some(spanned(ExprKind::IntLit(1))),
                                span: dummy_span(),
                            },
                            FieldDef {
                                name: "dc".into(),
                                ty: spanned(TypeExpr::Int),
                                default: None,
                                span: dummy_span(),
                            },
                        ],
                        is_external_ref: false,
                        is_required: false,
                        span: dummy_span(),
                    }],
                })),
            ],
        }))],
        ..Default::default()
    };
    program.build_index();

    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    let mut state = TestState::new();
    state.entity_type = Some("Monster".into());
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);
    env.bind("actor".into(), Value::Entity(EntityRef(1)));

    // Grant with only dc provided; spell_slots should use Monster's default (1)
    let stmt = spanned(StmtKind::Grant {
        entity: Box::new(spanned(ExprKind::Ident("actor".into()))),
        group_name: "Spellcasting".into(),
        fields: vec![StructFieldInit {
            name: "dc".into(),
            value: spanned(ExprKind::IntLit(15)),
            span: dummy_span(),
        }],
    });
    eval_stmt(&mut env, &stmt).unwrap();

    assert_eq!(handler.log.len(), 1);
    match &handler.log[0] {
        Effect::GrantGroup { fields, .. } => match fields {
            Value::Struct { fields, .. } => {
                assert_eq!(fields.get("dc"), Some(&Value::Int(15)));
                assert_eq!(
                    fields.get("spell_slots"),
                    Some(&Value::Int(1)),
                    "spell_slots should default to Monster's 1, not Character's 3"
                );
            }
            _ => panic!("expected Struct"),
        },
        _ => panic!("expected GrantGroup"),
    }
}

#[test]
fn grant_no_defaults_when_entity_type_unknown() {
    // When entity_type_name returns None, find_optional_group should NOT
    // fall back to a different entity's group — no defaults are filled.
    let mut program = Program {
        items: vec![spanned(TopLevel::System(SystemBlock {
            name: "test".into(),
            decls: vec![
                spanned(DeclKind::Entity(EntityDecl {
                    name: "Character".into(),
                    fields: vec![FieldDef {
                        name: "HP".into(),
                        ty: spanned(TypeExpr::Int),
                        default: None,
                        span: dummy_span(),
                    }],
                    optional_groups: vec![OptionalGroup {
                        name: "Spellcasting".into(),
                        fields: vec![
                            FieldDef {
                                name: "spell_slots".into(),
                                ty: spanned(TypeExpr::Int),
                                default: Some(spanned(ExprKind::IntLit(3))),
                                span: dummy_span(),
                            },
                            FieldDef {
                                name: "dc".into(),
                                ty: spanned(TypeExpr::Int),
                                default: None,
                                span: dummy_span(),
                            },
                        ],
                        is_external_ref: false,
                        is_required: false,
                        span: dummy_span(),
                    }],
                })),
                spanned(DeclKind::Entity(EntityDecl {
                    name: "Monster".into(),
                    fields: vec![FieldDef {
                        name: "HP".into(),
                        ty: spanned(TypeExpr::Int),
                        default: None,
                        span: dummy_span(),
                    }],
                    optional_groups: vec![OptionalGroup {
                        name: "Spellcasting".into(),
                        fields: vec![
                            FieldDef {
                                name: "spell_slots".into(),
                                ty: spanned(TypeExpr::Int),
                                default: Some(spanned(ExprKind::IntLit(1))),
                                span: dummy_span(),
                            },
                            FieldDef {
                                name: "dc".into(),
                                ty: spanned(TypeExpr::Int),
                                default: None,
                                span: dummy_span(),
                            },
                        ],
                        is_external_ref: false,
                        is_required: false,
                        span: dummy_span(),
                    }],
                })),
            ],
        }))],
        ..Default::default()
    };
    program.build_index();

    let type_env = empty_type_env();
    let interp = Interpreter::new(&program, &type_env).unwrap();
    // entity_type is None — simulates unknown entity type
    let state = TestState::new();
    let mut handler = ScriptedHandler::new();
    let mut env = make_env(&state, &mut handler, &interp);
    env.bind("actor".into(), Value::Entity(EntityRef(1)));

    // Grant with only dc provided; spell_slots should NOT be filled
    // because entity type is unknown and we don't fall back.
    let stmt = spanned(StmtKind::Grant {
        entity: Box::new(spanned(ExprKind::Ident("actor".into()))),
        group_name: "Spellcasting".into(),
        fields: vec![StructFieldInit {
            name: "dc".into(),
            value: spanned(ExprKind::IntLit(15)),
            span: dummy_span(),
        }],
    });
    eval_stmt(&mut env, &stmt).unwrap();

    assert_eq!(handler.log.len(), 1);
    match &handler.log[0] {
        Effect::GrantGroup { fields, .. } => match fields {
            Value::Struct { fields, .. } => {
                assert_eq!(fields.get("dc"), Some(&Value::Int(15)));
                assert_eq!(
                    fields.get("spell_slots"),
                    None,
                    "spell_slots should not be filled when entity type is unknown"
                );
            }
            _ => panic!("expected Struct"),
        },
        _ => panic!("expected GrantGroup"),
    }
}
