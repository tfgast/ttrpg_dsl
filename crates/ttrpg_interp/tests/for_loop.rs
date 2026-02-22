//! Integration tests for for-loop evaluation.

use ttrpg_ast::diagnostic::Severity;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

struct NoopHandler;
impl EffectHandler for NoopHandler {
    fn handle(&mut self, _: Effect) -> Response {
        Response::Acknowledged
    }
}

fn setup(source: &str) -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    let (program, parse_errors) = ttrpg_parser::parse(source);
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

#[test]
fn for_over_list_returns_unit() {
    let source = r#"
system "test" {
    derive f(xs: list<int>) -> int {
        for x in xs {
            x + 1
        }
        42
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "f",
            vec![Value::List(vec![Value::Int(1), Value::Int(2), Value::Int(3)])],
        )
        .unwrap();
    // for-loop returns unit; the derive body ends with 42
    assert_eq!(val, Value::Int(42));
}

#[test]
fn for_range_iteration() {
    // Use a mechanic that builds a list by calling a derive per iteration
    let source = r#"
system "test" {
    derive count_range(n: int) -> int {
        let result = [0]
        for i in 0..n {
            result
        }
        n
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "count_range", vec![Value::Int(5)])
        .unwrap();
    assert_eq!(val, Value::Int(5));
}

#[test]
fn for_empty_list() {
    let source = r#"
system "test" {
    derive f(xs: list<int>) -> int {
        for x in xs {
            x
        }
        99
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    // Empty list — zero iterations, body never runs
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "f",
            vec![Value::List(vec![])],
        )
        .unwrap();
    assert_eq!(val, Value::Int(99));
}

#[test]
fn for_empty_range() {
    let source = r#"
system "test" {
    derive f() -> int {
        for i in 5..3 {
            i
        }
        99
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    // 5..3 is empty — zero iterations
    let val = interp
        .evaluate_derive(&state, &mut handler, "f", vec![])
        .unwrap();
    assert_eq!(val, Value::Int(99));
}

#[test]
fn for_pattern_filtering() {
    // Use some(x) pattern to filter option values
    let source = r#"
system "test" {
    derive count_some(xs: list<option<int>>) -> int {
        let count = 0
        for some(x) in xs {
            x
        }
        0
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    // Non-matching patterns (none values) are silently skipped
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "count_some",
            vec![Value::List(vec![
                Value::Option(Some(Box::new(Value::Int(1)))),
                Value::Option(None),
                Value::Option(Some(Box::new(Value::Int(3)))),
            ])],
        )
        .unwrap();
    assert_eq!(val, Value::Int(0));
}

#[test]
fn for_over_set() {
    let source = r#"
system "test" {
    derive f(xs: set<int>) -> int {
        for x in xs {
            x
        }
        42
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let mut set = std::collections::BTreeSet::new();
    set.insert(Value::Int(10));
    set.insert(Value::Int(20));

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "f",
            vec![Value::Set(set)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(42));
}

#[test]
fn for_wildcard_pattern() {
    let source = r#"
system "test" {
    derive f(xs: list<int>) -> int {
        for _ in xs {
            0
        }
        77
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "f",
            vec![Value::List(vec![Value::Int(1), Value::Int(2)])],
        )
        .unwrap();
    assert_eq!(val, Value::Int(77));
}
