//! Integration tests for collection builtin functions.

use std::collections::BTreeMap;

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

// ── len ────────────────────────────────────────────────────────

#[test]
fn len_of_list() {
    let source = r#"
system "test" {
    derive f(xs: list<int>) -> int {
        len(xs)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "f", vec![
            Value::List(vec![Value::Int(1), Value::Int(2), Value::Int(3)]),
        ])
        .unwrap();
    assert_eq!(val, Value::Int(3));
}

#[test]
fn len_of_empty_list() {
    let source = r#"
system "test" {
    derive f(xs: list<int>) -> int {
        len(xs)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "f", vec![Value::List(vec![])])
        .unwrap();
    assert_eq!(val, Value::Int(0));
}

#[test]
fn len_of_set() {
    let source = r#"
system "test" {
    derive f(xs: set<int>) -> int {
        len(xs)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "f", vec![
            Value::Set([Value::Int(1), Value::Int(2)].into()),
        ])
        .unwrap();
    assert_eq!(val, Value::Int(2));
}

#[test]
fn len_of_map() {
    let source = r#"
system "test" {
    derive f(m: map<string, int>) -> int {
        len(m)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let mut m = BTreeMap::new();
    m.insert(Value::Str("a".into()), Value::Int(1));
    m.insert(Value::Str("b".into()), Value::Int(2));

    let val = interp
        .evaluate_derive(&state, &mut handler, "f", vec![Value::Map(m)])
        .unwrap();
    assert_eq!(val, Value::Int(2));
}

// ── keys / values ──────────────────────────────────────────────

#[test]
fn keys_of_map() {
    let source = r#"
system "test" {
    derive f(m: map<string, int>) -> list<string> {
        keys(m)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let mut m = BTreeMap::new();
    m.insert(Value::Str("a".into()), Value::Int(1));
    m.insert(Value::Str("b".into()), Value::Int(2));

    let val = interp
        .evaluate_derive(&state, &mut handler, "f", vec![Value::Map(m)])
        .unwrap();
    // BTreeMap keys come out sorted
    assert_eq!(val, Value::List(vec![Value::Str("a".into()), Value::Str("b".into())]));
}

#[test]
fn values_of_map() {
    let source = r#"
system "test" {
    derive f(m: map<string, int>) -> list<int> {
        values(m)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let mut m = BTreeMap::new();
    m.insert(Value::Str("a".into()), Value::Int(1));
    m.insert(Value::Str("b".into()), Value::Int(2));

    let val = interp
        .evaluate_derive(&state, &mut handler, "f", vec![Value::Map(m)])
        .unwrap();
    // BTreeMap values in key order
    assert_eq!(val, Value::List(vec![Value::Int(1), Value::Int(2)]));
}

#[test]
fn keys_of_empty_map() {
    let source = r#"
system "test" {
    derive f(m: map<string, int>) -> list<string> {
        keys(m)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "f", vec![Value::Map(BTreeMap::new())])
        .unwrap();
    assert_eq!(val, Value::List(vec![]));
}

// ── first / last ───────────────────────────────────────────────

#[test]
fn first_of_list() {
    let source = r#"
system "test" {
    derive f(xs: list<int>) -> option<int> {
        first(xs)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "f", vec![
            Value::List(vec![Value::Int(10), Value::Int(20)]),
        ])
        .unwrap();
    assert_eq!(val, Value::Option(Some(Box::new(Value::Int(10)))));
}

#[test]
fn first_of_empty_list() {
    let source = r#"
system "test" {
    derive f(xs: list<int>) -> option<int> {
        first(xs)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "f", vec![Value::List(vec![])])
        .unwrap();
    assert_eq!(val, Value::None);
}

#[test]
fn last_of_list() {
    let source = r#"
system "test" {
    derive f(xs: list<int>) -> option<int> {
        last(xs)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "f", vec![
            Value::List(vec![Value::Int(10), Value::Int(20)]),
        ])
        .unwrap();
    assert_eq!(val, Value::Option(Some(Box::new(Value::Int(20)))));
}

#[test]
fn last_of_empty_list() {
    let source = r#"
system "test" {
    derive f(xs: list<int>) -> option<int> {
        last(xs)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "f", vec![Value::List(vec![])])
        .unwrap();
    assert_eq!(val, Value::None);
}

// ── append ─────────────────────────────────────────────────────

#[test]
fn append_to_list() {
    let source = r#"
system "test" {
    derive f(xs: list<int>, val: int) -> list<int> {
        append(xs, val)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "f", vec![
            Value::List(vec![Value::Int(1), Value::Int(2)]),
            Value::Int(3),
        ])
        .unwrap();
    assert_eq!(val, Value::List(vec![Value::Int(1), Value::Int(2), Value::Int(3)]));
}

#[test]
fn append_to_empty_list() {
    let source = r#"
system "test" {
    derive f(xs: list<int>, val: int) -> list<int> {
        append(xs, val)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "f", vec![
            Value::List(vec![]),
            Value::Int(42),
        ])
        .unwrap();
    assert_eq!(val, Value::List(vec![Value::Int(42)]));
}

// ── concat ─────────────────────────────────────────────────────

#[test]
fn concat_two_lists() {
    let source = r#"
system "test" {
    derive f(a: list<int>, b: list<int>) -> list<int> {
        concat(a, b)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "f", vec![
            Value::List(vec![Value::Int(1), Value::Int(2)]),
            Value::List(vec![Value::Int(3), Value::Int(4)]),
        ])
        .unwrap();
    assert_eq!(val, Value::List(vec![
        Value::Int(1), Value::Int(2), Value::Int(3), Value::Int(4),
    ]));
}

#[test]
fn concat_with_empty() {
    let source = r#"
system "test" {
    derive f(xs: list<int>, ys: list<int>) -> list<int> {
        concat(xs, ys)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "f", vec![
            Value::List(vec![Value::Int(1), Value::Int(2)]),
            Value::List(vec![]),
        ])
        .unwrap();
    assert_eq!(val, Value::List(vec![Value::Int(1), Value::Int(2)]));
}

// ── reverse ────────────────────────────────────────────────────

#[test]
fn reverse_list() {
    let source = r#"
system "test" {
    derive f(xs: list<int>) -> list<int> {
        reverse(xs)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "f", vec![
            Value::List(vec![Value::Int(1), Value::Int(2), Value::Int(3)]),
        ])
        .unwrap();
    assert_eq!(val, Value::List(vec![Value::Int(3), Value::Int(2), Value::Int(1)]));
}

#[test]
fn reverse_empty_list() {
    let source = r#"
system "test" {
    derive f(xs: list<int>) -> list<int> {
        reverse(xs)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "f", vec![Value::List(vec![])])
        .unwrap();
    assert_eq!(val, Value::List(vec![]));
}

#[test]
fn reverse_single_element() {
    let source = r#"
system "test" {
    derive f() -> list<int> {
        reverse([42])
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "f", vec![])
        .unwrap();
    assert_eq!(val, Value::List(vec![Value::Int(42)]));
}

// ── composition ────────────────────────────────────────────────

#[test]
fn len_of_keys() {
    let source = r#"
system "test" {
    derive f(m: map<string, int>) -> int {
        len(keys(m))
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let mut m = BTreeMap::new();
    m.insert(Value::Str("x".into()), Value::Int(1));
    m.insert(Value::Str("y".into()), Value::Int(2));
    m.insert(Value::Str("z".into()), Value::Int(3));

    let val = interp
        .evaluate_derive(&state, &mut handler, "f", vec![Value::Map(m)])
        .unwrap();
    assert_eq!(val, Value::Int(3));
}

#[test]
fn first_of_reverse() {
    let source = r#"
system "test" {
    derive f(xs: list<int>) -> option<int> {
        first(reverse(xs))
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "f", vec![
            Value::List(vec![Value::Int(1), Value::Int(2), Value::Int(3)]),
        ])
        .unwrap();
    assert_eq!(val, Value::Option(Some(Box::new(Value::Int(3)))));
}
