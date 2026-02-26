//! Integration tests for collection builtin functions.

use std::collections::BTreeMap;

use ttrpg_ast::diagnostic::Severity;
use ttrpg_ast::FileId;
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
    let (program, parse_errors) = ttrpg_parser::parse(source, FileId::SYNTH);
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
        .evaluate_derive(
            &state,
            &mut handler,
            "f",
            vec![Value::List(vec![
                Value::Int(1),
                Value::Int(2),
                Value::Int(3),
            ])],
        )
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
        .evaluate_derive(
            &state,
            &mut handler,
            "f",
            vec![Value::Set([Value::Int(1), Value::Int(2)].into())],
        )
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
    assert_eq!(
        val,
        Value::List(vec![Value::Str("a".into()), Value::Str("b".into())])
    );
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
        .evaluate_derive(
            &state,
            &mut handler,
            "f",
            vec![Value::List(vec![Value::Int(10), Value::Int(20)])],
        )
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
        .evaluate_derive(
            &state,
            &mut handler,
            "f",
            vec![Value::List(vec![Value::Int(10), Value::Int(20)])],
        )
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
        .evaluate_derive(
            &state,
            &mut handler,
            "f",
            vec![
                Value::List(vec![Value::Int(1), Value::Int(2)]),
                Value::Int(3),
            ],
        )
        .unwrap();
    assert_eq!(
        val,
        Value::List(vec![Value::Int(1), Value::Int(2), Value::Int(3)])
    );
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
        .evaluate_derive(
            &state,
            &mut handler,
            "f",
            vec![Value::List(vec![]), Value::Int(42)],
        )
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
        .evaluate_derive(
            &state,
            &mut handler,
            "f",
            vec![
                Value::List(vec![Value::Int(1), Value::Int(2)]),
                Value::List(vec![Value::Int(3), Value::Int(4)]),
            ],
        )
        .unwrap();
    assert_eq!(
        val,
        Value::List(vec![
            Value::Int(1),
            Value::Int(2),
            Value::Int(3),
            Value::Int(4),
        ])
    );
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
        .evaluate_derive(
            &state,
            &mut handler,
            "f",
            vec![
                Value::List(vec![Value::Int(1), Value::Int(2)]),
                Value::List(vec![]),
            ],
        )
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
        .evaluate_derive(
            &state,
            &mut handler,
            "f",
            vec![Value::List(vec![
                Value::Int(1),
                Value::Int(2),
                Value::Int(3),
            ])],
        )
        .unwrap();
    assert_eq!(
        val,
        Value::List(vec![Value::Int(3), Value::Int(2), Value::Int(1)])
    );
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
        .evaluate_derive(
            &state,
            &mut handler,
            "f",
            vec![Value::List(vec![
                Value::Int(1),
                Value::Int(2),
                Value::Int(3),
            ])],
        )
        .unwrap();
    assert_eq!(val, Value::Option(Some(Box::new(Value::Int(3)))));
}

// ── sum ─────────────────────────────────────────────────────────

#[test]
fn sum_of_ints() {
    let source = r#"
system "test" {
    derive f(xs: list<int>) -> int {
        sum(xs)
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
            vec![Value::List(vec![
                Value::Int(1),
                Value::Int(2),
                Value::Int(3),
            ])],
        )
        .unwrap();
    assert_eq!(val, Value::Int(6));
}

#[test]
fn sum_of_empty_list() {
    let source = r#"
system "test" {
    derive f(xs: list<int>) -> int {
        sum(xs)
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
fn sum_method_on_list() {
    let source = r#"
system "test" {
    derive f(xs: list<int>) -> int {
        xs.sum()
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
            vec![Value::List(vec![
                Value::Int(1),
                Value::Int(2),
                Value::Int(3),
            ])],
        )
        .unwrap();
    assert_eq!(val, Value::Int(6));
}

// ── any / all ───────────────────────────────────────────────────

#[test]
fn any_with_true() {
    let source = r#"
system "test" {
    derive f(xs: list<bool>) -> bool {
        any(xs)
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
            vec![Value::List(vec![Value::Bool(false), Value::Bool(true)])],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(true));
}

#[test]
fn any_all_false() {
    let source = r#"
system "test" {
    derive f(xs: list<bool>) -> bool {
        any(xs)
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
            vec![Value::List(vec![Value::Bool(false), Value::Bool(false)])],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(false));
}

#[test]
fn any_empty() {
    let source = r#"
system "test" {
    derive f(xs: list<bool>) -> bool {
        any(xs)
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
    assert_eq!(val, Value::Bool(false));
}

#[test]
fn all_true() {
    let source = r#"
system "test" {
    derive f(xs: list<bool>) -> bool {
        all(xs)
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
            vec![Value::List(vec![Value::Bool(true), Value::Bool(true)])],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(true));
}

#[test]
fn all_with_false() {
    let source = r#"
system "test" {
    derive f(xs: list<bool>) -> bool {
        all(xs)
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
            vec![Value::List(vec![Value::Bool(true), Value::Bool(false)])],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(false));
}

#[test]
fn all_empty() {
    let source = r#"
system "test" {
    derive f(xs: list<bool>) -> bool {
        all(xs)
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
    assert_eq!(val, Value::Bool(true));
}

#[test]
fn any_method_on_list() {
    let source = r#"
system "test" {
    derive f(xs: list<bool>) -> bool {
        xs.any()
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
            vec![Value::List(vec![Value::Bool(false), Value::Bool(true)])],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(true));
}

#[test]
fn all_method_on_list() {
    let source = r#"
system "test" {
    derive f(xs: list<bool>) -> bool {
        xs.all()
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
            vec![Value::List(vec![Value::Bool(true), Value::Bool(true)])],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(true));
}

// ── sort ────────────────────────────────────────────────────────

#[test]
fn sort_ints() {
    let source = r#"
system "test" {
    derive f(xs: list<int>) -> list<int> {
        sort(xs)
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
            vec![Value::List(vec![
                Value::Int(3),
                Value::Int(1),
                Value::Int(2),
            ])],
        )
        .unwrap();
    assert_eq!(
        val,
        Value::List(vec![Value::Int(1), Value::Int(2), Value::Int(3)])
    );
}

#[test]
fn sort_method_on_list() {
    let source = r#"
system "test" {
    derive f(xs: list<int>) -> list<int> {
        xs.sort()
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
            vec![Value::List(vec![
                Value::Int(3),
                Value::Int(1),
                Value::Int(2),
            ])],
        )
        .unwrap();
    assert_eq!(
        val,
        Value::List(vec![Value::Int(1), Value::Int(2), Value::Int(3)])
    );
}

// ── list comprehension ──────────────────────────────────────────

#[test]
fn list_comprehension_basic_transform() {
    let source = r#"
system "test" {
    derive f(xs: list<int>) -> list<int> {
        [x + 1 for x in xs]
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
            vec![Value::List(vec![
                Value::Int(1),
                Value::Int(2),
                Value::Int(3),
            ])],
        )
        .unwrap();
    assert_eq!(
        val,
        Value::List(vec![Value::Int(2), Value::Int(3), Value::Int(4)])
    );
}

#[test]
fn list_comprehension_with_filter() {
    let source = r#"
system "test" {
    derive f(xs: list<int>) -> list<int> {
        [x for x in xs if x > 0]
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
            vec![Value::List(vec![
                Value::Int(-1),
                Value::Int(0),
                Value::Int(2),
                Value::Int(3),
            ])],
        )
        .unwrap();
    assert_eq!(val, Value::List(vec![Value::Int(2), Value::Int(3)]));
}

#[test]
fn list_comprehension_range() {
    let source = r#"
system "test" {
    derive f() -> list<int> {
        [i * 2 for i in 0..5]
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
    assert_eq!(
        val,
        Value::List(vec![
            Value::Int(0),
            Value::Int(2),
            Value::Int(4),
            Value::Int(6),
            Value::Int(8),
        ])
    );
}

#[test]
fn list_comprehension_inclusive_range() {
    let source = r#"
system "test" {
    derive f() -> list<int> {
        [i for i in 1..=3]
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
    assert_eq!(
        val,
        Value::List(vec![Value::Int(1), Value::Int(2), Value::Int(3)])
    );
}

#[test]
fn list_comprehension_pattern_filtering() {
    let source = r#"
system "test" {
    derive f(opts: list<option<int>>) -> list<int> {
        [x for some(x) in opts]
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
            vec![Value::List(vec![
                Value::Option(Some(Box::new(Value::Int(1)))),
                Value::None,
                Value::Option(Some(Box::new(Value::Int(3)))),
            ])],
        )
        .unwrap();
    assert_eq!(val, Value::List(vec![Value::Int(1), Value::Int(3)]));
}

#[test]
fn list_comprehension_empty_result() {
    let source = r#"
system "test" {
    derive f(xs: list<int>) -> list<int> {
        [x for x in xs if x > 100]
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
            vec![Value::List(vec![
                Value::Int(1),
                Value::Int(2),
                Value::Int(3),
            ])],
        )
        .unwrap();
    assert_eq!(val, Value::List(vec![]));
}

// ── composition: comprehension + aggregation ────────────────────

#[test]
fn sum_of_comprehension() {
    let source = r#"
system "test" {
    derive f(xs: list<int>) -> int {
        sum([x * x for x in xs])
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
            vec![Value::List(vec![
                Value::Int(1),
                Value::Int(2),
                Value::Int(3),
            ])],
        )
        .unwrap();
    // 1 + 4 + 9 = 14
    assert_eq!(val, Value::Int(14));
}

#[test]
fn sort_of_comprehension() {
    let source = r#"
system "test" {
    derive f(xs: list<int>) -> list<int> {
        sort([x * 2 for x in xs])
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
            vec![Value::List(vec![
                Value::Int(3),
                Value::Int(1),
                Value::Int(2),
            ])],
        )
        .unwrap();
    assert_eq!(
        val,
        Value::List(vec![Value::Int(2), Value::Int(4), Value::Int(6)])
    );
}

#[test]
fn comprehension_range_with_filter() {
    let source = r#"
system "test" {
    derive f() -> list<int> {
        [i for i in 0..10 if i > 5]
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
    assert_eq!(
        val,
        Value::List(vec![
            Value::Int(6),
            Value::Int(7),
            Value::Int(8),
            Value::Int(9),
        ])
    );
}
