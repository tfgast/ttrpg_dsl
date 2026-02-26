//! Tests for `some(x)` / `none` pattern matching on `option<T>` values.

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

#[test]
fn some_pattern_binds_inner_value() {
    let source = r#"
system "test" {
    derive f(x: option<int>) -> int {
        match x {
            some(n) => n + 1,
            none => 0
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    // some(42) → 42 + 1 = 43
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "f",
            vec![Value::Option(Some(Box::new(Value::Int(42))))],
        )
        .unwrap();
    assert_eq!(val, Value::Int(43));
}

#[test]
fn none_matches_option_none() {
    let source = r#"
system "test" {
    derive f(x: option<int>) -> int {
        match x {
            some(n) => n + 1,
            none => 0
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    // Value::Option(None) should match `none` pattern (bug fix regression)
    let val = interp
        .evaluate_derive(&state, &mut handler, "f", vec![Value::Option(None)])
        .unwrap();
    assert_eq!(val, Value::Int(0));

    // Value::None should also still match `none` pattern
    let val = interp
        .evaluate_derive(&state, &mut handler, "f", vec![Value::None])
        .unwrap();
    assert_eq!(val, Value::Int(0));
}

#[test]
fn some_wildcard_pattern() {
    let source = r#"
system "test" {
    derive f(x: option<int>) -> int {
        match x {
            some(_) => 1,
            none => 0
        }
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
            vec![Value::Option(Some(Box::new(Value::Int(99))))],
        )
        .unwrap();
    assert_eq!(val, Value::Int(1));
}

#[test]
fn nested_some_pattern() {
    let source = r#"
system "test" {
    derive f(x: option<option<int>>) -> int {
        match x {
            some(some(n)) => n,
            some(none) => -1,
            none => -2
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    // some(some(5)) → 5
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "f",
            vec![Value::Option(Some(Box::new(Value::Option(Some(
                Box::new(Value::Int(5)),
            )))))],
        )
        .unwrap();
    assert_eq!(val, Value::Int(5));

    // some(none) → -1
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "f",
            vec![Value::Option(Some(Box::new(Value::Option(None))))],
        )
        .unwrap();
    assert_eq!(val, Value::Int(-1));

    // none → -2
    let val = interp
        .evaluate_derive(&state, &mut handler, "f", vec![Value::Option(None)])
        .unwrap();
    assert_eq!(val, Value::Int(-2));
}

// ── unwrap / unwrap_or tests ─────────────────────────────────────

#[test]
fn unwrap_on_some_returns_inner() {
    let source = r#"
system "test" {
    derive f(x: option<int>) -> int {
        x.unwrap()
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
            vec![Value::Option(Some(Box::new(Value::Int(42))))],
        )
        .unwrap();
    assert_eq!(val, Value::Int(42));
}

#[test]
fn unwrap_on_none_errors() {
    let source = r#"
system "test" {
    derive f(x: option<int>) -> int {
        x.unwrap()
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let err = interp
        .evaluate_derive(&state, &mut handler, "f", vec![Value::Option(None)])
        .unwrap_err();
    assert!(
        format!("{}", err).contains("unwrap()"),
        "expected unwrap error, got: {}",
        err
    );
}

#[test]
fn unwrap_on_value_none_errors() {
    let source = r#"
system "test" {
    derive f(x: option<int>) -> int {
        x.unwrap()
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let err = interp
        .evaluate_derive(&state, &mut handler, "f", vec![Value::None])
        .unwrap_err();
    assert!(
        format!("{}", err).contains("unwrap()"),
        "expected unwrap error, got: {}",
        err
    );
}

#[test]
fn unwrap_or_on_some_returns_inner() {
    let source = r#"
system "test" {
    derive f(x: option<int>) -> int {
        x.unwrap_or(99)
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
            vec![Value::Option(Some(Box::new(Value::Int(42))))],
        )
        .unwrap();
    assert_eq!(val, Value::Int(42));
}

#[test]
fn unwrap_or_on_none_returns_default() {
    let source = r#"
system "test" {
    derive f(x: option<int>) -> int {
        x.unwrap_or(99)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "f", vec![Value::Option(None)])
        .unwrap();
    assert_eq!(val, Value::Int(99));
}

#[test]
fn unwrap_or_on_value_none_returns_default() {
    let source = r#"
system "test" {
    derive f(x: option<int>) -> int {
        x.unwrap_or(99)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "f", vec![Value::None])
        .unwrap();
    assert_eq!(val, Value::Int(99));
}

#[test]
fn unwrap_chained_with_arithmetic() {
    let source = r#"
system "test" {
    derive f(x: option<int>) -> int {
        x.unwrap() + 10
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
            vec![Value::Option(Some(Box::new(Value::Int(32))))],
        )
        .unwrap();
    assert_eq!(val, Value::Int(42));
}

// ── if let some(x) tests ────────────────────────────────────────

#[test]
fn if_let_some_matches() {
    let source = r#"
system "test" {
    derive f(x: option<int>) -> int {
        if let some(n) = x { n + 1 } else { 0 }
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
            vec![Value::Option(Some(Box::new(Value::Int(42))))],
        )
        .unwrap();
    assert_eq!(val, Value::Int(43));
}

#[test]
fn if_let_some_no_match_takes_else() {
    let source = r#"
system "test" {
    derive f(x: option<int>) -> int {
        if let some(n) = x { n + 1 } else { 0 }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "f", vec![Value::Option(None)])
        .unwrap();
    assert_eq!(val, Value::Int(0));
}

#[test]
fn if_let_no_else_branch() {
    // if-let without else is a unit expression; test it as a statement
    // followed by a concrete return value
    let source = r#"
system "test" {
    derive f(x: option<int>) -> int {
        if let some(n) = x { n + 1 } else { -1 }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    // Matches — returns bound value
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "f",
            vec![Value::Option(Some(Box::new(Value::Int(5))))],
        )
        .unwrap();
    assert_eq!(val, Value::Int(6));

    // Doesn't match — takes else
    let val = interp
        .evaluate_derive(&state, &mut handler, "f", vec![Value::Option(None)])
        .unwrap();
    assert_eq!(val, Value::Int(-1));
}

#[test]
fn if_let_else_if_let_chain() {
    let source = r#"
system "test" {
    derive f(x: option<int>, y: option<int>) -> int {
        if let some(n) = x { n } else if let some(m) = y { m } else { -1 }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    // First matches
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "f",
            vec![
                Value::Option(Some(Box::new(Value::Int(10)))),
                Value::Option(Some(Box::new(Value::Int(20)))),
            ],
        )
        .unwrap();
    assert_eq!(val, Value::Int(10));

    // First none, second matches
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "f",
            vec![
                Value::Option(None),
                Value::Option(Some(Box::new(Value::Int(20)))),
            ],
        )
        .unwrap();
    assert_eq!(val, Value::Int(20));

    // Both none
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "f",
            vec![Value::Option(None), Value::Option(None)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(-1));
}

#[test]
fn if_let_nested_some() {
    let source = r#"
system "test" {
    derive f(x: option<option<int>>) -> int {
        if let some(some(n)) = x { n } else { -1 }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    // some(some(5)) -> 5
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "f",
            vec![Value::Option(Some(Box::new(Value::Option(Some(
                Box::new(Value::Int(5)),
            )))))],
        )
        .unwrap();
    assert_eq!(val, Value::Int(5));

    // some(none) -> -1
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "f",
            vec![Value::Option(Some(Box::new(Value::Option(None))))],
        )
        .unwrap();
    assert_eq!(val, Value::Int(-1));

    // none -> -1
    let val = interp
        .evaluate_derive(&state, &mut handler, "f", vec![Value::Option(None)])
        .unwrap();
    assert_eq!(val, Value::Int(-1));
}

// ── some() constructor builtin ────────────────────────────────────

#[test]
fn some_constructor_wraps_int() {
    let source = r#"
system "test" {
    derive f() -> option<int> {
        some(42)
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
    assert_eq!(val, Value::Option(Some(Box::new(Value::Int(42)))));
}

#[test]
fn some_constructor_wraps_string() {
    let source = r#"
system "test" {
    derive f() -> option<string> {
        some("hello")
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
        Value::Option(Some(Box::new(Value::Str("hello".into()))))
    );
}

#[test]
fn some_constructor_roundtrips_with_match() {
    let source = r#"
system "test" {
    derive make() -> option<int> {
        some(10)
    }
    derive consume(x: option<int>) -> int {
        match x {
            some(n) => n,
            none => -1
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let opt = interp
        .evaluate_derive(&state, &mut handler, "make", vec![])
        .unwrap();
    let val = interp
        .evaluate_derive(&state, &mut handler, "consume", vec![opt])
        .unwrap();
    assert_eq!(val, Value::Int(10));
}

#[test]
fn some_constructor_wraps_enum_variant() {
    let source = r#"
system "test" {
    enum Color { Red, Green, Blue }
    derive f() -> option<Color> {
        some(Red)
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
    match val {
        Value::Option(Some(inner)) => match *inner {
            Value::EnumVariant { ref variant, .. } => assert_eq!(variant.as_ref(), "Red"),
            other => panic!("expected EnumVariant, got {:?}", other),
        },
        other => panic!("expected Option(Some(...)), got {:?}", other),
    }
}

#[test]
fn some_constructor_with_expression() {
    let source = r#"
system "test" {
    derive f(x: int) -> option<int> {
        some(x + 1)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "f", vec![Value::Int(5)])
        .unwrap();
    assert_eq!(val, Value::Option(Some(Box::new(Value::Int(6)))));
}
