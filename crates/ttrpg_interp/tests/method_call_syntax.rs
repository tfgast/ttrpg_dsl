//! Integration tests for method call syntax on collections, options, and dice.

use ttrpg_ast::diagnostic::Severity;
use ttrpg_ast::FileId;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::{DiceExpr, RollResult, Value};
use ttrpg_interp::Interpreter;

struct NoopHandler;
impl EffectHandler for NoopHandler {
    fn handle(&mut self, _: Effect) -> Response {
        Response::Acknowledged
    }
}

struct RollHandler;
impl EffectHandler for RollHandler {
    fn handle(&mut self, effect: Effect) -> Response {
        match effect {
            Effect::RollDice { expr } => {
                // Deterministic: every die rolls its max
                let mut dice = Vec::new();
                for g in &expr.groups {
                    dice.extend(vec![g.sides as i64; g.count as usize]);
                }
                let unmodified: i64 = dice.iter().sum();
                let total = unmodified + expr.modifier;
                Response::Rolled(RollResult {
                    dice: dice.clone(),
                    kept: dice,
                    modifier: expr.modifier,
                    unmodified,
                    total,
                    expr,
                })
            }
            _ => Response::Acknowledged,
        }
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

fn setup_with_errors(source: &str) -> Vec<String> {
    let (program, parse_errors) = ttrpg_parser::parse(source, FileId::SYNTH);
    if !parse_errors.is_empty() {
        return parse_errors.iter().map(|d| d.message.clone()).collect();
    }
    let mut lower_diags = Vec::new();
    let program = ttrpg_parser::lower_moves(program, &mut lower_diags);
    let result = ttrpg_checker::check(&program);
    result
        .diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .map(|d| d.message.clone())
        .collect()
}

// ── list methods ──────────────────────────────────────────────

#[test]
fn list_len_method() {
    let source = r#"
system "test" {
    derive f(xs: list<int>) -> int {
        xs.len()
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
    assert_eq!(val, Value::Int(2));
}

#[test]
fn list_first_method() {
    let source = r#"
system "test" {
    derive f(xs: list<int>) -> option<int> {
        xs.first()
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
            vec![Value::List(vec![Value::Int(42), Value::Int(99)])],
        )
        .unwrap();
    assert_eq!(val, Value::Option(Some(Box::new(Value::Int(42)))));

    // Empty list returns none
    let val = interp
        .evaluate_derive(&state, &mut handler, "f", vec![Value::List(vec![])])
        .unwrap();
    assert_eq!(val, Value::None);
}

#[test]
fn list_last_method() {
    let source = r#"
system "test" {
    derive f(xs: list<int>) -> option<int> {
        xs.last()
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

#[test]
fn list_reverse_method() {
    let source = r#"
system "test" {
    derive f(xs: list<int>) -> list<int> {
        xs.reverse()
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
        Value::List(vec![Value::Int(2), Value::Int(1), Value::Int(3)])
    );
}

#[test]
fn list_append_method() {
    let source = r#"
system "test" {
    derive f(xs: list<int>, val: int) -> list<int> {
        xs.append(val)
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
            vec![Value::List(vec![Value::Int(1)]), Value::Int(2)],
        )
        .unwrap();
    assert_eq!(val, Value::List(vec![Value::Int(1), Value::Int(2)]));
}

#[test]
fn list_concat_method() {
    let source = r#"
system "test" {
    derive f(a: list<int>, b: list<int>) -> list<int> {
        a.concat(b)
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

// ── set methods ───────────────────────────────────────────────

#[test]
fn set_len_method() {
    let source = r#"
system "test" {
    derive f(xs: set<int>) -> int {
        xs.len()
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
            vec![Value::Set(
                vec![Value::Int(1), Value::Int(2), Value::Int(3)]
                    .into_iter()
                    .collect(),
            )],
        )
        .unwrap();
    assert_eq!(val, Value::Int(3));
}

// ── map methods ───────────────────────────────────────────────

#[test]
fn map_len_method() {
    let source = r#"
system "test" {
    enum Color { red, blue }
    derive f(m: map<Color, int>) -> int {
        m.len()
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
            vec![Value::Map(
                vec![
                    (
                        Value::EnumVariant {
                            enum_name: "Color".into(),
                            variant: "red".into(),
                            fields: Default::default(),
                        },
                        Value::Int(10),
                    ),
                    (
                        Value::EnumVariant {
                            enum_name: "Color".into(),
                            variant: "blue".into(),
                            fields: Default::default(),
                        },
                        Value::Int(20),
                    ),
                ]
                .into_iter()
                .collect(),
            )],
        )
        .unwrap();
    assert_eq!(val, Value::Int(2));
}

#[test]
fn map_keys_method() {
    let source = r#"
system "test" {
    enum Color { red, blue }
    derive f(m: map<Color, int>) -> list<Color> {
        m.keys()
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
            vec![Value::Map(
                vec![(
                    Value::EnumVariant {
                        enum_name: "Color".into(),
                        variant: "red".into(),
                        fields: Default::default(),
                    },
                    Value::Int(10),
                )]
                .into_iter()
                .collect(),
            )],
        )
        .unwrap();
    match val {
        Value::List(items) => {
            assert_eq!(items.len(), 1);
            match &items[0] {
                Value::EnumVariant { variant, .. } => assert_eq!(variant.as_str(), "red"),
                other => panic!("expected EnumVariant, got {:?}", other),
            }
        }
        other => panic!("expected List, got {:?}", other),
    }
}

#[test]
fn map_values_method() {
    let source = r#"
system "test" {
    enum Color { red }
    derive f(m: map<Color, int>) -> list<int> {
        m.values()
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
            vec![Value::Map(
                vec![(
                    Value::EnumVariant {
                        enum_name: "Color".into(),
                        variant: "red".into(),
                        fields: Default::default(),
                    },
                    Value::Int(42),
                )]
                .into_iter()
                .collect(),
            )],
        )
        .unwrap();
    assert_eq!(val, Value::List(vec![Value::Int(42)]));
}

// ── option methods ────────────────────────────────────────────

#[test]
fn option_is_some_method() {
    let source = r#"
system "test" {
    derive f(xs: list<int>) -> bool {
        xs.first().is_some()
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
            vec![Value::List(vec![Value::Int(1)])],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(true));

    let val = interp
        .evaluate_derive(&state, &mut handler, "f", vec![Value::List(vec![])])
        .unwrap();
    assert_eq!(val, Value::Bool(false));
}

#[test]
fn option_is_none_method() {
    let source = r#"
system "test" {
    derive f(xs: list<int>) -> bool {
        xs.first().is_none()
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

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "f",
            vec![Value::List(vec![Value::Int(1)])],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(false));
}

// ── dice methods ──────────────────────────────────────────────

#[test]
fn dice_multiply_method() {
    let source = r#"
system "test" {
    mechanic f(d: DiceExpr) -> DiceExpr {
        d.multiply(3)
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "f",
            vec![Value::DiceExpr(DiceExpr::single(2, 6, None, 0))],
        )
        .unwrap();
    assert_eq!(
        val,
        Value::DiceExpr(DiceExpr::single(6, 6, None, 0))
    );
}

#[test]
fn dice_roll_method() {
    let source = r#"
system "test" {
    mechanic f(d: DiceExpr) -> RollResult {
        d.roll()
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = RollHandler;

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "f",
            vec![Value::DiceExpr(DiceExpr::single(2, 6, None, 0))],
        )
        .unwrap();
    // RollHandler rolls max on each die: 2d6 → 6+6 = 12
    match val {
        Value::RollResult(rr) => assert_eq!(rr.total, 12),
        other => panic!("expected RollResult, got {:?}", other),
    }
}

// ── string methods ────────────────────────────────────────────

#[test]
fn string_len_method() {
    let source = r#"
system "test" {
    derive f(s: string) -> int {
        s.len()
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "f", vec![Value::Str("hello".into())])
        .unwrap();
    assert_eq!(val, Value::Int(5));

    // Empty string
    let val = interp
        .evaluate_derive(&state, &mut handler, "f", vec![Value::Str("".into())])
        .unwrap();
    assert_eq!(val, Value::Int(0));
}

#[test]
fn string_contains_method() {
    let source = r#"
system "test" {
    derive f(s: string, sub: string) -> bool {
        s.contains(sub)
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
            vec![Value::Str("hello world".into()), Value::Str("world".into())],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(true));

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "f",
            vec![Value::Str("hello".into()), Value::Str("xyz".into())],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(false));
}

#[test]
fn string_starts_with_method() {
    let source = r#"
system "test" {
    derive f(s: string, prefix: string) -> bool {
        s.starts_with(prefix)
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
            vec![Value::Str("hello world".into()), Value::Str("hello".into())],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(true));

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "f",
            vec![Value::Str("hello".into()), Value::Str("world".into())],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(false));
}

#[test]
fn string_ends_with_method() {
    let source = r#"
system "test" {
    derive f(s: string, suffix: string) -> bool {
        s.ends_with(suffix)
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
            vec![Value::Str("hello world".into()), Value::Str("world".into())],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(true));

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "f",
            vec![Value::Str("hello".into()), Value::Str("xyz".into())],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(false));
}

#[test]
fn string_method_chaining_with_contains() {
    // Test using string method result in a larger expression
    let source = r#"
system "test" {
    derive f(s: string) -> int {
        if s.starts_with("fire") { 1 } else { 0 }
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
            vec![Value::Str("fireball".into())],
        )
        .unwrap();
    assert_eq!(val, Value::Int(1));

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "f",
            vec![Value::Str("icebolt".into())],
        )
        .unwrap();
    assert_eq!(val, Value::Int(0));
}

#[test]
fn unknown_method_on_string_error() {
    let errors = setup_with_errors(
        r#"
system "test" {
    derive f(s: string) -> int {
        s.foobar()
    }
}
"#,
    );
    assert!(!errors.is_empty());
    assert!(
        errors[0].contains("no method"),
        "expected 'no method' error, got: {}",
        errors[0]
    );
}

// ── chaining ──────────────────────────────────────────────────

#[test]
fn method_chaining_reverse_first_unwrap() {
    let source = r#"
system "test" {
    derive f(xs: list<int>) -> int {
        xs.reverse().first().unwrap()
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
    // reverse → [3,2,1], first → some(3), unwrap → 3
    assert_eq!(val, Value::Int(3));
}

#[test]
fn method_chaining_concat_len() {
    let source = r#"
system "test" {
    derive f(a: list<int>, b: list<int>) -> int {
        a.concat(b).len()
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
                Value::List(vec![Value::Int(3)]),
            ],
        )
        .unwrap();
    assert_eq!(val, Value::Int(3));
}

// ── free function forms still work ────────────────────────────

#[test]
fn free_function_len_still_works() {
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
            vec![Value::List(vec![Value::Int(1), Value::Int(2)])],
        )
        .unwrap();
    assert_eq!(val, Value::Int(2));
}

// ── error messages ────────────────────────────────────────────

#[test]
fn unknown_method_on_list_error() {
    let errors = setup_with_errors(
        r#"
system "test" {
    derive f(xs: list<int>) -> int {
        xs.foobar()
    }
}
"#,
    );
    assert!(!errors.is_empty());
    assert!(
        errors[0].contains("no method"),
        "expected 'no method' error, got: {}",
        errors[0]
    );
}

#[test]
fn unknown_method_on_int_error() {
    let errors = setup_with_errors(
        r#"
system "test" {
    derive f(x: int) -> int {
        x.len()
    }
}
"#,
    );
    assert!(!errors.is_empty());
    assert!(
        errors[0].contains("has no methods"),
        "expected 'has no methods' error, got: {}",
        errors[0]
    );
}

#[test]
fn dice_multiply_method_in_derive_rejected() {
    // .roll() should be rejected in derive context (no dice allowed)
    let errors = setup_with_errors(
        r#"
system "test" {
    derive f(d: DiceExpr) -> RollResult {
        d.roll()
    }
}
"#,
    );
    assert!(!errors.is_empty());
    assert!(
        errors[0].contains("can only be called in mechanic"),
        "expected dice permission error, got: {}",
        errors[0]
    );
}
