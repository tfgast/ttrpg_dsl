//! Integration tests for the `any` type with `is` guard narrowing.

use rustc_hash::FxHashMap;
use ttrpg_ast::FileId;
use ttrpg_ast::Name;
use ttrpg_ast::diagnostic::Severity;
use ttrpg_interp::Interpreter;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::Value;

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

fn setup_expect_errors(source: &str) -> Vec<String> {
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

// ── to_any and is with primitives ────────────────────────────────

#[test]
fn to_any_and_is_int() {
    let source = r#"
system "test" {
    derive check() -> bool {
        let x: any = to_any(42)
        x is int
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "check", vec![])
        .unwrap();
    assert_eq!(val, Value::Bool(true));
}

#[test]
fn to_any_is_int_false_for_string() {
    let source = r#"
system "test" {
    derive check() -> bool {
        let x: any = to_any("hello")
        x is int
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "check", vec![])
        .unwrap();
    assert_eq!(val, Value::Bool(false));
}

#[test]
fn to_any_is_string() {
    let source = r#"
system "test" {
    derive check() -> bool {
        let x: any = to_any("hello")
        x is string
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "check", vec![])
        .unwrap();
    assert_eq!(val, Value::Bool(true));
}

#[test]
fn to_any_is_bool() {
    let source = r#"
system "test" {
    derive check() -> bool {
        let x: any = to_any(true)
        x is bool
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "check", vec![])
        .unwrap();
    assert_eq!(val, Value::Bool(true));
}

// ── narrowing and field access ───────────────────────────────────

#[test]
fn any_narrowing_accesses_narrowed_type() {
    let source = r#"
system "test" {
    derive check() -> int {
        let x: any = to_any(42)
        if x is int {
            x + 1
        } else {
            0
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "check", vec![])
        .unwrap();
    assert_eq!(val, Value::Int(43));
}

// ── structs ──────────────────────────────────────────────────────

#[test]
fn any_is_struct() {
    let source = r#"
system "test" {
    struct Pos {
        x: int
        y: int
    }

    derive check() -> int {
        let p = Pos { x: 10, y: 20 }
        let a: any = to_any(p)
        if a is Pos {
            a.x + a.y
        } else {
            0
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "check", vec![])
        .unwrap();
    assert_eq!(val, Value::Int(30));
}

// ── enums ────────────────────────────────────────────────────────

#[test]
fn any_is_enum() {
    let source = r#"
system "test" {
    enum Color {
        Red
        Blue
    }

    derive check() -> bool {
        let c = Color.Red
        let a: any = to_any(c)
        a is Color
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "check", vec![])
        .unwrap();
    assert_eq!(val, Value::Bool(true));
}

// ── containers ───────────────────────────────────────────────────

#[test]
fn any_is_list_int() {
    let source = r#"
system "test" {
    derive check() -> bool {
        let xs: any = to_any([1, 2, 3])
        xs is list<int>
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "check", vec![])
        .unwrap();
    assert_eq!(val, Value::Bool(true));
}

#[test]
fn any_is_list_int_false_for_list_string() {
    let source = r#"
system "test" {
    derive check() -> bool {
        let xs: any = to_any(["a", "b"])
        xs is list<int>
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "check", vec![])
        .unwrap();
    assert_eq!(val, Value::Bool(false));
}

#[test]
fn any_is_option_string() {
    let source = r#"
system "test" {
    derive check_some() -> bool {
        let x: any = to_any(some("hello"))
        x is option<string>
    }

    derive check_none() -> bool {
        let x: any = to_any(none)
        x is option<string>
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NoopHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "check_some", vec![])
        .unwrap();
    assert_eq!(val, Value::Bool(true));

    let val = interp
        .evaluate_derive(&state, &mut handler, "check_none", vec![])
        .unwrap();
    assert_eq!(val, Value::Bool(true));
}

// ── entity types ─────────────────────────────────────────────────

#[test]
fn any_is_entity_type() {
    let source = r#"
system "test" {
    entity Character {
        name: string
    }

    entity Monster {
        cr: int
    }

    derive check(target: entity) -> bool {
        let a: any = to_any(target)
        a is Character
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NoopHandler;

    let mut char_fields = FxHashMap::default();
    char_fields.insert(Name::from("name"), Value::Str("Alice".into()));
    let char_ref = state.add_entity("Character", char_fields);

    let val = interp
        .evaluate_derive(&state, &mut handler, "check", vec![Value::Entity(char_ref)])
        .unwrap();
    assert_eq!(val, Value::Bool(true));

    let mut mon_fields = FxHashMap::default();
    mon_fields.insert(Name::from("cr"), Value::Int(5));
    let mon_ref = state.add_entity("Monster", mon_fields);

    let val = interp
        .evaluate_derive(&state, &mut handler, "check", vec![Value::Entity(mon_ref)])
        .unwrap();
    assert_eq!(val, Value::Bool(false));
}

// ── error cases ──────────────────────────────────────────────────

#[test]
fn is_on_non_any_non_entity_is_error() {
    let errors = setup_expect_errors(
        r#"
system "test" {
    derive check() -> bool {
        let x: int = 42
        x is int
    }
}
"#,
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("`is` can only be used with")),
        "expected error about `is` on int, got: {errors:?}"
    );
}

#[test]
fn is_any_is_error() {
    let errors = setup_expect_errors(
        r#"
system "test" {
    derive check() -> bool {
        let x: any = to_any(42)
        x is any
    }
}
"#,
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("`is any` is not meaningful")),
        "expected error about `is any`, got: {errors:?}"
    );
}

// ── existing entity is still works ───────────────────────────────

#[test]
fn entity_is_still_works() {
    let source = r#"
system "test" {
    entity Character {
        level: int
    }

    entity Monster {
        hit_dice: int
    }

    derive get_power(target: entity) -> int {
        if target is Character {
            target.level
        } else if target is Monster {
            target.hit_dice
        } else {
            0
        }
    }
}
"#;
    let (program, result) = setup(source);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut state = GameState::new();
    let mut handler = NoopHandler;

    let mut char_fields = FxHashMap::default();
    char_fields.insert(Name::from("level"), Value::Int(5));
    let char_ref = state.add_entity("Character", char_fields);

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "get_power",
            vec![Value::Entity(char_ref)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(5));

    let mut mon_fields = FxHashMap::default();
    mon_fields.insert(Name::from("hit_dice"), Value::Int(8));
    let mon_ref = state.add_entity("Monster", mon_fields);

    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "get_power",
            vec![Value::Entity(mon_ref)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(8));
}
