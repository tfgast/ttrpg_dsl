//! Integration tests for enum variant field defaults.
//!
//! Tests the full pipeline: parse → lower → check → interpret, verifying
//! that enum variants can have fields with default values.

use ttrpg_ast::FileId;
use ttrpg_ast::diagnostic::Severity;
use ttrpg_interp::Interpreter;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::Value;

// ── Setup ──────────────────────────────────────────────────────

fn compile(source: &str) -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
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

fn compile_errors(source: &str) -> Vec<String> {
    let (program, parse_errors) = ttrpg_parser::parse(source, FileId::SYNTH);
    if !parse_errors.is_empty() {
        return parse_errors.iter().map(|d| d.message.clone()).collect();
    }
    let mut lower_diags = Vec::new();
    let program = ttrpg_parser::lower_moves(program, &mut lower_diags);
    if !lower_diags.is_empty() {
        return lower_diags.iter().map(|d| d.message.clone()).collect();
    }
    let result = ttrpg_checker::check(&program);
    result
        .diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .map(|d| d.message.clone())
        .collect()
}

struct NullHandler;
impl EffectHandler for NullHandler {
    fn handle(&mut self, _effect: Effect) -> Response {
        Response::Acknowledged
    }
}

// ── Omitting a field with a default uses the default ───────────

#[test]
fn enum_variant_default_is_used_when_omitted() {
    let src = r#"
        system "test" {
            enum Weapon {
                Sword(name: string, magic_bonus: int = 0)
            }
            derive make_mundane() -> Weapon {
                Sword(name: "Longsword")
            }
            derive get_bonus(w: Weapon) -> int {
                match w {
                    Sword(name, magic_bonus) => magic_bonus
                }
            }
        }
    "#;
    let (program, result) = compile(src);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;
    let mundane = interp
        .evaluate_derive(&state, &mut handler, "make_mundane", vec![])
        .unwrap();
    let val = interp
        .evaluate_derive(&state, &mut handler, "get_bonus", vec![mundane])
        .unwrap();
    assert_eq!(val, Value::Int(0));
}

// ── Providing a value overrides the default ────────────────────

#[test]
fn enum_variant_default_overridden_by_explicit_value() {
    let src = r#"
        system "test" {
            enum Weapon {
                Sword(name: string, magic_bonus: int = 0)
            }
            derive make_magic() -> Weapon {
                Sword(name: "Longsword", magic_bonus: 3)
            }
            derive get_bonus(w: Weapon) -> int {
                match w {
                    Sword(name, magic_bonus) => magic_bonus
                }
            }
        }
    "#;
    let (program, result) = compile(src);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;
    let magic = interp
        .evaluate_derive(&state, &mut handler, "make_magic", vec![])
        .unwrap();
    let val = interp
        .evaluate_derive(&state, &mut handler, "get_bonus", vec![magic])
        .unwrap();
    assert_eq!(val, Value::Int(3));
}

// ── Multiple defaults ──────────────────────────────────────────

#[test]
fn enum_variant_multiple_defaults() {
    let src = r#"
        system "test" {
            enum Effect {
                Damage(amount: int, element: string = "physical", is_magical: bool = false)
            }
            derive make_fire() -> Effect {
                Damage(amount: 10, element: "fire")
            }
            derive get_element(e: Effect) -> string {
                match e {
                    Damage(amount, element, is_magical) => element
                }
            }
            derive is_magical(e: Effect) -> bool {
                match e {
                    Damage(amount, element, is_magical) => is_magical
                }
            }
        }
    "#;
    let (program, result) = compile(src);
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;
    let fire = interp
        .evaluate_derive(&state, &mut handler, "make_fire", vec![])
        .unwrap();
    let element = interp
        .evaluate_derive(&state, &mut handler, "get_element", vec![fire.clone()])
        .unwrap();
    let magical = interp
        .evaluate_derive(&state, &mut handler, "is_magical", vec![fire])
        .unwrap();
    assert_eq!(element, Value::Str("fire".into()));
    assert_eq!(magical, Value::Bool(false));
}

// ── Required field after default is an error ───────────────────

#[test]
fn required_field_after_default_is_error() {
    let src = r#"
        system "test" {
            enum Bad {
                Variant(a: int = 0, b: string)
            }
        }
    "#;
    let errors = compile_errors(src);
    assert!(
        errors
            .iter()
            .any(|e| e.contains("default") && e.contains("must come last")),
        "expected error about defaults coming last, got: {:?}",
        errors
    );
}

// ── Missing required field (no default) is still an error ──────

#[test]
fn missing_required_field_is_still_error() {
    let src = r#"
        system "test" {
            enum Weapon {
                Sword(name: string, magic_bonus: int = 0)
            }
            derive bad() -> Weapon {
                Sword()
            }
        }
    "#;
    let errors = compile_errors(src);
    assert!(
        errors.iter().any(|e| e.contains("missing required field")),
        "expected missing required field error, got: {:?}",
        errors
    );
}
