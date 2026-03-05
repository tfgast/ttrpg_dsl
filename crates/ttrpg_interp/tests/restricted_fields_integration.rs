//! End-to-end interpreter tests for the `restricted` field modifier.
//!
//! The `restricted` keyword is enforced by the checker, not the interpreter.
//! These tests verify that programs which pass the checker execute correctly
//! at runtime — same-module mutation, delegation patterns, and function-based
//! mutation all work as expected.

use rustc_hash::FxHashMap;
use ttrpg_ast::diagnostic::Severity;
use ttrpg_interp::adapter::StateAdapter;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::StateProvider;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

struct NoopHandler;
impl EffectHandler for NoopHandler {
    fn handle(&mut self, _: Effect) -> Response {
        Response::Acknowledged
    }
}

fn compile_multi(
    sources: &[(&str, &str)],
) -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    let owned: Vec<(String, String)> = sources
        .iter()
        .map(|(name, src)| (name.to_string(), src.to_string()))
        .collect();
    let parse_result = ttrpg_parser::parse_multi(&owned);
    let parse_errors: Vec<_> = parse_result
        .diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .collect();
    assert!(
        parse_errors.is_empty(),
        "parse/lower errors: {:?}",
        parse_errors.iter().map(|d| &d.message).collect::<Vec<_>>()
    );

    let (program, module_map) = parse_result.ok().unwrap();
    let result = ttrpg_checker::check_with_modules(program, module_map);
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

    (program.clone(), result)
}

fn make_character(gs: &mut GameState, hp: i64) -> ttrpg_interp::state::EntityRef {
    let mut fields = FxHashMap::default();
    fields.insert("HP".into(), Value::Int(hp));
    gs.add_entity("Character", fields)
}

// ── Same-module action can mutate restricted field ──────────────

#[test]
fn same_module_action_mutates_restricted_field() {
    let (program, result) = compile_multi(&[(
        "core.ttrpg",
        r#"
        system "Core" {
            entity Character {
                restricted HP: int
            }
            action TakeDamage on target: Character (amount: int) {
                resolve {
                    target.HP -= amount
                }
            }
        }
        "#,
    )]);

    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut gs = GameState::new();
    let target = make_character(&mut gs, 20);
    let mut handler = NoopHandler;

    let adapter = StateAdapter::new(gs);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "TakeDamage",
                target,
                vec![Value::Int(7)],
            )
            .unwrap();
    });
    let gs = adapter.into_inner();

    let hp = gs.read_field(&target, "HP").unwrap();
    assert_eq!(hp, Value::Int(13));
}

// ── Cross-module delegation: ext calls core action ──────────────

#[test]
fn cross_module_delegation_via_action_call() {
    // "Ext" cannot mutate HP directly (restricted), but can call Core's
    // TakeDamage action which does the mutation in the declaring module.
    let (program, result) = compile_multi(&[
        (
            "core.ttrpg",
            r#"
            system "Core" {
                entity Character {
                    restricted HP: int
                }
                action TakeDamage on target: Character (amount: int) {
                    resolve {
                        target.HP -= amount
                    }
                }
            }
            "#,
        ),
        (
            "ext.ttrpg",
            r#"
            use "Core"
            system "Ext" {
                action DoubleStrike on attacker: Character (target: Character) {
                    resolve {
                        // Delegate to Core's action — receiver is target
                        target.TakeDamage(3)
                        target.TakeDamage(3)
                    }
                }
            }
            "#,
        ),
    ]);

    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut gs = GameState::new();
    let attacker = make_character(&mut gs, 50);
    let target = make_character(&mut gs, 20);
    let mut handler = NoopHandler;

    let adapter = StateAdapter::new(gs);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "DoubleStrike",
                attacker,
                vec![Value::Entity(target)],
            )
            .unwrap();
    });
    let gs = adapter.into_inner();

    let hp = gs.read_field(&target, "HP").unwrap();
    assert_eq!(hp, Value::Int(14)); // 20 - 3 - 3
}

// ── Function in declaring module mutates restricted field ────────

#[test]
fn declaring_module_function_mutates_restricted_field() {
    // A function defined in the declaring module can mutate restricted
    // fields. When called from another module, the write statement is
    // still in the declaring module — so the checker allows it.
    let (program, result) = compile_multi(&[
        (
            "core.ttrpg",
            r#"
            system "Core" {
                entity Character {
                    restricted HP: int
                }
                function heal(target: Character, amount: int) {
                    target.HP += amount
                }
            }
            "#,
        ),
        (
            "ext.ttrpg",
            r#"
            use "Core"
            system "Ext" {
                action BigHeal on healer: Character (target: Character) {
                    resolve {
                        heal(target, 15)
                    }
                }
            }
            "#,
        ),
    ]);

    let interp = Interpreter::new(&program, &result.env).unwrap();
    let mut gs = GameState::new();
    let healer = make_character(&mut gs, 50);
    let target = make_character(&mut gs, 10);
    let mut handler = NoopHandler;

    let adapter = StateAdapter::new(gs);
    adapter.run(&mut handler, |state, eff_handler| {
        interp
            .execute_action(
                state,
                eff_handler,
                "BigHeal",
                healer,
                vec![Value::Entity(target)],
            )
            .unwrap();
    });
    let gs = adapter.into_inner();

    let hp = gs.read_field(&target, "HP").unwrap();
    assert_eq!(hp, Value::Int(25)); // 10 + 15
}
