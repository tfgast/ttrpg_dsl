//! Integration tests for DSL-side entity construction via struct literal syntax.

use ttrpg_ast::diagnostic::Severity;
use ttrpg_ast::FileId;
use ttrpg_interp::adapter::StateAdapter;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::StateProvider;
use ttrpg_interp::value::Value;
use ttrpg_interp::Interpreter;

const PROGRAM_SOURCE: &str = r#"
system "EntityConstructionTest" {
    entity Monster {
        name: string
        hit_dice: int
        max_hp: int
        ac: int = 10

        optional Spellcasting {
            spell_slots: int
            spell_dc: int = 10
        }

        include BasicStats
    }

    group BasicStats {
        str_score: int = 10
        dex_score: int = 10
    }

    function create_ogre() -> Monster {
        Monster {
            name: "Ogre",
            hit_dice: 4,
            max_hp: 26,
            ac: 5,
        }
    }

    function create_goblin_wizard() -> Monster {
        Monster {
            name: "Goblin Wizard",
            hit_dice: 1,
            max_hp: 4,
            ac: 6,
            Spellcasting {
                spell_slots: 3,
                spell_dc: 12,
            },
        }
    }

    function create_strong_monster() -> Monster {
        Monster {
            name: "Hill Giant",
            hit_dice: 8,
            max_hp: 44,
            BasicStats {
                str_score: 19,
                dex_score: 8,
            },
        }
    }

    derive monster_name(m: Monster) -> string {
        m.name
    }
}
"#;

fn setup() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    let (program, parse_errors) = ttrpg_parser::parse(PROGRAM_SOURCE, FileId::SYNTH);
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

struct AckHandler {
    log: Vec<Effect>,
}

impl AckHandler {
    fn new() -> Self {
        Self { log: Vec::new() }
    }
}

impl EffectHandler for AckHandler {
    fn handle(&mut self, effect: Effect) -> Response {
        self.log.push(effect);
        Response::Acknowledged
    }
}

#[test]
fn basic_entity_construction() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let adapter = StateAdapter::new(state);
    let mut handler = AckHandler::new();

    let val = adapter.run(&mut handler, |state, handler| {
        interp.evaluate_function(state, handler, "create_ogre", vec![])
    });
    let val = val.unwrap();

    match &val {
        Value::Entity(e) => {
            let final_state = adapter.into_inner();
            assert_eq!(
                final_state.read_field(e, "name"),
                Some(Value::Str("Ogre".into()))
            );
            assert_eq!(final_state.read_field(e, "hit_dice"), Some(Value::Int(4)));
            assert_eq!(final_state.read_field(e, "max_hp"), Some(Value::Int(26)));
            assert_eq!(final_state.read_field(e, "ac"), Some(Value::Int(5)));
        }
        other => panic!("expected Entity value, got {other:?}"),
    }
}

#[test]
fn entity_construction_with_inline_group() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let adapter = StateAdapter::new(state);
    let mut handler = AckHandler::new();

    let val = adapter.run(&mut handler, |state, handler| {
        interp.evaluate_function(state, handler, "create_goblin_wizard", vec![])
    });
    let val = val.unwrap();

    match &val {
        Value::Entity(e) => {
            let final_state = adapter.into_inner();
            assert_eq!(
                final_state.read_field(e, "name"),
                Some(Value::Str("Goblin Wizard".into()))
            );
            // Spellcasting group should be active
            let spell_group = final_state.read_field(e, "Spellcasting");
            assert!(spell_group.is_some(), "Spellcasting group should be active");
            match spell_group.unwrap() {
                Value::Struct { fields, .. } => {
                    assert_eq!(fields.get("spell_slots"), Some(&Value::Int(3)));
                    assert_eq!(fields.get("spell_dc"), Some(&Value::Int(12)));
                }
                other => panic!("expected Struct value for Spellcasting, got {other:?}"),
            }
        }
        other => panic!("expected Entity value, got {other:?}"),
    }
}

#[test]
fn entity_construction_auto_materializes_include_groups() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let adapter = StateAdapter::new(state);
    let mut handler = AckHandler::new();

    // create_ogre doesn't explicitly provide BasicStats — should be auto-materialized
    let val = adapter.run(&mut handler, |state, handler| {
        interp.evaluate_function(state, handler, "create_ogre", vec![])
    });
    let val = val.unwrap();

    match &val {
        Value::Entity(e) => {
            let final_state = adapter.into_inner();
            let stats = final_state.read_field(e, "BasicStats");
            assert!(
                stats.is_some(),
                "BasicStats include group should be auto-materialized"
            );
            match stats.unwrap() {
                Value::Struct { fields, .. } => {
                    assert_eq!(fields.get("str_score"), Some(&Value::Int(10)));
                    assert_eq!(fields.get("dex_score"), Some(&Value::Int(10)));
                }
                other => panic!("expected Struct, got {other:?}"),
            }
        }
        other => panic!("expected Entity, got {other:?}"),
    }
}

#[test]
fn entity_construction_include_group_with_custom_values() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let adapter = StateAdapter::new(state);
    let mut handler = AckHandler::new();

    let val = adapter.run(&mut handler, |state, handler| {
        interp.evaluate_function(state, handler, "create_strong_monster", vec![])
    });
    let val = val.unwrap();

    match &val {
        Value::Entity(e) => {
            let final_state = adapter.into_inner();
            let stats = final_state.read_field(e, "BasicStats");
            assert!(stats.is_some());
            match stats.unwrap() {
                Value::Struct { fields, .. } => {
                    assert_eq!(fields.get("str_score"), Some(&Value::Int(19)));
                    assert_eq!(fields.get("dex_score"), Some(&Value::Int(8)));
                }
                other => panic!("expected Struct, got {other:?}"),
            }
        }
        other => panic!("expected Entity, got {other:?}"),
    }
}

#[test]
fn checker_rejects_entity_construction_in_derive() {
    let source = r#"
system "DeriveTest" {
    entity Monster {
        name: string
    }

    derive make_monster() -> Monster {
        Monster { name: "Bad" }
    }
}
"#;
    let (program, parse_errors) = ttrpg_parser::parse(source, FileId::SYNTH);
    assert!(parse_errors.is_empty());
    let mut lower_diags = Vec::new();
    let program = ttrpg_parser::lower_moves(program, &mut lower_diags);
    let result = ttrpg_checker::check(&program);
    let errors: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .collect();
    assert!(
        !errors.is_empty(),
        "expected checker error for entity construction in derive"
    );
    assert!(
        errors
            .iter()
            .any(|d| d.message.contains("can only be constructed")),
        "expected context error, got: {:?}",
        errors.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

#[test]
fn checker_rejects_unknown_group_in_entity_literal() {
    let source = r#"
system "UnknownGroupTest" {
    entity Monster {
        name: string
    }

    function make_monster() -> Monster {
        Monster { name: "Bad", FakeGroup { x: 1 } }
    }
}
"#;
    let (program, parse_errors) = ttrpg_parser::parse(source, FileId::SYNTH);
    assert!(parse_errors.is_empty());
    let mut lower_diags = Vec::new();
    let program = ttrpg_parser::lower_moves(program, &mut lower_diags);
    let result = ttrpg_checker::check(&program);
    let errors: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .collect();
    assert!(
        !errors.is_empty(),
        "expected checker error for unknown group"
    );
    assert!(
        errors
            .iter()
            .any(|d| d.message.contains("no optional group")),
        "expected unknown group error, got: {:?}",
        errors.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

#[test]
fn checker_rejects_groups_on_struct_literal() {
    let source = r#"
system "StructGroupTest" {
    struct Point {
        x: int
        y: int
    }

    function bad() -> Point {
        Point { x: 1, y: 2, FakeGroup { z: 3 } }
    }
}
"#;
    let (program, parse_errors) = ttrpg_parser::parse(source, FileId::SYNTH);
    assert!(parse_errors.is_empty());
    let mut lower_diags = Vec::new();
    let program = ttrpg_parser::lower_moves(program, &mut lower_diags);
    let result = ttrpg_checker::check(&program);
    let errors: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .collect();
    assert!(
        !errors.is_empty(),
        "expected checker error for groups on struct"
    );
    assert!(
        errors
            .iter()
            .any(|d| d.message.contains("does not support inline group")),
        "expected struct group error, got: {:?}",
        errors.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}
