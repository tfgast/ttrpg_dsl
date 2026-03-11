//! Integration tests for DSL-side entity construction via struct literal syntax.
//!
//! Runtime field/group coverage has moved to `tests/entity_construction.ttrpg-cli`.
//! These Rust tests keep only pipeline construction and checker-only rejection
//! cases that still belong next to the interpreter.

use ttrpg_ast::FileId;
use ttrpg_ast::diagnostic::Severity;
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

#[test]
fn pipeline_parses_checks_and_builds_interpreter() {
    let (program, result) = setup();
    let interp = Interpreter::new(&program, &result.env);
    assert!(
        interp.is_ok(),
        "interpreter creation failed: {:?}",
        interp.err()
    );
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
