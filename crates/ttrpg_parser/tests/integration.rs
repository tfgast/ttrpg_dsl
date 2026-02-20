use ttrpg_parser::{parse, Severity, SourceMap};
use ttrpg_ast::ast::*;

#[test]
fn test_parse_full_example() {
    let source = include_str!("../../../spec/v0/04_full_example.ttrpg");
    let (program, diagnostics) = parse(source);

    if !diagnostics.is_empty() {
        let sm = SourceMap::new(source);
        for d in &diagnostics {
            eprintln!("{}", sm.render(d));
        }
    }
    assert!(
        diagnostics.is_empty(),
        "Parser produced {} error(s)",
        diagnostics.len()
    );

    // Should have 1 system block
    assert_eq!(program.items.len(), 1);
    let system = match &program.items[0].node {
        TopLevel::System(s) => s,
        _ => panic!("expected system block"),
    };
    assert_eq!(system.name, "D&D 5e Combat");

    // Count declarations by type
    let mut enums = 0;
    let mut structs = 0;
    let mut entities = 0;
    let mut derives = 0;
    let mut mechanics = 0;
    let mut actions = 0;
    let mut reactions = 0;
    let mut conditions = 0;
    let mut prompts = 0;
    let mut events = 0;

    for decl in &system.decls {
        match &decl.node {
            DeclKind::Enum(_) => enums += 1,
            DeclKind::Struct(_) => structs += 1,
            DeclKind::Entity(_) => entities += 1,
            DeclKind::Derive(_) => derives += 1,
            DeclKind::Mechanic(_) => mechanics += 1,
            DeclKind::Action(_) => actions += 1,
            DeclKind::Reaction(_) => reactions += 1,
            DeclKind::Condition(_) => conditions += 1,
            DeclKind::Prompt(_) => prompts += 1,
            DeclKind::Event(_) => events += 1,
            DeclKind::Option(_) | DeclKind::Move(_) => {}
        }
    }

    assert_eq!(enums, 5, "enum count");
    assert_eq!(structs, 2, "struct count");
    assert_eq!(entities, 2, "entity count");
    assert_eq!(derives, 4, "derive count");
    assert_eq!(mechanics, 6, "mechanic count");
    assert_eq!(actions, 4, "action count");
    assert_eq!(reactions, 1, "reaction count");
    assert_eq!(conditions, 3, "condition count");
    assert_eq!(prompts, 2, "prompt count");
    assert_eq!(events, 1, "event count");
}

#[test]
fn test_parse_simple_derive() {
    let source = r#"system "test" {
    derive modifier(score: int) -> int {
        floor((score - 10) / 2)
    }
}"#;
    let (program, diagnostics) = parse(source);
    assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>());
    assert_eq!(program.items.len(), 1);
}

#[test]
fn test_parse_option_decl() {
    let source = r#"system "test" {
    option flanking extends "D&D 5e Combat" {
        description: "Melee attackers on opposite sides gain advantage"
        default: off
        when enabled {
            modify attack_roll(attacker: _, target: _) {
                if flanking_position(attacker, target) {
                    mode = advantage
                }
            }
        }
    }
}"#;
    let (_program, diagnostics) = parse(source);
    assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>());
}

#[test]
fn test_parse_move_decl() {
    let source = r#"system "test" {
    move GoAggro on actor: Character (target: Character) {
        trigger: "threaten with force"
        roll: 2d6 + actor.stats[Hard]
        on strong_hit {
            target.HP -= 5
        }
        on weak_hit {
            target.HP -= 2
        }
        on miss {
            actor.HP -= 1
        }
    }
}"#;
    let (program, diagnostics) = parse(source);
    assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>());
    let system = match &program.items[0].node {
        TopLevel::System(s) => s,
        _ => panic!("expected system block"),
    };
    match &system.decls[0].node {
        DeclKind::Move(m) => {
            assert_eq!(m.name, "GoAggro");
            assert_eq!(m.outcomes.len(), 3);
        }
        _ => panic!("expected move decl"),
    }
}

// ── Validation tests ─────────────────────────────────────────────

#[test]
fn test_invalid_lvalue_produces_error() {
    let source = r#"system "test" {
    derive f(x: int) -> int {
        1 = 2
        x
    }
}"#;
    let (_, diagnostics) = parse(source);
    assert!(
        diagnostics.iter().any(|d| d.message.contains("invalid assignment target")),
        "should report invalid assignment target, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

#[test]
fn test_move_requires_outcome_blocks() {
    let source = r#"system "test" {
    move GoAggro on actor: Character (target: Character) {
        trigger: "threaten"
        roll: 2d6 + actor.stats[Hard]
    }
}"#;
    let (_, diagnostics) = parse(source);
    assert!(
        diagnostics.iter().any(|d| d.message.contains("outcome")),
        "should report missing outcome blocks, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

#[test]
fn test_enum_requires_at_least_one_variant() {
    let source = r#"system "test" {
    enum Empty {}
}"#;
    let (_, diagnostics) = parse(source);
    assert!(
        diagnostics.iter().any(|d| d.message.contains("at least one variant")),
        "should report empty enum, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

#[test]
fn test_enum_newline_separated_variants() {
    let source = r#"system "test" {
    enum Result {
        hit
        miss
        graze
    }
}"#;
    let (program, diagnostics) = parse(source);
    assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>());
    let system = match &program.items[0].node {
        TopLevel::System(s) => s,
        _ => panic!("expected system block"),
    };
    match &system.decls[0].node {
        DeclKind::Enum(e) => assert_eq!(e.variants.len(), 3),
        _ => panic!("expected enum decl"),
    }
}

#[test]
fn test_match_arms_newline_separated() {
    let source = r#"system "test" {
    derive f(x: int) -> int {
        match x {
            1 => 10
            2 => 20
            _ => 0
        }
    }
}"#;
    let (_, diagnostics) = parse(source);
    assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>());
}

#[test]
fn test_guard_match_newline_separated() {
    let source = r#"system "test" {
    derive f(x: int) -> int {
        match {
            x > 10 => 100
            x > 5 => 50
            _ => 0
        }
    }
}"#;
    let (_, diagnostics) = parse(source);
    assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>());
}

#[test]
fn test_trailing_comma_in_params() {
    let source = r#"system "test" {
    derive f(x: int, y: int,) -> int {
        x + y
    }
}"#;
    let (_, diagnostics) = parse(source);
    assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>());
}

#[test]
fn test_trailing_comma_in_args() {
    let source = r#"system "test" {
    derive f(x: int) -> int {
        f(x,)
    }
}"#;
    let (_, diagnostics) = parse(source);
    assert!(diagnostics.is_empty(), "errors: {:?}", diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>());
}

// ── Error recovery tests ─────────────────────────────────────────

#[test]
fn test_error_missing_colon_in_field() {
    let source = r#"system "test" {
    struct Foo {
        x int
        y: int
    }
}"#;
    let (program, diagnostics) = parse(source);
    // Should report error but still parse something
    assert!(!diagnostics.is_empty(), "should have at least one diagnostic");
    assert!(diagnostics.iter().any(|d| d.message.contains("expected")));

    // System block should still be present
    assert_eq!(program.items.len(), 1);
}

#[test]
fn test_error_missing_brace() {
    let source = r#"system "test" {
    enum Foo { A, B
    struct Bar {
        x: int
    }
}"#;
    let (program, diagnostics) = parse(source);
    // Should report errors but recover
    assert!(!diagnostics.is_empty());
    // Should still produce a system block
    assert_eq!(program.items.len(), 1);
}

#[test]
fn test_error_recovery_continues_past_bad_decl() {
    let source = r#"system "test" {
    derive bad_fn( -> int {
        42
    }
    derive good_fn(x: int) -> int {
        x + 1
    }
}"#;
    let (program, diagnostics) = parse(source);
    assert!(!diagnostics.is_empty(), "should report errors for bad decl");

    let system = match &program.items[0].node {
        TopLevel::System(s) => s,
        _ => panic!("expected system block"),
    };

    // Recovery should allow the second derive to be parsed
    let good_count = system.decls.iter().filter(|d| {
        matches!(&d.node, DeclKind::Derive(f) if f.name == "good_fn")
    }).count();
    assert_eq!(good_count, 1, "recovery should parse good_fn after bad_fn");
}

// ── Diagnostic rendering tests ───────────────────────────────────

#[test]
fn test_source_map_line_col() {
    let source = "line1\nline2\nline3";
    let sm = SourceMap::new(source);
    assert_eq!(sm.line_col(0), (1, 1));   // 'l' in line1
    assert_eq!(sm.line_col(5), (1, 6));   // '\n' after line1
    assert_eq!(sm.line_col(6), (2, 1));   // 'l' in line2
    assert_eq!(sm.line_col(12), (3, 1));  // 'l' in line3
}

#[test]
fn test_diagnostic_rendering() {
    let source = "let x = 42\nlet y foo\nlet z = 1";
    let sm = SourceMap::new(source);
    let diag = ttrpg_parser::Diagnostic::error("expected '=', found identifier", ttrpg_ast::Span::new(17, 20));
    let rendered = sm.render(&diag);

    assert!(rendered.contains("error:"), "should contain severity");
    assert!(rendered.contains("expected '=', found identifier"), "should contain message");
    assert!(rendered.contains("line 2:"), "should reference line 2");
    assert!(rendered.contains("let y foo"), "should show source line");
    assert!(rendered.contains("^^^"), "should have carets");
}

#[test]
fn test_error_severity() {
    let source = r#"system "test" {
    struct Foo {
        x int
    }
}"#;
    let (_, diagnostics) = parse(source);
    assert!(!diagnostics.is_empty());
    // All diagnostics from the parser should be errors
    for d in &diagnostics {
        assert_eq!(d.severity, Severity::Error);
    }
}
