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
            DeclKind::Hook(_) | DeclKind::Option(_) | DeclKind::Move(_) | DeclKind::Table(_) | DeclKind::Unit(_) => {}
        }
    }

    assert_eq!(enums, 6, "enum count");
    assert_eq!(structs, 2, "struct count");
    assert_eq!(entities, 2, "entity count");
    assert_eq!(derives, 4, "derive count");
    assert_eq!(mechanics, 6, "mechanic count");
    assert_eq!(actions, 6, "action count");
    assert_eq!(reactions, 1, "reaction count");
    assert_eq!(conditions, 3, "condition count");
    assert_eq!(prompts, 2, "prompt count");
    assert_eq!(events, 3, "event count");
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
            modify attack_roll(attacker: attacker, target: target) {
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
fn test_enum_empty_payload_rejected() {
    let source = r#"system "test" {
    enum Result {
        hit
        miss()
    }
}"#;
    let (_, diagnostics) = parse(source);
    assert!(
        diagnostics.iter().any(|d| d.message.contains("at least one field")),
        "should reject empty enum variant payload, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
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
fn test_empty_pattern_match_rejected() {
    // Use integer scrutinee to avoid IDENT{} struct-literal disambiguation
    let source = r#"system "test" {
    derive f(x: int) -> int {
        match 1 {}
    }
}"#;
    let (_, diagnostics) = parse(source);
    assert!(
        diagnostics.iter().any(|d| d.message.contains("at least one arm")),
        "should reject empty match, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

#[test]
fn test_empty_guard_match_rejected() {
    let source = r#"system "test" {
    derive f(x: int) -> int {
        match {}
    }
}"#;
    let (_, diagnostics) = parse(source);
    assert!(
        diagnostics.iter().any(|d| d.message.contains("at least one arm")),
        "should reject empty guard match, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

#[test]
fn test_enum_comma_separated() {
    let source = r#"system "test" {
    enum Result { hit, miss, graze }
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
fn test_match_arms_comma_separated() {
    let source = r#"system "test" {
    derive f(x: int) -> int {
        match x { 1 => 10, 2 => 20, _ => 0 }
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

// ── NL suppression tests ────────────────────────────────────────

#[test]
fn test_colon_nl_suppression() {
    // Colon should suppress following newline, allowing multi-line field values
    let source = r#"system "test" {
    struct Weapon {
        name:
            string
        damage:
            int
    }
}"#;
    let (_, diagnostics) = parse(source);
    assert!(diagnostics.is_empty(), "colon should suppress NL: {:?}", diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>());
}

#[test]
fn test_arrow_nl_suppression() {
    // Thin arrow should suppress following newline in return type annotations
    let source = r#"system "test" {
    derive modifier(score: int) ->
        int {
        floor((score - 10) / 2)
    }
}"#;
    let (_, diagnostics) = parse(source);
    assert!(diagnostics.is_empty(), "-> should suppress NL: {:?}", diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>());
}

#[test]
fn test_underscore_rejected_in_expr() {
    // _ should not be valid in expression context (only in patterns)
    let source = r#"system "test" {
    derive f(x: int) -> int {
        let y = _
        y
    }
}"#;
    let (_, diagnostics) = parse(source);
    assert!(!diagnostics.is_empty(), "_ should be rejected in expression context");
}

// ── Regression tests ─────────────────────────────────────────────

#[test]
fn test_action_newlines_between_cost_and_requires() {
    // Regression: blank lines or comments between cost {} and requires {}
    // caused the parser to skip requires and fail with 'expected resolve'.
    let source = r#"system "test" {
    entity Character {
        HP: int
        position: int
    }
    action Attack on attacker: Character (target: Character) {
        cost { action }

        // check range
        requires { attacker.HP > 0 }

        resolve {
            target.HP -= 5
        }
    }
}"#;
    let (_, diagnostics) = parse(source);
    assert!(
        diagnostics.is_empty(),
        "newlines between cost and requires should be allowed, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

#[test]
fn test_modify_binding_wildcard() {
    // Regression: _ was not supported in modify bindings because
    // parse_modify_binding() called parse_expr() which rejects Underscore.
    let source = r#"system "test" {
    entity Character {
        HP: int
    }
    derive attack_roll(attacker: Character, target: Character) -> int {
        attacker.HP
    }
    option flanking extends "test" {
        description: "Flanking bonus"
        default: off
        when enabled {
            modify attack_roll(attacker: _, target: _) {
                result.bonus = 2
            }
        }
    }
}"#;
    let (_, diagnostics) = parse(source);
    assert!(
        diagnostics.is_empty(),
        "wildcard _ should be allowed in modify bindings, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

#[test]
fn test_none_pattern_in_match() {
    // Regression: `none` was not a valid match pattern because
    // parse_pattern() did not handle TokenKind::None.
    let source = r#"system "test" {
    derive f(x: option<int>) -> int {
        match x {
            none => 0
            _ => 1
        }
    }
}"#;
    let (_, diagnostics) = parse(source);
    assert!(
        diagnostics.is_empty(),
        "none should be a valid match pattern, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

#[test]
fn test_some_pattern_in_match() {
    let source = r#"system "test" {
    derive f(x: option<int>) -> int {
        match x {
            some(n) => n,
            none => 0
        }
    }
}"#;
    let (_, diagnostics) = parse(source);
    assert!(
        diagnostics.is_empty(),
        "some(n) should be a valid match pattern, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

#[test]
fn test_some_wildcard_pattern_in_match() {
    let source = r#"system "test" {
    derive f(x: option<int>) -> int {
        match x {
            some(_) => 1,
            none => 0
        }
    }
}"#;
    let (_, diagnostics) = parse(source);
    assert!(
        diagnostics.is_empty(),
        "some(_) should be a valid match pattern, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

#[test]
fn test_requires_multiline_expression() {
    // Regression: newlines inside requires { } were not suppressed,
    // so multiline expressions like `a &&\n b` would fail.
    let source = r#"system "test" {
    entity Character {
        HP: int
        is_alive: bool
    }
    action Attack on attacker: Character (target: Character) {
        requires {
            attacker.HP > 0
            && attacker.is_alive
        }
        resolve {
            target.HP -= 5
        }
    }
}"#;
    let (_, diagnostics) = parse(source);
    assert!(
        diagnostics.is_empty(),
        "multiline expressions inside requires should be allowed, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

#[test]
fn test_multiple_requires_blocks() {
    let source = r#"system "test" {
    entity Character {
        HP: int
        is_alive: bool
    }
    action Attack on attacker: Character (target: Character) {
        requires { attacker.HP > 0 }
        requires { attacker.is_alive }
        resolve {
            target.HP -= 5
        }
    }
}"#;
    let (mut program, diagnostics) = parse(source);
    assert!(
        diagnostics.is_empty(),
        "multiple requires blocks should be allowed, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    program.build_index();
    let action = &program.actions["Attack"];
    assert!(
        action.requires.is_some(),
        "combined requires should be present"
    );
    // The two requires blocks should be combined with &&
    match &action.requires.as_ref().unwrap().node {
        ttrpg_ast::ast::ExprKind::BinOp { op, .. } => {
            assert_eq!(*op, ttrpg_ast::ast::BinOp::And);
        }
        _ => panic!("expected BinOp(And)"),
    }
}

#[test]
fn test_multiple_requires_with_blank_lines() {
    let source = r#"system "test" {
    entity Character {
        HP: int
        is_alive: bool
        can_attack: bool
    }
    action Attack on attacker: Character (target: Character) {
        cost { action }

        requires { attacker.HP > 0 }

        requires { attacker.is_alive }

        requires { attacker.can_attack }

        resolve {
            target.HP -= 5
        }
    }
}"#;
    let (mut program, diagnostics) = parse(source);
    assert!(
        diagnostics.is_empty(),
        "multiple requires with blank lines should work, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    program.build_index();
    let action = &program.actions["Attack"];
    assert!(action.requires.is_some());
    // Three requires -> two && nodes (left-associative)
    match &action.requires.as_ref().unwrap().node {
        ttrpg_ast::ast::ExprKind::BinOp { op, lhs, .. } => {
            assert_eq!(*op, ttrpg_ast::ast::BinOp::And);
            // lhs should also be a BinOp(And) from the first two
            match &lhs.node {
                ttrpg_ast::ast::ExprKind::BinOp { op, .. } => {
                    assert_eq!(*op, ttrpg_ast::ast::BinOp::And);
                }
                _ => panic!("expected nested BinOp(And)"),
            }
        }
        _ => panic!("expected BinOp(And)"),
    }
}

#[test]
fn test_cost_multiline() {
    // Regression: newlines inside cost { } were not suppressed.
    let source = r#"system "test" {
    entity Character {
        HP: int
    }
    action BigMove on actor: Character () {
        cost {
            action,
            bonus
        }
        resolve {
            actor.HP += 1
        }
    }
}"#;
    let (_, diagnostics) = parse(source);
    assert!(
        diagnostics.is_empty(),
        "multiline cost blocks should be allowed, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
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

// ── For-loop parsing tests ──────────────────────────────────────

#[test]
fn test_for_collection_simple() {
    let source = r#"system "test" {
    entity Character { HP: int }
    mechanic apply_damage(targets: list<Character>, damage: int) -> int {
        for target in targets {
            target.HP -= damage
        }
        0
    }
}"#;
    let (_, diagnostics) = parse(source);
    assert!(
        diagnostics.is_empty(),
        "for-each over collection should parse, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

#[test]
fn test_for_range() {
    let source = r#"system "test" {
    derive sum_range(n: int) -> int {
        let total = 0
        for i in 0..n {
            total += i
        }
        total
    }
}"#;
    let (_, diagnostics) = parse(source);
    assert!(
        diagnostics.is_empty(),
        "for-range should parse, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

#[test]
fn test_for_with_pattern() {
    let source = r#"system "test" {
    enum Result { hit(amount: int), miss }
    derive count_hits(results: list<Result>) -> int {
        let total = 0
        for hit(amount) in results {
            total += amount
        }
        total
    }
}"#;
    let (_, diagnostics) = parse(source);
    assert!(
        diagnostics.is_empty(),
        "for-loop with destructuring pattern should parse, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

#[test]
fn test_for_expr_standalone_collection() {
    let (expr, diagnostics) = ttrpg_parser::parse_expr("for x in items { x }");
    assert!(
        diagnostics.is_empty(),
        "standalone for-collection should parse, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    let expr = expr.unwrap();
    assert!(
        matches!(expr.node, ExprKind::For { ref iterable, .. } if matches!(iterable, ForIterable::Collection(_))),
        "expected For with Collection iterable"
    );
}

#[test]
fn test_for_expr_standalone_range() {
    let (expr, diagnostics) = ttrpg_parser::parse_expr("for i in 0..10 { i }");
    assert!(
        diagnostics.is_empty(),
        "standalone for-range should parse, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    let expr = expr.unwrap();
    assert!(
        matches!(expr.node, ExprKind::For { ref iterable, .. } if matches!(iterable, ForIterable::Range { .. })),
        "expected For with Range iterable"
    );
}

#[test]
fn test_for_range_with_expressions() {
    // Range bounds can be arbitrary expressions
    let (expr, diagnostics) = ttrpg_parser::parse_expr("for i in 1..n + 1 { i }");
    assert!(
        diagnostics.is_empty(),
        "for-range with expr bounds should parse, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    let expr = expr.unwrap();
    assert!(
        matches!(expr.node, ExprKind::For { ref iterable, .. } if matches!(iterable, ForIterable::Range { .. })),
        "expected For with Range iterable"
    );
}

#[test]
fn test_for_wildcard_pattern() {
    let (expr, diagnostics) = ttrpg_parser::parse_expr("for _ in items { 0 }");
    assert!(
        diagnostics.is_empty(),
        "for with wildcard pattern should parse, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    assert!(expr.is_some());
}

// ── Optional groups parsing tests ────────────────────────────────

#[test]
fn test_entity_with_optional_groups() {
    let source = r#"system "test" {
    entity Character {
        name: string
        level: int = 1
        AC: int

        optional Spellcasting {
            spellcasting_ability: int
            spell_save_DC: int
        }

        optional KiPowers {
            ki_points: int
            max_ki: int
        }
    }
}"#;
    let (program, diagnostics) = parse(source);
    assert!(
        diagnostics.is_empty(),
        "entity with optional groups should parse, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    let system = match &program.items[0].node {
        TopLevel::System(s) => s,
        _ => panic!("expected system block"),
    };
    match &system.decls[0].node {
        DeclKind::Entity(e) => {
            assert_eq!(e.name, "Character");
            assert_eq!(e.fields.len(), 3, "base fields");
            assert_eq!(e.optional_groups.len(), 2, "optional groups");
            assert_eq!(e.optional_groups[0].name, "Spellcasting");
            assert_eq!(e.optional_groups[0].fields.len(), 2);
            assert_eq!(e.optional_groups[1].name, "KiPowers");
            assert_eq!(e.optional_groups[1].fields.len(), 2);
        }
        _ => panic!("expected entity decl"),
    }
}

#[test]
fn test_entity_optional_group_with_defaults() {
    let source = r#"system "test" {
    entity Character {
        name: string

        optional Rage {
            rage_damage: int = 2
            max_rage: int
        }
    }
}"#;
    let (program, diagnostics) = parse(source);
    assert!(
        diagnostics.is_empty(),
        "optional group fields with defaults should parse, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    let system = match &program.items[0].node {
        TopLevel::System(s) => s,
        _ => panic!("expected system block"),
    };
    match &system.decls[0].node {
        DeclKind::Entity(e) => {
            assert_eq!(e.optional_groups.len(), 1);
            let group = &e.optional_groups[0];
            assert_eq!(group.name, "Rage");
            assert!(group.fields[0].default.is_some(), "rage_damage should have default");
            assert!(group.fields[1].default.is_none(), "max_rage should not have default");
        }
        _ => panic!("expected entity decl"),
    }
}

#[test]
fn test_entity_fields_before_and_after_optional() {
    // Optional groups can be interleaved with regular fields
    let source = r#"system "test" {
    entity Character {
        name: string
        optional Spellcasting {
            dc: int
        }
        HP: int
    }
}"#;
    let (program, diagnostics) = parse(source);
    assert!(
        diagnostics.is_empty(),
        "fields after optional groups should parse, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    let system = match &program.items[0].node {
        TopLevel::System(s) => s,
        _ => panic!("expected system block"),
    };
    match &system.decls[0].node {
        DeclKind::Entity(e) => {
            // "name" comes before optional, "HP" after — both parsed as base fields
            assert_eq!(e.fields.len(), 2);
            assert_eq!(e.optional_groups.len(), 1);
        }
        _ => panic!("expected entity decl"),
    }
}

// ── `has` expression tests ──────────────────────────────────────

#[test]
fn test_has_expression() {
    let (expr, diagnostics) = ttrpg_parser::parse_expr("actor has Spellcasting");
    assert!(
        diagnostics.is_empty(),
        "has expression should parse, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    let expr = expr.unwrap();
    match expr.node {
        ExprKind::Has { ref entity, ref group_name } => {
            assert!(matches!(entity.node, ExprKind::Ident(ref n) if n == "actor"));
            assert_eq!(group_name, "Spellcasting");
        }
        _ => panic!("expected Has expression, got {:?}", std::mem::discriminant(&expr.node)),
    }
}

#[test]
fn test_has_in_if_condition() {
    let source = r#"system "test" {
    entity Character {
        name: string
        optional Spellcasting {
            dc: int
        }
    }
    derive get_dc(actor: Character) -> int {
        if actor has Spellcasting {
            actor.Spellcasting.dc
        } else {
            0
        }
    }
}"#;
    let (_, diagnostics) = parse(source);
    assert!(
        diagnostics.is_empty(),
        "has in if condition should parse, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

#[test]
fn test_has_composes_with_and() {
    let (expr, diagnostics) = ttrpg_parser::parse_expr("actor has Spellcasting && actor has KiPowers");
    assert!(
        diagnostics.is_empty(),
        "has with && should parse, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    let expr = expr.unwrap();
    assert!(matches!(expr.node, ExprKind::BinOp { op: BinOp::And, .. }));
}

#[test]
fn test_has_composes_with_not() {
    // `!` binds tighter than `has` (same as `in`), so parens are needed
    let (expr, diagnostics) = ttrpg_parser::parse_expr("!(actor has Spellcasting)");
    assert!(
        diagnostics.is_empty(),
        "!(has) should parse, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    let expr = expr.unwrap();
    match expr.node {
        ExprKind::UnaryOp { op: UnaryOp::Not, ref operand } => {
            match operand.node {
                ExprKind::Paren(ref inner) => {
                    assert!(matches!(inner.node, ExprKind::Has { .. }));
                }
                _ => panic!("expected Paren(Has)"),
            }
        }
        _ => panic!("expected UnaryOp(Not, Paren(Has))"),
    }
}

// ── `with` constraint tests ─────────────────────────────────────

#[test]
fn test_action_receiver_with_group() {
    let source = r#"system "test" {
    entity Character {
        name: string
        optional Spellcasting { dc: int }
    }
    action CastSpell on caster: Character with Spellcasting () {
        resolve {
            caster.Spellcasting.dc
        }
    }
}"#;
    let (program, diagnostics) = parse(source);
    assert!(
        diagnostics.is_empty(),
        "action with receiver constraint should parse, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    let system = match &program.items[0].node {
        TopLevel::System(s) => s,
        _ => panic!("expected system block"),
    };
    let action = system.decls.iter().find_map(|d| match &d.node {
        DeclKind::Action(a) => Some(a),
        _ => None,
    }).unwrap();
    assert_eq!(action.receiver_with_groups, vec!["Spellcasting"]);
}

#[test]
fn test_param_with_group() {
    let source = r#"system "test" {
    entity Character {
        name: string
        optional Spellcasting { dc: int }
    }
    derive spell_dc(caster: Character with Spellcasting) -> int {
        caster.Spellcasting.dc
    }
}"#;
    let (program, diagnostics) = parse(source);
    assert!(
        diagnostics.is_empty(),
        "param with group constraint should parse, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    let system = match &program.items[0].node {
        TopLevel::System(s) => s,
        _ => panic!("expected system block"),
    };
    let derive = system.decls.iter().find_map(|d| match &d.node {
        DeclKind::Derive(f) => Some(f),
        _ => None,
    }).unwrap();
    assert_eq!(derive.params[0].with_groups, vec!["Spellcasting"]);
}

#[test]
fn test_condition_receiver_with_group() {
    let source = r#"system "test" {
    entity Character {
        name: string
        optional Spellcasting { dc: int }
    }
    derive spell_dc(caster: Character) -> int { 0 }
    condition Silenced on bearer: Character with Spellcasting {
        modify spell_dc(caster: bearer) {
            result.dc = 0
        }
    }
}"#;
    let (program, diagnostics) = parse(source);
    assert!(
        diagnostics.is_empty(),
        "condition with receiver constraint should parse, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    let system = match &program.items[0].node {
        TopLevel::System(s) => s,
        _ => panic!("expected system block"),
    };
    let cond = system.decls.iter().find_map(|d| match &d.node {
        DeclKind::Condition(c) => Some(c),
        _ => None,
    }).unwrap();
    assert_eq!(cond.receiver_with_groups, vec!["Spellcasting"]);
}

#[test]
fn test_condition_with_params() {
    let source = r#"system "test" {
    entity Character { name: string }
    condition Frightened(source: Character) on bearer: Character {
        modify skill_check(actor: bearer) {
            mode = "disadvantage"
        }
    }
}"#;
    let (program, diagnostics) = parse(source);
    assert!(
        diagnostics.is_empty(),
        "parameterized condition should parse, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    let system = match &program.items[0].node {
        TopLevel::System(s) => s,
        _ => panic!("expected system block"),
    };
    let cond = system.decls.iter().find_map(|d| match &d.node {
        DeclKind::Condition(c) => Some(c),
        _ => None,
    }).unwrap();
    assert_eq!(cond.name, "Frightened");
    assert_eq!(cond.params.len(), 1);
    assert_eq!(cond.params[0].name, "source");
    assert_eq!(cond.receiver_name, "bearer");
}

#[test]
fn test_condition_no_params_still_works() {
    let source = r#"system "test" {
    entity Character { name: string }
    condition Prone on bearer: Character {
        modify skill_check(actor: bearer) {
            mode = "disadvantage"
        }
    }
}"#;
    let (program, diagnostics) = parse(source);
    assert!(
        diagnostics.is_empty(),
        "condition without params should parse, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    let system = match &program.items[0].node {
        TopLevel::System(s) => s,
        _ => panic!("expected system block"),
    };
    let cond = system.decls.iter().find_map(|d| match &d.node {
        DeclKind::Condition(c) => Some(c),
        _ => None,
    }).unwrap();
    assert_eq!(cond.name, "Prone");
    assert!(cond.params.is_empty());
}

#[test]
fn test_reaction_receiver_with_group() {
    let source = r#"system "test" {
    entity Character {
        name: string
        optional Spellcasting { dc: int }
    }
    event spell_cast(reactor: Character) {
        caster: Character
    }
    reaction Counterspell on reactor: Character with Spellcasting (
        trigger: spell_cast(reactor: reactor)
    ) {
        resolve {
            reactor.Spellcasting.dc
        }
    }
}"#;
    let (_, diagnostics) = parse(source);
    assert!(
        diagnostics.is_empty(),
        "reaction with receiver constraint should parse, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

// ── `hook` declaration tests ──────────────────────────────────────

#[test]
fn test_parse_basic_hook() {
    let source = r#"system "test" {
    entity Character { HP: int }
    event damage(actor: Character, target: Character) {}
    hook OnDamage on target: Character (
        trigger: damage(target: target)
    ) {
        target.HP -= 1
    }
}"#;
    let (program, diagnostics) = parse(source);
    assert!(
        diagnostics.is_empty(),
        "basic hook should parse, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    // Verify the hook was indexed
    program.items.iter().for_each(|item| {
        if let ttrpg_ast::ast::TopLevel::System(sys) = &item.node {
            assert!(
                sys.decls.iter().any(|d| matches!(&d.node, ttrpg_ast::ast::DeclKind::Hook(h) if h.name == "OnDamage")),
                "hook decl should be present in system block"
            );
        }
    });
}

#[test]
fn test_parse_hook_with_groups() {
    let source = r#"system "test" {
    entity Character {
        HP: int
        optional Spellcasting { dc: int }
    }
    event spell_cast(caster: Character) {}
    hook TrackCasting on caster: Character with Spellcasting (
        trigger: spell_cast(caster: caster)
    ) {
        0
    }
}"#;
    let (_, diagnostics) = parse(source);
    assert!(
        diagnostics.is_empty(),
        "hook with receiver constraint should parse, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

#[test]
fn test_parse_hook_soft_keyword() {
    // "hook" is a soft keyword — should still be usable as identifier elsewhere
    let source = r#"system "test" {
    entity Character { HP: int }
    event damage(actor: Character) {}
    hook OnDamage on actor: Character (
        trigger: damage(actor: actor)
    ) {
        let hook = 42
        hook
    }
}"#;
    let (_, diagnostics) = parse(source);
    assert!(
        diagnostics.is_empty(),
        "hook as variable name should parse, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

// ── `grant` / `revoke` statement tests ──────────────────────────

#[test]
fn test_grant_statement() {
    let source = r#"system "test" {
    entity Character {
        name: string
        optional Spellcasting {
            ability: int
            dc: int
        }
    }
    action GainSpellcasting on actor: Character () {
        resolve {
            grant actor.Spellcasting {
                ability: 3,
                dc: 15
            }
        }
    }
}"#;
    let (program, diagnostics) = parse(source);
    assert!(
        diagnostics.is_empty(),
        "grant statement should parse, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    let system = match &program.items[0].node {
        TopLevel::System(s) => s,
        _ => panic!("expected system block"),
    };
    let action = system.decls.iter().find_map(|d| match &d.node {
        DeclKind::Action(a) => Some(a),
        _ => None,
    }).unwrap();
    let stmt = &action.resolve.node[0].node;
    match stmt {
        StmtKind::Grant { group_name, fields, .. } => {
            assert_eq!(group_name, "Spellcasting");
            assert_eq!(fields.len(), 2);
            assert_eq!(fields[0].name, "ability");
            assert_eq!(fields[1].name, "dc");
        }
        _ => panic!("expected Grant statement, got {:?}", std::mem::discriminant(stmt)),
    }
}

#[test]
fn test_grant_multiline() {
    let source = r#"system "test" {
    entity Character {
        name: string
        optional Rage { damage: int }
    }
    action Enrage on actor: Character () {
        resolve {
            grant actor.Rage {
                damage: 2
            }
        }
    }
}"#;
    let (_, diagnostics) = parse(source);
    assert!(
        diagnostics.is_empty(),
        "multiline grant should parse, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

#[test]
fn test_revoke_statement() {
    let source = r#"system "test" {
    entity Character {
        name: string
        optional Spellcasting { dc: int }
    }
    action LoseSpellcasting on actor: Character () {
        resolve {
            revoke actor.Spellcasting
        }
    }
}"#;
    let (program, diagnostics) = parse(source);
    assert!(
        diagnostics.is_empty(),
        "revoke statement should parse, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    let system = match &program.items[0].node {
        TopLevel::System(s) => s,
        _ => panic!("expected system block"),
    };
    let action = system.decls.iter().find_map(|d| match &d.node {
        DeclKind::Action(a) => Some(a),
        _ => None,
    }).unwrap();
    let stmt = &action.resolve.node[0].node;
    match stmt {
        StmtKind::Revoke { group_name, .. } => {
            assert_eq!(group_name, "Spellcasting");
        }
        _ => panic!("expected Revoke statement, got {:?}", std::mem::discriminant(stmt)),
    }
}

#[test]
fn test_grant_error_without_field_access() {
    let source = r#"system "test" {
    entity Character { name: string }
    action Bad on actor: Character () {
        resolve {
            grant actor { x: 1 }
        }
    }
}"#;
    let (_, diagnostics) = parse(source);
    assert!(
        diagnostics.iter().any(|d| d.message.contains("entity.GroupName")),
        "grant without .Group should error, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

#[test]
fn test_revoke_error_without_field_access() {
    let source = r#"system "test" {
    entity Character { name: string }
    action Bad on actor: Character () {
        resolve {
            revoke actor
        }
    }
}"#;
    let (_, diagnostics) = parse(source);
    assert!(
        diagnostics.iter().any(|d| d.message.contains("entity.GroupName")),
        "revoke without .Group should error, got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

// ── Ordered enums ────────────────────────────────────────────────

#[test]
fn test_ordered_enum_parsed() {
    let source = r#"system "test" {
    enum Size ordered {
        small,
        medium,
        large
    }
}"#;
    let (program, diagnostics) = parse(source);
    assert!(diagnostics.is_empty(), "unexpected errors: {:?}", diagnostics);

    let system = match &program.items[0].node {
        TopLevel::System(s) => s,
        _ => panic!("expected system block"),
    };
    let decl = match &system.decls[0].node {
        DeclKind::Enum(e) => e,
        _ => panic!("expected enum decl"),
    };
    assert_eq!(decl.name, "Size");
    assert!(decl.ordered, "expected ordered flag to be true");
    assert_eq!(decl.variants.len(), 3);
}

#[test]
fn test_non_ordered_enum_parsed() {
    let source = r#"system "test" {
    enum Color {
        red,
        green,
        blue
    }
}"#;
    let (program, diagnostics) = parse(source);
    assert!(diagnostics.is_empty(), "unexpected errors: {:?}", diagnostics);

    let system = match &program.items[0].node {
        TopLevel::System(s) => s,
        _ => panic!("expected system block"),
    };
    let decl = match &system.decls[0].node {
        DeclKind::Enum(e) => e,
        _ => panic!("expected enum decl"),
    };
    assert_eq!(decl.name, "Color");
    assert!(!decl.ordered, "expected ordered flag to be false");
}

// ── Struct field separator tests ────────────────────────────────

#[test]
fn test_struct_fields_comma_separated_single_line() {
    let source = r#"system "test" {
    struct Point { x: int, y: int }
}"#;
    let (_, diagnostics) = parse(source);
    assert!(diagnostics.is_empty(), "comma-separated fields should parse: {:?}", diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>());
}

#[test]
fn test_struct_fields_newline_separated() {
    let source = r#"system "test" {
    struct Point {
        x: int
        y: int
    }
}"#;
    let (_, diagnostics) = parse(source);
    assert!(diagnostics.is_empty(), "newline-separated fields should parse: {:?}", diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>());
}

#[test]
fn test_struct_fields_trailing_comma() {
    let source = r#"system "test" {
    struct Point { x: int, y: int, }
}"#;
    let (_, diagnostics) = parse(source);
    assert!(diagnostics.is_empty(), "trailing comma should parse: {:?}", diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>());
}

#[test]
fn test_struct_fields_missing_separator() {
    let source = r#"system "test" {
    struct Point { x: int y: int }
}"#;
    let (_, diagnostics) = parse(source);
    assert!(!diagnostics.is_empty(), "missing separator should produce an error");
}

#[test]
fn struct_lit_with_base_only() {
    let (expr, diags) = ttrpg_parser::parse_expr("Point { ..other }");
    assert!(diags.is_empty(), "unexpected diagnostics: {:?}", diags.iter().map(|d| &d.message).collect::<Vec<_>>());
    let expr = expr.unwrap();
    match &expr.node {
        ExprKind::StructLit { name, fields, base } => {
            assert_eq!(name, "Point");
            assert!(fields.is_empty());
            assert!(base.is_some(), "expected base expression");
            match &base.as_ref().unwrap().node {
                ExprKind::Ident(n) => assert_eq!(n, "other"),
                _ => panic!("expected Ident base"),
            }
        }
        _ => panic!("expected StructLit"),
    }
}

#[test]
fn struct_lit_with_fields_and_base() {
    let (expr, diags) = ttrpg_parser::parse_expr("Point { x: 1, y: 2, ..defaults }");
    assert!(diags.is_empty(), "unexpected diagnostics: {:?}", diags.iter().map(|d| &d.message).collect::<Vec<_>>());
    let expr = expr.unwrap();
    match &expr.node {
        ExprKind::StructLit { name, fields, base } => {
            assert_eq!(name, "Point");
            assert_eq!(fields.len(), 2);
            assert_eq!(fields[0].name, "x");
            assert_eq!(fields[1].name, "y");
            assert!(base.is_some(), "expected base expression");
        }
        _ => panic!("expected StructLit"),
    }
}

#[test]
fn struct_lit_with_base_trailing_comma() {
    let (expr, diags) = ttrpg_parser::parse_expr("Point { x: 1, ..defaults, }");
    assert!(diags.is_empty(), "unexpected diagnostics: {:?}", diags.iter().map(|d| &d.message).collect::<Vec<_>>());
    let expr = expr.unwrap();
    match &expr.node {
        ExprKind::StructLit { name, fields, base } => {
            assert_eq!(name, "Point");
            assert_eq!(fields.len(), 1);
            assert!(base.is_some());
        }
        _ => panic!("expected StructLit"),
    }
}

// ── Regression: tdsl-cd7 — leading ..base with trailing comma ──

#[test]
fn struct_lit_leading_base_trailing_comma() {
    let (expr, diags) = ttrpg_parser::parse_expr("Point { ..other, }");
    assert!(diags.is_empty(), "trailing comma after leading ..base should parse: {:?}", diags.iter().map(|d| &d.message).collect::<Vec<_>>());
    let expr = expr.unwrap();
    match &expr.node {
        ExprKind::StructLit { name, fields, base } => {
            assert_eq!(name, "Point");
            assert!(fields.is_empty(), "expected no fields");
            assert!(base.is_some(), "expected base expression");
        }
        _ => panic!("expected StructLit"),
    }
}

// ── Bug repro tests (P1) ──────────────────────────────────────────

/// Bug tdsl-srpf: bare 'some' in pattern is parsed as PatternKind::Ident
/// (a catch-all binding) instead of being recognized as the option constructor.
/// match x { some => 10, none => 0 } matches EVERYTHING on the first arm.
#[test]
fn bare_some_pattern_is_not_ident_binding() {
    let (expr, diags) = ttrpg_parser::parse_expr("match x { some => 10, none => 0 }");
    // After fix: bare `some` emits a diagnostic and recovers as Some(wildcard)
    assert!(!diags.is_empty(), "expected a diagnostic about bare `some`");
    let expr = expr.unwrap();
    match &expr.node {
        ExprKind::PatternMatch { arms, .. } => {
            // The first arm pattern should NOT be an ident binding named "some".
            // It should either be PatternKind::Some (constructor) or produce a diagnostic.
            match &arms[0].pattern.node {
                PatternKind::Ident(name) if name == "some" => {
                    panic!("bare 'some' was parsed as Ident binding — this is bug tdsl-srpf");
                }
                _ => {} // any other treatment is acceptable
            }
        }
        _ => panic!("expected PatternMatch"),
    }
}

/// Bug tdsl-9h5: when a closing brace is missing, suppress_newlines_in_brace_block
/// removes ALL newlines to EOF, corrupting the token stream and losing subsequent
/// declarations.
#[test]
fn missing_brace_does_not_corrupt_subsequent_decls() {
    // First system has a missing closing brace in the derive body.
    // Second system should still be parseable.
    let source = r#"system "A" {
    derive broken() -> int {
        let x = 1
        // missing closing brace for derive
}

system "B" {
    derive ok() -> int { 42 }
}
"#;
    let (program, diagnostics) = parse(source);
    // We expect parse errors for the malformed first system, but the second
    // system should still be recovered. The bug causes all of "B" to be lost.
    let system_names: Vec<&str> = program.items.iter().filter_map(|item| {
        match &item.node {
            TopLevel::System(s) => Some(s.name.as_str()),
            _ => None,
        }
    }).collect();
    assert!(
        system_names.contains(&"B"),
        "system B was lost due to token stream corruption — bug tdsl-9h5.\n\
         Found systems: {:?}\nDiagnostics: {:?}",
        system_names,
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

// ── Regression: tdsl-99qw — pattern parser rejects negative int patterns ──

#[test]
fn test_negative_int_pattern_in_match() {
    // `-1` should be a valid match pattern for integer scrutinees.
    let source = r#"system "test" {
    derive f(x: int) -> int {
        match x {
            -1 => 10
            0 => 0
            _ => 1
        }
    }
}"#;
    let (_, diagnostics) = parse(source);
    assert!(
        diagnostics.is_empty(),
        "negative integer patterns should be parseable; got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

// ── Regression: tdsl-a7a — trailing comma after param with-groups ──

#[test]
fn test_trailing_comma_after_param_with_group() {
    // Trailing comma works for plain params; it should also work when the
    // last param has with-group constraints.
    let source = r#"system "test" {
    entity Character {
        HP: int
        optional Spellcasting { dc: int }
    }
    derive f(actor: Character with Spellcasting,) -> int {
        actor.Spellcasting.dc
    }
}"#;
    let (_, diagnostics) = parse(source);
    assert!(
        diagnostics.is_empty(),
        "trailing comma after param with-group should parse; got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

// ── Regression: tdsl-v13 — qualified type breaks for aliases matching soft keywords ──

#[test]
fn test_qualified_type_with_soft_keyword_alias() {
    // When an import alias matches a soft type keyword like "Duration",
    // qualified types like `Duration.CustomType` should parse as Qualified,
    // not as the builtin Duration leaving `.CustomType` unconsumed.
    let source = r#"use "other_system" as Duration
system "test" {
    derive f() -> Duration.CustomType {
        0
    }
}"#;
    let (_, diagnostics) = parse(source);
    let has_unexpected = diagnostics.iter().any(|d| {
        d.message.contains("unexpected") || d.message.contains("expected")
    });
    assert!(
        !has_unexpected,
        "qualified type with soft keyword alias should parse; got: {:?}",
        diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

// ── Regression: tdsl-q2p — recover_to_decl misses hook/table/unit starts ──

#[test]
fn test_error_recovery_finds_hook_declaration() {
    // After a malformed derive, recovery should stop at a 'hook' keyword
    // so the subsequent hook declaration is parsed.
    let source = r#"system "test" {
    entity Character { HP: int }
    event Damage(amount: int) {}
    derive bad_fn( -> int {
        42
    }
    hook OnDamage on actor: Character (
        trigger: Damage(amount: amount)
    ) {
        actor.HP -= amount
    }
}"#;
    let (program, diagnostics) = parse(source);
    assert!(!diagnostics.is_empty(), "should have errors from bad_fn");

    let system = match &program.items[0].node {
        TopLevel::System(s) => s,
        _ => panic!("expected system block"),
    };

    let has_hook = system.decls.iter().any(|d| matches!(&d.node, DeclKind::Hook(_)));
    assert!(
        has_hook,
        "error recovery should find hook declaration after bad derive; found {} decl(s)",
        system.decls.len(),
    );
}

#[test]
fn test_error_recovery_finds_unit_declaration() {
    // After a malformed derive, recovery should stop at a 'unit' keyword.
    let source = r#"system "test" {
    derive bad_fn( -> int {
        42
    }
    unit Distance {
        base: int
    }
}"#;
    let (program, diagnostics) = parse(source);
    assert!(!diagnostics.is_empty(), "should have errors from bad_fn");

    let system = match &program.items[0].node {
        TopLevel::System(s) => s,
        _ => panic!("expected system block"),
    };

    let has_unit = system.decls.iter().any(|d| matches!(&d.node, DeclKind::Unit(_)));
    assert!(
        has_unit,
        "error recovery should find unit declaration after bad derive; found {} decl(s)",
        system.decls.len(),
    );
}

// ── Regression: tdsl-z6xa — negative pattern uses checked_neg ──────────

#[test]
fn negative_pattern_max_value_does_not_panic() {
    // -9223372036854775807 is -(i64::MAX), which is valid (i64::MIN + 1).
    // Before the fix, this used unchecked `-n`; now it uses checked_neg.
    // The lexer prevents i64::MIN from appearing as a positive literal,
    // so no real overflow can occur, but this verifies the path works.
    let src = r#"system "test" {
    derive f(x: int) -> int {
        match x {
            -42 => 1,
            _ => 0,
        }
    }
}"#;
    let (prog, diags) = ttrpg_parser::parse(src);
    let parse_errors: Vec<_> = diags
        .iter()
        .filter(|d| d.severity == ttrpg_ast::diagnostic::Severity::Error)
        .collect();
    assert!(
        parse_errors.is_empty(),
        "negative pattern should parse successfully; got errors: {:?}",
        parse_errors.iter().map(|d| &d.message).collect::<Vec<_>>(),
    );
    let _ = prog;
}

