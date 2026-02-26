use ttrpg_ast::FileId;
use ttrpg_lexer::{Lexer, RawLexer, TokenKind};

#[test]
fn test_lex_full_example_no_errors() {
    let source = include_str!("../../../spec/v0/04_full_example.ttrpg");
    let tokens: Vec<_> = Lexer::new(source, FileId::SYNTH).collect();
    let errors: Vec<_> = tokens
        .iter()
        .filter(|t| matches!(&t.kind, TokenKind::Error(_)))
        .collect();
    assert!(
        errors.is_empty(),
        "Lexer produced {} error token(s): {:#?}",
        errors.len(),
        errors
    );
}

// ── Regression: tdsl-w3ef — numeric literal overflow ────────────────

#[test]
fn test_overflow_int_literal_produces_error() {
    // A number that overflows i64 should produce an error token, not Int(0)
    let source = "99999999999999999999";
    let tokens: Vec<_> = RawLexer::new(source, FileId::SYNTH).collect();
    let has_error = tokens
        .iter()
        .any(|t| matches!(&t.kind, TokenKind::Error(_)));
    let has_zero = tokens.iter().any(|t| matches!(&t.kind, TokenKind::Int(0)));
    assert!(
        has_error && !has_zero,
        "overflowing int literal should produce Error token, not Int(0); got: {:?}",
        tokens.iter().map(|t| &t.kind).collect::<Vec<_>>()
    );
}

#[test]
fn test_overflow_dice_sides_gives_misleading_error() {
    // 1d followed by a number that overflows u32 currently produces "dice sides
    // must be at least 1" because overflow → 0. It should instead report overflow.
    let source = "1d99999999999";
    let tokens: Vec<_> = RawLexer::new(source, FileId::SYNTH).collect();
    let error_msgs: Vec<_> = tokens
        .iter()
        .filter_map(|t| match &t.kind {
            TokenKind::Error(msg) => Some(msg.as_str()),
            _ => None,
        })
        .collect();
    assert!(!error_msgs.is_empty(), "should produce an error");
    // The error should mention overflow, not "dice sides must be at least 1"
    assert!(
        error_msgs
            .iter()
            .any(|m| m.contains("overflow") || m.contains("too large")),
        "error should mention overflow, not misleading 'sides must be at least 1'; got: {:?}",
        error_msgs,
    );
}

#[test]
fn test_overflow_dice_count_produces_error() {
    // A count that overflows u32 when cast: 4294967296d6 should error, not become 0d6
    let source = "4294967296d6";
    let tokens: Vec<_> = RawLexer::new(source, FileId::SYNTH).collect();
    let has_zero_count = tokens
        .iter()
        .any(|t| matches!(&t.kind, TokenKind::Dice { count: 0, .. }));
    assert!(
        !has_zero_count,
        "overflowing dice count should not silently wrap to 0; got: {:?}",
        tokens.iter().map(|t| &t.kind).collect::<Vec<_>>()
    );
}

#[test]
fn test_overflow_unit_literal_produces_error() {
    // A unit literal with overflowing numeric part should error, not become 0ft
    let source = "99999999999999999999ft";
    let tokens: Vec<_> = RawLexer::new(source, FileId::SYNTH).collect();
    let has_error = tokens
        .iter()
        .any(|t| matches!(&t.kind, TokenKind::Error(_)));
    let has_zero_unit = tokens
        .iter()
        .any(|t| matches!(&t.kind, TokenKind::UnitLiteral { value: 0, .. }));
    assert!(
        has_error && !has_zero_unit,
        "overflowing unit literal should produce Error, not UnitLiteral(0, ft); got: {:?}",
        tokens.iter().map(|t| &t.kind).collect::<Vec<_>>()
    );
}
