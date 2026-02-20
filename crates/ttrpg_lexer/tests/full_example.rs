use ttrpg_lexer::{Lexer, TokenKind};

#[test]
fn test_lex_full_example_no_errors() {
    let source = include_str!("../../../spec/v0/04_full_example.ttrpg");
    let tokens: Vec<_> = Lexer::new(source).collect();
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
