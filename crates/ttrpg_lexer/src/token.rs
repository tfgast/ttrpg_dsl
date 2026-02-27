use ttrpg_ast::{DiceFilter, Span};

#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

impl Token {
    pub fn new(kind: TokenKind, span: Span) -> Self {
        Self { kind, span }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    // Literals
    Int(i64),
    String(String),
    Dice {
        count: u32,
        sides: u32,
        filter: Option<DiceFilter>,
    },
    UnitLiteral {
        value: i64,
        suffix: String,
    },

    // Identifier (includes soft keywords)
    Ident(String),

    // Reserved keywords
    Let,
    If,
    Else,
    Match,
    True,
    False,
    None,
    In,
    For,

    // Punctuation
    LParen,     // (
    RParen,     // )
    LBrace,     // {
    RBrace,     // }
    LBracket,   // [
    RBracket,   // ]
    Comma,      // ,
    Colon,      // :
    Dot,        // .
    DotDot,     // ..
    DotDotEq,   // ..=
    Arrow,      // ->
    FatArrow,   // =>
    Underscore, // _ (standalone)
    Hash,       // #

    // Operators
    Plus,     // +
    Minus,    // -
    Star,     // *
    Slash,    // /
    Bang,     // !
    Eq,       // =
    PlusEq,   // +=
    MinusEq,  // -=
    EqEq,     // ==
    BangEq,   // !=
    Lt,       // <
    Gt,       // >
    LtEq,     // <=
    GtEq,     // >=
    AmpAmp,   // &&
    PipePipe, // ||

    // Whitespace / structure
    Newline,
    Eof,

    // Error
    Error(String),
}

impl TokenKind {
    /// Returns true if this token kind suppresses a following newline.
    pub fn suppresses_next_newline(&self) -> bool {
        matches!(
            self,
            // Binary/assignment operators and arrows
            TokenKind::Plus
            | TokenKind::Minus
            | TokenKind::Star
            | TokenKind::Slash
            | TokenKind::PipePipe
            | TokenKind::AmpAmp
            | TokenKind::EqEq
            | TokenKind::BangEq
            | TokenKind::GtEq
            | TokenKind::LtEq
            // Note: bare > and < are NOT suppressing because they're ambiguous
            // with generic type brackets (e.g., set<T>). >= and <= still suppress.
            | TokenKind::In
            | TokenKind::FatArrow
            | TokenKind::Arrow
            | TokenKind::Eq
            | TokenKind::PlusEq
            | TokenKind::MinusEq
            // After {  ,  :  and  #
            | TokenKind::LBrace
            | TokenKind::Comma
            | TokenKind::Colon
            | TokenKind::Hash
        )
    }
}
