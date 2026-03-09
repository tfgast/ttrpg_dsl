use std::fmt;
use std::sync::Arc;

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
        suffix: Arc<str>,
    },

    // Identifier (includes soft keywords)
    Ident(Arc<str>),

    // Reserved keywords
    Let,
    If,
    Else,
    Match,
    True,
    False,
    None,
    In,
    Div,
    For,
    Return,

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
    Percent,  // %
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
    Pipe,     // |
    PipePipe, // ||

    // Whitespace / structure
    Semicolon, // ; (converted to Newline by wrapping lexer)
    Newline,
    Eof,

    // Error
    Error(String),
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TokenKind::Int(n) => write!(f, "integer `{n}`"),
            TokenKind::String(s) => write!(f, "string \"{}\"", s.escape_debug()),
            TokenKind::Dice { count, sides, .. } => write!(f, "dice `{count}d{sides}`"),
            TokenKind::UnitLiteral { value, suffix } => {
                write!(f, "unit literal `{value}{suffix}`")
            }
            TokenKind::Ident(name) => write!(f, "`{name}`"),
            TokenKind::Let => write!(f, "`let`"),
            TokenKind::If => write!(f, "`if`"),
            TokenKind::Else => write!(f, "`else`"),
            TokenKind::Match => write!(f, "`match`"),
            TokenKind::True => write!(f, "`true`"),
            TokenKind::False => write!(f, "`false`"),
            TokenKind::None => write!(f, "`none`"),
            TokenKind::In => write!(f, "`in`"),
            TokenKind::Div => write!(f, "`div`"),
            TokenKind::For => write!(f, "`for`"),
            TokenKind::Return => write!(f, "`return`"),
            TokenKind::LParen => write!(f, "`(`"),
            TokenKind::RParen => write!(f, "`)`"),
            TokenKind::LBrace => write!(f, "`{{`"),
            TokenKind::RBrace => write!(f, "`}}`"),
            TokenKind::LBracket => write!(f, "`[`"),
            TokenKind::RBracket => write!(f, "`]`"),
            TokenKind::Comma => write!(f, "`,`"),
            TokenKind::Colon => write!(f, "`:`"),
            TokenKind::Dot => write!(f, "`.`"),
            TokenKind::DotDot => write!(f, "`..`"),
            TokenKind::DotDotEq => write!(f, "`..=`"),
            TokenKind::Arrow => write!(f, "`->`"),
            TokenKind::FatArrow => write!(f, "`=>`"),
            TokenKind::Underscore => write!(f, "`_`"),
            TokenKind::Hash => write!(f, "`#`"),
            TokenKind::Plus => write!(f, "`+`"),
            TokenKind::Minus => write!(f, "`-`"),
            TokenKind::Star => write!(f, "`*`"),
            TokenKind::Slash => write!(f, "`/`"),
            TokenKind::Percent => write!(f, "`%`"),
            TokenKind::Bang => write!(f, "`!`"),
            TokenKind::Eq => write!(f, "`=`"),
            TokenKind::PlusEq => write!(f, "`+=`"),
            TokenKind::MinusEq => write!(f, "`-=`"),
            TokenKind::EqEq => write!(f, "`==`"),
            TokenKind::BangEq => write!(f, "`!=`"),
            TokenKind::Lt => write!(f, "`<`"),
            TokenKind::Gt => write!(f, "`>`"),
            TokenKind::LtEq => write!(f, "`<=`"),
            TokenKind::GtEq => write!(f, "`>=`"),
            TokenKind::AmpAmp => write!(f, "`&&`"),
            TokenKind::Pipe => write!(f, "`|`"),
            TokenKind::PipePipe => write!(f, "`||`"),
            TokenKind::Semicolon => write!(f, "`;`"),
            TokenKind::Newline => write!(f, "newline"),
            TokenKind::Eof => write!(f, "end of file"),
            TokenKind::Error(msg) => write!(f, "error: {msg}"),
        }
    }
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
            | TokenKind::Percent
            | TokenKind::PipePipe
            | TokenKind::AmpAmp
            | TokenKind::EqEq
            | TokenKind::BangEq
            | TokenKind::GtEq
            | TokenKind::LtEq
            // Note: bare > and < are NOT suppressing because they're ambiguous
            // with generic type brackets (e.g., set<T>). >= and <= still suppress.
            | TokenKind::In
            | TokenKind::Div
            | TokenKind::FatArrow
            | TokenKind::Arrow
            | TokenKind::Eq
            | TokenKind::PlusEq
            | TokenKind::MinusEq
            // After {  ,  :  and  #
            | TokenKind::LBrace
            | TokenKind::Comma
            | TokenKind::Pipe
            | TokenKind::Colon
            | TokenKind::Hash
        )
    }
}
