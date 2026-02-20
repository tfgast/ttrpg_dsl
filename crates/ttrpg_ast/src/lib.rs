pub mod span;
pub mod ast;
pub mod diagnostic;

pub use span::{Span, Spanned};
pub use diagnostic::{Diagnostic, Severity, SourceMap};

/// Dice filter type — shared between lexer (token representation) and AST.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiceFilter {
    KeepHighest(u32),
    KeepLowest(u32),
    DropHighest(u32),
    DropLowest(u32),
}
