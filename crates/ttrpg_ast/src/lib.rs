pub mod span;
pub mod ast;
pub mod diagnostic;
pub mod module;
pub mod name;
pub mod visit;

pub use span::{Span, Spanned};
pub use diagnostic::{Diagnostic, MultiSourceMap, Severity, SourceMap};
pub use name::Name;
pub use visit::VisitSpansMut;

/// Dice filter type — shared between lexer (token representation) and AST.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DiceFilter {
    KeepHighest(u32),
    KeepLowest(u32),
    DropHighest(u32),
    DropLowest(u32),
}
