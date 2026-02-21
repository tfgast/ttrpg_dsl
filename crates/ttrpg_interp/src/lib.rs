pub mod value;
pub mod effect;
pub mod state;

use ttrpg_ast::Span;

/// A runtime error produced by the interpreter.
///
/// Since the interpreter trusts that programs have passed type-checking,
/// runtime errors indicate either host state sync issues (e.g., missing
/// entity fields), protocol errors (invalid effect responses), arithmetic
/// errors (division by zero, overflow), or internal bugs.
#[derive(Debug, Clone)]
pub struct RuntimeError {
    pub message: String,
    pub span: Option<Span>,
}

impl RuntimeError {
    pub fn new(message: impl Into<String>) -> Self {
        RuntimeError {
            message: message.into(),
            span: None,
        }
    }

    pub fn with_span(message: impl Into<String>, span: Span) -> Self {
        RuntimeError {
            message: message.into(),
            span: Some(span),
        }
    }
}

impl std::fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)?;
        if let Some(span) = self.span {
            write!(f, " (at {}..{})", span.start, span.end)?;
        }
        Ok(())
    }
}

impl std::error::Error for RuntimeError {}
