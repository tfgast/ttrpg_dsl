pub mod diagnostic;
pub mod lower;
pub mod parser;
mod decl;
mod expr;
mod pattern;
mod stmt;
mod types;

pub use diagnostic::{Diagnostic, Severity, SourceMap};
pub use lower::lower_moves;
use ttrpg_ast::ast::{ExprKind, Program};
use ttrpg_ast::Spanned;
use ttrpg_lexer::TokenKind;
use parser::Parser;

pub fn parse(source: &str) -> (Program, Vec<Diagnostic>) {
    Parser::new(source).parse()
}

/// Parse a standalone expression from source text.
///
/// Returns the parsed expression (if successful) and any diagnostics.
/// Emits a diagnostic if there are trailing tokens after the expression.
pub fn parse_expr(source: &str) -> (Option<Spanned<ExprKind>>, Vec<Diagnostic>) {
    let mut parser = Parser::new(source);
    let result = parser.parse_expr();
    match result {
        Ok(expr) => {
            if !matches!(parser.peek(), TokenKind::Eof) {
                parser.error(format!("unexpected trailing token: {:?}", parser.peek()));
            }
            let diags = parser.into_diagnostics();
            (Some(expr), diags)
        }
        Err(()) => {
            let diags = parser.into_diagnostics();
            (None, diags)
        }
    }
}
