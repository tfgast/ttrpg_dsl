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
use ttrpg_ast::ast::Program;
use parser::Parser;

pub fn parse(source: &str) -> (Program, Vec<Diagnostic>) {
    Parser::new(source).parse()
}
