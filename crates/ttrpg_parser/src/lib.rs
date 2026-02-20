pub mod diagnostic;
pub mod parser;
mod decl;
mod expr;
mod pattern;
mod stmt;
mod types;

pub use diagnostic::{Diagnostic, Severity, SourceMap};
use ttrpg_ast::ast::Program;
use parser::Parser;

pub fn parse(source: &str) -> (Program, Vec<Diagnostic>) {
    Parser::new(source).parse()
}
