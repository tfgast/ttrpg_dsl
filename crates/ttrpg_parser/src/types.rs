use crate::parser::Parser;
use ttrpg_ast::ast::*;
use ttrpg_ast::Spanned;
use ttrpg_lexer::TokenKind;

impl Parser {
    pub(crate) fn parse_type(&mut self) -> Result<Spanned<TypeExpr>, ()> {
        let start = self.start_span();

        match self.peek().clone() {
            TokenKind::Ident(name) => {
                let ty = match name.as_str() {
                    "int" => { self.advance(); TypeExpr::Int }
                    "bool" => { self.advance(); TypeExpr::Bool }
                    "string" => { self.advance(); TypeExpr::String }
                    "float" => { self.advance(); TypeExpr::Float }
                    "DiceExpr" => { self.advance(); TypeExpr::DiceExpr }
                    "RollResult" => { self.advance(); TypeExpr::RollResult }
                    "TurnBudget" => { self.advance(); TypeExpr::TurnBudget }
                    "Duration" => { self.advance(); TypeExpr::Duration }
                    "Position" => { self.advance(); TypeExpr::Position }
                    "Condition" => { self.advance(); TypeExpr::Condition }

                    "map" => {
                        self.advance();
                        self.expect(&TokenKind::Lt)?;
                        let key = self.parse_type()?;
                        self.expect(&TokenKind::Comma)?;
                        let val = self.parse_type()?;
                        self.expect(&TokenKind::Gt)?;
                        TypeExpr::Map(Box::new(key), Box::new(val))
                    }
                    "list" => {
                        self.advance();
                        self.expect(&TokenKind::Lt)?;
                        let inner = self.parse_type()?;
                        self.expect(&TokenKind::Gt)?;
                        TypeExpr::List(Box::new(inner))
                    }
                    "set" => {
                        self.advance();
                        self.expect(&TokenKind::Lt)?;
                        let inner = self.parse_type()?;
                        self.expect(&TokenKind::Gt)?;
                        TypeExpr::Set(Box::new(inner))
                    }
                    "option" => {
                        // Disambiguate: option<T> (type) vs option Name (decl)
                        // If followed by `<`, it's a type.
                        if matches!(self.peek_at(1), TokenKind::Lt) {
                            self.advance();
                            self.expect(&TokenKind::Lt)?;
                            let inner = self.parse_type()?;
                            self.expect(&TokenKind::Gt)?;
                            TypeExpr::OptionType(Box::new(inner))
                        } else {
                            self.advance();
                            TypeExpr::Named("option".into())
                        }
                    }
                    "resource" => {
                        self.advance();
                        self.expect(&TokenKind::LParen)?;
                        let lo = self.parse_expr()?;
                        self.expect(&TokenKind::DotDot)?;
                        let hi = self.parse_expr()?;
                        self.expect(&TokenKind::RParen)?;
                        TypeExpr::Resource(Box::new(lo), Box::new(hi))
                    }
                    _ => {
                        let name = name.clone();
                        self.advance();
                        TypeExpr::Named(name)
                    }
                };
                Ok(Spanned::new(ty, self.end_span(start)))
            }
            _ => {
                self.error(format!("expected type, found {:?}", self.peek()));
                Err(())
            }
        }
    }
}
