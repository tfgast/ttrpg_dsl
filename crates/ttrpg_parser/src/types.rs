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
                    "int" => {
                        self.advance();
                        TypeExpr::Int
                    }
                    "bool" => {
                        self.advance();
                        TypeExpr::Bool
                    }
                    "string" => {
                        self.advance();
                        TypeExpr::String
                    }
                    "float" => {
                        self.advance();
                        TypeExpr::Float
                    }
                    "DiceExpr" => {
                        self.advance();
                        TypeExpr::DiceExpr
                    }
                    "RollResult" => {
                        self.advance();
                        TypeExpr::RollResult
                    }
                    "entity" => {
                        self.advance();
                        TypeExpr::Named("entity".into())
                    }
                    "TurnBudget" | "Duration" | "Position" | "Condition"
                        if !matches!(self.peek_at(1), TokenKind::Dot) =>
                    {
                        let ty = match name.as_str() {
                            "TurnBudget" => TypeExpr::TurnBudget,
                            "Duration" => TypeExpr::Duration,
                            "Position" => TypeExpr::Position,
                            "Condition" => TypeExpr::Condition,
                            _ => unreachable!(),
                        };
                        self.advance();
                        ty
                    }

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
                        if matches!(self.peek(), TokenKind::DotDot) {
                            self.advance();
                            self.error("resource bounds are inclusive; use `..=` instead of `..`");
                        } else {
                            self.expect(&TokenKind::DotDotEq)?;
                        }
                        let hi = self.parse_expr()?;
                        self.expect(&TokenKind::RParen)?;
                        TypeExpr::Resource(Box::new(lo), Box::new(hi))
                    }
                    _ => {
                        let name = ttrpg_ast::Name::from(name.clone());
                        self.advance();
                        // Check for qualified type: IDENT.IDENT
                        if matches!(self.peek(), TokenKind::Dot) {
                            if let TokenKind::Ident(_) = self.peek_at(1) {
                                self.advance(); // consume dot
                                let (qualified_name, _) = self.expect_ident()?;
                                TypeExpr::Qualified {
                                    qualifier: name,
                                    name: qualified_name,
                                }
                            } else {
                                TypeExpr::Named(name)
                            }
                        } else {
                            TypeExpr::Named(name)
                        }
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
