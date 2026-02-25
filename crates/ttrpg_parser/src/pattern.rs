use crate::parser::Parser;
use ttrpg_ast::ast::*;
use ttrpg_ast::Spanned;
use ttrpg_lexer::TokenKind;

impl Parser {
    pub(crate) fn parse_pattern(&mut self) -> Result<Spanned<PatternKind>, ()> {
        let start = self.start_span();

        match self.peek().clone() {
            TokenKind::Underscore => {
                self.advance();
                Ok(Spanned::new(PatternKind::Wildcard, self.end_span(start)))
            }

            TokenKind::Int(n) => {
                self.advance();
                Ok(Spanned::new(PatternKind::IntLit(n), self.end_span(start)))
            }

            TokenKind::Minus => {
                self.advance();
                if let TokenKind::Int(n) = self.peek().clone() {
                    self.advance();
                    Ok(Spanned::new(PatternKind::IntLit(-n), self.end_span(start)))
                } else {
                    self.error(format!("expected integer after '-' in pattern, found {:?}", self.peek()));
                    Err(())
                }
            }

            TokenKind::String(s) => {
                let s = s.clone();
                self.advance();
                Ok(Spanned::new(PatternKind::StringLit(s), self.end_span(start)))
            }

            TokenKind::True => {
                self.advance();
                Ok(Spanned::new(PatternKind::BoolLit(true), self.end_span(start)))
            }

            TokenKind::False => {
                self.advance();
                Ok(Spanned::new(PatternKind::BoolLit(false), self.end_span(start)))
            }

            TokenKind::None => {
                self.advance();
                Ok(Spanned::new(PatternKind::NoneLit, self.end_span(start)))
            }

            TokenKind::Ident(name) => {
                let name = name.clone();
                self.advance();

                // some(pattern) — option destructuring
                if name == "some" && matches!(self.peek(), TokenKind::LParen) {
                    self.advance(); // consume '('
                    let inner = self.parse_pattern()?;
                    self.expect(&TokenKind::RParen)?;
                    return Ok(Spanned::new(
                        PatternKind::Some(Box::new(inner)),
                        self.end_span(start),
                    ));
                }

                // Bare `some` without parens — recover as some(_) with diagnostic
                if name == "some" {
                    self.error(
                        "bare `some` in pattern position — use `some(x)` to match or `_` for wildcard"
                    );
                    let wildcard = Spanned::new(PatternKind::Wildcard, self.end_span(start));
                    return Ok(Spanned::new(
                        PatternKind::Some(Box::new(wildcard)),
                        self.end_span(start),
                    ));
                }

                // Check for qualified: IDENT.IDENT or IDENT.IDENT(...)
                if matches!(self.peek(), TokenKind::Dot) {
                    self.advance();
                    let (variant, _) = self.expect_ident()?;
                    if matches!(self.peek(), TokenKind::LParen) {
                        // Qualified destructure: IDENT.IDENT(patterns)
                        self.advance();
                        let fields = self.parse_pattern_list()?;
                        self.expect(&TokenKind::RParen)?;
                        Ok(Spanned::new(
                            PatternKind::QualifiedDestructure {
                                ty: name,
                                variant,
                                fields,
                            },
                            self.end_span(start),
                        ))
                    } else {
                        // Qualified variant: IDENT.IDENT
                        Ok(Spanned::new(
                            PatternKind::QualifiedVariant {
                                ty: name,
                                variant,
                            },
                            self.end_span(start),
                        ))
                    }
                } else if matches!(self.peek(), TokenKind::LParen) {
                    // Bare destructure: IDENT(patterns)
                    self.advance();
                    let fields = self.parse_pattern_list()?;
                    self.expect(&TokenKind::RParen)?;
                    Ok(Spanned::new(
                        PatternKind::BareDestructure { name, fields },
                        self.end_span(start),
                    ))
                } else {
                    // Bare ident (binding or variant, resolved in semantic)
                    Ok(Spanned::new(PatternKind::Ident(name), self.end_span(start)))
                }
            }

            _ => {
                self.error(format!("expected pattern, found {:?}", self.peek()));
                Err(())
            }
        }
    }

    fn parse_pattern_list(&mut self) -> Result<Vec<Spanned<PatternKind>>, ()> {
        let mut patterns = Vec::new();
        if !matches!(self.peek(), TokenKind::RParen) {
            patterns.push(self.parse_pattern()?);
            while matches!(self.peek(), TokenKind::Comma) {
                self.advance();
                if matches!(self.peek(), TokenKind::RParen) {
                    break;
                }
                patterns.push(self.parse_pattern()?);
            }
        }
        Ok(patterns)
    }
}
