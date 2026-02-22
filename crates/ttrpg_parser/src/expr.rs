use crate::parser::Parser;
use ttrpg_ast::ast::*;
use ttrpg_ast::Spanned;
use ttrpg_lexer::TokenKind;

impl Parser {
    #[allow(clippy::result_unit_err)]
    pub fn parse_expr(&mut self) -> Result<Spanned<ExprKind>, ()> {
        self.parse_or_expr()
    }

    // ── Precedence levels ────────────────────────────────────────

    fn parse_or_expr(&mut self) -> Result<Spanned<ExprKind>, ()> {
        let start = self.start_span();
        let mut lhs = self.parse_and_expr()?;
        while matches!(self.peek(), TokenKind::PipePipe) {
            self.advance();
            let rhs = self.parse_and_expr()?;
            let span = self.end_span(start);
            lhs = Spanned::new(
                ExprKind::BinOp {
                    op: BinOp::Or,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                span,
            );
        }
        Ok(lhs)
    }

    fn parse_and_expr(&mut self) -> Result<Spanned<ExprKind>, ()> {
        let start = self.start_span();
        let mut lhs = self.parse_cmp_expr()?;
        while matches!(self.peek(), TokenKind::AmpAmp) {
            self.advance();
            let rhs = self.parse_cmp_expr()?;
            let span = self.end_span(start);
            lhs = Spanned::new(
                ExprKind::BinOp {
                    op: BinOp::And,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                span,
            );
        }
        Ok(lhs)
    }

    fn parse_cmp_expr(&mut self) -> Result<Spanned<ExprKind>, ()> {
        let start = self.start_span();
        let lhs = self.parse_in_expr()?;
        let op = match self.peek() {
            TokenKind::EqEq => Some(BinOp::Eq),
            TokenKind::BangEq => Some(BinOp::NotEq),
            TokenKind::GtEq => Some(BinOp::GtEq),
            TokenKind::LtEq => Some(BinOp::LtEq),
            TokenKind::Gt => Some(BinOp::Gt),
            TokenKind::Lt => Some(BinOp::Lt),
            _ => None,
        };
        if let Some(op) = op {
            self.advance();
            let rhs = self.parse_in_expr()?;
            Ok(Spanned::new(
                ExprKind::BinOp {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                self.end_span(start),
            ))
        } else {
            Ok(lhs)
        }
    }

    fn parse_in_expr(&mut self) -> Result<Spanned<ExprKind>, ()> {
        let start = self.start_span();
        let lhs = self.parse_add_expr()?;
        if matches!(self.peek(), TokenKind::In) {
            self.advance();
            let rhs = self.parse_add_expr()?;
            Ok(Spanned::new(
                ExprKind::BinOp {
                    op: BinOp::In,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                self.end_span(start),
            ))
        } else {
            Ok(lhs)
        }
    }

    fn parse_add_expr(&mut self) -> Result<Spanned<ExprKind>, ()> {
        let start = self.start_span();
        let mut lhs = self.parse_mul_expr()?;
        loop {
            let op = match self.peek() {
                TokenKind::Plus => BinOp::Add,
                TokenKind::Minus => BinOp::Sub,
                _ => break,
            };
            self.advance();
            let rhs = self.parse_mul_expr()?;
            let span = self.end_span(start);
            lhs = Spanned::new(
                ExprKind::BinOp {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                span,
            );
        }
        Ok(lhs)
    }

    fn parse_mul_expr(&mut self) -> Result<Spanned<ExprKind>, ()> {
        let start = self.start_span();
        let mut lhs = self.parse_unary_expr()?;
        loop {
            let op = match self.peek() {
                TokenKind::Star => BinOp::Mul,
                TokenKind::Slash => BinOp::Div,
                _ => break,
            };
            self.advance();
            let rhs = self.parse_unary_expr()?;
            let span = self.end_span(start);
            lhs = Spanned::new(
                ExprKind::BinOp {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                span,
            );
        }
        Ok(lhs)
    }

    fn parse_unary_expr(&mut self) -> Result<Spanned<ExprKind>, ()> {
        let start = self.start_span();
        match self.peek() {
            TokenKind::Bang => {
                self.advance();
                let operand = self.parse_unary_expr()?;
                Ok(Spanned::new(
                    ExprKind::UnaryOp {
                        op: UnaryOp::Not,
                        operand: Box::new(operand),
                    },
                    self.end_span(start),
                ))
            }
            TokenKind::Minus => {
                // Unary minus: check it's not an assignment like -=
                // Actually MinusEq is its own token, so Minus is always just -
                self.advance();
                let operand = self.parse_unary_expr()?;
                Ok(Spanned::new(
                    ExprKind::UnaryOp {
                        op: UnaryOp::Neg,
                        operand: Box::new(operand),
                    },
                    self.end_span(start),
                ))
            }
            _ => self.parse_postfix_expr(),
        }
    }

    fn parse_postfix_expr(&mut self) -> Result<Spanned<ExprKind>, ()> {
        let start = self.start_span();
        let mut expr = self.parse_primary_expr()?;

        loop {
            match self.peek() {
                TokenKind::Dot => {
                    self.advance();
                    let (field, _) = self.expect_ident()?;
                    expr = Spanned::new(
                        ExprKind::FieldAccess {
                            object: Box::new(expr),
                            field,
                        },
                        self.end_span(start),
                    );
                }
                TokenKind::LBracket => {
                    self.advance();
                    let index = self.parse_expr()?;
                    self.expect(&TokenKind::RBracket)?;
                    expr = Spanned::new(
                        ExprKind::Index {
                            object: Box::new(expr),
                            index: Box::new(index),
                        },
                        self.end_span(start),
                    );
                }
                TokenKind::LParen => {
                    self.advance();
                    let args = if matches!(self.peek(), TokenKind::RParen) {
                        vec![]
                    } else {
                        self.parse_arg_list()?
                    };
                    self.expect(&TokenKind::RParen)?;
                    expr = Spanned::new(
                        ExprKind::Call {
                            callee: Box::new(expr),
                            args,
                        },
                        self.end_span(start),
                    );
                }
                _ => break,
            }
        }

        Ok(expr)
    }

    pub(crate) fn parse_primary_expr(&mut self) -> Result<Spanned<ExprKind>, ()> {
        let start = self.start_span();

        match self.peek().clone() {
            TokenKind::Int(_) | TokenKind::Dice { .. } => {
                // Need to handle dice and int
                let tok = self.advance();
                match tok.kind {
                    TokenKind::Int(n) => Ok(Spanned::new(ExprKind::IntLit(n), tok.span)),
                    TokenKind::Dice { count, sides, filter } => {
                        Ok(Spanned::new(
                            ExprKind::DiceLit { count, sides, filter },
                            tok.span,
                        ))
                    }
                    _ => unreachable!(),
                }
            }

            TokenKind::String(s) => {
                let s = s.clone();
                let tok = self.advance();
                Ok(Spanned::new(ExprKind::StringLit(s), tok.span))
            }

            TokenKind::True => {
                let tok = self.advance();
                Ok(Spanned::new(ExprKind::BoolLit(true), tok.span))
            }
            TokenKind::False => {
                let tok = self.advance();
                Ok(Spanned::new(ExprKind::BoolLit(false), tok.span))
            }
            TokenKind::None => {
                let tok = self.advance();
                Ok(Spanned::new(ExprKind::NoneLit, tok.span))
            }

            TokenKind::Ident(_) => {
                // Could be: simple ident, struct lit, or just ident
                // Struct lit disambiguation: IDENT { ... } where we peek
                // to see if it looks like struct lit (field: expr)
                if self.is_struct_lit_start() {
                    self.parse_struct_lit()
                } else {
                    let (name, span) = self.expect_ident()?;
                    Ok(Spanned::new(ExprKind::Ident(name), span))
                }
            }

            TokenKind::LBracket => {
                // List literal: [ expr, ... ]
                self.advance();
                let mut items = Vec::new();
                if !matches!(self.peek(), TokenKind::RBracket) {
                    items.push(self.parse_expr()?);
                    while matches!(self.peek(), TokenKind::Comma) {
                        self.advance();
                        if matches!(self.peek(), TokenKind::RBracket) {
                            break; // trailing comma
                        }
                        items.push(self.parse_expr()?);
                    }
                }
                self.expect(&TokenKind::RBracket)?;
                Ok(Spanned::new(ExprKind::ListLit(items), self.end_span(start)))
            }

            TokenKind::LParen => {
                // Parenthesized expr
                self.advance();
                let inner = self.parse_expr()?;
                self.expect(&TokenKind::RParen)?;
                Ok(Spanned::new(
                    ExprKind::Paren(Box::new(inner)),
                    self.end_span(start),
                ))
            }

            TokenKind::If => self.parse_if_expr(),

            TokenKind::Match => self.parse_match_expr(),

            TokenKind::For => self.parse_for_expr(),

            _ => {
                self.error(format!("expected expression, found {:?}", self.peek()));
                Err(())
            }
        }
    }

    /// Check if current IDENT + `{` looks like a struct literal.
    /// Heuristic: IDENT { IDENT : ... } or IDENT { }
    fn is_struct_lit_start(&self) -> bool {
        if !matches!(self.peek(), TokenKind::Ident(_)) {
            return false;
        }
        if !matches!(self.peek_at(1), TokenKind::LBrace) {
            return false;
        }
        // IDENT { } → struct lit
        if matches!(self.peek_at(2), TokenKind::RBrace) {
            return true;
        }
        // IDENT { IDENT : → struct lit
        if matches!(self.peek_at(2), TokenKind::Ident(_))
            && matches!(self.peek_at(3), TokenKind::Colon)
        {
            return true;
        }
        false
    }

    fn parse_struct_lit(&mut self) -> Result<Spanned<ExprKind>, ()> {
        let start = self.start_span();
        let (name, _) = self.expect_ident()?;
        self.expect(&TokenKind::LBrace)?;
        self.skip_newlines();

        let mut fields = Vec::new();
        if !matches!(self.peek(), TokenKind::RBrace) {
            fields.push(self.parse_struct_field_init()?);
            while matches!(self.peek(), TokenKind::Comma) {
                self.advance();
                self.skip_newlines();
                if matches!(self.peek(), TokenKind::RBrace) {
                    break; // trailing comma
                }
                fields.push(self.parse_struct_field_init()?);
            }
        }
        self.skip_newlines();
        self.expect(&TokenKind::RBrace)?;
        Ok(Spanned::new(
            ExprKind::StructLit { name, fields },
            self.end_span(start),
        ))
    }

    fn parse_struct_field_init(&mut self) -> Result<StructFieldInit, ()> {
        let start = self.start_span();
        let (name, _) = self.expect_ident()?;
        self.expect(&TokenKind::Colon)?;
        let value = self.parse_expr()?;
        self.skip_newlines();
        Ok(StructFieldInit {
            name,
            value,
            span: self.end_span(start),
        })
    }

    pub(crate) fn parse_if_expr(&mut self) -> Result<Spanned<ExprKind>, ()> {
        let start = self.start_span();
        self.expect(&TokenKind::If)?;

        // if let pattern = expr { ... } else { ... }
        if matches!(self.peek(), TokenKind::Let) {
            return self.parse_if_let_expr(start);
        }

        let condition = self.parse_expr()?;
        let then_block = self.parse_block()?;
        let else_branch = self.parse_else_branch()?;
        Ok(Spanned::new(
            ExprKind::If {
                condition: Box::new(condition),
                then_block,
                else_branch,
            },
            self.end_span(start),
        ))
    }

    fn parse_if_let_expr(&mut self, start: usize) -> Result<Spanned<ExprKind>, ()> {
        self.expect(&TokenKind::Let)?;
        let pattern = self.parse_pattern()?;
        self.expect(&TokenKind::Eq)?;
        let scrutinee = self.parse_expr()?;
        let then_block = self.parse_block()?;
        let else_branch = self.parse_else_branch()?;
        Ok(Spanned::new(
            ExprKind::IfLet {
                pattern: Box::new(pattern),
                scrutinee: Box::new(scrutinee),
                then_block,
                else_branch,
            },
            self.end_span(start),
        ))
    }

    fn parse_else_branch(&mut self) -> Result<Option<ElseBranch>, ()> {
        if matches!(self.peek(), TokenKind::Else) {
            self.advance();
            if matches!(self.peek(), TokenKind::If) {
                let if_expr = self.parse_if_expr()?;
                Ok(Some(ElseBranch::If(Box::new(if_expr))))
            } else {
                let block = self.parse_block()?;
                Ok(Some(ElseBranch::Block(block)))
            }
        } else {
            Ok(None)
        }
    }

    pub(crate) fn parse_match_expr(&mut self) -> Result<Spanned<ExprKind>, ()> {
        let start = self.start_span();
        self.expect(&TokenKind::Match)?;

        // Distinguish: `match expr {` vs `match {`
        if matches!(self.peek(), TokenKind::LBrace) {
            // Guard match
            self.parse_guard_match(start)
        } else {
            // Pattern match
            self.parse_pattern_match(start)
        }
    }

    fn parse_pattern_match(&mut self, start: usize) -> Result<Spanned<ExprKind>, ()> {
        let scrutinee = self.parse_expr()?;
        self.expect(&TokenKind::LBrace)?;

        let mut arms = Vec::new();
        loop {
            self.skip_newlines();
            if matches!(self.peek(), TokenKind::RBrace | TokenKind::Eof) {
                break;
            }
            arms.push(self.parse_pattern_arm()?);
            let saw_comma = matches!(self.peek(), TokenKind::Comma);
            if saw_comma {
                self.advance();
            }
            let saw_newline = self.skip_newlines();
            if !saw_comma && !saw_newline && !matches!(self.peek(), TokenKind::RBrace | TokenKind::Eof) {
                self.error("expected ',' or newline between match arms");
                return Err(());
            }
        }

        if arms.is_empty() {
            self.error("match expression requires at least one arm");
            return Err(());
        }

        self.expect(&TokenKind::RBrace)?;

        Ok(Spanned::new(
            ExprKind::PatternMatch {
                scrutinee: Box::new(scrutinee),
                arms,
            },
            self.end_span(start),
        ))
    }

    fn parse_guard_match(&mut self, start: usize) -> Result<Spanned<ExprKind>, ()> {
        self.expect(&TokenKind::LBrace)?;

        let mut arms = Vec::new();
        loop {
            self.skip_newlines();
            if matches!(self.peek(), TokenKind::RBrace | TokenKind::Eof) {
                break;
            }
            arms.push(self.parse_guard_arm()?);
            let saw_comma = matches!(self.peek(), TokenKind::Comma);
            if saw_comma {
                self.advance();
            }
            let saw_newline = self.skip_newlines();
            if !saw_comma && !saw_newline && !matches!(self.peek(), TokenKind::RBrace | TokenKind::Eof) {
                self.error("expected ',' or newline between match arms");
                return Err(());
            }
        }

        if arms.is_empty() {
            self.error("match expression requires at least one arm");
            return Err(());
        }

        self.expect(&TokenKind::RBrace)?;

        Ok(Spanned::new(
            ExprKind::GuardMatch { arms },
            self.end_span(start),
        ))
    }

    fn parse_pattern_arm(&mut self) -> Result<PatternArm, ()> {
        let start = self.start_span();
        let pattern = self.parse_pattern()?;
        self.expect(&TokenKind::FatArrow)?;
        let body = self.parse_arm_body()?;
        Ok(PatternArm {
            pattern,
            body,
            span: self.end_span(start),
        })
    }

    fn parse_guard_arm(&mut self) -> Result<GuardArm, ()> {
        let start = self.start_span();
        let guard = if matches!(self.peek(), TokenKind::Underscore) {
            self.advance();
            GuardKind::Wildcard
        } else {
            let expr = self.parse_expr()?;
            GuardKind::Expr(expr)
        };
        self.expect(&TokenKind::FatArrow)?;
        let body = self.parse_arm_body()?;
        Ok(GuardArm {
            guard,
            body,
            span: self.end_span(start),
        })
    }

    fn parse_for_expr(&mut self) -> Result<Spanned<ExprKind>, ()> {
        let start = self.start_span();
        self.expect(&TokenKind::For)?;
        let pattern = self.parse_pattern()?;
        self.expect(&TokenKind::In)?;

        // Parse the first expression. Since `..` is not an expression
        // operator, parse_expr() naturally stops before it.
        let first = self.parse_expr()?;

        let iterable = if matches!(self.peek(), TokenKind::DotDot) {
            self.advance();
            let end = self.parse_expr()?;
            ForIterable::Range {
                start: Box::new(first),
                end: Box::new(end),
            }
        } else {
            ForIterable::Collection(Box::new(first))
        };

        let body = self.parse_block()?;

        Ok(Spanned::new(
            ExprKind::For {
                pattern: Box::new(pattern),
                iterable,
                body,
            },
            self.end_span(start),
        ))
    }

    fn parse_arm_body(&mut self) -> Result<ArmBody, ()> {
        if matches!(self.peek(), TokenKind::LBrace) {
            Ok(ArmBody::Block(self.parse_block()?))
        } else {
            Ok(ArmBody::Expr(self.parse_expr()?))
        }
    }

    fn parse_arg_list(&mut self) -> Result<Vec<Arg>, ()> {
        let mut args = Vec::new();
        args.push(self.parse_arg()?);
        while matches!(self.peek(), TokenKind::Comma) {
            self.advance();
            if matches!(self.peek(), TokenKind::RParen) {
                break;
            }
            args.push(self.parse_arg()?);
        }
        Ok(args)
    }

    fn parse_arg(&mut self) -> Result<Arg, ()> {
        let start = self.start_span();

        // Named arg: IDENT : expr
        if matches!(self.peek(), TokenKind::Ident(_)) && matches!(self.peek_at(1), TokenKind::Colon)
        {
            let (name, _) = self.expect_ident()?;
            self.advance(); // colon
            let value = self.parse_expr()?;
            return Ok(Arg {
                name: Some(name),
                value,
                span: self.end_span(start),
            });
        }

        let value = self.parse_expr()?;
        Ok(Arg {
            name: None,
            value,
            span: self.end_span(start),
        })
    }
}
