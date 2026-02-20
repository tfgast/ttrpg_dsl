use crate::parser::Parser;
use ttrpg_ast::ast::*;
use ttrpg_ast::Spanned;
use ttrpg_lexer::TokenKind;

impl Parser {
    pub(crate) fn parse_block(&mut self) -> Result<Block, ()> {
        let start = self.start_span();
        self.expect(&TokenKind::LBrace)?;
        self.skip_newlines();

        let mut stmts = Vec::new();
        while !matches!(self.peek(), TokenKind::RBrace | TokenKind::Eof) {
            let stmt_start = self.start_span();
            match self.parse_stmt() {
                Ok(s) => stmts.push(Spanned::new(s, self.end_span(stmt_start))),
                Err(()) => {
                    // Recovery: skip to next newline or }
                    while !matches!(
                        self.peek(),
                        TokenKind::Newline | TokenKind::RBrace | TokenKind::Eof
                    ) {
                        self.advance();
                    }
                    if matches!(self.peek(), TokenKind::Newline) {
                        self.advance();
                    }
                }
            }
            self.skip_newlines();
        }

        self.expect(&TokenKind::RBrace)?;
        Ok(Spanned::new(stmts, self.end_span(start)))
    }

    pub(crate) fn parse_stmt(&mut self) -> Result<StmtKind, ()> {
        // let stmt
        if matches!(self.peek(), TokenKind::Let) {
            return self.parse_let_stmt();
        }

        // Parse as expression first, then check if it's an assignment
        let expr = self.parse_expr()?;

        // Check for assignment: if followed by = += -=
        match self.peek() {
            TokenKind::Eq | TokenKind::PlusEq | TokenKind::MinusEq => {
                let op = match self.peek() {
                    TokenKind::Eq => AssignOp::Eq,
                    TokenKind::PlusEq => AssignOp::PlusEq,
                    TokenKind::MinusEq => AssignOp::MinusEq,
                    _ => unreachable!(),
                };
                self.advance();
                let value = self.parse_expr()?;
                let target = self.expr_to_lvalue(expr)?;
                self.expect_term()?;
                Ok(StmtKind::Assign { target, op, value })
            }
            _ => {
                // Expression statement
                self.expect_term()?;
                Ok(StmtKind::Expr(expr))
            }
        }
    }

    fn parse_let_stmt(&mut self) -> Result<StmtKind, ()> {
        self.expect(&TokenKind::Let)?;
        let (name, _) = self.expect_ident()?;

        let ty = if matches!(self.peek(), TokenKind::Colon) {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };

        self.expect(&TokenKind::Eq)?;
        let value = self.parse_expr()?;
        self.expect_term()?;

        Ok(StmtKind::Let { name, ty, value })
    }

    fn expr_to_lvalue(&self, expr: Spanned<ExprKind>) -> Result<LValue, ()> {
        match expr.node {
            ExprKind::Ident(name) => Ok(LValue {
                root: name,
                segments: vec![],
                span: expr.span,
            }),
            ExprKind::FieldAccess { object, field } => {
                let mut lval = self.expr_to_lvalue(*object)?;
                lval.segments.push(LValueSegment::Field(field));
                lval.span = expr.span;
                Ok(lval)
            }
            ExprKind::Index { object, index } => {
                let mut lval = self.expr_to_lvalue(*object)?;
                lval.segments.push(LValueSegment::Index(*index));
                lval.span = expr.span;
                Ok(lval)
            }
            _ => {
                // Can't convert arbitrary expression to lvalue
                Err(())
            }
        }
    }
}
