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

        // grant entity.Group { field: val, ... }
        if self.at_ident("grant") {
            return self.parse_grant_stmt();
        }

        // revoke entity.Group
        if self.at_ident("revoke") {
            return self.parse_revoke_stmt();
        }

        // emit EventName(args)
        if self.at_ident("emit") {
            return self.parse_emit_stmt();
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

    /// Parse `grant entity.Group { field: val, ... }`
    fn parse_grant_stmt(&mut self) -> Result<StmtKind, ()> {
        self.expect_soft_keyword("grant")?;
        let entity_expr = self.parse_expr()?;

        // Decompose trailing FieldAccess into entity + group_name
        let (entity, group_name) = match entity_expr.node {
            ExprKind::FieldAccess { object, field } => (*object, field),
            _ => {
                self.error("expected 'entity.GroupName' after 'grant'");
                return Err(());
            }
        };

        // Parse the field initializer block { field: val, ... }
        self.expect(&TokenKind::LBrace)?;
        self.skip_newlines();
        let mut fields = Vec::new();
        if !matches!(self.peek(), TokenKind::RBrace) {
            fields.push(self.parse_struct_field_init()?);
            while matches!(self.peek(), TokenKind::Comma) {
                self.advance();
                self.skip_newlines();
                if matches!(self.peek(), TokenKind::RBrace) {
                    break;
                }
                fields.push(self.parse_struct_field_init()?);
            }
        }
        self.skip_newlines();
        self.expect(&TokenKind::RBrace)?;
        self.expect_term()?;

        Ok(StmtKind::Grant {
            entity: Box::new(entity),
            group_name,
            fields,
        })
    }

    /// Parse `revoke entity.Group`
    fn parse_revoke_stmt(&mut self) -> Result<StmtKind, ()> {
        self.expect_soft_keyword("revoke")?;
        let entity_expr = self.parse_expr()?;

        // Decompose trailing FieldAccess into entity + group_name
        let (entity, group_name) = match entity_expr.node {
            ExprKind::FieldAccess { object, field } => (*object, field),
            _ => {
                self.error("expected 'entity.GroupName' after 'revoke'");
                return Err(());
            }
        };

        self.expect_term()?;
        Ok(StmtKind::Revoke {
            entity: Box::new(entity),
            group_name,
        })
    }

    /// Parse `emit EventName(param: expr, ...)`
    fn parse_emit_stmt(&mut self) -> Result<StmtKind, ()> {
        let start = self.start_span();
        self.expect_soft_keyword("emit")?;
        let (event_name, _) = self.expect_ident()?;

        self.expect(&TokenKind::LParen)?;
        let args = if matches!(self.peek(), TokenKind::RParen) {
            Vec::new()
        } else {
            self.parse_arg_list()?
        };
        self.expect(&TokenKind::RParen)?;
        self.expect_term()?;

        let span = self.end_span(start);
        Ok(StmtKind::Emit {
            event_name,
            args,
            span,
        })
    }

    fn expr_to_lvalue(&mut self, expr: Spanned<ExprKind>) -> Result<LValue, ()> {
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
                self.error("invalid assignment target");
                Err(())
            }
        }
    }
}
