use crate::diagnostic::Diagnostic;
use ttrpg_ast::ast::*;
use ttrpg_ast::name::Name;
use ttrpg_ast::{FileId, Span, Spanned};
use ttrpg_lexer::{Lexer, Token, TokenKind};

pub struct Parser {
    tokens: Vec<Token>,
    pos: usize,
    file: FileId,
    diagnostics: Vec<Diagnostic>,
    /// When true, `is_struct_lit_start()` returns false. Set while parsing
    /// if-conditions, for-sources, and match-scrutinees to prevent `IDENT {}`
    /// from being misinterpreted as a struct literal when `{}` is really the
    /// body block of the enclosing construct.
    pub(crate) restrict_struct_lit: bool,
}

impl Parser {
    pub fn new(source: &str, file: FileId) -> Self {
        let tokens: Vec<Token> = Lexer::new(source, file).collect();
        Self {
            tokens,
            pos: 0,
            file,
            diagnostics: Vec::new(),
            restrict_struct_lit: false,
        }
    }

    // ── Token helpers ────────────────────────────────────────────

    pub fn peek(&self) -> &TokenKind {
        self.tokens
            .get(self.pos)
            .map(|t| &t.kind)
            .unwrap_or(&TokenKind::Eof)
    }

    pub(crate) fn peek_at(&self, offset: usize) -> &TokenKind {
        self.tokens
            .get(self.pos + offset)
            .map(|t| &t.kind)
            .unwrap_or(&TokenKind::Eof)
    }

    pub(crate) fn peek_span(&self) -> Span {
        self.tokens
            .get(self.pos)
            .map(|t| t.span)
            .unwrap_or_else(|| {
                // Use end of last token or 0
                self.tokens
                    .last()
                    .map(|t| Span::new(self.file, t.span.end, t.span.end))
                    .unwrap_or(Span::dummy())
            })
    }

    pub(crate) fn at(&self, kind: &TokenKind) -> bool {
        std::mem::discriminant(self.peek()) == std::mem::discriminant(kind)
    }

    pub(crate) fn at_ident(&self, name: &str) -> bool {
        matches!(self.peek(), TokenKind::Ident(s) if s == name)
    }

    pub(crate) fn advance(&mut self) -> Token {
        let tok = self
            .tokens
            .get(self.pos)
            .cloned()
            .unwrap_or_else(|| Token::new(TokenKind::Eof, Span::dummy()));
        if self.pos < self.tokens.len() {
            self.pos += 1;
        }
        tok
    }

    pub(crate) fn expect(&mut self, expected: &TokenKind) -> Result<Token, ()> {
        if self.at(expected) {
            Ok(self.advance())
        } else {
            self.error(format!("expected {:?}, found {:?}", expected, self.peek()));
            Err(())
        }
    }

    pub(crate) fn expect_ident(&mut self) -> Result<(Name, Span), ()> {
        match self.peek().clone() {
            TokenKind::Ident(name) => {
                let tok = self.advance();
                Ok((Name::from(name), tok.span))
            }
            _ => {
                self.error(format!("expected identifier, found {:?}", self.peek()));
                Err(())
            }
        }
    }

    pub(crate) fn expect_soft_keyword(&mut self, kw: &str) -> Result<Span, ()> {
        if self.at_ident(kw) {
            Ok(self.advance().span)
        } else {
            self.error(format!("expected '{}', found {:?}", kw, self.peek()));
            Err(())
        }
    }

    pub(crate) fn expect_string(&mut self) -> Result<(String, Span), ()> {
        match self.peek().clone() {
            TokenKind::String(s) => {
                let tok = self.advance();
                Ok((s, tok.span))
            }
            _ => {
                self.error(format!("expected string literal, found {:?}", self.peek()));
                Err(())
            }
        }
    }

    /// Consume a statement terminator: NL, lookahead `}`, or EOF.
    pub(crate) fn expect_term(&mut self) -> Result<(), ()> {
        match self.peek() {
            TokenKind::Newline => {
                self.advance();
                Ok(())
            }
            TokenKind::RBrace | TokenKind::Eof => Ok(()),
            _ => {
                self.error(format!("expected newline or '}}', found {:?}", self.peek()));
                Err(())
            }
        }
    }

    pub(crate) fn skip_newlines(&mut self) -> bool {
        let mut found = false;
        while matches!(self.peek(), TokenKind::Newline) {
            self.advance();
            found = true;
        }
        found
    }

    /// Remove all `Newline` tokens between `self.pos` and the matching `}`.
    /// Call immediately after consuming `{` in expression-brace contexts
    /// (e.g. `requires { expr }`, `cost { tokens }`) so that multiline
    /// content is parsed without newline-termination issues.
    pub(crate) fn suppress_newlines_in_brace_block(&mut self) {
        let mut depth = 1usize;
        let mut end = self.pos;
        while end < self.tokens.len() {
            match self.tokens[end].kind {
                TokenKind::LBrace => depth += 1,
                TokenKind::RBrace => {
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                }
                _ => {}
            }
            end += 1;
        }
        // If no matching `}` was found, bail out without mutating
        if depth != 0 {
            return;
        }
        // Remove Newline tokens in [self.pos..end)
        let mut i = self.pos;
        while i < end {
            if self.tokens[i].kind == TokenKind::Newline {
                self.tokens.remove(i);
                end -= 1;
            } else {
                i += 1;
            }
        }
    }

    /// Save the current token position for backtracking.
    pub(crate) fn save_pos(&self) -> usize {
        self.pos
    }

    /// Restore a previously saved token position.
    pub(crate) fn restore_pos(&mut self, pos: usize) {
        self.pos = pos;
    }

    pub(crate) fn start_span(&self) -> usize {
        self.peek_span().start
    }

    pub(crate) fn end_span(&self, start: usize) -> Span {
        let end = if self.pos > 0 {
            self.tokens[self.pos - 1].span.end
        } else {
            start
        };
        Span::new(self.file, start, end)
    }

    pub fn error(&mut self, message: impl Into<String>) {
        let span = self.peek_span();
        self.diagnostics.push(Diagnostic::error(message, span));
    }

    // ── Program parsing ──────────────────────────────────────────

    pub fn parse(mut self) -> (Program, Vec<Diagnostic>) {
        let program = self.parse_program();
        (program, self.diagnostics)
    }

    /// Consume the parser and return its collected diagnostics.
    pub fn into_diagnostics(self) -> Vec<Diagnostic> {
        self.diagnostics
    }

    fn parse_program(&mut self) -> Program {
        let mut items = Vec::new();
        self.skip_newlines();
        while !matches!(self.peek(), TokenKind::Eof) {
            let start = self.start_span();
            if self.at_ident("use") {
                match self.parse_use_decl() {
                    Ok(u) => items.push(Spanned::new(TopLevel::Use(u), self.end_span(start))),
                    Err(()) => self.recover_to_top_level(),
                }
            } else if self.at_ident("system") {
                match self.parse_system_block() {
                    Ok(s) => items.push(Spanned::new(TopLevel::System(s), self.end_span(start))),
                    Err(()) => self.recover_to_top_level(),
                }
            } else {
                self.error(format!(
                    "expected 'use' or 'system', found {:?}",
                    self.peek()
                ));
                self.advance();
            }
            self.skip_newlines();
        }
        Program {
            items,
            ..Default::default()
        }
    }

    fn parse_use_decl(&mut self) -> Result<UseDecl, ()> {
        let start = self.start_span();
        self.expect_soft_keyword("use")?;
        let (path, _) = self.expect_string()?;
        let alias = if self.at_ident("as") {
            self.advance();
            let (name, _) = self.expect_ident()?;
            Some(name)
        } else {
            None
        };
        self.expect_term()?;
        Ok(UseDecl {
            path,
            alias,
            span: self.end_span(start),
        })
    }

    fn parse_system_block(&mut self) -> Result<SystemBlock, ()> {
        self.expect_soft_keyword("system")?;
        let (name_str, _) = self.expect_string()?;
        let name: Name = name_str.into();
        self.expect(&TokenKind::LBrace)?;
        self.skip_newlines();

        let mut decls = Vec::new();
        while !matches!(self.peek(), TokenKind::RBrace | TokenKind::Eof) {
            // If we see a top-level keyword, this system block is missing its closing brace
            if self.at_ident("system") || self.at_ident("use") {
                break;
            }
            let start = self.start_span();
            match self.parse_decl() {
                Ok(d) => decls.push(Spanned::new(d, self.end_span(start))),
                Err(()) => self.recover_to_decl(),
            }
            self.skip_newlines();
        }

        self.expect(&TokenKind::RBrace)?;
        Ok(SystemBlock { name, decls })
    }

    fn recover_to_top_level(&mut self) {
        while !matches!(self.peek(), TokenKind::Eof) {
            if self.at_ident("use") || self.at_ident("system") {
                return;
            }
            self.advance();
        }
    }

    fn recover_to_decl(&mut self) {
        // Skip tokens until we find a declaration keyword at brace depth 0.
        // We track brace depth so we don't stop at a `}` inside a nested block.
        let mut depth: usize = 0;
        loop {
            match self.peek() {
                TokenKind::Eof => return,
                TokenKind::LBrace => {
                    depth += 1;
                    self.advance();
                }
                TokenKind::RBrace if depth > 0 => {
                    depth -= 1;
                    self.advance();
                }
                TokenKind::RBrace => return, // system block's closing brace
                _ if depth == 0 && self.is_decl_start() => return,
                // Stop at top-level keywords so an unclosed system block
                // doesn't consume subsequent system declarations.
                _ if depth == 0 && (self.at_ident("system") || self.at_ident("use")) => return,
                _ => {
                    self.advance();
                }
            }
        }
    }

    pub(crate) fn is_decl_start(&self) -> bool {
        matches!(
            self.peek(),
            TokenKind::Ident(ref s) if matches!(
                s.as_str(),
                "enum" | "struct" | "entity" | "derive" | "mechanic"
                | "action" | "reaction" | "condition" | "prompt"
                | "option" | "event" | "move"
                | "hook" | "table" | "unit" | "tag"
            )
        )
    }
}
