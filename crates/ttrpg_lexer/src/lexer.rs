use crate::cursor::Cursor;
use crate::token::{Token, TokenKind};
use ttrpg_ast::{DiceFilter, FileId, Span};

/// Raw lexer: produces all tokens including newlines.
pub struct RawLexer<'a> {
    cursor: Cursor<'a>,
    file: FileId,
    done: bool,
}

impl<'a> RawLexer<'a> {
    pub fn new(source: &'a str, file: FileId) -> Self {
        Self {
            cursor: Cursor::new(source),
            file,
            done: false,
        }
    }

    /// Convenience: build a span in this file.
    fn span(&self, start: usize, end: usize) -> Span {
        Span::new(self.file, start, end)
    }

    fn skip_whitespace_and_comments(&mut self) {
        loop {
            // Skip horizontal whitespace (not newlines)
            self.cursor
                .eat_while(|ch| ch == ' ' || ch == '\t' || ch == '\r');

            // Check for line comments
            if self.cursor.peek() == Some('/') && self.cursor.peek_next() == Some('/') {
                // Consume until end of line (but NOT the newline itself)
                self.cursor.advance(); // /
                self.cursor.advance(); // /
                self.cursor.eat_while(|ch| ch != '\n');
                continue;
            }

            break;
        }
    }

    fn lex_string(&mut self) -> TokenKind {
        // Opening quote already consumed
        let mut value = String::new();
        loop {
            match self.cursor.advance() {
                None => return TokenKind::Error("unterminated string".into()),
                Some('"') => return TokenKind::String(value),
                Some('\\') => match self.cursor.advance() {
                    Some('n') => value.push('\n'),
                    Some('t') => value.push('\t'),
                    Some('\\') => value.push('\\'),
                    Some('"') => value.push('"'),
                    Some(ch) => {
                        value.push('\\');
                        value.push(ch);
                    }
                    None => return TokenKind::Error("unterminated string escape".into()),
                },
                Some(ch) => value.push(ch),
            }
        }
    }

    fn lex_number_or_dice(&mut self, first_digit_start: usize) -> Token {
        // We've already consumed the first digit character. Consume the rest.
        self.cursor.eat_while(|ch| ch.is_ascii_digit());
        let num_end = self.cursor.pos();
        let num_str = self.cursor.slice(first_digit_start, num_end);
        let count_result: Result<i64, _> = num_str.parse();

        // Check for dice literal: INT d INT filter?
        // The 'd' must immediately follow the number (no whitespace)
        if self.cursor.peek() == Some('d') {
            // Peek further: next char after 'd' must be a digit for this to be a dice literal
            if self
                .cursor
                .peek_at_offset(1)
                .is_some_and(|ch| ch.is_ascii_digit())
            {
                self.cursor.advance(); // consume 'd'
                let sides_start = self.cursor.pos();
                self.cursor.eat_while(|ch| ch.is_ascii_digit());
                let sides_end = self.cursor.pos();
                let sides_str = self.cursor.slice(sides_start, sides_end);

                // Validate count fits in u32
                let count: u32 = match count_result {
                    Ok(c) if c >= 0 && c <= u32::MAX as i64 => c as u32,
                    _ => {
                        let _ = self.try_lex_dice_filter();
                        let span = self.span(first_digit_start, self.cursor.pos());
                        return Token::new(
                            TokenKind::Error("dice count too large (overflow)".into()),
                            span,
                        );
                    }
                };

                // Validate sides fits in u32
                let sides: u32 = match sides_str.parse() {
                    Ok(s) => s,
                    Err(_) => {
                        let _ = self.try_lex_dice_filter();
                        let span = self.span(first_digit_start, self.cursor.pos());
                        return Token::new(
                            TokenKind::Error("dice sides too large (overflow)".into()),
                            span,
                        );
                    }
                };

                if sides == 0 {
                    let span = self.span(first_digit_start, self.cursor.pos());
                    return Token::new(
                        TokenKind::Error(
                            "dice sides must be at least 1 (e.g. 1d0 is invalid)".into(),
                        ),
                        span,
                    );
                }

                // Check for filter: kh, kl, dh, dl followed by digits
                let filter = match self.try_lex_dice_filter() {
                    Ok(f) => f,
                    Err(msg) => {
                        let span = self.span(first_digit_start, self.cursor.pos());
                        return Token::new(TokenKind::Error(msg), span);
                    }
                };

                let span = self.span(first_digit_start, self.cursor.pos());
                return Token::new(
                    TokenKind::Dice {
                        count,
                        sides,
                        filter,
                    },
                    span,
                );
            }
        }

        // Non-dice paths require a valid i64 count
        let count: i64 = match count_result {
            Ok(c) => c,
            Err(_) => {
                // Consume unit suffix if present so the lexer stays in sync
                if self
                    .cursor
                    .peek()
                    .is_some_and(|ch| ch.is_ascii_alphabetic())
                {
                    self.cursor
                        .eat_while(|ch| ch.is_ascii_alphanumeric() || ch == '_');
                }
                let span = self.span(first_digit_start, self.cursor.pos());
                return Token::new(
                    TokenKind::Error("numeric literal too large (overflow)".into()),
                    span,
                );
            }
        };

        // Check for unit literal: INT followed immediately by alpha chars (e.g., 30ft)
        if self
            .cursor
            .peek()
            .is_some_and(|ch| ch.is_ascii_alphabetic())
        {
            let suffix_start = self.cursor.pos();
            self.cursor
                .eat_while(|ch| ch.is_ascii_alphanumeric() || ch == '_');
            let suffix_end = self.cursor.pos();
            let suffix = self.cursor.slice(suffix_start, suffix_end).to_string();
            return Token::new(
                TokenKind::UnitLiteral {
                    value: count,
                    suffix,
                },
                self.span(first_digit_start, suffix_end),
            );
        }

        Token::new(TokenKind::Int(count), self.span(first_digit_start, num_end))
    }

    fn try_lex_dice_filter(&mut self) -> Result<Option<DiceFilter>, String> {
        let Some(first) = self.cursor.peek() else {
            return Ok(None);
        };
        let Some(second) = self.cursor.peek_at_offset(1) else {
            return Ok(None);
        };

        let filter_kind = match (first, second) {
            ('k', 'h') => 0,
            ('k', 'l') => 1,
            ('d', 'h') => 2,
            ('d', 'l') => 3,
            _ => return Ok(None),
        };

        // Check that the third char is a digit
        if !self
            .cursor
            .peek_at_offset(2)
            .is_some_and(|ch| ch.is_ascii_digit())
        {
            return Ok(None);
        }

        self.cursor.advance(); // k/d
        self.cursor.advance(); // h/l
        let start = self.cursor.pos();
        self.cursor.eat_while(|ch| ch.is_ascii_digit());
        let end = self.cursor.pos();
        let n: u32 = self
            .cursor
            .slice(start, end)
            .parse()
            .map_err(|_| "dice filter count too large (overflow)".to_string())?;

        Ok(Some(match filter_kind {
            0 => DiceFilter::KeepHighest(n),
            1 => DiceFilter::KeepLowest(n),
            2 => DiceFilter::DropHighest(n),
            3 => DiceFilter::DropLowest(n),
            _ => unreachable!(),
        }))
    }

    fn lex_ident_or_keyword(&mut self, start: usize) -> Token {
        self.cursor
            .eat_while(|ch| ch.is_ascii_alphanumeric() || ch == '_');
        let end = self.cursor.pos();
        let text = self.cursor.slice(start, end);
        let span = self.span(start, end);

        let kind = match text {
            "let" => TokenKind::Let,
            "if" => TokenKind::If,
            "else" => TokenKind::Else,
            "match" => TokenKind::Match,
            "true" => TokenKind::True,
            "false" => TokenKind::False,
            "none" => TokenKind::None,
            "in" => TokenKind::In,
            "for" => TokenKind::For,
            _ => TokenKind::Ident(text.to_string()),
        };

        Token::new(kind, span)
    }

    fn next_token(&mut self) -> Token {
        self.skip_whitespace_and_comments();

        if self.cursor.is_eof() {
            return Token::new(
                TokenKind::Eof,
                self.span(self.cursor.pos(), self.cursor.pos()),
            );
        }

        let start = self.cursor.pos();
        let Some(ch) = self.cursor.advance() else {
            return Token::new(TokenKind::Eof, self.span(start, start));
        };

        match ch {
            '\n' => Token::new(TokenKind::Newline, self.span(start, self.cursor.pos())),

            '(' => Token::new(TokenKind::LParen, self.span(start, self.cursor.pos())),
            ')' => Token::new(TokenKind::RParen, self.span(start, self.cursor.pos())),
            '{' => Token::new(TokenKind::LBrace, self.span(start, self.cursor.pos())),
            '}' => Token::new(TokenKind::RBrace, self.span(start, self.cursor.pos())),
            '[' => Token::new(TokenKind::LBracket, self.span(start, self.cursor.pos())),
            ']' => Token::new(TokenKind::RBracket, self.span(start, self.cursor.pos())),
            ',' => Token::new(TokenKind::Comma, self.span(start, self.cursor.pos())),
            ':' => Token::new(TokenKind::Colon, self.span(start, self.cursor.pos())),
            '#' => Token::new(TokenKind::Hash, self.span(start, self.cursor.pos())),

            '.' => {
                if self.cursor.peek() == Some('.') {
                    self.cursor.advance();
                    if self.cursor.peek() == Some('=') {
                        self.cursor.advance();
                        Token::new(TokenKind::DotDotEq, self.span(start, self.cursor.pos()))
                    } else {
                        Token::new(TokenKind::DotDot, self.span(start, self.cursor.pos()))
                    }
                } else {
                    Token::new(TokenKind::Dot, self.span(start, self.cursor.pos()))
                }
            }

            '+' => {
                if self.cursor.peek() == Some('=') {
                    self.cursor.advance();
                    Token::new(TokenKind::PlusEq, self.span(start, self.cursor.pos()))
                } else {
                    Token::new(TokenKind::Plus, self.span(start, self.cursor.pos()))
                }
            }

            '-' => {
                if self.cursor.peek() == Some('>') {
                    self.cursor.advance();
                    Token::new(TokenKind::Arrow, self.span(start, self.cursor.pos()))
                } else if self.cursor.peek() == Some('=') {
                    self.cursor.advance();
                    Token::new(TokenKind::MinusEq, self.span(start, self.cursor.pos()))
                } else {
                    Token::new(TokenKind::Minus, self.span(start, self.cursor.pos()))
                }
            }

            '*' => Token::new(TokenKind::Star, self.span(start, self.cursor.pos())),
            '/' => Token::new(TokenKind::Slash, self.span(start, self.cursor.pos())),

            '!' => {
                if self.cursor.peek() == Some('=') {
                    self.cursor.advance();
                    Token::new(TokenKind::BangEq, self.span(start, self.cursor.pos()))
                } else {
                    Token::new(TokenKind::Bang, self.span(start, self.cursor.pos()))
                }
            }

            '=' => {
                if self.cursor.peek() == Some('=') {
                    self.cursor.advance();
                    Token::new(TokenKind::EqEq, self.span(start, self.cursor.pos()))
                } else if self.cursor.peek() == Some('>') {
                    self.cursor.advance();
                    Token::new(TokenKind::FatArrow, self.span(start, self.cursor.pos()))
                } else {
                    Token::new(TokenKind::Eq, self.span(start, self.cursor.pos()))
                }
            }

            '<' => {
                if self.cursor.peek() == Some('=') {
                    self.cursor.advance();
                    Token::new(TokenKind::LtEq, self.span(start, self.cursor.pos()))
                } else {
                    Token::new(TokenKind::Lt, self.span(start, self.cursor.pos()))
                }
            }

            '>' => {
                if self.cursor.peek() == Some('=') {
                    self.cursor.advance();
                    Token::new(TokenKind::GtEq, self.span(start, self.cursor.pos()))
                } else {
                    Token::new(TokenKind::Gt, self.span(start, self.cursor.pos()))
                }
            }

            '&' => {
                if self.cursor.peek() == Some('&') {
                    self.cursor.advance();
                    Token::new(TokenKind::AmpAmp, self.span(start, self.cursor.pos()))
                } else {
                    Token::new(
                        TokenKind::Error("unexpected character '&'".to_string()),
                        self.span(start, self.cursor.pos()),
                    )
                }
            }

            '|' => {
                if self.cursor.peek() == Some('|') {
                    self.cursor.advance();
                    Token::new(TokenKind::PipePipe, self.span(start, self.cursor.pos()))
                } else {
                    Token::new(
                        TokenKind::Error("unexpected character '|'".to_string()),
                        self.span(start, self.cursor.pos()),
                    )
                }
            }

            '"' => {
                let kind = self.lex_string();
                Token::new(kind, self.span(start, self.cursor.pos()))
            }

            '_' => {
                // Underscore: if followed by alphanumeric or _, it's an identifier
                if self
                    .cursor
                    .peek()
                    .is_some_and(|ch| ch.is_ascii_alphanumeric() || ch == '_')
                {
                    self.lex_ident_or_keyword(start)
                } else {
                    Token::new(TokenKind::Underscore, self.span(start, self.cursor.pos()))
                }
            }

            ch if ch.is_ascii_digit() => self.lex_number_or_dice(start),

            ch if ch.is_ascii_alphabetic() => self.lex_ident_or_keyword(start),

            _ => Token::new(
                TokenKind::Error(format!("unexpected character '{ch}'")),
                self.span(start, self.cursor.pos()),
            ),
        }
    }
}

impl<'a> Iterator for RawLexer<'a> {
    type Item = Token;

    fn next(&mut self) -> Option<Token> {
        if self.done {
            return None;
        }
        let tok = self.next_token();
        if tok.kind == TokenKind::Eof {
            self.done = true;
        }
        Some(tok)
    }
}

/// Wrapping lexer: suppresses newlines per the spec rules.
///
/// Rules:
/// 1. Inside `()` and `[]`: all NL tokens are discarded.
/// 2. After binary/assignment operators and arrows, `{`, and `,`: suppress next NL.
/// 3. (Combined with rule 2 via `suppresses_next_newline`)
pub struct Lexer<'a> {
    raw: RawLexer<'a>,
    paren_depth: usize,
    bracket_depth: usize,
    suppress_next_nl: bool,
}

impl<'a> Lexer<'a> {
    pub fn new(source: &'a str, file: FileId) -> Self {
        Self {
            raw: RawLexer::new(source, file),
            paren_depth: 0,
            bracket_depth: 0,
            suppress_next_nl: false,
        }
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Token;

    fn next(&mut self) -> Option<Token> {
        loop {
            let tok = self.raw.next()?;

            match &tok.kind {
                TokenKind::LParen => self.paren_depth += 1,
                TokenKind::RParen => self.paren_depth = self.paren_depth.saturating_sub(1),
                TokenKind::LBracket => self.bracket_depth += 1,
                TokenKind::RBracket => self.bracket_depth = self.bracket_depth.saturating_sub(1),
                _ => {}
            }

            if tok.kind == TokenKind::Newline {
                // Rule 1: suppress inside parens/brackets
                if self.paren_depth > 0 || self.bracket_depth > 0 {
                    continue;
                }
                // Rule 2: suppress after operators/arrows/{/,
                if self.suppress_next_nl {
                    self.suppress_next_nl = false;
                    continue;
                }
            }

            // Update suppress flag for next iteration
            self.suppress_next_nl = tok.kind.suppresses_next_newline();

            return Some(tok);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lex(source: &str) -> Vec<TokenKind> {
        Lexer::new(source, FileId::SYNTH).map(|t| t.kind).collect()
    }

    #[test]
    fn test_simple_int() {
        assert_eq!(lex("42"), vec![TokenKind::Int(42), TokenKind::Eof]);
    }

    #[test]
    fn test_dice_literal() {
        assert_eq!(
            lex("4d6kh3"),
            vec![
                TokenKind::Dice {
                    count: 4,
                    sides: 6,
                    filter: Some(DiceFilter::KeepHighest(3))
                },
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_dice_no_filter() {
        assert_eq!(
            lex("1d20"),
            vec![
                TokenKind::Dice {
                    count: 1,
                    sides: 20,
                    filter: None
                },
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_dice_keep_lowest() {
        assert_eq!(
            lex("2d20kl1"),
            vec![
                TokenKind::Dice {
                    count: 2,
                    sides: 20,
                    filter: Some(DiceFilter::KeepLowest(1))
                },
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_dice_drop_highest() {
        assert_eq!(
            lex("4d6dh1"),
            vec![
                TokenKind::Dice {
                    count: 4,
                    sides: 6,
                    filter: Some(DiceFilter::DropHighest(1))
                },
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_dice_drop_lowest() {
        assert_eq!(
            lex("4d6dl1"),
            vec![
                TokenKind::Dice {
                    count: 4,
                    sides: 6,
                    filter: Some(DiceFilter::DropLowest(1))
                },
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_int_vs_dice_disambiguation() {
        let result = lex("4 d6");
        assert_eq!(
            result,
            vec![
                TokenKind::Int(4),
                TokenKind::Ident("d6".into()),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_reserved_keywords() {
        let result = lex("let if else match true false none in for");
        assert_eq!(
            result,
            vec![
                TokenKind::Let,
                TokenKind::If,
                TokenKind::Else,
                TokenKind::Match,
                TokenKind::True,
                TokenKind::False,
                TokenKind::None,
                TokenKind::In,
                TokenKind::For,
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_soft_keywords_are_idents() {
        let result = lex("system action derive");
        assert_eq!(
            result,
            vec![
                TokenKind::Ident("system".into()),
                TokenKind::Ident("action".into()),
                TokenKind::Ident("derive".into()),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_underscore_standalone() {
        let result = lex("_ _foo");
        assert_eq!(
            result,
            vec![
                TokenKind::Underscore,
                TokenKind::Ident("_foo".into()),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_nl_suppression_inside_parens() {
        let result = lex("(\n)");
        assert_eq!(
            result,
            vec![TokenKind::LParen, TokenKind::RParen, TokenKind::Eof]
        );
    }

    #[test]
    fn test_nl_suppression_inside_brackets() {
        let result = lex("[\n]");
        assert_eq!(
            result,
            vec![TokenKind::LBracket, TokenKind::RBracket, TokenKind::Eof]
        );
    }

    #[test]
    fn test_nl_suppression_after_operators() {
        // After +, NL is suppressed
        let result = lex("a +\nb");
        assert_eq!(
            result,
            vec![
                TokenKind::Ident("a".into()),
                TokenKind::Plus,
                TokenKind::Ident("b".into()),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_nl_suppression_after_comma() {
        let result = lex("a,\nb");
        assert_eq!(
            result,
            vec![
                TokenKind::Ident("a".into()),
                TokenKind::Comma,
                TokenKind::Ident("b".into()),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_nl_suppression_after_lbrace() {
        let result = lex("{\na\n}");
        assert_eq!(
            result,
            vec![
                TokenKind::LBrace,
                TokenKind::Ident("a".into()),
                TokenKind::Newline,
                TokenKind::RBrace,
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_nl_suppression_after_fat_arrow() {
        let result = lex("=>\na");
        assert_eq!(
            result,
            vec![
                TokenKind::FatArrow,
                TokenKind::Ident("a".into()),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_nl_suppression_after_eq() {
        let result = lex("x =\n5");
        assert_eq!(
            result,
            vec![
                TokenKind::Ident("x".into()),
                TokenKind::Eq,
                TokenKind::Int(5),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_nl_preserved_between_stmts() {
        let result = lex("a\nb");
        assert_eq!(
            result,
            vec![
                TokenKind::Ident("a".into()),
                TokenKind::Newline,
                TokenKind::Ident("b".into()),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_nested_brackets_suppress_nl() {
        let result = lex("([\n\n])");
        assert_eq!(
            result,
            vec![
                TokenKind::LParen,
                TokenKind::LBracket,
                TokenKind::RBracket,
                TokenKind::RParen,
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_comments_stripped() {
        let result = lex("a // comment\nb");
        assert_eq!(
            result,
            vec![
                TokenKind::Ident("a".into()),
                TokenKind::Newline,
                TokenKind::Ident("b".into()),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_string_literal() {
        assert_eq!(
            lex(r#""hello""#),
            vec![TokenKind::String("hello".into()), TokenKind::Eof]
        );
    }

    #[test]
    fn test_string_with_escapes() {
        assert_eq!(
            lex(r#""hello\nworld""#),
            vec![TokenKind::String("hello\nworld".into()), TokenKind::Eof]
        );
    }

    #[test]
    fn test_operators() {
        let result = lex("+ - * / -> => .. ..= == != >= <= += -=");
        assert_eq!(
            result,
            vec![
                TokenKind::Plus,
                TokenKind::Minus,
                TokenKind::Star,
                TokenKind::Slash,
                TokenKind::Arrow,
                TokenKind::FatArrow,
                TokenKind::DotDot,
                TokenKind::DotDotEq,
                TokenKind::EqEq,
                TokenKind::BangEq,
                TokenKind::GtEq,
                TokenKind::LtEq,
                TokenKind::PlusEq,
                TokenKind::MinusEq,
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_nl_suppression_after_in() {
        let result = lex("x in\ny");
        assert_eq!(
            result,
            vec![
                TokenKind::Ident("x".into()),
                TokenKind::In,
                TokenKind::Ident("y".into()),
                TokenKind::Eof,
            ]
        );
    }
}
