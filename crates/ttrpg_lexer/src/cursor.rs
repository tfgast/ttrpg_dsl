/// Low-level character iterator with byte position tracking.
pub struct Cursor<'a> {
    source: &'a str,
    pos: usize,
}

impl<'a> Cursor<'a> {
    pub fn new(source: &'a str) -> Self {
        Self { source, pos: 0 }
    }

    pub fn pos(&self) -> usize {
        self.pos
    }

    pub fn is_eof(&self) -> bool {
        self.pos >= self.source.len()
    }

    pub fn peek(&self) -> Option<char> {
        self.source[self.pos..].chars().next()
    }

    pub fn peek_next(&self) -> Option<char> {
        let mut chars = self.source[self.pos..].chars();
        chars.next();
        chars.next()
    }

    /// Peek at a character at the given byte offset from current position.
    /// offset=0 is same as peek(), offset=1 is same as peek_next(), etc.
    pub fn peek_at_offset(&self, offset: usize) -> Option<char> {
        let mut chars = self.source[self.pos..].chars();
        for _ in 0..offset {
            chars.next()?;
        }
        chars.next()
    }

    pub fn advance(&mut self) -> Option<char> {
        let ch = self.peek()?;
        self.pos += ch.len_utf8();
        Some(ch)
    }

    pub fn eat_while(&mut self, predicate: impl Fn(char) -> bool) {
        while let Some(ch) = self.peek() {
            if predicate(ch) {
                self.advance();
            } else {
                break;
            }
        }
    }

    pub fn slice(&self, start: usize, end: usize) -> &'a str {
        &self.source[start..end]
    }

    pub fn remaining(&self) -> &'a str {
        &self.source[self.pos..]
    }
}
