/// Low-level character iterator with byte position tracking.
///
/// Hot-path methods use byte-level access for ASCII characters (which covers
/// virtually all DSL source), falling back to `str::chars()` only for
/// multi-byte UTF-8 sequences.
pub struct Cursor<'a> {
    source: &'a str,
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> Cursor<'a> {
    pub fn new(source: &'a str) -> Self {
        Self {
            source,
            bytes: source.as_bytes(),
            pos: 0,
        }
    }

    pub fn pos(&self) -> usize {
        self.pos
    }

    pub fn is_eof(&self) -> bool {
        self.pos >= self.bytes.len()
    }

    pub fn peek(&self) -> Option<char> {
        let &b = self.bytes.get(self.pos)?;
        if b.is_ascii() {
            Some(b as char)
        } else {
            self.source[self.pos..].chars().next()
        }
    }

    pub fn peek_next(&self) -> Option<char> {
        let &b = self.bytes.get(self.pos)?;
        let next_pos = if b.is_ascii() {
            self.pos + 1
        } else {
            self.pos + char_len_utf8(b)
        };
        let &b2 = self.bytes.get(next_pos)?;
        if b2.is_ascii() {
            Some(b2 as char)
        } else {
            self.source[next_pos..].chars().next()
        }
    }

    /// Peek at a character at the given byte offset from current position.
    /// offset=0 is same as peek(), offset=1 is same as peek_next(), etc.
    pub fn peek_at_offset(&self, offset: usize) -> Option<char> {
        // Walk `offset` characters forward from pos
        let mut p = self.pos;
        for _ in 0..offset {
            let &b = self.bytes.get(p)?;
            p += if b.is_ascii() { 1 } else { char_len_utf8(b) };
        }
        let &b = self.bytes.get(p)?;
        if b.is_ascii() {
            Some(b as char)
        } else {
            self.source[p..].chars().next()
        }
    }

    pub fn advance(&mut self) -> Option<char> {
        let &b = self.bytes.get(self.pos)?;
        if b.is_ascii() {
            self.pos += 1;
            Some(b as char)
        } else {
            let ch = self.source[self.pos..].chars().next()?;
            self.pos += ch.len_utf8();
            Some(ch)
        }
    }

    /// Fast path for skipping ` `, `\t`, `\r` — avoids closure overhead.
    #[inline]
    pub fn eat_horizontal_whitespace(&mut self) {
        while self.pos < self.bytes.len() {
            match self.bytes[self.pos] {
                b' ' | b'\t' | b'\r' => self.pos += 1,
                _ => return,
            }
        }
    }

    pub fn eat_while(&mut self, predicate: impl Fn(char) -> bool) {
        // Fast path: scan ASCII bytes directly
        while self.pos < self.bytes.len() {
            let b = self.bytes[self.pos];
            if b.is_ascii() {
                if predicate(b as char) {
                    self.pos += 1;
                } else {
                    return;
                }
            } else {
                // Slow path for multi-byte chars
                let ch = match self.source[self.pos..].chars().next() {
                    Some(ch) => ch,
                    None => return,
                };
                if predicate(ch) {
                    self.pos += ch.len_utf8();
                } else {
                    return;
                }
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

/// UTF-8 leading byte → character length.
#[inline]
fn char_len_utf8(first_byte: u8) -> usize {
    match first_byte {
        0..=0x7F => 1,
        0xC0..=0xDF => 2,
        0xE0..=0xEF => 3,
        0xF0..=0xFF => 4,
        _ => 1, // unreachable for valid UTF-8
    }
}
