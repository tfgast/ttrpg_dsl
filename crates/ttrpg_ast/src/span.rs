#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    /// Sentinel span that does not correspond to any source location.
    pub fn dummy() -> Self {
        Self {
            start: usize::MAX,
            end: usize::MAX,
        }
    }

    /// Returns true if this span is the dummy sentinel (no source location).
    pub fn is_dummy(self) -> bool {
        self.start == usize::MAX && self.end == usize::MAX
    }

    pub fn merge(self, other: Span) -> Span {
        if self.is_dummy() {
            return other;
        }
        if other.is_dummy() {
            return self;
        }
        Span {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Spanned<T> {
    pub node: T,
    pub span: Span,
}

impl<T> Spanned<T> {
    pub fn new(node: T, span: Span) -> Self {
        Self { node, span }
    }
}
