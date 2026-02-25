#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FileId(pub u32);

impl FileId {
    pub const SYNTH: FileId = FileId(u32::MAX);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    pub file: FileId,
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(file: FileId, start: usize, end: usize) -> Self {
        Self { file, start, end }
    }

    /// Sentinel span that does not correspond to any source location.
    pub fn dummy() -> Self {
        Self {
            file: FileId::SYNTH,
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
        debug_assert_eq!(
            self.file.0, other.file.0,
            "cannot merge spans from different files"
        );
        Span {
            file: self.file,
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
