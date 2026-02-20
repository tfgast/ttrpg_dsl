use ttrpg_ast::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    Error,
    Warning,
}

#[derive(Debug, Clone)]
pub struct Diagnostic {
    pub severity: Severity,
    pub message: String,
    pub span: Span,
}

impl Diagnostic {
    pub fn error(message: impl Into<String>, span: Span) -> Self {
        Self {
            severity: Severity::Error,
            message: message.into(),
            span,
        }
    }

    pub fn warning(message: impl Into<String>, span: Span) -> Self {
        Self {
            severity: Severity::Warning,
            message: message.into(),
            span,
        }
    }
}

/// Maps byte offsets to line/column positions and renders diagnostics.
pub struct SourceMap<'a> {
    source: &'a str,
    line_starts: Vec<usize>,
}

impl<'a> SourceMap<'a> {
    pub fn new(source: &'a str) -> Self {
        let mut line_starts = vec![0];
        for (i, ch) in source.char_indices() {
            if ch == '\n' {
                line_starts.push(i + 1);
            }
        }
        Self {
            source,
            line_starts,
        }
    }

    /// Returns (1-indexed line, 1-indexed column).
    pub fn line_col(&self, byte_offset: usize) -> (usize, usize) {
        let line = self
            .line_starts
            .partition_point(|&start| start <= byte_offset)
            .saturating_sub(1);
        let col = byte_offset - self.line_starts[line];
        (line + 1, col + 1)
    }

    /// Get the source text for a given 1-indexed line number.
    fn line_text(&self, line_1indexed: usize) -> &str {
        let idx = line_1indexed - 1;
        let start = self.line_starts[idx];
        let end = self
            .line_starts
            .get(idx + 1)
            .copied()
            .unwrap_or(self.source.len());
        self.source[start..end].trim_end_matches('\n').trim_end_matches('\r')
    }

    /// Render a diagnostic in rustc-style format.
    pub fn render(&self, diag: &Diagnostic) -> String {
        let (line, col) = self.line_col(diag.span.start);
        let severity_str = match diag.severity {
            Severity::Error => "error",
            Severity::Warning => "warning",
        };
        let line_text = self.line_text(line);
        let line_num_width = line.to_string().len();

        // Caret underline
        let caret_len = (diag.span.end - diag.span.start).max(1);
        let carets: String = "^".repeat(caret_len);

        format!(
            "{severity}: {msg}\n\
             {pad} --> line {line}:{col}\n\
             {pad} |\n\
             {ln} | {text}\n\
             {pad} | {spaces}{carets}",
            severity = severity_str,
            msg = diag.message,
            pad = " ".repeat(line_num_width),
            ln = line,
            col = col,
            text = line_text,
            spaces = " ".repeat(col - 1),
            carets = carets,
        )
    }
}
