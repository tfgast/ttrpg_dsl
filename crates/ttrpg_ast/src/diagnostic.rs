use crate::Span;

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
    /// Optional help text rendered as `= help: ...` after the caret line.
    pub help: Option<String>,
}

impl Diagnostic {
    pub fn error(message: impl Into<String>, span: Span) -> Self {
        Self {
            severity: Severity::Error,
            message: message.into(),
            span,
            help: None,
        }
    }

    pub fn warning(message: impl Into<String>, span: Span) -> Self {
        Self {
            severity: Severity::Warning,
            message: message.into(),
            span,
            help: None,
        }
    }

    /// Attach a help message to this diagnostic.
    pub fn with_help(mut self, help: impl Into<String>) -> Self {
        self.help = Some(help.into());
        self
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

    /// Render a diagnostic in rustc-style format.
    pub fn render(&self, diag: &Diagnostic) -> String {
        render_diagnostic(
            diag,
            "line",
            self.source,
            &self.line_starts,
        )
    }
}

/// Shared rendering logic for both SourceMap and MultiSourceMap.
fn render_diagnostic(
    diag: &Diagnostic,
    location_prefix: &str,
    source: &str,
    line_starts: &[usize],
) -> String {
    let local_start = diag.span.start;
    let local_end = diag.span.end;

    let line = line_starts
        .partition_point(|&start| start <= local_start)
        .saturating_sub(1);
    let col = local_start - line_starts[line];
    let line_1indexed = line + 1;
    let col_1indexed = col + 1;

    let severity_str = match diag.severity {
        Severity::Error => "error",
        Severity::Warning => "warning",
    };

    // Get line text
    let line_text_start = line_starts[line];
    let line_text_end = line_starts
        .get(line + 1)
        .copied()
        .unwrap_or(source.len());
    let line_text = source[line_text_start..line_text_end]
        .trim_end_matches('\n')
        .trim_end_matches('\r');

    let line_num_width = line_1indexed.to_string().len();

    // Caret underline (saturating_sub guards against inverted spans)
    let caret_len = local_end.saturating_sub(local_start).max(1);
    let carets: String = "^".repeat(caret_len);

    let mut result = format!(
        "{severity}: {msg}\n\
         {pad} --> {prefix} {line}:{col}\n\
         {pad} |\n\
         {ln} | {text}\n\
         {pad} | {spaces}{carets}",
        severity = severity_str,
        msg = diag.message,
        pad = " ".repeat(line_num_width),
        prefix = location_prefix,
        line = line_1indexed,
        col = col_1indexed,
        ln = line_1indexed,
        text = line_text,
        spaces = " ".repeat(col_1indexed - 1),
        carets = carets,
    );

    if let Some(ref help) = diag.help {
        result.push_str(&format!(
            "\n{pad} = help: {help}",
            pad = " ".repeat(line_num_width),
            help = help,
        ));
    }

    result
}

/// Renders diagnostics across multiple source files.
/// Owns source strings to avoid self-referential borrowing in the host.
pub struct MultiSourceMap {
    files: Vec<FileEntry>,
}

struct FileEntry {
    filename: String,
    source: String,
    line_starts: Vec<usize>,
}

impl MultiSourceMap {
    /// Construct from `(filename, source_text)` pairs.
    /// Files are indexed by position: the first file is `FileId(0)`, etc.
    pub fn new(sources: Vec<(String, String)>) -> Self {
        let files = sources
            .into_iter()
            .map(|(filename, source)| {
                let mut line_starts = vec![0];
                for (i, ch) in source.char_indices() {
                    if ch == '\n' {
                        line_starts.push(i + 1);
                    }
                }
                FileEntry {
                    filename,
                    source,
                    line_starts,
                }
            })
            .collect();

        Self { files }
    }

    /// Render a diagnostic with filename:line:col location.
    pub fn render(&self, diag: &Diagnostic) -> String {
        // Dummy spans have no source location — render without file attribution
        if diag.span.is_dummy() {
            let severity_str = match diag.severity {
                Severity::Error => "error",
                Severity::Warning => "warning",
            };
            return format!("[{}] {}", severity_str, diag.message);
        }

        let file_idx = diag.span.file.0 as usize;
        match self.files.get(file_idx) {
            Some(file) => {
                let prefix = format!("{}:", file.filename);
                render_diagnostic(
                    diag,
                    &prefix,
                    &file.source,
                    &file.line_starts,
                )
            }
            None => {
                // Fallback — FileId doesn't map to any file
                let severity_str = match diag.severity {
                    Severity::Error => "error",
                    Severity::Warning => "warning",
                };
                format!("[{}] {}", severity_str, diag.message)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::span::FileId;

    // ── FileId-based lookup ──

    #[test]
    fn multi_source_map_file_id_lookup() {
        // FileId(0) → "a.ttrpg", FileId(1) → "b.ttrpg"
        let msm = MultiSourceMap::new(vec![
            ("a.ttrpg".into(), "hello".into()),
            ("b.ttrpg".into(), "world".into()),
        ]);
        let diag_a = Diagnostic::error("err in a", Span::new(FileId(0), 0, 3));
        let diag_b = Diagnostic::error("err in b", Span::new(FileId(1), 0, 3));
        assert!(msm.render(&diag_a).contains("a.ttrpg"));
        assert!(msm.render(&diag_b).contains("b.ttrpg"));
    }

    #[test]
    fn multi_source_map_out_of_range_file_id() {
        // A FileId beyond the file list should fall through gracefully
        let msm = MultiSourceMap::new(vec![
            ("a.ttrpg".into(), "hello".into()),
        ]);
        let diag = Diagnostic::error("oops", Span::new(FileId(99), 0, 3));
        let rendered = msm.render(&diag);
        assert!(
            rendered.contains("[error]"),
            "unknown FileId should use no-attribution format, got: {rendered}",
        );
    }

    // ── Regression: tdsl-rsdi — (0,0) span at BOF should not lose filename ──

    #[test]
    fn multi_source_map_zero_span_renders_with_filename() {
        let msm = MultiSourceMap::new(vec![
            ("a.ttrpg".into(), "let x = 1\n".into()),
            ("b.ttrpg".into(), "let y = 2\n".into()),
        ]);
        let diag = Diagnostic::error("unexpected token", Span::new(FileId(0), 0, 0));
        let rendered = msm.render(&diag);
        assert!(
            rendered.contains("a.ttrpg"),
            "diagnostic at BOF should include filename, got: {rendered}",
        );
    }

    #[test]
    fn multi_source_map_dummy_span_no_attribution() {
        let msm = MultiSourceMap::new(vec![
            ("a.ttrpg".into(), "let x = 1\n".into()),
            ("b.ttrpg".into(), "let y = 2\n".into()),
        ]);
        let diag = Diagnostic::error("type error", Span::dummy());
        let rendered = msm.render(&diag);
        assert!(
            rendered.contains("[error]"),
            "dummy span should use no-attribution format, got: {rendered}",
        );
        assert!(
            !rendered.contains("a.ttrpg") && !rendered.contains("b.ttrpg"),
            "dummy span should not attribute to any file, got: {rendered}",
        );
    }

    // ── Regression: tdsl-li9m — inverted span should not panic in renderer ──

    #[test]
    fn render_inverted_span_does_not_panic() {
        let sm = SourceMap::new("hello world");
        let diag = Diagnostic::error("test", Span::new(FileId::SYNTH, 5, 3));
        // Should not panic despite start > end (saturating_sub guards it)
        let rendered = sm.render(&diag);
        assert!(rendered.contains("test"), "should still contain the message");
        assert!(rendered.contains("^"), "should still have caret(s)");
    }
}
