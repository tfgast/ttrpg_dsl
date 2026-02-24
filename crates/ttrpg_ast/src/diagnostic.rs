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

    /// Render a diagnostic in rustc-style format.
    pub fn render(&self, diag: &Diagnostic) -> String {
        render_diagnostic(
            diag,
            "line",
            self.source,
            &self.line_starts,
            0, // no base offset
        )
    }
}

/// Shared rendering logic for both SourceMap and MultiSourceMap.
fn render_diagnostic(
    diag: &Diagnostic,
    location_prefix: &str,
    source: &str,
    line_starts: &[usize],
    base_offset: usize,
) -> String {
    let local_start = diag.span.start - base_offset;
    let local_end = diag.span.end - base_offset;

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

    // Caret underline
    let caret_len = (local_end - local_start).max(1);
    let carets: String = "^".repeat(caret_len);

    format!(
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
    )
}

/// Renders diagnostics across multiple source files.
/// Owns source strings to avoid self-referential borrowing in the host.
pub struct MultiSourceMap {
    files: Vec<FileEntry>,
}

struct FileEntry {
    filename: String,
    base_offset: usize,
    /// Half-open upper bound: base_offset + source.len().
    /// The 1-byte sentinel gap guarantees end_exclusive < next file's base_offset.
    end_exclusive: usize,
    source: String,
    line_starts: Vec<usize>,
}

impl MultiSourceMap {
    /// Construct from sources + their base offsets (as computed by parse_multi).
    pub fn new(sources: Vec<(String, String)>) -> Self {
        let mut files = Vec::with_capacity(sources.len());
        let mut current_offset: usize = 0;

        for (filename, source) in sources {
            let mut line_starts = vec![0];
            for (i, ch) in source.char_indices() {
                if ch == '\n' {
                    line_starts.push(i + 1);
                }
            }

            let end_exclusive = current_offset + source.len();
            files.push(FileEntry {
                filename,
                base_offset: current_offset,
                end_exclusive,
                source,
                line_starts,
            });

            // 1-byte sentinel gap
            current_offset = end_exclusive + 1;
        }

        Self { files }
    }

    /// Find which file owns a span.
    fn find_file(&self, span_start: usize) -> Option<&FileEntry> {
        self.files.iter().find(|f| {
            f.base_offset <= span_start && span_start <= f.end_exclusive
        })
    }

    /// Render a diagnostic with filename:line:col location.
    pub fn render(&self, diag: &Diagnostic) -> String {
        // Handle dummy spans (0,0) — no file attribution
        if diag.span.start == 0 && diag.span.end == 0 && self.files.len() > 1 {
            let severity_str = match diag.severity {
                Severity::Error => "error",
                Severity::Warning => "warning",
            };
            return format!("[{}] {}", severity_str, diag.message);
        }

        match self.find_file(diag.span.start) {
            Some(file) => {
                let prefix = format!("{}:", file.filename);
                render_diagnostic(
                    diag,
                    &prefix,
                    &file.source,
                    &file.line_starts,
                    file.base_offset,
                )
            }
            None => {
                // Fallback — span doesn't map to any file
                let severity_str = match diag.severity {
                    Severity::Error => "error",
                    Severity::Warning => "warning",
                };
                format!("[{}] {}", severity_str, diag.message)
            }
        }
    }
}
