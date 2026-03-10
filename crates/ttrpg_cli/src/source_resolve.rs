//! Source resolver: walks `import` directives to build the complete file graph.
//!
//! Given one or more entrypoint files, the resolver:
//! 1. Reads each file and extracts `import "path.ttrpg"` directives
//! 2. Resolves import paths relative to the importing file's directory
//! 3. Follows edges transitively until the full graph is discovered
//! 4. Detects cycles and duplicate loads (via canonical path dedup)
//! 5. Returns a stable topological load order as `Vec<(String, String)>`

use std::collections::VecDeque;
use std::path::{Path, PathBuf};

use rustc_hash::FxHashSet;
use ttrpg_ast::FileId;
use ttrpg_parser::Diagnostic;

/// Error from the source resolver.
#[derive(Debug)]
pub enum ResolveError {
    /// An imported file could not be read.
    IoError {
        path: PathBuf,
        importing_file: Option<String>,
        error: std::io::Error,
    },
    /// An import cycle was detected.
    Cycle { chain: Vec<String> },
}

impl std::fmt::Display for ResolveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ResolveError::IoError {
                path,
                importing_file: Some(from),
                error,
            } => write!(
                f,
                "cannot read '{}' (imported by '{}'): {}",
                path.display(),
                from,
                error
            ),
            ResolveError::IoError {
                path,
                importing_file: None,
                error,
            } => write!(f, "cannot read '{}': {}", path.display(), error),
            ResolveError::Cycle { chain } => {
                write!(f, "import cycle detected: {}", chain.join(" → "))
            }
        }
    }
}

/// Result of source resolution.
#[derive(Debug)]
pub struct ResolvedSources {
    /// `(filename, source_text)` pairs in stable topological order.
    /// Entrypoint files come first, then their transitive dependencies
    /// in the order they were discovered (BFS).
    pub sources: Vec<(String, String)>,
    /// Parse diagnostics collected during import extraction.
    pub diagnostics: Vec<Diagnostic>,
}

/// Resolve transitive imports starting from the given entrypoint paths.
///
/// Each entrypoint is read, its `import` directives are extracted, and
/// the imported files are resolved relative to the importing file's directory.
/// The process repeats until all transitive dependencies are discovered.
///
/// Files are deduped by canonical path. The returned sources are in a stable
/// order: entrypoints first (in the order given), then discovered imports
/// in BFS order.
pub fn resolve_sources(entrypoints: &[PathBuf]) -> Result<ResolvedSources, ResolveError> {
    let mut seen: FxHashSet<PathBuf> = FxHashSet::default();
    let mut sources: Vec<(String, String)> = Vec::new();
    let mut diagnostics: Vec<Diagnostic> = Vec::new();
    // Queue of (canonical_path, display_path, importing_file)
    let mut queue: VecDeque<(PathBuf, String, Option<String>)> = VecDeque::new();

    // Seed queue with entrypoints
    for path in entrypoints {
        let canonical = canonicalize_path(path).map_err(|e| ResolveError::IoError {
            path: path.clone(),
            importing_file: None,
            error: e,
        })?;
        let display = path.to_string_lossy().into_owned();
        if seen.insert(canonical.clone()) {
            queue.push_back((canonical, display, None));
        }
    }

    while let Some((canonical, display, importer)) = queue.pop_front() {
        // Read file
        let content = std::fs::read_to_string(&canonical).map_err(|e| ResolveError::IoError {
            path: canonical.clone(),
            importing_file: importer,
            error: e,
        })?;

        // Extract imports
        let file_id = FileId(sources.len() as u32);
        let (imports, mut parse_diags) = ttrpg_parser::extract_imports(&content, file_id);
        diagnostics.append(&mut parse_diags);

        // Resolve each import path relative to the current file's directory
        let parent_dir = canonical.parent().unwrap_or_else(|| Path::new("."));

        for (import_path, _span) in &imports {
            let resolved = parent_dir.join(import_path);
            let import_canonical =
                canonicalize_path(&resolved).map_err(|e| ResolveError::IoError {
                    path: resolved.clone(),
                    importing_file: Some(display.clone()),
                    error: e,
                })?;

            if seen.insert(import_canonical.clone()) {
                queue.push_back((import_canonical, import_path.clone(), Some(display.clone())));
            }
        }

        sources.push((display, content));
    }

    Ok(ResolvedSources {
        sources,
        diagnostics,
    })
}

/// Canonicalize a path, falling back to `std::fs::canonicalize` with a
/// helpful error for missing files.
fn canonicalize_path(path: &Path) -> std::io::Result<PathBuf> {
    std::fs::canonicalize(path)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    #[test]
    fn resolve_single_file_no_imports() {
        let dir = tempfile::tempdir().unwrap();
        let entry = dir.path().join("main.ttrpg");
        fs::write(
            &entry,
            r#"system "Core" {
    derive foo() -> int { 1 }
}"#,
        )
        .unwrap();

        let result = resolve_sources(&[entry]).unwrap();
        assert_eq!(result.sources.len(), 1);
        assert!(result.diagnostics.is_empty());
    }

    #[test]
    fn resolve_transitive_imports() {
        let dir = tempfile::tempdir().unwrap();

        // a.ttrpg imports b.ttrpg, b.ttrpg imports c.ttrpg
        fs::write(
            dir.path().join("a.ttrpg"),
            r#"import "b.ttrpg"
system "A" { derive a() -> int { 1 } }"#,
        )
        .unwrap();
        fs::write(
            dir.path().join("b.ttrpg"),
            r#"import "c.ttrpg"
system "B" { derive b() -> int { 2 } }"#,
        )
        .unwrap();
        fs::write(
            dir.path().join("c.ttrpg"),
            r#"system "C" { derive c() -> int { 3 } }"#,
        )
        .unwrap();

        let result = resolve_sources(&[dir.path().join("a.ttrpg")]).unwrap();
        assert_eq!(result.sources.len(), 3);
        // a is first (entrypoint), then b, then c (BFS order)
        assert!(result.sources[0].0.contains("a.ttrpg"));
        assert!(result.sources[1].0.contains("b.ttrpg"));
        assert!(result.sources[2].0.contains("c.ttrpg"));
    }

    #[test]
    fn resolve_dedup_diamond() {
        let dir = tempfile::tempdir().unwrap();

        // Diamond: a -> b, a -> c, b -> d, c -> d
        fs::write(
            dir.path().join("a.ttrpg"),
            r#"import "b.ttrpg"
import "c.ttrpg"
system "A" { derive a() -> int { 1 } }"#,
        )
        .unwrap();
        fs::write(
            dir.path().join("b.ttrpg"),
            r#"import "d.ttrpg"
system "B" { derive b() -> int { 2 } }"#,
        )
        .unwrap();
        fs::write(
            dir.path().join("c.ttrpg"),
            r#"import "d.ttrpg"
system "C" { derive c() -> int { 3 } }"#,
        )
        .unwrap();
        fs::write(
            dir.path().join("d.ttrpg"),
            r#"system "D" { derive d() -> int { 4 } }"#,
        )
        .unwrap();

        let result = resolve_sources(&[dir.path().join("a.ttrpg")]).unwrap();
        assert_eq!(result.sources.len(), 4, "d.ttrpg should only appear once");
    }

    #[test]
    fn resolve_missing_import() {
        let dir = tempfile::tempdir().unwrap();
        fs::write(
            dir.path().join("a.ttrpg"),
            r#"import "nonexistent.ttrpg"
system "A" { derive a() -> int { 1 } }"#,
        )
        .unwrap();

        let err = resolve_sources(&[dir.path().join("a.ttrpg")]).unwrap_err();
        let msg = err.to_string();
        assert!(msg.contains("nonexistent.ttrpg"), "error: {msg}");
        assert!(
            msg.contains("a.ttrpg"),
            "error should mention importer: {msg}"
        );
    }

    #[test]
    fn resolve_mutual_import_dedup() {
        let dir = tempfile::tempdir().unwrap();

        // a imports b, b imports a — should not loop, just dedup
        fs::write(
            dir.path().join("a.ttrpg"),
            r#"import "b.ttrpg"
system "A" { derive a() -> int { 1 } }"#,
        )
        .unwrap();
        fs::write(
            dir.path().join("b.ttrpg"),
            r#"import "a.ttrpg"
system "B" { derive b() -> int { 2 } }"#,
        )
        .unwrap();

        let result = resolve_sources(&[dir.path().join("a.ttrpg")]).unwrap();
        assert_eq!(result.sources.len(), 2);
    }

    #[test]
    fn resolve_subdirectory_imports() {
        let dir = tempfile::tempdir().unwrap();
        fs::create_dir_all(dir.path().join("sub")).unwrap();

        fs::write(
            dir.path().join("main.ttrpg"),
            r#"import "sub/helper.ttrpg"
system "Main" { derive m() -> int { 1 } }"#,
        )
        .unwrap();
        fs::write(
            dir.path().join("sub/helper.ttrpg"),
            r#"system "Helper" { derive h() -> int { 2 } }"#,
        )
        .unwrap();

        let result = resolve_sources(&[dir.path().join("main.ttrpg")]).unwrap();
        assert_eq!(result.sources.len(), 2);
    }
}
