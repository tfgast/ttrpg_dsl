pub mod diagnostic;
pub mod lower;
pub mod parser;
pub mod resolve;
mod decl;
mod expr;
mod pattern;
mod stmt;
mod types;

pub use diagnostic::{Diagnostic, Severity, SourceMap};
pub use lower::lower_moves;
pub use resolve::FileSystemInfo;
use ttrpg_ast::ast::*;
use ttrpg_ast::module::ModuleMap;
use ttrpg_ast::{FileId, Spanned};
use ttrpg_lexer::TokenKind;
use parser::Parser;

pub fn parse(source: &str, file: FileId) -> (Program, Vec<Diagnostic>) {
    Parser::new(source, file).parse()
}

/// Parse a standalone expression from source text.
///
/// Returns the parsed expression (if successful) and any diagnostics.
/// Emits a diagnostic if there are trailing tokens after the expression.
pub fn parse_expr(source: &str) -> (Option<Spanned<ExprKind>>, Vec<Diagnostic>) {
    let mut parser = Parser::new(source, FileId::SYNTH);
    let result = parser.parse_expr();
    match result {
        Ok(expr) => {
            if !matches!(parser.peek(), TokenKind::Eof) {
                parser.error(format!("unexpected trailing token: {:?}", parser.peek()));
            }
            let diags = parser.into_diagnostics();
            (Some(expr), diags)
        }
        Err(()) => {
            let diags = parser.into_diagnostics();
            (None, diags)
        }
    }
}

/// Result of parsing multiple source files.
pub struct ParseMultiResult {
    pub program: Program,
    pub module_map: ModuleMap,
    pub diagnostics: Vec<Diagnostic>,
    pub has_errors: bool,
}

impl ParseMultiResult {
    /// Returns program + module_map only if no errors.
    /// CLI and other callers use this before calling check_with_modules.
    pub fn ok(&self) -> Option<(&Program, &ModuleMap)> {
        if self.has_errors {
            None
        } else {
            Some((&self.program, &self.module_map))
        }
    }
}

/// Parse multiple source files, lower moves, merge, and resolve modules.
///
/// Each source is a `(filename, source_text)` pair.
/// Files are assigned `FileId(0)`, `FileId(1)`, etc.
///
/// Steps:
/// 1. Parse each file with its FileId (spans embed the file identity)
/// 2. Lower moves per file (so synthetic decls are visible to resolver)
/// 3. Merge programs into single Program
/// 4. Resolve modules (registry, validation, collision detection, visibility, desugar)
/// 5. Return merged Program + ModuleMap + all diagnostics
pub fn parse_multi(sources: &[(String, String)]) -> ParseMultiResult {
    let mut all_diagnostics: Vec<Diagnostic> = Vec::new();
    let mut file_systems_info: Vec<FileSystemInfo> = Vec::new();
    let mut programs: Vec<Program> = Vec::new();

    for (i, (_filename, source)) in sources.iter().enumerate() {
        let file = FileId(i as u32);

        let (program, mut diags) = parse(source, file);
        let program = lower_moves(program, &mut diags);

        // Extract file-system info
        let mut system_names: Vec<String> = Vec::new();
        let mut use_decls = Vec::new();
        for item in &program.items {
            match &item.node {
                TopLevel::System(s) => system_names.push(s.name.to_string()),
                TopLevel::Use(u) => use_decls.push(u.clone()),
            }
        }

        all_diagnostics.extend(diags);

        programs.push(program);
        file_systems_info.push(FileSystemInfo {
            system_names,
            use_decls,
        });
    }

    // Merge programs into single Program
    let mut merged = Program::default();
    for p in programs {
        merged.items.extend(p.items);
    }
    merged.build_index();

    // Resolve modules
    let (module_map, resolve_diags) = resolve::resolve_modules(&mut merged, &file_systems_info);
    all_diagnostics.extend(resolve_diags);

    let has_errors = all_diagnostics
        .iter()
        .any(|d| d.severity == Severity::Error);

    ParseMultiResult {
        program: merged,
        module_map,
        diagnostics: all_diagnostics,
        has_errors,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_multi_single_file() {
        let sources = vec![(
            "test.ttrpg".to_string(),
            r#"system "Core" {
    enum Ability { STR, DEX }
    derive modifier(score: int) -> int {
        floor((score - 10) / 2)
    }
}"#.to_string(),
        )];

        let result = parse_multi(&sources);
        assert!(!result.has_errors, "unexpected errors: {:?}", result.diagnostics);
        assert!(result.ok().is_some());

        let (program, map) = result.ok().unwrap();
        assert!(!program.items.is_empty());
        let core = map.systems.get("Core").unwrap();
        assert!(core.types.contains("Ability"));
        assert!(core.functions.contains("modifier"));
    }

    #[test]
    fn parse_multi_two_files_different_systems() {
        let sources = vec![
            (
                "core.ttrpg".to_string(),
                r#"system "Core" {
    enum Ability { STR, DEX }
}"#.to_string(),
            ),
            (
                "extra.ttrpg".to_string(),
                r#"system "Extra" {
    enum Size { small, medium, large }
}"#.to_string(),
            ),
        ];

        let result = parse_multi(&sources);
        assert!(!result.has_errors, "unexpected errors: {:?}", result.diagnostics);

        let (_, map) = result.ok().unwrap();
        assert!(map.systems.contains_key("Core"));
        assert!(map.systems.contains_key("Extra"));
    }

    #[test]
    fn parse_multi_cross_system_collision() {
        let sources = vec![
            (
                "a.ttrpg".to_string(),
                r#"system "A" {
    enum Ability { STR }
}"#.to_string(),
            ),
            (
                "b.ttrpg".to_string(),
                r#"system "B" {
    enum Ability { DEX }
}"#.to_string(),
            ),
        ];

        let result = parse_multi(&sources);
        assert!(result.has_errors, "expected collision error");
        assert!(result.ok().is_none());
    }

    #[test]
    fn parse_multi_use_as_parsed() {
        let sources = vec![(
            "main.ttrpg".to_string(),
            r#"use "Core" as C
system "Main" {
    derive foo() -> int { 1 }
}
system "Core" {
    derive bar() -> int { 2 }
}"#.to_string(),
        )];

        let result = parse_multi(&sources);
        assert!(!result.has_errors, "unexpected errors: {:?}", result.diagnostics);

        let (_, map) = result.ok().unwrap();
        let main_info = map.systems.get("Main").unwrap();
        assert_eq!(main_info.imports.len(), 1);
        assert_eq!(main_info.imports[0].system_name, "Core");
        assert_eq!(main_info.imports[0].alias, Some("C".into()));
    }

    #[test]
    fn parse_multi_file_ids_assigned() {
        // Items from each file should carry the correct FileId
        let sources = vec![
            (
                "a.ttrpg".to_string(),
                r#"system "A" {
    derive foo() -> int { 1 }
}"#.to_string(),
            ),
            (
                "b.ttrpg".to_string(),
                r#"system "B" {
    derive bar() -> int { 2 }
}"#.to_string(),
            ),
        ];

        let result = parse_multi(&sources);

        for item in &result.program.items {
            if let TopLevel::System(sys) = &item.node {
                if sys.name == "A" {
                    assert_eq!(
                        item.span.file, FileId(0),
                        "system A should have FileId(0), got {:?}",
                        item.span.file,
                    );
                }
                if sys.name == "B" {
                    assert_eq!(
                        item.span.file, FileId(1),
                        "system B should have FileId(1), got {:?}",
                        item.span.file,
                    );
                }
            }
        }
    }

    #[test]
    fn parse_multi_local_offsets_not_rebased() {
        // Spans should have local (file-relative) byte offsets, not rebased global ones
        let sources = vec![
            (
                "a.ttrpg".to_string(),
                r#"system "A" {
    derive foo() -> int { 1 }
}"#.to_string(),
            ),
            (
                "b.ttrpg".to_string(),
                r#"system "B" {
    derive bar() -> int { 2 }
}"#.to_string(),
            ),
        ];

        let result = parse_multi(&sources);

        for item in &result.program.items {
            if let TopLevel::System(sys) = &item.node {
                if sys.name == "B" {
                    // B's span should start at 0, not at some rebased offset
                    assert_eq!(
                        item.span.start, 0,
                        "system B's span.start should be 0 (local offset), got {}",
                        item.span.start,
                    );
                }
            }
        }
    }
}
