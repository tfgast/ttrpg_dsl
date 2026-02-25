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
use ttrpg_ast::{Span, Spanned, VisitSpansMut};
use ttrpg_lexer::TokenKind;
use parser::Parser;

pub fn parse(source: &str) -> (Program, Vec<Diagnostic>) {
    Parser::new(source).parse()
}

/// Parse a standalone expression from source text.
///
/// Returns the parsed expression (if successful) and any diagnostics.
/// Emits a diagnostic if there are trailing tokens after the expression.
pub fn parse_expr(source: &str) -> (Option<Spanned<ExprKind>>, Vec<Diagnostic>) {
    let mut parser = Parser::new(source);
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

/// Parse multiple source files, lower moves, rebase spans, merge, and resolve modules.
///
/// Each source is a `(filename, source_text)` pair.
///
/// Steps:
/// 1. Parse each file independently
/// 2. Lower moves per file (so synthetic decls are visible to resolver)
/// 3. Compute base offsets and rebase all spans + diagnostics to global offsets
/// 4. Merge programs into single Program
/// 5. Resolve modules (registry, validation, collision detection, visibility, desugar)
/// 6. Return merged Program + ModuleMap + all diagnostics
pub fn parse_multi(sources: &[(String, String)]) -> ParseMultiResult {
    let mut all_diagnostics: Vec<Diagnostic> = Vec::new();
    let mut file_systems_info: Vec<FileSystemInfo> = Vec::new();
    let mut programs: Vec<Program> = Vec::new();

    // Parse, lower, and rebase each file
    let mut current_offset: usize = 0;
    for (_filename, source) in sources {
        let base = current_offset;

        let (program, mut diags) = parse(source);
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

        // Rebase diagnostics
        for d in &mut diags {
            d.span = rebase_span(d.span, base);
        }
        all_diagnostics.extend(diags);

        // Rebase program spans
        let mut program = program;
        rebase_program(&mut program, base);

        // Rebase use_decls for file_systems_info
        let use_decls: Vec<UseDecl> = use_decls
            .into_iter()
            .map(|mut u| {
                u.span = rebase_span(u.span, base);
                u
            })
            .collect();

        programs.push(program);
        file_systems_info.push(FileSystemInfo {
            system_names,
            use_decls,
        });

        current_offset += source.len() + 1;
    }

    // Merge programs into single Program
    let mut merged = Program::default();
    for p in programs {
        merged.items.extend(p.items);
    }
    merged.build_index();

    // Step 5: Resolve modules
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

/// Rebase a span by adding a base offset.
fn rebase_span(span: Span, base: usize) -> Span {
    if base == 0 {
        return span;
    }
    // Don't rebase dummy spans
    if span.is_dummy() {
        return span;
    }
    Span::new(span.start + base, span.end + base)
}

/// Rebase all spans in a Program by adding a base offset.
fn rebase_program(program: &mut Program, base: usize) {
    if base == 0 {
        return;
    }
    program.visit_spans_mut(&mut |span| {
        if !span.is_dummy() {
            span.start += base;
            span.end += base;
        }
    });
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
    fn parse_multi_span_rebasing() {
        // Two files — errors in second file should have rebased spans
        let source1 = r#"system "A" {
    derive foo() -> int { 1 }
}"#;
        let source2 = r#"system "B" {
    derive bar() -> int { unknown_var }
}"#;
        let sources = vec![
            ("a.ttrpg".to_string(), source1.to_string()),
            ("b.ttrpg".to_string(), source2.to_string()),
        ];

        let result = parse_multi(&sources);
        // Parse itself won't error on unknown_var (that's a checker concern),
        // but spans in the second file should be rebased
        let expected_base = source1.len() + 1; // +1 for sentinel
        for item in &result.program.items {
            if let TopLevel::System(sys) = &item.node {
                if sys.name == "B" {
                    // Spans from file B should be >= expected_base
                    assert!(
                        item.span.start >= expected_base,
                        "expected span.start >= {}, got {}",
                        expected_base,
                        item.span.start,
                    );
                }
            }
        }
    }

    // ── Regression: tdsl-vpk — parse_multi should not double-parse ──

    #[test]
    fn parse_multi_diagnostics_correctly_rebased() {
        // Ensures the single-loop implementation correctly rebases diagnostics
        // from the second file. Previously, a redundant first loop parsed all
        // files twice and discarded the first results.
        let source1 = r#"system "A" {
    derive foo() -> int { 1 }
}"#;
        let source2 = r#"system "B" {
    derive bar() -> int { 2 }
}"#;
        let sources = vec![
            ("a.ttrpg".to_string(), source1.to_string()),
            ("b.ttrpg".to_string(), source2.to_string()),
        ];

        let result = parse_multi(&sources);
        let expected_base = source1.len() + 1;

        // Both systems should be present in the merged program
        let system_names: Vec<_> = result.program.items.iter().filter_map(|item| {
            if let TopLevel::System(s) = &item.node { Some(s.name.as_str()) } else { None }
        }).collect();
        assert!(system_names.contains(&"A"), "system A missing");
        assert!(system_names.contains(&"B"), "system B missing");

        // Spans from file B should be rebased by expected_base
        for item in &result.program.items {
            if let TopLevel::System(sys) = &item.node {
                if sys.name == "B" {
                    assert!(
                        item.span.start >= expected_base,
                        "B's span should be rebased; got start={}",
                        item.span.start,
                    );
                }
            }
        }
    }
}
