//! Validates that all fenced code blocks in `doc/ai_authoring.md` are correct.
//!
//! - ` ```ttrpg ` blocks must parse and type-check with zero errors.
//! - ` ```ttrpg-err ` blocks must produce at least one error.
//!
//! This keeps the AI authoring guide in sync with the language as it evolves.

use ttrpg_ast::diagnostic::{Severity, SourceMap};
use ttrpg_ast::FileId;

static AI_AUTHORING_MD: &str = include_str!("../../../doc/ai_authoring.md");

/// Extract fenced code blocks with a given info string from markdown.
fn extract_blocks<'a>(md: &'a str, info_string: &str) -> Vec<(usize, &'a str)> {
    let fence = format!("```{info_string}");
    let mut blocks = Vec::new();
    let mut lines = md.lines().enumerate().peekable();

    while let Some((line_no, line)) = lines.next() {
        let trimmed = line.trim();
        // Match the exact info string (not a prefix — "ttrpg" must not match "ttrpg-err")
        if trimmed.starts_with(&fence) {
            let after_fence = &trimmed[fence.len()..];
            if !after_fence.is_empty() && !after_fence.starts_with(' ') {
                // Info string continues (e.g., "ttrpg-err" when looking for "ttrpg")
                continue;
            }
            let mut body = String::new();
            for (_inner_no, inner_line) in lines.by_ref() {
                if inner_line.trim() == "```" {
                    break;
                }
                if !body.is_empty() {
                    body.push('\n');
                }
                body.push_str(inner_line);
            }
            // Store owned string via leak for test lifetime (acceptable in tests)
            blocks.push((line_no + 1, &*Box::leak(body.into_boxed_str())));
        }
    }
    blocks
}

fn check_snippet(source: &str) -> Vec<String> {
    let wrapped = format!("system \"<snippet>\" {{\n{source}\n}}\n");
    let (program, parse_errors) = ttrpg_parser::parse(&wrapped, FileId::SYNTH);

    let sm = SourceMap::new(&wrapped);
    let mut errors: Vec<String> = parse_errors
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .map(|d| sm.render(d))
        .collect();

    if parse_errors.iter().any(|d| d.severity == Severity::Error) {
        return errors;
    }

    let result = ttrpg_checker::check(&program);
    errors.extend(
        result
            .diagnostics
            .iter()
            .filter(|d| d.severity == Severity::Error)
            .map(|d| sm.render(d)),
    );
    errors
}

#[test]
fn valid_snippets_pass_check() {
    let blocks = extract_blocks(AI_AUTHORING_MD, "ttrpg");
    assert!(
        !blocks.is_empty(),
        "no ```ttrpg blocks found in ai_authoring.md"
    );

    let mut failures = Vec::new();
    for (line, snippet) in &blocks {
        let errors = check_snippet(snippet);
        if !errors.is_empty() {
            failures.push(format!(
                "--- line {line} ---\n{snippet}\n\nErrors:\n{}",
                errors.join("\n")
            ));
        }
    }

    if !failures.is_empty() {
        panic!(
            "{} valid snippet(s) failed:\n\n{}",
            failures.len(),
            failures.join("\n\n")
        );
    }
}

#[test]
fn invalid_snippets_produce_errors() {
    let blocks = extract_blocks(AI_AUTHORING_MD, "ttrpg-err");
    assert!(
        !blocks.is_empty(),
        "no ```ttrpg-err blocks found in ai_authoring.md"
    );

    let mut failures = Vec::new();
    for (line, snippet) in &blocks {
        let errors = check_snippet(snippet);
        if errors.is_empty() {
            failures.push(format!(
                "--- line {line} ---\n{snippet}\n\nExpected at least one error, got none"
            ));
        }
    }

    if !failures.is_empty() {
        panic!(
            "{} error snippet(s) passed unexpectedly:\n\n{}",
            failures.len(),
            failures.join("\n\n")
        );
    }
}
