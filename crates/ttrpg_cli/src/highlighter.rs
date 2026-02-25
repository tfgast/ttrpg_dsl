use reedline::{Highlighter, StyledText};
use nu_ansi_term::{Color, Style};
use ttrpg_lexer::RawLexer;
use ttrpg_lexer::token::TokenKind;

/// CLI command names that get special highlighting.
const CLI_COMMANDS: &[&str] = &[
    "load", "eval", "reload", "errors",
    "spawn", "set", "destroy", "do", "call",
    "grant", "revoke",
    "inspect", "state", "types", "actions", "mechanics", "conditions",
    "assert", "assert_eq", "assert_err",
    "seed", "rolls",
];

/// Syntax highlighter for the TTRPG REPL.
///
/// Uses the DSL lexer to tokenize input and applies color based on
/// token kind. The first word is checked against CLI command names
/// and highlighted specially.
pub struct TtrpgHighlighter;

impl Highlighter for TtrpgHighlighter {
    fn highlight(&self, line: &str, _cursor: usize) -> StyledText {
        let mut styled = StyledText::new();

        if line.is_empty() {
            return styled;
        }

        // Detect the first word to check if it's a CLI command
        let first_word = line.split_whitespace().next().unwrap_or("");
        let is_cli_cmd = CLI_COMMANDS.contains(&first_word);

        let mut last_end = 0;
        let mut is_first_token = true;

        for token in RawLexer::new(line) {
            let start = token.span.start;
            let end = token.span.end;

            if matches!(token.kind, TokenKind::Eof) {
                break;
            }

            // Handle gaps between tokens (whitespace and comments)
            if start > last_end {
                let gap = &line[last_end..start];
                // Check if the gap contains a comment
                if let Some(comment_start) = gap.find("//") {
                    // Text before the comment (whitespace)
                    let before_comment = &gap[..comment_start];
                    if !before_comment.is_empty() {
                        styled.push((Style::default(), before_comment.to_string()));
                    }
                    // The comment itself
                    let comment_text = &gap[comment_start..];
                    styled.push((Color::DarkGray.normal(), comment_text.to_string()));
                } else {
                    styled.push((Style::default(), gap.to_string()));
                }
            }

            let text = &line[start..end];
            let style = token_style(&token.kind, is_cli_cmd && is_first_token);
            is_first_token = false;

            styled.push((style, text.to_string()));
            last_end = end;
        }

        // Handle any trailing content after the last token (trailing comments)
        if last_end < line.len() {
            let trailing = &line[last_end..];
            if let Some(comment_start) = trailing.find("//") {
                let before = &trailing[..comment_start];
                if !before.is_empty() {
                    styled.push((Style::default(), before.to_string()));
                }
                let comment = &trailing[comment_start..];
                styled.push((Color::DarkGray.normal(), comment.to_string()));
            } else {
                styled.push((Style::default(), trailing.to_string()));
            }
        }

        styled
    }
}

/// Map a token kind to its display style.
fn token_style(kind: &TokenKind, is_first_cli_command: bool) -> Style {
    match kind {
        // CLI commands (first word only)
        TokenKind::Ident(_) if is_first_cli_command => Color::Cyan.bold(),

        // DSL keywords
        TokenKind::If | TokenKind::Else | TokenKind::Match | TokenKind::Let | TokenKind::In | TokenKind::For => {
            Color::Blue.bold()
        }

        // Literals
        TokenKind::True | TokenKind::False | TokenKind::None => Color::Yellow.normal(),
        TokenKind::Int(_) => Color::Magenta.normal(),
        TokenKind::String(_) => Color::Green.normal(),
        TokenKind::Dice { .. } | TokenKind::UnitLiteral { .. } => Color::Magenta.bold(),

        // Errors
        TokenKind::Error(_) => Color::Red.bold(),

        // Everything else (operators, identifiers, punctuation)
        _ => Style::default(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn highlight_empty() {
        let h = TtrpgHighlighter;
        let result = h.highlight("", 0);
        assert_eq!(result.buffer.len(), 0);
    }

    #[test]
    fn highlight_cli_command() {
        let h = TtrpgHighlighter;
        let result = h.highlight("eval 2 + 3", 0);
        // First segment should be the CLI command in bold cyan
        assert!(!result.buffer.is_empty());
        let (style, text) = &result.buffer[0];
        assert_eq!(text, "eval");
        assert_eq!(*style, Color::Cyan.bold());
    }

    #[test]
    fn highlight_integer() {
        let h = TtrpgHighlighter;
        let result = h.highlight("42", 0);
        let (style, text) = &result.buffer[0];
        assert_eq!(text, "42");
        assert_eq!(*style, Color::Magenta.normal());
    }

    #[test]
    fn highlight_string() {
        let h = TtrpgHighlighter;
        let result = h.highlight(r#""hello""#, 0);
        let (style, text) = &result.buffer[0];
        assert_eq!(text, r#""hello""#);
        assert_eq!(*style, Color::Green.normal());
    }

    #[test]
    fn highlight_keyword() {
        let h = TtrpgHighlighter;
        let result = h.highlight("if", 0);
        let (style, text) = &result.buffer[0];
        assert_eq!(text, "if");
        assert_eq!(*style, Color::Blue.bold());
    }

    #[test]
    fn highlight_bool() {
        let h = TtrpgHighlighter;
        let result = h.highlight("true", 0);
        let (style, text) = &result.buffer[0];
        assert_eq!(text, "true");
        assert_eq!(*style, Color::Yellow.normal());
    }

    #[test]
    fn highlight_dice() {
        let h = TtrpgHighlighter;
        let result = h.highlight("2d6", 0);
        let (style, text) = &result.buffer[0];
        assert_eq!(text, "2d6");
        assert_eq!(*style, Color::Magenta.bold());
    }

    // ── Regression: tdsl-d51v / tdsl-i0i — leading whitespace highlighting ──

    #[test]
    fn highlight_cli_command_with_leading_whitespace() {
        let h = TtrpgHighlighter;
        let result = h.highlight("  eval 2 + 3", 0);
        // First segment is leading whitespace, second should be the command
        let cmd_segment = result.buffer.iter().find(|(_, text)| text == "eval");
        assert!(cmd_segment.is_some(), "eval should appear in output");
        let (style, _) = cmd_segment.unwrap();
        assert_eq!(*style, Color::Cyan.bold(), "eval should be highlighted as CLI command even with leading whitespace");
    }

    #[test]
    fn highlight_non_command_ident() {
        let h = TtrpgHighlighter;
        let result = h.highlight("fighter", 0);
        // "fighter" is not a CLI command, so default style
        let (style, text) = &result.buffer[0];
        assert_eq!(text, "fighter");
        assert_eq!(*style, Style::default());
    }
}
