use reedline::{ValidationResult, Validator};

/// Validates whether a line of input is complete or needs continuation.
///
/// Returns `Incomplete` when delimiters (`{`, `(`, `[`) are unclosed,
/// allowing multiline input for spawn blocks and expressions.
pub struct TtrpgValidator;

impl Validator for TtrpgValidator {
    fn validate(&self, line: &str) -> ValidationResult {
        if has_unclosed_delimiters(line) {
            ValidationResult::Incomplete
        } else {
            ValidationResult::Complete
        }
    }
}

/// Counts unmatched `{`, `(`, `[` (respecting string literals).
fn has_unclosed_delimiters(line: &str) -> bool {
    let mut depth = 0i32;
    let mut in_string = false;
    let bytes = line.as_bytes();
    let mut i = 0;

    while i < bytes.len() {
        if in_string {
            if bytes[i] == b'\\' {
                i += 2;
                continue;
            }
            if bytes[i] == b'"' {
                in_string = false;
            }
        } else {
            match bytes[i] {
                b'"' => in_string = true,
                b'(' | b'[' | b'{' => depth += 1,
                b')' | b']' | b'}' => depth -= 1,
                b'/' if i + 1 < bytes.len() && bytes[i + 1] == b'/' => {
                    // Line comment — skip to end of line
                    while i < bytes.len() && bytes[i] != b'\n' {
                        i += 1;
                    }
                    continue;
                }
                _ => {}
            }
        }
        i += 1;
    }

    // Also incomplete if we're inside an unterminated string
    in_string || depth > 0
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn complete_simple() {
        let v = TtrpgValidator;
        assert!(matches!(v.validate("eval 2 + 3"), ValidationResult::Complete));
    }

    #[test]
    fn complete_empty() {
        let v = TtrpgValidator;
        assert!(matches!(v.validate(""), ValidationResult::Complete));
    }

    #[test]
    fn incomplete_open_brace() {
        let v = TtrpgValidator;
        assert!(matches!(
            v.validate("spawn Character fighter {"),
            ValidationResult::Incomplete
        ));
    }

    #[test]
    fn complete_matched_braces() {
        let v = TtrpgValidator;
        assert!(matches!(
            v.validate("spawn Character fighter { HP: 30 }"),
            ValidationResult::Complete
        ));
    }

    #[test]
    fn incomplete_open_paren() {
        let v = TtrpgValidator;
        assert!(matches!(
            v.validate("do Attack(fighter"),
            ValidationResult::Incomplete
        ));
    }

    #[test]
    fn incomplete_open_bracket() {
        let v = TtrpgValidator;
        assert!(matches!(
            v.validate("eval [1, 2"),
            ValidationResult::Incomplete
        ));
    }

    #[test]
    fn complete_nested() {
        let v = TtrpgValidator;
        assert!(matches!(
            v.validate("eval f([1, 2], {a: 3})"),
            ValidationResult::Complete
        ));
    }

    #[test]
    fn string_with_braces_not_counted() {
        let v = TtrpgValidator;
        assert!(matches!(
            v.validate(r#"eval "open { brace""#),
            ValidationResult::Complete
        ));
    }

    #[test]
    fn unterminated_string() {
        let v = TtrpgValidator;
        assert!(matches!(
            v.validate(r#"eval "hello"#),
            ValidationResult::Incomplete
        ));
    }

    #[test]
    fn escaped_quote_in_string() {
        let v = TtrpgValidator;
        assert!(matches!(
            v.validate(r#"eval "say \"hi\"""#),
            ValidationResult::Complete
        ));
    }

    #[test]
    fn multiline_complete() {
        let v = TtrpgValidator;
        assert!(matches!(
            v.validate("spawn Character fighter {\n  HP: 30,\n  AC: 15\n}"),
            ValidationResult::Complete
        ));
    }

    #[test]
    fn multiline_incomplete() {
        let v = TtrpgValidator;
        assert!(matches!(
            v.validate("spawn Character fighter {\n  HP: 30,"),
            ValidationResult::Incomplete
        ));
    }

    #[test]
    fn comment_with_open_brace_ignored() {
        let v = TtrpgValidator;
        assert!(matches!(
            v.validate("eval 2 + 3 // open {"),
            ValidationResult::Complete
        ));
    }
}
