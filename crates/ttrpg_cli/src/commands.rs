/// A parsed CLI command.
#[derive(Debug, PartialEq)]
pub enum Command {
    Load(String),
    Eval(String),
    Reload,
    Errors,
    Unknown(String),
}

/// Parse a line of input into a command.
///
/// Strips `//` comments, skips blank lines (returns `None`),
/// and splits on the first whitespace token.
pub fn parse_command(line: &str) -> Option<Command> {
    let stripped = strip_comment(line);
    let trimmed = stripped.trim();
    if trimmed.is_empty() {
        return None;
    }

    let (keyword, tail) = split_first_token(trimmed);
    match keyword {
        "load" => {
            let path = tail.trim();
            if path.is_empty() {
                Some(Command::Unknown("load".into()))
            } else {
                Some(Command::Load(path.into()))
            }
        }
        "eval" => {
            let expr = tail.trim();
            if expr.is_empty() {
                Some(Command::Unknown("eval".into()))
            } else {
                Some(Command::Eval(expr.into()))
            }
        }
        "reload" => Some(Command::Reload),
        "errors" => Some(Command::Errors),
        _ => Some(Command::Unknown(keyword.into())),
    }
}

/// Strip a `//` line comment, skipping `//` inside string literals.
fn strip_comment(line: &str) -> &str {
    let bytes = line.as_bytes();
    let mut in_string = false;
    let mut i = 0;
    while i < bytes.len() {
        if in_string {
            if bytes[i] == b'\\' {
                i += 2; // skip escaped character
                continue;
            }
            if bytes[i] == b'"' {
                in_string = false;
            }
        } else {
            if bytes[i] == b'"' {
                in_string = true;
            } else if bytes[i] == b'/' && i + 1 < bytes.len() && bytes[i + 1] == b'/' {
                return &line[..i];
            }
        }
        i += 1;
    }
    line
}

/// Split a trimmed line into the first whitespace-delimited token and the rest.
fn split_first_token(s: &str) -> (&str, &str) {
    match s.find(char::is_whitespace) {
        Some(pos) => (&s[..pos], &s[pos + 1..]),
        None => (s, ""),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_load() {
        assert_eq!(
            parse_command("load spec/v0/04_full_example.ttrpg"),
            Some(Command::Load("spec/v0/04_full_example.ttrpg".into()))
        );
    }

    #[test]
    fn parse_eval() {
        assert_eq!(
            parse_command("eval 2 + 3"),
            Some(Command::Eval("2 + 3".into()))
        );
    }

    #[test]
    fn parse_reload() {
        assert_eq!(parse_command("reload"), Some(Command::Reload));
    }

    #[test]
    fn parse_errors() {
        assert_eq!(parse_command("errors"), Some(Command::Errors));
    }

    #[test]
    fn parse_unknown() {
        assert_eq!(
            parse_command("foobar"),
            Some(Command::Unknown("foobar".into()))
        );
    }

    #[test]
    fn blank_line_returns_none() {
        assert_eq!(parse_command(""), None);
        assert_eq!(parse_command("   "), None);
    }

    #[test]
    fn comment_only_returns_none() {
        assert_eq!(parse_command("// this is a comment"), None);
    }

    #[test]
    fn comment_after_command() {
        assert_eq!(
            parse_command("eval 2 + 3 // inline comment"),
            Some(Command::Eval("2 + 3".into()))
        );
    }

    #[test]
    fn load_without_path_is_unknown() {
        assert_eq!(
            parse_command("load"),
            Some(Command::Unknown("load".into()))
        );
    }

    #[test]
    fn eval_without_expr_is_unknown() {
        assert_eq!(
            parse_command("eval"),
            Some(Command::Unknown("eval".into()))
        );
    }

    #[test]
    fn comment_inside_string_preserved() {
        // `//` inside a string literal should NOT be treated as a comment
        assert_eq!(
            parse_command(r#"eval "https://example.com""#),
            Some(Command::Eval(r#""https://example.com""#.into()))
        );
    }

    #[test]
    fn comment_after_string_with_slashes() {
        assert_eq!(
            parse_command(r#"eval "a//b" // real comment"#),
            Some(Command::Eval(r#""a//b""#.into()))
        );
    }

    #[test]
    fn escaped_quote_in_string() {
        assert_eq!(
            parse_command(r#"eval "say \"hi//there\"" // comment"#),
            Some(Command::Eval(r#""say \"hi//there\"""#.into()))
        );
    }
}
