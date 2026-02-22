/// A parsed CLI command.
#[derive(Debug, PartialEq)]
pub enum Command {
    Load(String),
    Eval(String),
    Reload,
    Errors,
    Spawn(String),
    Set(String),
    Destroy(String),
    Do(String),
    Call(String),
    // Inspection
    Inspect(String),
    State,
    Types,
    Actions,
    Mechanics,
    Conditions,
    // Assertions
    Assert(String),
    AssertEq(String),
    AssertErr(String),
    // Configuration
    Seed(String),
    Rolls(String),
    Unknown(String),
}

/// Parse a line of input into a command.
///
/// Skips blank lines and `//`-only lines (returns `None`).
/// Comment stripping is applied per-command: `eval` expressions
/// have trailing `//` comments removed, while `load` paths are
/// taken as the first whitespace-delimited token (preserving `//`
/// that may appear in valid file paths).
pub fn parse_command(line: &str) -> Option<Command> {
    let trimmed = line.trim();
    if trimmed.is_empty() || trimmed.starts_with("//") {
        return None;
    }

    let (keyword, tail) = split_first_token(trimmed);
    match keyword {
        "load" => {
            // Take the first token as the path — paths don't contain
            // unquoted spaces, and this avoids mangling `//` in paths.
            let tail_trimmed = tail.trim_start();
            let (path, _) = split_first_token(tail_trimmed);
            if path.is_empty() {
                Some(Command::Unknown("load".into()))
            } else {
                Some(Command::Load(path.into()))
            }
        }
        "eval" => {
            let expr = strip_comment(tail).trim();
            if expr.is_empty() {
                Some(Command::Unknown("eval".into()))
            } else {
                Some(Command::Eval(expr.into()))
            }
        }
        "reload" => Some(Command::Reload),
        "errors" => Some(Command::Errors),
        "spawn" => {
            let s = strip_comment(tail).trim();
            if s.is_empty() {
                Some(Command::Unknown("spawn".into()))
            } else {
                Some(Command::Spawn(s.into()))
            }
        }
        "set" => {
            let s = strip_comment(tail).trim();
            if s.is_empty() {
                Some(Command::Unknown("set".into()))
            } else {
                Some(Command::Set(s.into()))
            }
        }
        "destroy" => {
            let s = strip_comment(tail).trim();
            if s.is_empty() {
                Some(Command::Unknown("destroy".into()))
            } else {
                Some(Command::Destroy(s.into()))
            }
        }
        "do" => {
            let s = strip_comment(tail).trim();
            if s.is_empty() {
                Some(Command::Unknown("do".into()))
            } else {
                Some(Command::Do(s.into()))
            }
        }
        "call" => {
            let s = strip_comment(tail).trim();
            if s.is_empty() {
                Some(Command::Unknown("call".into()))
            } else {
                Some(Command::Call(s.into()))
            }
        }
        // Inspection
        "inspect" => {
            let s = strip_comment(tail).trim();
            if s.is_empty() {
                Some(Command::Unknown("inspect".into()))
            } else {
                Some(Command::Inspect(s.into()))
            }
        }
        "state" => Some(Command::State),
        "types" => Some(Command::Types),
        "actions" => Some(Command::Actions),
        "mechanics" => Some(Command::Mechanics),
        "conditions" => Some(Command::Conditions),
        // Assertions
        "assert" => {
            let s = strip_comment(tail).trim();
            if s.is_empty() {
                Some(Command::Unknown("assert".into()))
            } else {
                Some(Command::Assert(s.into()))
            }
        }
        "assert_eq" => {
            let s = strip_comment(tail).trim();
            if s.is_empty() {
                Some(Command::Unknown("assert_eq".into()))
            } else {
                Some(Command::AssertEq(s.into()))
            }
        }
        "assert_err" => {
            let s = tail.trim();
            if s.is_empty() {
                Some(Command::Unknown("assert_err".into()))
            } else {
                Some(Command::AssertErr(s.into()))
            }
        }
        // Configuration
        "seed" => {
            let s = strip_comment(tail).trim();
            if s.is_empty() {
                Some(Command::Unknown("seed".into()))
            } else {
                Some(Command::Seed(s.into()))
            }
        }
        "rolls" => {
            let s = strip_comment(tail).trim();
            if s.is_empty() {
                Some(Command::Unknown("rolls".into()))
            } else {
                Some(Command::Rolls(s.into()))
            }
        }
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
        } else if bytes[i] == b'"' {
            in_string = true;
        } else if bytes[i] == b'/' && i + 1 < bytes.len() && bytes[i + 1] == b'/' {
            return &line[..i];
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
    fn load_path_with_double_slash() {
        // `//` in a file path should NOT be treated as a comment
        assert_eq!(
            parse_command("load /tmp//file.ttrpg"),
            Some(Command::Load("/tmp//file.ttrpg".into()))
        );
    }

    #[test]
    fn load_path_with_trailing_comment() {
        assert_eq!(
            parse_command("load /some/path // comment"),
            Some(Command::Load("/some/path".into()))
        );
    }

    #[test]
    fn escaped_quote_in_string() {
        assert_eq!(
            parse_command(r#"eval "say \"hi//there\"" // comment"#),
            Some(Command::Eval(r#""say \"hi//there\"""#.into()))
        );
    }

    #[test]
    fn parse_spawn() {
        assert_eq!(
            parse_command("spawn Character fighter { HP: 30 }"),
            Some(Command::Spawn("Character fighter { HP: 30 }".into()))
        );
    }

    #[test]
    fn parse_spawn_empty_is_unknown() {
        assert_eq!(
            parse_command("spawn"),
            Some(Command::Unknown("spawn".into()))
        );
    }

    #[test]
    fn parse_set() {
        assert_eq!(
            parse_command("set fighter.AC = 18"),
            Some(Command::Set("fighter.AC = 18".into()))
        );
    }

    #[test]
    fn parse_set_empty_is_unknown() {
        assert_eq!(
            parse_command("set"),
            Some(Command::Unknown("set".into()))
        );
    }

    #[test]
    fn parse_destroy() {
        assert_eq!(
            parse_command("destroy goblin"),
            Some(Command::Destroy("goblin".into()))
        );
    }

    #[test]
    fn parse_destroy_empty_is_unknown() {
        assert_eq!(
            parse_command("destroy"),
            Some(Command::Unknown("destroy".into()))
        );
    }

    #[test]
    fn parse_do() {
        assert_eq!(
            parse_command("do Attack(fighter, goblin)"),
            Some(Command::Do("Attack(fighter, goblin)".into()))
        );
    }

    #[test]
    fn parse_do_empty_is_unknown() {
        assert_eq!(
            parse_command("do"),
            Some(Command::Unknown("do".into()))
        );
    }

    #[test]
    fn parse_call() {
        assert_eq!(
            parse_command("call modifier(16)"),
            Some(Command::Call("modifier(16)".into()))
        );
    }

    #[test]
    fn parse_call_empty_is_unknown() {
        assert_eq!(
            parse_command("call"),
            Some(Command::Unknown("call".into()))
        );
    }

    #[test]
    fn parse_spawn_with_comment() {
        assert_eq!(
            parse_command("spawn Character fighter { HP: 30 } // create fighter"),
            Some(Command::Spawn("Character fighter { HP: 30 }".into()))
        );
    }

    #[test]
    fn parse_do_with_comment() {
        assert_eq!(
            parse_command("do Attack(fighter, goblin) // attack!"),
            Some(Command::Do("Attack(fighter, goblin)".into()))
        );
    }

    // ── Phase 3: Inspection commands ─────────────────────────────

    #[test]
    fn parse_inspect() {
        assert_eq!(
            parse_command("inspect fighter.HP"),
            Some(Command::Inspect("fighter.HP".into()))
        );
    }

    #[test]
    fn parse_inspect_empty_is_unknown() {
        assert_eq!(
            parse_command("inspect"),
            Some(Command::Unknown("inspect".into()))
        );
    }

    #[test]
    fn parse_state() {
        assert_eq!(parse_command("state"), Some(Command::State));
    }

    #[test]
    fn parse_types() {
        assert_eq!(parse_command("types"), Some(Command::Types));
    }

    #[test]
    fn parse_actions() {
        assert_eq!(parse_command("actions"), Some(Command::Actions));
    }

    #[test]
    fn parse_mechanics() {
        assert_eq!(parse_command("mechanics"), Some(Command::Mechanics));
    }

    #[test]
    fn parse_conditions() {
        assert_eq!(parse_command("conditions"), Some(Command::Conditions));
    }

    // ── Phase 3: Assertion commands ──────────────────────────────

    #[test]
    fn parse_assert() {
        assert_eq!(
            parse_command("assert 2 + 3 == 5"),
            Some(Command::Assert("2 + 3 == 5".into()))
        );
    }

    #[test]
    fn parse_assert_empty_is_unknown() {
        assert_eq!(
            parse_command("assert"),
            Some(Command::Unknown("assert".into()))
        );
    }

    #[test]
    fn parse_assert_eq() {
        assert_eq!(
            parse_command("assert_eq 2 + 3, 5"),
            Some(Command::AssertEq("2 + 3, 5".into()))
        );
    }

    #[test]
    fn parse_assert_eq_empty_is_unknown() {
        assert_eq!(
            parse_command("assert_eq"),
            Some(Command::Unknown("assert_eq".into()))
        );
    }

    #[test]
    fn parse_assert_err() {
        assert_eq!(
            parse_command("assert_err destroy nonexistent"),
            Some(Command::AssertErr("destroy nonexistent".into()))
        );
    }

    #[test]
    fn parse_assert_err_empty_is_unknown() {
        assert_eq!(
            parse_command("assert_err"),
            Some(Command::Unknown("assert_err".into()))
        );
    }

    // ── Phase 3: Configuration commands ──────────────────────────

    #[test]
    fn parse_seed() {
        assert_eq!(
            parse_command("seed 42"),
            Some(Command::Seed("42".into()))
        );
    }

    #[test]
    fn parse_seed_empty_is_unknown() {
        assert_eq!(
            parse_command("seed"),
            Some(Command::Unknown("seed".into()))
        );
    }

    #[test]
    fn parse_rolls() {
        assert_eq!(
            parse_command("rolls 3 5 2"),
            Some(Command::Rolls("3 5 2".into()))
        );
    }

    #[test]
    fn parse_rolls_empty_is_unknown() {
        assert_eq!(
            parse_command("rolls"),
            Some(Command::Unknown("rolls".into()))
        );
    }

    #[test]
    fn parse_rolls_clear() {
        assert_eq!(
            parse_command("rolls clear"),
            Some(Command::Rolls("clear".into()))
        );
    }
}
