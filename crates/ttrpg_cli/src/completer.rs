use std::sync::{Arc, Mutex};

use reedline::{Completer, Suggestion, Span};

/// All CLI command names.
const ALL_COMMANDS: &[&str] = &[
    "load", "eval", "reload", "errors",
    "spawn", "set", "destroy", "do", "call",
    "inspect", "state", "types", "actions", "mechanics", "conditions",
    "assert", "assert_eq", "assert_err",
    "seed", "rolls",
];

/// DSL keywords useful in expression contexts.
const DSL_KEYWORDS: &[&str] = &[
    "if", "else", "match", "let", "in", "for",
    "true", "false", "none",
];

/// Dynamic completion data refreshed after each command execution.
#[derive(Default)]
pub struct CompletionContext {
    pub handles: Vec<String>,
    pub entity_types: Vec<String>,
    pub action_names: Vec<String>,
    pub derive_names: Vec<String>,
    pub mechanic_names: Vec<String>,
}

/// Context-aware tab completer for the TTRPG REPL.
pub struct TtrpgCompleter {
    ctx: Arc<Mutex<CompletionContext>>,
}

impl TtrpgCompleter {
    pub fn new(ctx: Arc<Mutex<CompletionContext>>) -> Self {
        Self { ctx }
    }
}

/// Build a Suggestion value.
fn suggestion(value: String, span: Span, append_whitespace: bool) -> Suggestion {
    Suggestion {
        value,
        description: None,
        style: None,
        extra: None,
        span,
        append_whitespace,
        match_indices: None,
    }
}

impl Completer for TtrpgCompleter {
    fn complete(&mut self, line: &str, pos: usize) -> Vec<Suggestion> {
        let line_to_cursor = &line[..pos];
        let trimmed = line_to_cursor.trim_start();

        if trimmed.is_empty() {
            // No input yet — suggest all commands
            return ALL_COMMANDS
                .iter()
                .map(|cmd| suggestion(cmd.to_string(), Span::new(pos, pos), true))
                .collect();
        }

        // Find the first word and the rest
        let (first_word, after_first) = split_first_word(trimmed);

        if after_first.is_none() {
            // Still typing the first word — prefix-match commands
            let offset = line_to_cursor.len() - trimmed.len();
            return prefix_matches(ALL_COMMANDS, first_word)
                .into_iter()
                .map(|cmd| suggestion(cmd.to_string(), Span::new(offset, pos), true))
                .collect();
        }

        let rest = after_first.unwrap();
        let ctx = self.ctx.lock().unwrap();

        match first_word {
            "spawn" => {
                // After spawn: complete entity type names
                let (current, _) = split_first_word(rest);
                let word_start = pos - current.len();
                prefix_matches_owned(&ctx.entity_types, current)
                    .into_iter()
                    .map(|s| suggestion(s, Span::new(word_start, pos), true))
                    .collect()
            }
            "do" => {
                // After do: complete action names (before '(')
                let before_paren = rest.split('(').next().unwrap_or(rest);
                let current = before_paren.trim();
                let word_start = pos - current.len();
                prefix_matches_owned(&ctx.action_names, current)
                    .into_iter()
                    .map(|s| suggestion(s, Span::new(word_start, pos), false))
                    .collect()
            }
            "call" => {
                // After call: complete derive + mechanic names (before '(')
                let before_paren = rest.split('(').next().unwrap_or(rest);
                let current = before_paren.trim();
                let word_start = pos - current.len();
                let mut candidates: Vec<String> = Vec::new();
                candidates.extend(ctx.derive_names.iter().cloned());
                candidates.extend(ctx.mechanic_names.iter().cloned());
                prefix_matches_owned(&candidates, current)
                    .into_iter()
                    .map(|s| suggestion(s, Span::new(word_start, pos), false))
                    .collect()
            }
            "set" | "inspect" | "destroy" => {
                // Complete handle names
                let current_word = last_word(rest);
                let word_start = pos - current_word.len();

                if current_word.contains('.') {
                    // After handle.field — no completions for now
                    Vec::new()
                } else {
                    prefix_matches_owned(&ctx.handles, current_word)
                        .into_iter()
                        .map(|s| suggestion(s, Span::new(word_start, pos), first_word != "set"))
                        .collect()
                }
            }
            "eval" | "assert" | "assert_eq" => {
                // Complete handles + DSL keywords
                let current_word = last_word(rest);
                let word_start = pos - current_word.len();
                let mut suggestions: Vec<Suggestion> = Vec::new();

                for s in prefix_matches_owned(&ctx.handles, current_word) {
                    suggestions.push(suggestion(s, Span::new(word_start, pos), true));
                }

                for kw in prefix_matches(DSL_KEYWORDS, current_word) {
                    suggestions.push(suggestion(kw.to_string(), Span::new(word_start, pos), true));
                }

                suggestions
            }
            _ => Vec::new(),
        }
    }
}

/// Split into first whitespace-delimited word and the rest (if any).
fn split_first_word(s: &str) -> (&str, Option<&str>) {
    let s = s.trim_start();
    match s.find(char::is_whitespace) {
        Some(pos) => (&s[..pos], Some(s[pos..].trim_start())),
        None => (s, None),
    }
}

/// Get the last whitespace-delimited word being typed.
fn last_word(s: &str) -> &str {
    s.rsplit(|c: char| c.is_whitespace() || c == ',' || c == '(')
        .next()
        .unwrap_or(s)
}

/// Prefix-match against a list of static strings.
fn prefix_matches<'a>(candidates: &[&'a str], prefix: &str) -> Vec<&'a str> {
    if prefix.is_empty() {
        return candidates.to_vec();
    }
    candidates
        .iter()
        .filter(|c| c.starts_with(prefix))
        .copied()
        .collect()
}

/// Prefix-match against a list of owned strings.
fn prefix_matches_owned(candidates: &[String], prefix: &str) -> Vec<String> {
    if prefix.is_empty() {
        return candidates.to_vec();
    }
    candidates
        .iter()
        .filter(|c| c.starts_with(prefix))
        .cloned()
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_ctx() -> Arc<Mutex<CompletionContext>> {
        Arc::new(Mutex::new(CompletionContext {
            handles: vec!["fighter".into(), "goblin".into()],
            entity_types: vec!["Character".into(), "Monster".into()],
            action_names: vec!["Attack".into(), "Heal".into()],
            derive_names: vec!["modifier".into()],
            mechanic_names: vec!["add".into()],
        }))
    }

    #[test]
    fn complete_empty_gives_all_commands() {
        let ctx = make_ctx();
        let mut c = TtrpgCompleter::new(ctx);
        let results = c.complete("", 0);
        assert_eq!(results.len(), ALL_COMMANDS.len());
    }

    #[test]
    fn complete_partial_command() {
        let ctx = make_ctx();
        let mut c = TtrpgCompleter::new(ctx);
        let results = c.complete("sp", 2);
        let values: Vec<_> = results.iter().map(|s| s.value.as_str()).collect();
        assert!(values.contains(&"spawn"));
        assert!(!values.contains(&"eval"));
    }

    #[test]
    fn complete_spawn_entity_types() {
        let ctx = make_ctx();
        let mut c = TtrpgCompleter::new(ctx);
        let results = c.complete("spawn C", 7);
        let values: Vec<_> = results.iter().map(|s| s.value.as_str()).collect();
        assert!(values.contains(&"Character"));
        assert!(!values.contains(&"Monster"));
    }

    #[test]
    fn complete_do_actions() {
        let ctx = make_ctx();
        let mut c = TtrpgCompleter::new(ctx);
        let results = c.complete("do A", 4);
        let values: Vec<_> = results.iter().map(|s| s.value.as_str()).collect();
        assert!(values.contains(&"Attack"));
    }

    #[test]
    fn complete_call_functions() {
        let ctx = make_ctx();
        let mut c = TtrpgCompleter::new(ctx);
        let results = c.complete("call ", 5);
        let values: Vec<_> = results.iter().map(|s| s.value.as_str()).collect();
        assert!(values.contains(&"modifier"));
        assert!(values.contains(&"add"));
    }

    #[test]
    fn complete_inspect_handles() {
        let ctx = make_ctx();
        let mut c = TtrpgCompleter::new(ctx);
        let results = c.complete("inspect f", 9);
        let values: Vec<_> = results.iter().map(|s| s.value.as_str()).collect();
        assert!(values.contains(&"fighter"));
    }

    #[test]
    fn complete_eval_handles_and_keywords() {
        let ctx = make_ctx();
        let mut c = TtrpgCompleter::new(ctx);
        let results = c.complete("eval f", 6);
        let values: Vec<_> = results.iter().map(|s| s.value.as_str()).collect();
        assert!(values.contains(&"fighter"));
        assert!(values.contains(&"false"));
    }
}
