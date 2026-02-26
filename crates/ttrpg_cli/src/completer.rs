use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use reedline::{Completer, Span, Suggestion};

/// All CLI command names.
const ALL_COMMANDS: &[&str] = &[
    "load",
    "eval",
    "reload",
    "errors",
    "spawn",
    "set",
    "destroy",
    "do",
    "call",
    "grant",
    "revoke",
    "inspect",
    "state",
    "types",
    "actions",
    "mechanics",
    "conditions",
    "assert",
    "assert_eq",
    "assert_err",
    "seed",
    "rolls",
];

/// DSL keywords and builtins useful in expression contexts.
const DSL_KEYWORDS: &[&str] = &[
    "if", "else", "match", "let", "in", "for", "true", "false", "none",
    // collection builtins
    "len", "keys", "values", "first", "last", "append", "concat", "reverse", "sum", "any", "all",
    "sort",
];

/// Method names available after a dot, grouped by type.
/// Since we don't track variable types, we offer all methods after any dot.
const DOT_METHODS: &[&str] = &[
    // list
    "len",
    "first",
    "last",
    "reverse",
    "append",
    "concat",
    "sum",
    "any",
    "all",
    "sort",
    // set
    // (len already listed)
    // map
    "keys",
    "values",
    // option
    "unwrap",
    "unwrap_or",
    "is_some",
    "is_none",
    // dice
    "multiply",
    "roll",
    // string
    "contains",
    "starts_with",
    "ends_with",
];

/// Dynamic completion data refreshed after each command execution.
#[derive(Default)]
pub struct CompletionContext {
    pub handles: Vec<String>,
    pub entity_types: Vec<String>,
    pub action_names: Vec<String>,
    pub derive_names: Vec<String>,
    pub mechanic_names: Vec<String>,
    /// Maps handle name → entity type name.
    pub handle_types: HashMap<String, String>,
    /// Maps entity type name → optional group names.
    pub type_groups: HashMap<String, Vec<String>>,
    /// Maps (entity type, group name) → field names within the group.
    pub group_fields: HashMap<(String, String), Vec<String>>,
    /// Maps entity type name → base field names.
    pub type_fields: HashMap<String, Vec<String>>,
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

        let Some(rest) = after_first else {
            return Vec::new();
        };
        let Ok(ctx) = self.ctx.lock() else {
            return Vec::new();
        };

        match first_word {
            "spawn" => {
                // After spawn: complete entity type names (only while typing the first arg)
                let (current, extra) = split_first_word(rest);
                if extra.is_some() {
                    // Cursor is past the entity type — no entity type completions
                    return Vec::new();
                }
                let word_start = pos - current.len();
                prefix_matches_owned(&ctx.entity_types, current)
                    .into_iter()
                    .map(|s| suggestion(s, Span::new(word_start, pos), true))
                    .collect()
            }
            "do" => {
                // After do: complete action names (only before '(')
                if rest.contains('(') {
                    // Cursor is inside arguments — no action name completions
                    return Vec::new();
                }
                let current = rest.trim();
                let word_start = pos - current.len();
                prefix_matches_owned(&ctx.action_names, current)
                    .into_iter()
                    .map(|s| suggestion(s, Span::new(word_start, pos), false))
                    .collect()
            }
            "call" => {
                // After call: complete derive + mechanic names (only before '(')
                if rest.contains('(') {
                    // Cursor is inside arguments — no function name completions
                    return Vec::new();
                }
                let current = rest.trim();
                let word_start = pos - current.len();
                let mut candidates: Vec<String> = Vec::new();
                candidates.extend(ctx.derive_names.iter().cloned());
                candidates.extend(ctx.mechanic_names.iter().cloned());
                prefix_matches_owned(&candidates, current)
                    .into_iter()
                    .map(|s| suggestion(s, Span::new(word_start, pos), false))
                    .collect()
            }
            "set" | "inspect" | "destroy" | "grant" | "revoke" => {
                // Complete handle names, group names, and group field names
                let current_word = last_word(rest);
                let word_start = pos - current_word.len();

                if let Some(dot_pos) = current_word.find('.') {
                    let handle = &current_word[..dot_pos];
                    let after_dot = &current_word[dot_pos + 1..];

                    // Check for second dot: handle.GroupName.field
                    if let Some(inner_dot) = after_dot.find('.') {
                        let group_name = &after_dot[..inner_dot];
                        let field_prefix = &after_dot[inner_dot + 1..];
                        let prefix_str = format!("{}.{}.", handle, group_name);
                        let field_start = word_start + prefix_str.len();

                        if let Some(entity_type) = ctx.handle_types.get(handle) {
                            let key = (entity_type.clone(), group_name.to_string());
                            if let Some(field_names) = ctx.group_fields.get(&key) {
                                return prefix_matches_owned(field_names, field_prefix)
                                    .into_iter()
                                    .map(|s| suggestion(s, Span::new(field_start, pos), true))
                                    .collect();
                            }
                        }
                        Vec::new()
                    } else {
                        // After handle. — complete base fields + group names
                        let prefix_str = format!("{}.", handle);
                        let field_start = word_start + prefix_str.len();

                        if let Some(entity_type) = ctx.handle_types.get(handle) {
                            let mut candidates = Vec::new();
                            if let Some(fields) = ctx.type_fields.get(entity_type.as_str()) {
                                candidates.extend(fields.iter().cloned());
                            }
                            if let Some(groups) = ctx.type_groups.get(entity_type.as_str()) {
                                candidates.extend(groups.iter().cloned());
                            }
                            prefix_matches_owned(&candidates, after_dot)
                                .into_iter()
                                .map(|s| suggestion(s, Span::new(field_start, pos), true))
                                .collect()
                        } else {
                            Vec::new()
                        }
                    }
                } else {
                    prefix_matches_owned(&ctx.handles, current_word)
                        .into_iter()
                        .map(|s| suggestion(s, Span::new(word_start, pos), first_word != "set"))
                        .collect()
                }
            }
            "eval" | "assert" | "assert_eq" | "assert_err" => {
                let current_word = last_word(rest);
                let word_start = pos - current_word.len();

                // After a dot: complete method names
                if let Some(dot_pos) = current_word.rfind('.') {
                    let method_prefix = &current_word[dot_pos + 1..];
                    let method_start = word_start + dot_pos + 1;
                    return prefix_matches(DOT_METHODS, method_prefix)
                        .into_iter()
                        .map(|m| suggestion(m.to_string(), Span::new(method_start, pos), false))
                        .collect();
                }

                // Complete handles + DSL keywords
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
            handle_types: HashMap::new(),
            type_groups: HashMap::new(),
            group_fields: HashMap::new(),
            type_fields: HashMap::new(),
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

    // ── Regression: tdsl-1k4 — wrong replacement span after extra input ──

    #[test]
    fn complete_spawn_extra_input_replacement_span() {
        // "spawn Character hero" — extra text after the entity type.
        // The replacement span should only cover the entity type word,
        // not extend into the handle name.
        let ctx = make_ctx();
        let mut c = TtrpgCompleter::new(ctx);
        let results = c.complete("spawn Character hero", 20);
        for r in &results {
            assert!(
                r.span.end <= 15,
                "spawn completion span should only cover entity type word, not subsequent text; \
                 got span ({}, {})",
                r.span.start,
                r.span.end,
            );
        }
    }

    // ── Regression: tdsl-uid — assert_err gets expression completions ──

    #[test]
    fn complete_assert_err_handles_and_keywords() {
        let ctx = make_ctx();
        let mut c = TtrpgCompleter::new(ctx);
        let results = c.complete("assert_err f", 12);
        let values: Vec<_> = results.iter().map(|s| s.value.as_str()).collect();
        assert!(
            values.contains(&"fighter"),
            "assert_err should complete handles"
        );
        assert!(
            values.contains(&"false"),
            "assert_err should complete DSL keywords"
        );
    }

    #[test]
    fn complete_eval_dot_methods() {
        let ctx = make_ctx();
        let mut c = TtrpgCompleter::new(ctx);
        // "eval xs." should suggest all method names
        let results = c.complete("eval xs.", 8);
        let values: Vec<_> = results.iter().map(|s| s.value.as_str()).collect();
        assert!(values.contains(&"len"), "should suggest len");
        assert!(values.contains(&"first"), "should suggest first");
        assert!(values.contains(&"unwrap"), "should suggest unwrap");
        assert!(values.contains(&"roll"), "should suggest roll");
        assert!(values.contains(&"contains"), "should suggest contains");
        assert!(
            values.contains(&"starts_with"),
            "should suggest starts_with"
        );
    }

    #[test]
    fn complete_eval_dot_methods_prefix() {
        let ctx = make_ctx();
        let mut c = TtrpgCompleter::new(ctx);
        // "eval xs.le" should suggest "len" only
        let results = c.complete("eval xs.le", 10);
        let values: Vec<_> = results.iter().map(|s| s.value.as_str()).collect();
        assert!(values.contains(&"len"), "should suggest len");
        assert!(!values.contains(&"first"), "should not suggest first");
    }

    #[test]
    fn complete_do_after_paren_replacement_span() {
        // "do Attack(fighter" — cursor after '(' inside args.
        // The replacement span should only cover the action name before '(',
        // not extend into the argument text.
        let ctx = make_ctx();
        let mut c = TtrpgCompleter::new(ctx);
        let results = c.complete("do Attack(fighter", 17);
        for r in &results {
            assert!(
                r.span.end <= 9,
                "do completion span should only cover action name, not args after '('; \
                 got span ({}, {})",
                r.span.start,
                r.span.end,
            );
        }
    }
}
