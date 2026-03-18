use ttrpg_ast::ast::ExprKind;
use ttrpg_checker::env::DeclInfo;
use ttrpg_checker::ty::Ty;

use super::*;

/// Extract the head identifier name from an expression.
///
/// For `Radius` → `"Radius"`, for `Radius(radius: 15ft)` → `"Radius"`.
fn expr_head_ident(expr: &ExprKind) -> Option<&str> {
    match expr {
        ExprKind::Ident(name) => Some(name.as_str()),
        ExprKind::Call { callee, .. } => {
            if let ExprKind::Ident(name) = &callee.node {
                Some(name.as_str())
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Extract the span of the head identifier from an expression.
///
/// For a bare ident, returns its span. For a call, returns the callee span.
fn expr_head_span(expr: &ttrpg_ast::Spanned<ExprKind>) -> ttrpg_ast::Span {
    match &expr.node {
        ExprKind::Call { callee, .. } => callee.span,
        _ => expr.span,
    }
}

impl Runner {
    /// If a field's declared type is an enum and the parsed expression's head
    /// ident matches a variant of that enum, inject the resolution into
    /// `self.type_env.resolved_variants` so the interpreter can disambiguate
    /// overlapping variant names.
    ///
    /// Returns the injected span (if any) so the caller can remove it after
    /// evaluation — SYNTH spans overlap across parse_expr calls.
    fn inject_enum_hint(
        &mut self,
        field_name: &str,
        parsed: &ttrpg_ast::Spanned<ExprKind>,
        schema_fields: &[ttrpg_checker::env::FieldInfo],
    ) -> Option<ttrpg_ast::Span> {
        let enum_name = schema_fields
            .iter()
            .find(|f| f.name == field_name)
            .and_then(|fi| match &fi.ty {
                Ty::Enum(n) => Some(n.clone()),
                _ => None,
            });
        let enum_name = enum_name?;
        let head = expr_head_ident(&parsed.node)?;
        // Check if the enum actually has this variant
        let has_variant =
            self.type_env
                .types
                .get(enum_name.as_str())
                .is_some_and(|decl| match decl {
                    DeclInfo::Enum(info) => info.variants.iter().any(|v| v.name == head),
                    _ => false,
                });
        if has_variant {
            let span = expr_head_span(parsed);
            Arc::make_mut(&mut self.type_env)
                .resolved_variants
                .insert(span, enum_name);
            Some(span)
        } else {
            None
        }
    }

    /// Parse a spawn block that may contain both fields and inline groups.
    ///
    /// Entries are split by top-level commas. Each entry is classified as:
    /// - field: `key: value` (has `:` before any `{`)
    /// - group: `GroupName { ... }` (has `{` before any `:`)
    pub(super) fn parse_spawn_block(
        &mut self,
        block: &str,
        entity_type: &str,
    ) -> Result<SpawnBlock, CliError> {
        let mut fields = HashMap::new();
        let mut groups = Vec::new();
        let entries = split_top_level_commas(block);

        for entry in entries {
            let entry = entry.trim();
            if entry.is_empty() {
                continue;
            }

            // Classify: find first ':' and first '{' outside strings
            let colon_pos = find_unquoted(entry, ':');
            let brace_pos = find_unquoted(entry, '{');

            let is_group = match (colon_pos, brace_pos) {
                (None, Some(_)) => true,     // only { found
                (Some(_), None) => false,    // only : found
                (Some(c), Some(b)) => b < c, // { comes before :
                (None, None) => false,       // treat as field (will error in parse)
            };

            if is_group {
                // Group: Name { field: val, ... }
                let Some(brace_start) = brace_pos else {
                    return Err(CliError::Message(format!(
                        "internal: is_group set but brace_pos is None in '{}'",
                        entry.trim(),
                    )));
                };
                let group_name = entry[..brace_start].trim();
                let inner_block = entry[brace_start..]
                    .strip_prefix('{')
                    .and_then(|s| s.strip_suffix('}'))
                    .ok_or_else(|| {
                        CliError::Message(format!("unmatched '{{' in inline group '{group_name}'"))
                    })?;

                if group_name.is_empty() {
                    return Err(CliError::Message("empty group name in spawn block".into()));
                }

                // Validate this is actually an optional group
                if self
                    .type_env
                    .lookup_optional_group(entity_type, group_name)
                    .is_none()
                {
                    return Err(CliError::Message(format!(
                        "unknown group '{group_name}' on entity type '{entity_type}'"
                    )));
                }

                if groups.iter().any(|(name, _)| name == group_name) {
                    return Err(CliError::Message(format!(
                        "duplicate group '{group_name}' in spawn block"
                    )));
                }

                let group_schema: Option<Vec<_>> = self
                    .type_env
                    .lookup_optional_group(entity_type, group_name)
                    .map(|g| g.fields.clone());
                let group_fields = self.parse_field_block(inner_block, group_schema.as_deref())?;
                groups.push((group_name.to_string(), group_fields));
            } else {
                // Field: key: value
                let cp = colon_pos.ok_or_else(|| {
                    CliError::Message(format!(
                        "expected 'key: value' in field block, got: {entry}"
                    ))
                })?;
                let key = entry[..cp].trim();
                let val_str = entry[cp + 1..].trim();
                if key.is_empty() || val_str.is_empty() {
                    return Err(CliError::Message(format!("invalid field entry: {entry}")));
                }

                let val = if let Some(val) = self.variables.get(val_str) {
                    val.clone()
                } else {
                    let (parsed, diags) = ttrpg_parser::parse_expr(val_str);
                    if !diags.is_empty() {
                        let msgs: Vec<_> = diags.iter().map(|d| d.message.as_str()).collect();
                        return Err(CliError::Message(format!(
                            "parse error in field '{}': {}",
                            key,
                            msgs.join("; ")
                        )));
                    }
                    let parsed = parsed.ok_or_else(|| {
                        CliError::Message(format!("failed to parse value for field '{key}'"))
                    })?;

                    // Inject enum type hint so the interpreter can disambiguate
                    // bare variant names that appear in multiple enums.
                    let hint_span = if let Some(fields) = self.type_env.lookup_fields(entity_type) {
                        let fields = fields.to_vec();
                        self.inject_enum_hint(key, &parsed, &fields)
                    } else {
                        None
                    };

                    let cov_rc = self.coverage_rc();
                    let mut interp = Interpreter::new(&self.program, &self.type_env)
                        .map_err(|e| render_runtime_error(&e, &self.source_map))?;
                    if let Some(cov) = cov_rc {
                        interp.set_coverage(cov);
                    }
                    let state = RefCellState(&self.game_state);
                    let mut handler = CliHandler::new(
                        &self.game_state,
                        self.handles.by_entity(),
                        &mut self.rng,
                        &mut self.roll_queue,
                        &mut self.prompt_queue,
                        &self.unit_suffixes,
                    )
                    .quiet(self.quiet)
                    .interactive(self.interactive);
                    let result = interp
                        .evaluate_expr(&state, &mut handler, &parsed)
                        .map_err(|e| {
                            for line in handler.log.drain(..) {
                                self.output.push(line);
                            }
                            render_runtime_error(&e, &self.source_map)
                        })?;
                    for line in handler.log.drain(..) {
                        self.output.push(line);
                    }

                    // Clean up injected hint — SYNTH spans overlap across
                    // parse_expr calls and could poison later evaluations.
                    if let Some(span) = hint_span {
                        Arc::make_mut(&mut self.type_env)
                            .resolved_variants
                            .remove(&span);
                    }

                    result
                };
                if fields.contains_key(key) {
                    return Err(CliError::Message(format!(
                        "duplicate field '{key}' in field block"
                    )));
                }
                fields.insert(key.to_string(), val);
            }
        }

        Ok((fields, groups))
    }

    /// Parse a field block like `key: expr, key: expr` into a HashMap.
    ///
    /// If `schema_fields` is provided, enum type hints are injected to
    /// disambiguate bare variant names that appear in multiple enums.
    pub(super) fn parse_field_block(
        &mut self,
        block: &str,
        schema_fields: Option<&[ttrpg_checker::env::FieldInfo]>,
    ) -> Result<HashMap<String, Value>, CliError> {
        // Clone schema fields to avoid holding a borrow on self.type_env.
        let schema: Option<Vec<ttrpg_checker::env::FieldInfo>> = schema_fields.map(|f| f.to_vec());

        let mut fields = HashMap::new();
        let entries = split_top_level_commas(block);
        for entry in entries {
            let entry = entry.trim();
            if entry.is_empty() {
                continue;
            }
            let colon_pos = entry.find(':').ok_or_else(|| {
                CliError::Message(format!(
                    "expected 'key: value' in field block, got: {entry}"
                ))
            })?;
            let key = entry[..colon_pos].trim();
            let val_str = entry[colon_pos + 1..].trim();
            if key.is_empty() || val_str.is_empty() {
                return Err(CliError::Message(format!("invalid field entry: {entry}")));
            }

            // Try variable resolution first, then fall back to expression eval
            let val = if let Some(val) = self.variables.get(val_str) {
                val.clone()
            } else {
                let (parsed, diags) = ttrpg_parser::parse_expr(val_str);
                if !diags.is_empty() {
                    let msgs: Vec<_> = diags.iter().map(|d| d.message.as_str()).collect();
                    return Err(CliError::Message(format!(
                        "parse error in field '{}': {}",
                        key,
                        msgs.join("; ")
                    )));
                }
                let parsed = parsed.ok_or_else(|| {
                    CliError::Message(format!("failed to parse value for field '{key}'"))
                })?;

                // Inject enum type hint for disambiguation.
                let hint_span = schema
                    .as_ref()
                    .and_then(|sf| self.inject_enum_hint(key, &parsed, sf));

                let interp = Interpreter::new(&self.program, &self.type_env)
                    .map_err(|e| render_runtime_error(&e, &self.source_map))?;
                let state = RefCellState(&self.game_state);
                let mut handler = CliHandler::new(
                    &self.game_state,
                    self.handles.by_entity(),
                    &mut self.rng,
                    &mut self.roll_queue,
                    &mut self.prompt_queue,
                    &self.unit_suffixes,
                )
                .quiet(self.quiet)
                .interactive(self.interactive);
                let result = interp
                    .evaluate_expr(&state, &mut handler, &parsed)
                    .map_err(|e| {
                        for line in handler.log.drain(..) {
                            self.output.push(line);
                        }
                        render_runtime_error(&e, &self.source_map)
                    })?;
                for line in handler.log.drain(..) {
                    self.output.push(line);
                }

                // Clean up injected hint — SYNTH spans overlap.
                if let Some(span) = hint_span {
                    Arc::make_mut(&mut self.type_env)
                        .resolved_variants
                        .remove(&span);
                }

                result
            };
            if fields.contains_key(key) {
                return Err(CliError::Message(format!(
                    "duplicate field '{key}' in field block"
                )));
            }
            fields.insert(key.to_string(), val);
        }
        Ok(fields)
    }
}
