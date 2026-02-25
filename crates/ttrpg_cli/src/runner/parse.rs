use super::*;

impl Runner {
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
                (None, Some(_)) => true,       // only { found
                (Some(_), None) => false,      // only : found
                (Some(c), Some(b)) => b < c,   // { comes before :
                (None, None) => false,         // treat as field (will error in parse)
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
                        CliError::Message(format!(
                            "unmatched '{{' in inline group '{}'",
                            group_name
                        ))
                    })?;

                if group_name.is_empty() {
                    return Err(CliError::Message(
                        "empty group name in spawn block".into(),
                    ));
                }

                // Validate this is actually an optional group
                if self
                    .type_env
                    .lookup_optional_group(entity_type, group_name)
                    .is_none()
                {
                    return Err(CliError::Message(format!(
                        "unknown optional group '{}' on entity type '{}'",
                        group_name, entity_type
                    )));
                }

                let group_fields = self.parse_field_block(inner_block)?;
                groups.push((group_name.to_string(), group_fields));
            } else {
                // Field: key: value
                let cp = colon_pos.ok_or_else(|| {
                    CliError::Message(format!(
                        "expected 'key: value' in field block, got: {}",
                        entry
                    ))
                })?;
                let key = entry[..cp].trim();
                let val_str = entry[cp + 1..].trim();
                if key.is_empty() || val_str.is_empty() {
                    return Err(CliError::Message(format!(
                        "invalid field entry: {}",
                        entry
                    )));
                }

                let val = if let Some(&ent) = self.handles.get(val_str) {
                    Value::Entity(ent)
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
                        CliError::Message(format!("failed to parse value for field '{}'", key))
                    })?;

                    let interp = Interpreter::new(&self.program, &self.type_env)
                        .map_err(|e| CliError::Message(format!("interpreter error: {}", e)))?;
                    let state = RefCellState(&self.game_state);
                    let mut handler = CliHandler::new(
                        &self.game_state,
                        &self.reverse_handles,
                        &mut self.rng,
                        &mut self.roll_queue,
                    );
                    let result = interp
                        .evaluate_expr(&state, &mut handler, &parsed)
                        .map_err(|e| {
                            for line in handler.log.drain(..) {
                                self.output.push(line);
                            }
                            CliError::Message(format!("error evaluating field '{}': {}", key, e))
                        })?;
                    for line in handler.log.drain(..) {
                        self.output.push(line);
                    }
                    result
                };
                if fields.contains_key(key) {
                    return Err(CliError::Message(format!(
                        "duplicate field '{}' in field block",
                        key
                    )));
                }
                fields.insert(key.to_string(), val);
            }
        }

        Ok((fields, groups))
    }

    /// Parse a field block like `key: expr, key: expr` into a HashMap.
    pub(super) fn parse_field_block(&mut self, block: &str) -> Result<HashMap<String, Value>, CliError> {
        let mut fields = HashMap::new();
        let entries = split_top_level_commas(block);
        for entry in entries {
            let entry = entry.trim();
            if entry.is_empty() {
                continue;
            }
            let colon_pos = entry
                .find(':')
                .ok_or_else(|| CliError::Message(format!("expected 'key: value' in field block, got: {}", entry)))?;
            let key = entry[..colon_pos].trim();
            let val_str = entry[colon_pos + 1..].trim();
            if key.is_empty() || val_str.is_empty() {
                return Err(CliError::Message(format!(
                    "invalid field entry: {}",
                    entry
                )));
            }

            // Try handle resolution first, then fall back to expression eval
            let val = if let Some(&ent) = self.handles.get(val_str) {
                Value::Entity(ent)
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
                    CliError::Message(format!("failed to parse value for field '{}'", key))
                })?;

                let interp = Interpreter::new(&self.program, &self.type_env)
                    .map_err(|e| CliError::Message(format!("interpreter error: {}", e)))?;
                let state = RefCellState(&self.game_state);
                let mut handler =
                    CliHandler::new(&self.game_state, &self.reverse_handles, &mut self.rng, &mut self.roll_queue);
                let result = interp
                    .evaluate_expr(&state, &mut handler, &parsed)
                    .map_err(|e| {
                        for line in handler.log.drain(..) {
                            self.output.push(line);
                        }
                        CliError::Message(format!("error evaluating field '{}': {}", key, e))
                    })?;
                for line in handler.log.drain(..) {
                    self.output.push(line);
                }
                result
            };
            if fields.contains_key(key) {
                return Err(CliError::Message(format!(
                    "duplicate field '{}' in field block",
                    key
                )));
            }
            fields.insert(key.to_string(), val);
        }
        Ok(fields)
    }
}
