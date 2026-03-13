use super::*;

impl Runner {
    /// `spawn <EntityType> <handle> { field: value, ..., GroupName { ... } }`
    pub(super) fn cmd_spawn(&mut self, tail: &str) -> Result<(), CliError> {
        // Extract entity type and handle
        let tail = tail.trim();

        // Split into: type, handle, optional { ... }
        let (entity_type, rest) = split_first_token(tail);
        if entity_type.is_empty() {
            return Err(CliError::Message(
                "usage: spawn <EntityType> <handle> [{ field: value, ... }]".into(),
            ));
        }
        let rest = rest.trim();
        let (handle, rest) = split_first_token(rest);
        if handle.is_empty() {
            return Err(CliError::Message(
                "usage: spawn <EntityType> <handle> [{ field: value, ... }]".into(),
            ));
        }

        if !is_valid_handle(handle) {
            return Err(CliError::Message(format!(
                "invalid handle '{handle}': must be a bare identifier"
            )));
        }

        if self.handles.contains(handle) {
            return Err(CliError::Message(format!(
                "handle '{handle}' already exists"
            )));
        }

        // Validate entity type against loaded declarations
        match self.type_env.types.get(entity_type) {
            Some(ttrpg_checker::env::DeclInfo::Entity(_)) => {} // valid
            Some(_) => {
                return Err(CliError::Message(format!(
                    "'{entity_type}' is not an entity type"
                )));
            }
            None => {
                return Err(CliError::Message(format!(
                    "unknown entity type '{entity_type}'"
                )));
            }
        }

        // Parse optional field block (may contain inline groups) and `with [...]` clause
        let rest = rest.trim();
        let (fields, inline_groups, with_conditions_str) = if rest.starts_with('{') {
            let close = find_matching_brace(rest)
                .ok_or_else(|| CliError::Message("unmatched '{' in spawn".into()))?;
            let block = &rest[1..close]; // contents between { }
            let after_brace = rest[close + 1..].trim();
            let (flds, grps) = self.parse_spawn_block(block, entity_type)?;
            (flds, grps, after_brace)
        } else if rest.is_empty() || rest.starts_with("with") {
            (HashMap::new(), Vec::new(), rest)
        } else {
            return Err(CliError::Message(format!(
                "unexpected text after handle: {rest}"
            )));
        };

        // Parse optional `with [Cond1, Cond2(...)]` clause
        let condition_strs = parse_with_clause(with_conditions_str)?;

        // Validate field names and types against entity schema
        if let Some(schema_fields) = self.type_env.lookup_fields(entity_type) {
            for (field_name, field_val) in &fields {
                match schema_fields.iter().find(|f| f.name == field_name.as_str()) {
                    None => {
                        return Err(CliError::Message(format!(
                            "unknown field '{field_name}' on entity type '{entity_type}'"
                        )));
                    }
                    Some(fi) => {
                        if !value_matches_ty(field_val, &fi.ty, Some(&*self.game_state.borrow())) {
                            return Err(CliError::Message(format!(
                                "type mismatch for field '{}': expected {}, got {}",
                                field_name,
                                fi.ty.display(),
                                value_type_display(field_val)
                            )));
                        }
                    }
                }
            }
        }

        // Validate and prepare inline groups BEFORE mutating state.
        // This ensures spawn is atomic: if any group validation fails,
        // no entity or handles are created.
        let mut prepared_groups = Vec::new();
        for (group_name, group_fields) in inline_groups {
            let struct_val =
                self.validate_and_prepare_group(&group_name, entity_type, group_fields)?;
            prepared_groups.push((group_name, struct_val));
        }

        // Included groups are required and always active.
        // Materialize any omitted included group using defaults.
        if let Some(DeclInfo::Entity(info)) = self.type_env.types.get(entity_type) {
            let already_prepared: std::collections::HashSet<String> =
                prepared_groups.iter().map(|(n, _)| n.clone()).collect();
            let required_groups: Vec<String> = info
                .optional_groups
                .iter()
                .filter(|g| g.required && !already_prepared.contains(g.name.as_str()))
                .map(|g| g.name.to_string())
                .collect();
            for group_name in required_groups {
                let struct_val =
                    self.validate_and_prepare_group(&group_name, entity_type, HashMap::new())?;
                prepared_groups.push((group_name, struct_val));
            }
        }

        // Fill defaults for entity base fields not explicitly provided.
        let mut fields = fields;
        self.fill_entity_defaults(entity_type, &mut fields)?;

        // All validation passed — now apply mutations (cannot fail).
        let fields: rustc_hash::FxHashMap<Name, Value> = fields
            .into_iter()
            .map(|(k, v)| (Name::from(k), v))
            .collect();
        let entity = self.game_state.borrow_mut().add_entity(entity_type, fields);
        self.handles.insert(handle.to_string(), entity);

        for (group_name, struct_val) in prepared_groups {
            self.game_state.borrow_mut().write_field(
                &entity,
                &[FieldPathSegment::Field(Name::from(group_name))],
                struct_val,
            );
        }

        // Apply `with [...]` conditions as Indefinite
        for cond_str in &condition_strs {
            let expr = format!("apply_condition({handle}, {cond_str}, Duration.Indefinite)");
            self.eval(&expr)?;
        }

        self.output
            .push(format!("spawned {} {} ({})", entity_type, handle, entity.0));
        Ok(())
    }

    /// `set <handle>.<field> [+= | -= | =] <value>`
    ///
    /// Supports `=`, `+=`, and `-=`. Resource fields are automatically clamped
    /// to their declared bounds.
    pub(super) fn cmd_set(&mut self, tail: &str) -> Result<(), CliError> {
        let tail = tail.trim();

        // Parse operator and split into LHS / RHS
        let (assign_op, lhs, rhs) = parse_set_operator(tail)?;

        if rhs.is_empty() {
            return Err(CliError::Message("missing value after operator".into()));
        }

        // Split lhs on first '.'
        let dot_pos = lhs
            .find('.')
            .ok_or_else(|| CliError::Message("usage: set <handle>.<field> = <value>".into()))?;
        let handle = &lhs[..dot_pos];
        let field_path = &lhs[dot_pos + 1..];

        if handle.is_empty() || field_path.is_empty() {
            return Err(CliError::Message(
                "usage: set <handle>.<field> = <value>".into(),
            ));
        }

        let entity = self.resolve_handle(handle)?;

        // Check if the path has a second '.' (GroupName.field)
        let (path_segments, expected_ty, display_path) = if let Some(inner_dot) =
            field_path.find('.')
        {
            let group_name = &field_path[..inner_dot];
            let field_name = &field_path[inner_dot + 1..];
            if group_name.is_empty() || field_name.is_empty() {
                return Err(CliError::Message(
                    "usage: set <handle>.<GroupName>.<field> = <value>".into(),
                ));
            }

            // Validate it's an optional group
            let type_name = {
                let gs = self.game_state.borrow();
                gs.entity_type_name(&entity)
                    .map(|s| s.to_string())
                    .unwrap_or_default()
            };
            let group_info = self
                .type_env
                .lookup_optional_group(&type_name, group_name)
                .ok_or_else(|| {
                    CliError::Message(format!(
                        "unknown group '{group_name}' on entity type '{type_name}'"
                    ))
                })?;

            // Check the group is active/present
            {
                let gs = self.game_state.borrow();
                if gs.read_field(&entity, group_name).is_none() {
                    let status = if group_info.required {
                        "is required but missing in state"
                    } else {
                        "is not currently granted"
                    };
                    return Err(CliError::Message(format!("{handle}.{group_name} {status}")));
                }
            }

            // Validate field within group
            let ty = group_info
                .fields
                .iter()
                .find(|f| f.name == field_name)
                .map(|f| f.ty.clone())
                .ok_or_else(|| {
                    CliError::Message(format!(
                        "unknown field '{field_name}' in optional group '{group_name}'"
                    ))
                })?;

            let segments = vec![
                FieldPathSegment::Field(Name::from(group_name)),
                FieldPathSegment::Field(Name::from(field_name)),
            ];
            (
                segments,
                Some(ty),
                format!("{handle}.{group_name}.{field_name}"),
            )
        } else {
            // Simple field path
            let field = field_path;
            let type_name = {
                let gs = self.game_state.borrow();
                gs.entity_type_name(&entity)
                    .map(|s| s.to_string())
                    .unwrap_or_default()
            };
            let expected_ty = if !type_name.is_empty() {
                if let Some(schema_fields) = self.type_env.lookup_fields(&type_name) {
                    schema_fields
                        .iter()
                        .find(|f| f.name == field)
                        .map(|fi| fi.ty.clone())
                } else {
                    None
                }
            } else {
                None
            };

            // Check for flattened included-group field
            if expected_ty.is_none() {
                if let Some(group_name) = self.type_env.lookup_flattened_field(&type_name, field) {
                    // Validate group is active
                    {
                        let gs = self.game_state.borrow();
                        if gs.read_field(&entity, group_name).is_none() {
                            return Err(CliError::Message(format!(
                                "{handle}.{field} included group '{group_name}' is missing in state"
                            )));
                        }
                    }

                    let group_info = self
                        .type_env
                        .lookup_optional_group(&type_name, group_name)
                        .ok_or_else(|| {
                            CliError::Message(format!(
                                "internal: flattened field group '{group_name}' not found"
                            ))
                        })?;
                    let ty = group_info
                        .fields
                        .iter()
                        .find(|f| f.name == field)
                        .map(|f| f.ty.clone());

                    let segments = vec![
                        FieldPathSegment::Field(group_name.clone()),
                        FieldPathSegment::Field(Name::from(field)),
                    ];
                    (segments, ty, format!("{handle}.{field}"))
                } else {
                    return Err(CliError::Message(format!(
                        "unknown field '{field}' on entity type '{type_name}'"
                    )));
                }
            } else {
                (
                    vec![FieldPathSegment::Field(Name::from(field))],
                    expected_ty,
                    format!("{handle}.{field}"),
                )
            }
        };

        // Parse and evaluate the RHS expression (try handle resolution first)
        let val = if let Some(ent) = self.handles.get(rhs) {
            Value::Entity(ent)
        } else {
            self.eval(rhs)?
        };

        // Validate type compatibility (only for plain assignment; compound ops
        // produce a new value from the existing field so the RHS is a delta)
        if assign_op == AssignOp::Eq
            && let Some(ref ty) = expected_ty
            && !value_matches_ty(&val, ty, Some(&*self.game_state.borrow()))
        {
            return Err(CliError::Message(format!(
                "type mismatch for field '{}': expected {}, got {}",
                display_path.split('.').next_back().unwrap_or("?"),
                ty.display(),
                value_type_display(&val)
            )));
        }

        // Resolve resource bounds and compute the final (possibly clamped) value
        let bounds = {
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
            interp.resolve_resource_bounds(&state, &mut handler, &entity, &path_segments)
        };

        let result = {
            let state = RefCellState(&self.game_state);
            ttrpg_interp::adapter::compute_field_value(
                &state,
                &entity,
                &path_segments,
                assign_op,
                &val,
                &bounds,
            )
            .map_err(|e| render_runtime_error(&e, &self.source_map))?
        };

        let clamped_suffix = if result.clamped { " (clamped)" } else { "" };

        // Write the computed value to GameState
        self.game_state
            .borrow_mut()
            .write_field(&entity, &path_segments, result.value.clone());

        let op_str = match assign_op {
            AssignOp::Eq => "=",
            AssignOp::PlusEq => "+=",
            AssignOp::MinusEq => "-=",
        };
        if assign_op == AssignOp::Eq {
            self.output.push(format!(
                "{} = {}{}",
                display_path,
                format_value(&result.value, &self.unit_suffixes),
                clamped_suffix
            ));
        } else {
            self.output.push(format!(
                "{} {} {} => {}",
                display_path,
                op_str,
                format_value(&val, &self.unit_suffixes),
                format_value(&result.value, &self.unit_suffixes)
            ));
        }
        Ok(())
    }

    /// `destroy <handle>`
    pub(super) fn cmd_destroy(&mut self, tail: &str) -> Result<(), CliError> {
        let handle = tail.trim();
        if handle.is_empty() {
            return Err(CliError::Message("usage: destroy <handle>".into()));
        }

        let entity = self.resolve_handle(handle)?;
        let removed = self.game_state.borrow_mut().remove_entity(&entity);
        if !removed {
            return Err(CliError::Message(format!(
                "entity for handle '{handle}' not found in state"
            )));
        }
        self.handles.remove_by_name(handle);
        self.output.push(format!("destroyed {handle}"));
        Ok(())
    }

    /// `do <Action>(actor, args...)`
    pub(super) fn cmd_do(&mut self, tail: &str) -> Result<(), CliError> {
        let result = self.eval(tail.trim())?;
        self.output
            .push(format!("=> {}", format_value(&result, &self.unit_suffixes)));
        Ok(())
    }

    /// `call <fn>(args...)` — alias for `do`
    pub(super) fn cmd_call(&mut self, tail: &str) -> Result<(), CliError> {
        self.cmd_do(tail)
    }

    // ── Grant/Revoke handlers ─────────────────────────────────────

    /// `revoke handle.GroupName`
    pub(super) fn cmd_revoke(&mut self, tail: &str) -> Result<(), CliError> {
        let tail = tail.trim();
        let dot_pos = tail
            .find('.')
            .ok_or_else(|| CliError::Message("usage: revoke <handle>.<GroupName>".into()))?;
        let handle = &tail[..dot_pos];
        let group_name = &tail[dot_pos + 1..];
        if handle.is_empty() || group_name.is_empty() {
            return Err(CliError::Message(
                "usage: revoke <handle>.<GroupName>".into(),
            ));
        }

        let entity = self.resolve_handle(handle)?;

        // Validate group exists in the type schema
        let type_name = {
            let gs = self.game_state.borrow();
            gs.entity_type_name(&entity)
                .ok_or_else(|| {
                    CliError::Message(format!("entity for handle '{handle}' not found in state"))
                })?
                .to_string()
        };
        let group_info = self
            .type_env
            .lookup_optional_group(&type_name, group_name)
            .ok_or_else(|| {
                CliError::Message(format!(
                    "unknown group '{group_name}' on entity type '{type_name}'"
                ))
            })?;
        if group_info.required {
            return Err(CliError::Message(format!(
                "{handle}.{group_name} is required and cannot be revoked"
            )));
        }

        // Check it's currently granted
        {
            let gs = self.game_state.borrow();
            if gs.read_field(&entity, group_name).is_none() {
                return Err(CliError::Message(format!(
                    "{handle}.{group_name} is not currently granted"
                )));
            }
        }

        self.game_state
            .borrow_mut()
            .remove_field(&entity, group_name);
        self.output.push(format!("revoked {handle}.{group_name}"));
        Ok(())
    }

    /// `grant handle.GroupName { field: val, ... }` or `grant handle.GroupName`
    pub(super) fn cmd_grant(&mut self, tail: &str) -> Result<(), CliError> {
        let tail = tail.trim();
        let dot_pos = tail.find('.').ok_or_else(|| {
            CliError::Message("usage: grant <handle>.<GroupName> [{ ... }]".into())
        })?;
        let handle = &tail[..dot_pos];
        let after_dot = &tail[dot_pos + 1..];
        if handle.is_empty() || after_dot.is_empty() {
            return Err(CliError::Message(
                "usage: grant <handle>.<GroupName> [{ ... }]".into(),
            ));
        }

        // Split group_name from optional { ... } block
        let (group_name, rest) = split_first_token(after_dot);
        let rest = rest.trim();

        let entity = self.resolve_handle(handle)?;

        // Validate group exists
        let type_name = {
            let gs = self.game_state.borrow();
            gs.entity_type_name(&entity)
                .ok_or_else(|| {
                    CliError::Message(format!("entity for handle '{handle}' not found in state"))
                })?
                .to_string()
        };
        let group_info = self
            .type_env
            .lookup_optional_group(&type_name, group_name)
            .ok_or_else(|| {
                CliError::Message(format!(
                    "unknown group '{group_name}' on entity type '{type_name}'"
                ))
            })?;
        if group_info.required {
            return Err(CliError::Message(format!(
                "{handle}.{group_name} is required and cannot be granted"
            )));
        }

        // Check not already granted
        {
            let gs = self.game_state.borrow();
            if gs.read_field(&entity, group_name).is_some() {
                return Err(CliError::Message(format!(
                    "{handle}.{group_name} is already granted"
                )));
            }
        }

        // Parse optional { ... } block
        let fields = if rest.starts_with('{') {
            let block = rest
                .strip_prefix('{')
                .and_then(|s| s.strip_suffix('}'))
                .ok_or_else(|| CliError::Message("unmatched '{' in grant".into()))?;
            self.parse_field_block(block)?
        } else if rest.is_empty() {
            HashMap::new()
        } else {
            return Err(CliError::Message(format!(
                "unexpected text after group name: {rest}"
            )));
        };

        let struct_val = self.validate_and_prepare_group(group_name, &type_name, fields)?;
        self.game_state.borrow_mut().write_field(
            &entity,
            &[FieldPathSegment::Field(Name::from(group_name))],
            struct_val.clone(),
        );
        self.output.push(format!(
            "granted {}.{}: {}",
            handle,
            group_name,
            format_value(&struct_val, &self.unit_suffixes)
        ));
        Ok(())
    }
}

/// Parse the operator in a `set` command, returning `(op, lhs, rhs)`.
///
/// Recognises `+=`, `-=`, and plain `=`. The scan is quote-aware so that
/// `=` inside a string literal on the RHS doesn't confuse the split.
/// Find the index of the `}` that matches the opening `{` at position 0.
/// Returns `None` if braces are unmatched.
fn find_matching_brace(s: &str) -> Option<usize> {
    let mut depth = 0i32;
    let mut in_string = false;
    for (i, c) in s.char_indices() {
        if c == '"' {
            in_string = !in_string;
            continue;
        }
        if in_string {
            if c == '\\' {
                // skip next char (handled by char_indices advancing)
            }
            continue;
        }
        match c {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

/// Parse a `with [Cond1, Cond2(...)]` clause from the remaining text after
/// a spawn block. Returns the individual condition expression strings.
fn parse_with_clause(s: &str) -> Result<Vec<String>, CliError> {
    let s = s.trim();
    if s.is_empty() {
        return Ok(Vec::new());
    }
    if !s.starts_with("with") {
        return Err(CliError::Message(format!(
            "unexpected text after spawn block: {s}"
        )));
    }
    let rest = s[4..].trim();
    let inner = rest
        .strip_prefix('[')
        .and_then(|s| s.strip_suffix(']'))
        .ok_or_else(|| {
            CliError::Message("expected `[...]` after `with` in spawn command".into())
        })?;
    let inner = inner.trim();
    if inner.is_empty() {
        return Ok(Vec::new());
    }
    // Split on top-level commas (respecting parentheses)
    let mut conds = Vec::new();
    let mut depth = 0i32;
    let mut start = 0;
    for (i, c) in inner.char_indices() {
        match c {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth -= 1,
            ',' if depth == 0 => {
                let part = inner[start..i].trim();
                if !part.is_empty() {
                    conds.push(part.to_string());
                }
                start = i + 1;
            }
            _ => {}
        }
    }
    let last = inner[start..].trim();
    if !last.is_empty() {
        conds.push(last.to_string());
    }
    Ok(conds)
}

fn parse_set_operator(input: &str) -> Result<(AssignOp, &str, &str), CliError> {
    let bytes = input.as_bytes();
    let mut in_string = false;
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'"' {
            in_string = !in_string;
            i += 1;
            continue;
        }
        if in_string {
            // Skip escaped characters inside strings
            if bytes[i] == b'\\' {
                i += 2;
            } else {
                i += 1;
            }
            continue;
        }
        if bytes[i] == b'+' && i + 1 < bytes.len() && bytes[i + 1] == b'=' {
            return Ok((AssignOp::PlusEq, input[..i].trim(), input[i + 2..].trim()));
        }
        if bytes[i] == b'-' && i + 1 < bytes.len() && bytes[i + 1] == b'=' {
            return Ok((AssignOp::MinusEq, input[..i].trim(), input[i + 2..].trim()));
        }
        if bytes[i] == b'=' {
            return Ok((AssignOp::Eq, input[..i].trim(), input[i + 1..].trim()));
        }
        i += 1;
    }
    Err(CliError::Message(
        "usage: set <handle>.<field> [+= | -= | =] <value>".into(),
    ))
}
