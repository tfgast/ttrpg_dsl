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
                "invalid handle '{}': must be a bare identifier",
                handle
            )));
        }

        if self.handles.contains_key(handle) {
            return Err(CliError::Message(format!(
                "handle '{}' already exists",
                handle
            )));
        }

        // Validate entity type against loaded declarations
        match self.type_env.types.get(entity_type) {
            Some(ttrpg_checker::env::DeclInfo::Entity(_)) => {} // valid
            Some(_) => {
                return Err(CliError::Message(format!(
                    "'{}' is not an entity type",
                    entity_type
                )));
            }
            None => {
                return Err(CliError::Message(format!(
                    "unknown entity type '{}'",
                    entity_type
                )));
            }
        }

        // Parse optional field block (may contain inline groups)
        let rest = rest.trim();
        let (fields, inline_groups) = if rest.starts_with('{') {
            let block = rest
                .strip_prefix('{')
                .and_then(|s| s.strip_suffix('}'))
                .ok_or_else(|| CliError::Message("unmatched '{' in spawn".into()))?;
            self.parse_spawn_block(block, entity_type)?
        } else if rest.is_empty() {
            (HashMap::new(), Vec::new())
        } else {
            return Err(CliError::Message(format!(
                "unexpected text after handle: {}",
                rest
            )));
        };

        // Validate field names and types against entity schema
        if let Some(schema_fields) = self.type_env.lookup_fields(entity_type) {
            for (field_name, field_val) in &fields {
                match schema_fields.iter().find(|f| f.name == field_name.as_str()) {
                    None => {
                        return Err(CliError::Message(format!(
                            "unknown field '{}' on entity type '{}'",
                            field_name, entity_type
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

        // All validation passed — now apply mutations (cannot fail).
        let fields: HashMap<Name, Value> = fields.into_iter().map(|(k, v)| (Name::from(k), v)).collect();
        let entity = self.game_state.borrow_mut().add_entity(entity_type, fields);
        self.handles.insert(handle.to_string(), entity);
        self.reverse_handles.insert(entity, handle.to_string());

        for (group_name, struct_val) in prepared_groups {
            self.game_state.borrow_mut().write_field(
                &entity,
                &[FieldPathSegment::Field(Name::from(group_name))],
                struct_val,
            );
        }

        self.output.push(format!(
            "spawned {} {} ({})",
            entity_type,
            handle,
            entity.0
        ));
        Ok(())
    }

    /// `set <handle>.<field> = <value>` or `set <handle>.<GroupName>.<field> = <value>`
    pub(super) fn cmd_set(&mut self, tail: &str) -> Result<(), CliError> {
        let tail = tail.trim();

        // Split on '='
        let eq_pos = tail
            .find('=')
            .ok_or_else(|| CliError::Message("usage: set <handle>.<field> = <value>".into()))?;
        let lhs = tail[..eq_pos].trim();
        let rhs = tail[eq_pos + 1..].trim();

        if rhs.is_empty() {
            return Err(CliError::Message("missing value after '='".into()));
        }

        // Split lhs on first '.'
        let dot_pos = lhs
            .find('.')
            .ok_or_else(|| CliError::Message("usage: set <handle>.<field> = <value>".into()))?;
        let handle = &lhs[..dot_pos];
        let field_path = &lhs[dot_pos + 1..];

        if handle.is_empty() || field_path.is_empty() {
            return Err(CliError::Message("usage: set <handle>.<field> = <value>".into()));
        }

        let entity = self.resolve_handle(handle)?;

        // Check if the path has a second '.' (GroupName.field)
        let (path_segments, expected_ty, display_path) =
            if let Some(inner_dot) = field_path.find('.') {
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
                            "unknown optional group '{}' on entity type '{}'",
                            group_name, type_name
                        ))
                    })?;

                // Check the group is granted
                {
                    let gs = self.game_state.borrow();
                    if gs.read_field(&entity, group_name).is_none() {
                        return Err(CliError::Message(format!(
                            "{}.{} is not currently granted",
                            handle, group_name
                        )));
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
                            "unknown field '{}' in optional group '{}'",
                            field_name, group_name
                        ))
                    })?;

                let segments = vec![
                    FieldPathSegment::Field(Name::from(group_name)),
                    FieldPathSegment::Field(Name::from(field_name)),
                ];
                (
                    segments,
                    Some(ty),
                    format!("{}.{}.{}", handle, group_name, field_name),
                )
            } else {
                // Simple field path
                let field = field_path;
                let expected_ty = {
                    let gs = self.game_state.borrow();
                    if let Some(type_name) = gs.entity_type_name(&entity) {
                        if let Some(schema_fields) = self.type_env.lookup_fields(type_name) {
                            match schema_fields.iter().find(|f| f.name == field) {
                                Some(fi) => Some(fi.ty.clone()),
                                None => {
                                    return Err(CliError::Message(format!(
                                        "unknown field '{}' on entity type '{}'",
                                        field, type_name
                                    )));
                                }
                            }
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                };
                (
                    vec![FieldPathSegment::Field(Name::from(field))],
                    expected_ty,
                    format!("{}.{}", handle, field),
                )
            };

        // Parse and evaluate the RHS expression (try handle resolution first)
        let val = if let Some(&ent) = self.handles.get(rhs) {
            Value::Entity(ent)
        } else {
            self.eval(rhs)?
        };

        // Validate type compatibility
        if let Some(ref ty) = expected_ty {
            if !value_matches_ty(&val, ty, Some(&*self.game_state.borrow())) {
                return Err(CliError::Message(format!(
                    "type mismatch for field '{}': expected {}, got {}",
                    display_path.split('.').next_back().unwrap_or("?"),
                    ty.display(),
                    value_type_display(&val)
                )));
            }
        }

        // Write directly to GameState
        self.game_state
            .borrow_mut()
            .write_field(&entity, &path_segments, val.clone());
        self.output
            .push(format!("{} = {}", display_path, format_value(&val)));
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
                "entity for handle '{}' not found in state",
                handle
            )));
        }
        self.handles.remove(handle);
        self.reverse_handles.remove(&entity);
        self.output.push(format!("destroyed {}", handle));
        Ok(())
    }

    /// `do <Action>(actor, args...)`
    pub(super) fn cmd_do(&mut self, tail: &str) -> Result<(), CliError> {
        let tail = tail.trim();

        // Parse: Name(arg1, arg2, ...)
        let paren_pos = tail
            .find('(')
            .ok_or_else(|| CliError::Message("usage: do <Action>(actor, args...)".into()))?;
        let action_name = tail[..paren_pos].trim();
        if action_name.is_empty() {
            return Err(CliError::Message("missing action name".into()));
        }

        let args_str = tail[paren_pos + 1..]
            .strip_suffix(')')
            .ok_or_else(|| CliError::Message("unmatched '(' in do".into()))?;

        let arg_strs = split_top_level_commas(args_str);
        if arg_strs.is_empty() || arg_strs[0].trim().is_empty() {
            return Err(CliError::Message(
                "do requires at least an actor argument".into(),
            ));
        }

        // Validate no empty args (e.g. "do Act(fighter,,target)")
        for (i, arg_str) in arg_strs.iter().enumerate() {
            if i > 0 && arg_str.trim().is_empty() {
                return Err(CliError::Message("empty argument in do".into()));
            }
        }

        // Check that the action exists before evaluating args (avoid side effects)
        {
            let interp = Interpreter::new(&self.program, &self.type_env)
                .map_err(|e| CliError::Message(format!("interpreter error: {}", e)))?;
            if !interp.has_action(action_name) {
                return Err(CliError::Message(format!(
                    "undefined action '{}'",
                    action_name
                )));
            }
        }

        // First arg is the actor handle
        let actor_str = arg_strs[0].trim();
        let actor = self.resolve_handle(actor_str)?;

        // Remaining args: try handle resolution first, then parse as expression
        let mut args = Vec::new();
        for arg_str in &arg_strs[1..] {
            let arg_str = arg_str.trim();
            if let Some(&entity) = self.handles.get(arg_str) {
                args.push(Value::Entity(entity));
            } else {
                let val = self.eval(arg_str)?;
                args.push(val);
            }
        }

        let interp = Interpreter::new(&self.program, &self.type_env)
            .map_err(|e| CliError::Message(format!("interpreter error: {}", e)))?;
        let state = RefCellState(&self.game_state);
        let mut handler =
            CliHandler::new(&self.game_state, &self.reverse_handles, &mut self.rng, &mut self.roll_queue);

        let result = interp
            .execute_action(&state, &mut handler, action_name, actor, args)
            .map_err(|e| {
                // Emit effect log even on error
                for line in handler.log.drain(..) {
                    self.output.push(line);
                }
                CliError::Message(format!("runtime error: {}", e))
            })?;

        // Emit effect log
        for line in handler.log.drain(..) {
            self.output.push(line);
        }

        self.output.push(format!("=> {}", format_value(&result)));
        Ok(())
    }

    /// `call <fn>(args...)`
    pub(super) fn cmd_call(&mut self, tail: &str) -> Result<(), CliError> {
        let tail = tail.trim();

        // Parse: Name(arg1, arg2, ...)
        let paren_pos = tail
            .find('(')
            .ok_or_else(|| CliError::Message("usage: call <fn>(args...)".into()))?;
        let fn_name = tail[..paren_pos].trim();
        if fn_name.is_empty() {
            return Err(CliError::Message("missing function name".into()));
        }

        let args_str = tail[paren_pos + 1..]
            .strip_suffix(')')
            .ok_or_else(|| CliError::Message("unmatched '(' in call".into()))?;

        let arg_strs = split_top_level_commas(args_str);

        // Reject empty positional arguments (e.g. "call f(1,,2)")
        // Only skip the single-empty-string case from `call f()`
        let has_args = !(arg_strs.len() == 1 && arg_strs[0].trim().is_empty());
        if has_args {
            for arg_str in &arg_strs {
                if arg_str.trim().is_empty() {
                    return Err(CliError::Message("empty argument in call".into()));
                }
            }
        }

        // Check that the derive or mechanic exists before evaluating args
        let is_derive;
        let is_mechanic;
        {
            let interp = Interpreter::new(&self.program, &self.type_env)
                .map_err(|e| CliError::Message(format!("interpreter error: {}", e)))?;
            is_derive = interp.has_derive(fn_name);
            is_mechanic = interp.has_mechanic(fn_name);
        }
        if !is_derive && !is_mechanic {
            return Err(CliError::Message(format!(
                "undefined function '{}' (no derive or mechanic with that name)",
                fn_name
            )));
        }

        // Evaluate arguments: try handle resolution first, then parse as expression
        let mut args = Vec::new();
        if has_args {
            for arg_str in &arg_strs {
                let arg_str = arg_str.trim();
                if let Some(&entity) = self.handles.get(arg_str) {
                    args.push(Value::Entity(entity));
                } else {
                    let val = self.eval(arg_str)?;
                    args.push(val);
                }
            }
        }

        let interp = Interpreter::new(&self.program, &self.type_env)
            .map_err(|e| CliError::Message(format!("interpreter error: {}", e)))?;
        let state = RefCellState(&self.game_state);
        let mut handler =
            CliHandler::new(&self.game_state, &self.reverse_handles, &mut self.rng, &mut self.roll_queue);

        // Dispatch to derive or mechanic based on structured check
        let result = if is_derive {
            interp
                .evaluate_derive(&state, &mut handler, fn_name, args)
                .map_err(|e| {
                    for line in handler.log.drain(..) {
                        self.output.push(line);
                    }
                    CliError::Message(format!("runtime error: {}", e))
                })?
        } else {
            interp
                .evaluate_mechanic(&state, &mut handler, fn_name, args)
                .map_err(|e| {
                    for line in handler.log.drain(..) {
                        self.output.push(line);
                    }
                    CliError::Message(format!("runtime error: {}", e))
                })?
        };

        // Emit effect log
        for line in handler.log.drain(..) {
            self.output.push(line);
        }

        self.output.push(format!("=> {}", format_value(&result)));
        Ok(())
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
                    CliError::Message(format!(
                        "entity for handle '{}' not found in state",
                        handle
                    ))
                })?
                .to_string()
        };
        if self
            .type_env
            .lookup_optional_group(&type_name, group_name)
            .is_none()
        {
            return Err(CliError::Message(format!(
                "unknown optional group '{}' on entity type '{}'",
                group_name, type_name
            )));
        }

        // Check it's currently granted
        {
            let gs = self.game_state.borrow();
            if gs.read_field(&entity, group_name).is_none() {
                return Err(CliError::Message(format!(
                    "{}.{} is not currently granted",
                    handle, group_name
                )));
            }
        }

        self.game_state
            .borrow_mut()
            .remove_field(&entity, group_name);
        self.output
            .push(format!("revoked {}.{}", handle, group_name));
        Ok(())
    }

    /// `grant handle.GroupName { field: val, ... }` or `grant handle.GroupName`
    pub(super) fn cmd_grant(&mut self, tail: &str) -> Result<(), CliError> {
        let tail = tail.trim();
        let dot_pos = tail
            .find('.')
            .ok_or_else(|| CliError::Message("usage: grant <handle>.<GroupName> [{ ... }]".into()))?;
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
                    CliError::Message(format!(
                        "entity for handle '{}' not found in state",
                        handle
                    ))
                })?
                .to_string()
        };
        // Check not already granted
        {
            let gs = self.game_state.borrow();
            if gs.read_field(&entity, group_name).is_some() {
                return Err(CliError::Message(format!(
                    "{}.{} is already granted",
                    handle, group_name
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
                "unexpected text after group name: {}",
                rest
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
            format_value(&struct_val)
        ));
        Ok(())
    }
}
