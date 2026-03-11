use super::*;

impl Runner {
    pub(super) fn cmd_inspect(&mut self, tail: &str) -> Result<(), CliError> {
        let tail = tail.trim();

        // Split on first '.' to detect handle.field vs handle
        if let Some(dot_pos) = tail.find('.') {
            let handle = &tail[..dot_pos];
            let rest = &tail[dot_pos + 1..];
            if handle.is_empty() || rest.is_empty() {
                return Err(CliError::Message(
                    "usage: inspect <handle> or inspect <handle>.<field>".into(),
                ));
            }
            let entity = self.resolve_handle(handle)?;

            // Check for a second dot: handle.GroupName.field
            if let Some(inner_dot) = rest.find('.') {
                let group_name = &rest[..inner_dot];
                let field_name = &rest[inner_dot + 1..];
                if group_name.is_empty() || field_name.is_empty() {
                    return Err(CliError::Message(
                        "usage: inspect <handle>.<GroupName>.<field>".into(),
                    ));
                }

                let gs = self.game_state.borrow();
                match gs.read_field(&entity, group_name) {
                    Some(Value::Struct { fields, .. }) => match fields.get(field_name) {
                        Some(val) => {
                            self.output.push(format!(
                                "{}.{}.{} = {}",
                                handle,
                                group_name,
                                field_name,
                                format_value(val, &self.unit_suffixes)
                            ));
                        }
                        None => {
                            return Err(CliError::Message(format!(
                                "field '{field_name}' not found in group '{group_name}'"
                            )));
                        }
                    },
                    Some(_) => {
                        return Err(CliError::Message(format!(
                            "field '{group_name}' is not a group on {handle}"
                        )));
                    }
                    None => {
                        let type_name = gs.entity_type_name(&entity).map(|s| s.to_string());
                        let group_info = type_name
                            .as_deref()
                            .and_then(|tn| self.type_env.lookup_optional_group(tn, group_name));
                        let msg = match group_info {
                            Some(info) if info.required => {
                                format!("{handle}.{group_name} is required but missing in state")
                            }
                            Some(_) => {
                                format!("{handle}.{group_name} is not currently granted")
                            }
                            None => {
                                let entity_type = type_name.as_deref().unwrap_or("unknown");
                                format!("unknown group '{group_name}' on {entity_type}")
                            }
                        };
                        return Err(CliError::Message(msg));
                    }
                }
            } else {
                let field = rest;

                // Check if it's an optional group name
                let type_name = {
                    let gs = self.game_state.borrow();
                    gs.entity_type_name(&entity).map(|s| s.to_string())
                };
                let is_group = type_name
                    .as_ref()
                    .and_then(|tn| self.type_env.lookup_optional_group(tn, field))
                    .is_some();

                if is_group {
                    let gs = self.game_state.borrow();
                    match gs.read_field(&entity, field) {
                        Some(val) => {
                            self.output.push(format!(
                                "{}.{} = {}",
                                handle,
                                field,
                                format_value(&val, &self.unit_suffixes)
                            ));
                        }
                        None => {
                            self.output
                                .push(format!("{handle}.{field} = <not granted>"));
                        }
                    }
                } else {
                    let gs = self.game_state.borrow();
                    let is_declared = type_name
                        .as_ref()
                        .and_then(|tn| self.type_env.lookup_fields(tn))
                        .is_some_and(|fields| fields.iter().any(|f| f.name == field));
                    match gs.read_field(&entity, field) {
                        Some(val) => {
                            self.output.push(format!(
                                "{}.{} = {}",
                                handle,
                                field,
                                format_value(&val, &self.unit_suffixes)
                            ));
                        }
                        None if is_declared => {
                            self.output.push(format!("{handle}.{field} = <unset>"));
                        }
                        None => {
                            // Check for flattened included-group field
                            let flattened = type_name
                                .as_ref()
                                .and_then(|tn| self.type_env.lookup_flattened_field(tn, field));
                            if let Some(group_name) = flattened {
                                match gs.read_field(&entity, group_name) {
                                    Some(Value::Struct {
                                        fields: group_fields,
                                        ..
                                    }) => match group_fields.get(field) {
                                        Some(val) => {
                                            self.output.push(format!(
                                                "{}.{} = {}",
                                                handle,
                                                field,
                                                format_value(val, &self.unit_suffixes)
                                            ));
                                        }
                                        None => {
                                            self.output.push(format!("{handle}.{field} = <unset>"));
                                        }
                                    },
                                    _ => {
                                        return Err(CliError::Message(format!(
                                            "included group '{group_name}' is missing in state for {handle}"
                                        )));
                                    }
                                }
                            } else {
                                return Err(CliError::Message(format!(
                                    "field '{field}' not found on {handle}"
                                )));
                            }
                        }
                    }
                }
            }
        } else {
            let handle = tail;
            let entity = self.resolve_handle(handle)?;
            let gs = self.game_state.borrow();
            let type_name = gs
                .entity_type_name(&entity)
                .ok_or_else(|| {
                    CliError::Message(format!("entity for handle '{handle}' not found in state"))
                })?
                .to_string();
            drop(gs);

            self.output.push(format!("{handle} ({type_name})"));

            if let Some(fields) = self.type_env.lookup_fields(&type_name) {
                let gs = self.game_state.borrow();
                for fi in fields {
                    let val = gs.read_field(&entity, &fi.name).map_or_else(
                        || "<unset>".into(),
                        |v| format_value(&v, &self.unit_suffixes),
                    );
                    self.output
                        .push(format!("  {}: {} = {}", fi.name, fi.ty.display(), val));
                }
            }

            // Show granted optional groups
            if let Some(DeclInfo::Entity(info)) = self.type_env.types.get(type_name.as_str()) {
                let gs = self.game_state.borrow();
                for group_info in &info.optional_groups {
                    if let Some(Value::Struct { fields, .. }) =
                        gs.read_field(&entity, &group_info.name)
                    {
                        let status = if group_info.required {
                            "included"
                        } else {
                            "granted"
                        };
                        self.output
                            .push(format!("  [group] {} ({})", group_info.name, status));
                        for fi in &group_info.fields {
                            let val = fields.get(&fi.name).map_or_else(
                                || "<unset>".into(),
                                |v| format_value(v, &self.unit_suffixes),
                            );
                            self.output.push(format!(
                                "    {}: {} = {}",
                                fi.name,
                                fi.ty.display(),
                                val
                            ));
                        }
                    }
                }
            }

            let gs = self.game_state.borrow();
            if let Some(conditions) = gs.read_conditions(&entity) {
                for cond in &conditions {
                    self.output.push(format!(
                        "  [condition] {} ({})",
                        cond.name,
                        format_value(&cond.duration, &self.unit_suffixes)
                    ));
                }
            }
        }
        Ok(())
    }

    pub(super) fn cmd_state(&mut self) -> Result<(), CliError> {
        if self.handles.is_empty() {
            self.output.push("no entities".into());
            return Ok(());
        }

        let mut sorted: Vec<_> = self.handles.iter().collect();
        sorted.sort_by_key(|(name, _)| *name);

        for (handle, entity) in &sorted {
            let gs = self.game_state.borrow();
            let type_name = gs
                .entity_type_name(entity)
                .map_or_else(|| "?".to_string(), |n| n.to_string());
            drop(gs);

            self.output.push(format!("{handle} ({type_name})"));

            if let Some(fields) = self.type_env.lookup_fields(&type_name) {
                let gs = self.game_state.borrow();
                for fi in fields {
                    let val = gs.read_field(entity, &fi.name).map_or_else(
                        || "<unset>".into(),
                        |v| format_value(&v, &self.unit_suffixes),
                    );
                    self.output
                        .push(format!("  {}: {} = {}", fi.name, fi.ty.display(), val));
                }
            }

            // Show granted optional groups
            if let Some(DeclInfo::Entity(info)) = self.type_env.types.get(type_name.as_str()) {
                let gs = self.game_state.borrow();
                for group_info in &info.optional_groups {
                    if let Some(Value::Struct { fields, .. }) =
                        gs.read_field(entity, &group_info.name)
                    {
                        let status = if group_info.required {
                            "included"
                        } else {
                            "granted"
                        };
                        self.output
                            .push(format!("  [group] {} ({})", group_info.name, status));
                        for fi in &group_info.fields {
                            let val = fields.get(&fi.name).map_or_else(
                                || "<unset>".into(),
                                |v| format_value(v, &self.unit_suffixes),
                            );
                            self.output.push(format!(
                                "    {}: {} = {}",
                                fi.name,
                                fi.ty.display(),
                                val
                            ));
                        }
                    }
                }
            }

            let gs = self.game_state.borrow();
            if let Some(conditions) = gs.read_conditions(entity) {
                for cond in &conditions {
                    self.output.push(format!(
                        "  [condition] {} ({})",
                        cond.name,
                        format_value(&cond.duration, &self.unit_suffixes)
                    ));
                }
            }
        }
        Ok(())
    }

    pub(super) fn cmd_entity(&mut self, name: &str) -> Result<(), CliError> {
        match crate::format::format_entity(&self.type_env, name, false) {
            Ok(lines) => {
                self.output.extend(lines);
                Ok(())
            }
            Err(msg) => Err(CliError::Message(msg)),
        }
    }

    pub(super) fn cmd_types(&mut self) -> Result<(), CliError> {
        let lines = crate::format::format_types(&self.type_env);
        if lines.is_empty() {
            self.output.push("no types".into());
        } else {
            self.output.extend(lines);
        }
        Ok(())
    }

    pub(super) fn cmd_actions(&mut self) -> Result<(), CliError> {
        let lines = crate::format::format_actions(&self.type_env);
        if lines.is_empty() {
            self.output.push("no actions".into());
        } else {
            self.output.extend(lines);
        }
        Ok(())
    }

    pub(super) fn cmd_mechanics(&mut self) -> Result<(), CliError> {
        let lines = crate::format::format_mechanics(&self.type_env);
        if lines.is_empty() {
            self.output.push("no mechanics".into());
        } else {
            self.output.extend(lines);
        }
        Ok(())
    }

    pub(super) fn cmd_functions(&mut self) -> Result<(), CliError> {
        let lines = crate::format::format_functions(&self.type_env);
        if lines.is_empty() {
            self.output.push("no functions".into());
        } else {
            self.output.extend(lines);
        }
        Ok(())
    }

    pub(super) fn cmd_reactions(&mut self) -> Result<(), CliError> {
        let lines = crate::format::format_reactions(&self.type_env);
        if lines.is_empty() {
            self.output.push("no reactions".into());
        } else {
            self.output.extend(lines);
        }
        Ok(())
    }

    pub(super) fn cmd_hooks(&mut self) -> Result<(), CliError> {
        let lines = crate::format::format_hooks(&self.type_env);
        if lines.is_empty() {
            self.output.push("no hooks".into());
        } else {
            self.output.extend(lines);
        }
        Ok(())
    }

    pub(super) fn cmd_condition_decls(&mut self) -> Result<(), CliError> {
        let lines = crate::format::format_condition_decls(&self.type_env);
        if lines.is_empty() {
            self.output.push("no condition declarations".into());
        } else {
            self.output.extend(lines);
        }
        Ok(())
    }

    pub(super) fn cmd_events(&mut self) -> Result<(), CliError> {
        let lines = crate::format::format_events(&self.type_env);
        if lines.is_empty() {
            self.output.push("no events".into());
        } else {
            self.output.extend(lines);
        }
        Ok(())
    }

    pub(super) fn cmd_enable(&mut self, name: &str) -> Result<(), CliError> {
        let name = name.trim();
        if !self.type_env.options.contains(name) {
            return Err(CliError::Message(format!("unknown option '{name}'")));
        }
        self.game_state.borrow_mut().enable_option(name);
        self.output.push(format!("enabled option '{name}'"));
        Ok(())
    }

    pub(super) fn cmd_disable(&mut self, name: &str) -> Result<(), CliError> {
        let name = name.trim();
        if !self.type_env.options.contains(name) {
            return Err(CliError::Message(format!("unknown option '{name}'")));
        }
        self.game_state.borrow_mut().disable_option(name);
        self.output.push(format!("disabled option '{name}'"));
        Ok(())
    }

    pub(super) fn cmd_options(&mut self) -> Result<(), CliError> {
        if self.program.options.is_empty() {
            self.output.push("no options".into());
            return Ok(());
        }
        let enabled = self.game_state.borrow().read_enabled_options();
        let enabled_set: std::collections::HashSet<&str> =
            enabled.iter().map(|n| n.as_str()).collect();
        // Use option_order for deterministic output
        for name in &self.program.option_order {
            let status = if enabled_set.contains(name.as_str()) {
                "on"
            } else {
                "off"
            };
            let decl = &self.program.options[name];
            let desc = decl
                .description
                .as_deref()
                .map(|d| format!(" — {d}"))
                .unwrap_or_default();
            self.output.push(format!("  {name} [{status}]{desc}"));
        }
        Ok(())
    }

    pub(super) fn cmd_conditions(&mut self) -> Result<(), CliError> {
        if self.handles.is_empty() {
            self.output.push("no entities".into());
            return Ok(());
        }

        let mut sorted: Vec<_> = self.handles.iter().collect();
        sorted.sort_by_key(|(name, _)| *name);

        let mut found_any = false;
        for (handle, entity) in &sorted {
            let gs = self.game_state.borrow();
            if let Some(conditions) = gs.read_conditions(entity) {
                for cond in &conditions {
                    self.output.push(format!(
                        "{}: {} ({})",
                        handle,
                        cond.name,
                        format_value(&cond.duration, &self.unit_suffixes)
                    ));
                    found_any = true;
                }
            }
        }

        if !found_any {
            self.output.push("no active conditions".into());
        }
        Ok(())
    }

    /// `breakdown <expr>` — evaluate expression and show modify provenance.
    pub(super) fn cmd_breakdown(&mut self, tail: &str) -> Result<(), CliError> {
        use ttrpg_interp::effect::{Effect, ModifySource};

        let (parsed, diags) = ttrpg_parser::parse_expr(tail);
        if !diags.is_empty() {
            let msgs: Vec<_> = diags.iter().map(|d| d.message.as_str()).collect();
            return Err(CliError::Message(format!(
                "parse error: {}",
                msgs.join("; ")
            )));
        }
        let parsed =
            parsed.ok_or_else(|| CliError::Message("failed to parse expression".into()))?;

        let cov_rc = self.coverage_rc();
        let mut interp = TrackedInterpreter::new(&self.program, &self.type_env, &self.game_state)
            .map_err(|e| render_runtime_error(&e, &self.source_map))?;
        if let Some(cov) = cov_rc {
            interp.interp.set_coverage(cov);
        }

        let state = RefCellState(&self.game_state);
        let mut handler = crate::effects::CliHandler::new(
            &self.game_state,
            &self.reverse_handles,
            &mut self.rng,
            &mut self.roll_queue,
            &mut self.prompt_queue,
            &self.unit_suffixes,
        )
        .quiet(true); // suppress normal log output

        let bindings: rustc_hash::FxHashMap<ttrpg_ast::Name, Value> = self
            .variables
            .iter()
            .map(|(name, val)| (ttrpg_ast::Name::from(name.as_str()), val.clone()))
            .chain(self.handles.iter().map(|(name, entity)| {
                (ttrpg_ast::Name::from(name.as_str()), Value::Entity(*entity))
            }))
            .collect();

        let result = interp
            .evaluate_expr_with_bindings(&state, &mut handler, &parsed, bindings)
            .map_err(|e| render_runtime_error(&e, &self.source_map))?;

        // Extract ModifyApplied effects
        let modify_effects: Vec<_> = handler
            .effects
            .iter()
            .filter_map(|e| match e {
                Effect::ModifyApplied {
                    source,
                    target_fn,
                    phase,
                    changes,
                    tags,
                } => Some((source, target_fn, phase, changes, tags)),
                _ => None,
            })
            .collect();

        // Format result
        self.output.push(format!(
            "result: {}",
            format_value(&result, &self.unit_suffixes)
        ));

        if modify_effects.is_empty() {
            self.output.push("  (no modifiers applied)".into());
        } else {
            self.output
                .push(format!("  {} modifier(s) applied:", modify_effects.len()));
            for (source, target_fn, phase, changes, tags) in &modify_effects {
                let source_str = match source {
                    ModifySource::Condition(c) => format!("condition {c}"),
                    ModifySource::Option(o) => format!("option {o}"),
                };
                let tag_str = if tags.is_empty() {
                    String::new()
                } else {
                    let tag_list: Vec<_> = tags.iter().map(|t| format!("#{t}")).collect();
                    format!(" [{}]", tag_list.join(", "))
                };
                self.output.push(format!(
                    "  - {source_str}{tag_str} on {target_fn} ({phase:?}):"
                ));
                for change in *changes {
                    self.output.push(format!(
                        "      {}: {} -> {}",
                        change.name,
                        format_value(&change.old, &self.unit_suffixes),
                        format_value(&change.new, &self.unit_suffixes),
                    ));
                }
            }
        }

        Ok(())
    }
}
