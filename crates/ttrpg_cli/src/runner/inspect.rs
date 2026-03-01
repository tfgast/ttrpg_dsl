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
                                "field '{}' not found in group '{}'",
                                field_name, group_name
                            )));
                        }
                    },
                    Some(_) => {
                        return Err(CliError::Message(format!(
                            "field '{}' is not a group on {}",
                            group_name, handle
                        )));
                    }
                    None => {
                        let type_name = gs.entity_type_name(&entity).map(|s| s.to_string());
                        let group_info = type_name
                            .as_deref()
                            .and_then(|tn| self.type_env.lookup_optional_group(tn, group_name));
                        let suffix = match group_info {
                            Some(info) if info.required => "is required but missing in state",
                            _ => "is not currently granted",
                        };
                        return Err(CliError::Message(format!(
                            "{}.{} {}",
                            handle, group_name, suffix
                        )));
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
                                .push(format!("{}.{} = <not granted>", handle, field));
                        }
                    }
                } else {
                    let gs = self.game_state.borrow();
                    let is_declared = type_name
                        .as_ref()
                        .and_then(|tn| self.type_env.lookup_fields(tn))
                        .map(|fields| fields.iter().any(|f| f.name == field))
                        .unwrap_or(false);
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
                            self.output.push(format!("{}.{} = <unset>", handle, field));
                        }
                        None => {
                            // Check for flattened included-group field
                            let flattened = type_name.as_ref().and_then(|tn| {
                                self.type_env.lookup_flattened_field(tn, field)
                            });
                            if let Some(group_name) = flattened {
                                match gs.read_field(&entity, group_name) {
                                    Some(Value::Struct { fields: group_fields, .. }) => {
                                        match group_fields.get(field) {
                                            Some(val) => {
                                                self.output.push(format!(
                                                    "{}.{} = {}",
                                                    handle,
                                                    field,
                                                    format_value(val, &self.unit_suffixes)
                                                ));
                                            }
                                            None => {
                                                self.output.push(format!(
                                                    "{}.{} = <unset>",
                                                    handle, field
                                                ));
                                            }
                                        }
                                    }
                                    _ => {
                                        return Err(CliError::Message(format!(
                                            "included group '{}' is missing in state for {}",
                                            group_name, handle
                                        )));
                                    }
                                }
                            } else {
                                return Err(CliError::Message(format!(
                                    "field '{}' not found on {}",
                                    field, handle
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
                    CliError::Message(format!("entity for handle '{}' not found in state", handle))
                })?
                .to_string();
            drop(gs);

            self.output.push(format!("{} ({})", handle, type_name));

            if let Some(fields) = self.type_env.lookup_fields(&type_name) {
                let gs = self.game_state.borrow();
                for fi in fields {
                    let val = gs
                        .read_field(&entity, &fi.name)
                        .map(|v| format_value(&v, &self.unit_suffixes))
                        .unwrap_or_else(|| "<unset>".into());
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
                            let val = fields
                                .get(&fi.name)
                                .map(|v| format_value(v, &self.unit_suffixes))
                                .unwrap_or_else(|| "<unset>".into());
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
                .map(|n| n.to_string())
                .unwrap_or_else(|| "?".to_string());
            drop(gs);

            self.output.push(format!("{} ({})", handle, type_name));

            if let Some(fields) = self.type_env.lookup_fields(&type_name) {
                let gs = self.game_state.borrow();
                for fi in fields {
                    let val = gs
                        .read_field(entity, &fi.name)
                        .map(|v| format_value(&v, &self.unit_suffixes))
                        .unwrap_or_else(|| "<unset>".into());
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
                            let val = fields
                                .get(&fi.name)
                                .map(|v| format_value(v, &self.unit_suffixes))
                                .unwrap_or_else(|| "<unset>".into());
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

    pub(super) fn cmd_types(&mut self) -> Result<(), CliError> {
        let mut sorted: Vec<_> = self.type_env.types.iter().collect();
        sorted.sort_by_key(|(name, _)| *name);

        if sorted.is_empty() {
            self.output.push("no types".into());
            return Ok(());
        }

        for (name, decl) in &sorted {
            match decl {
                DeclInfo::Entity(info) => {
                    self.output.push(format!("entity {}", name));
                    for fi in &info.fields {
                        self.output
                            .push(format!("  {}: {}", fi.name, fi.ty.display()));
                    }
                    for group in &info.optional_groups {
                        let decl_kw = if group.required {
                            "include"
                        } else {
                            "optional"
                        };
                        self.output.push(format!("  {} {}", decl_kw, group.name));
                        for fi in &group.fields {
                            self.output
                                .push(format!("    {}: {}", fi.name, fi.ty.display()));
                        }
                    }
                }
                DeclInfo::Struct(info) => {
                    self.output.push(format!("struct {}", name));
                    for fi in &info.fields {
                        self.output
                            .push(format!("  {}: {}", fi.name, fi.ty.display()));
                    }
                }
                DeclInfo::Enum(info) => {
                    self.output.push(format!("enum {}", name));
                    for variant in &info.variants {
                        if variant.fields.is_empty() {
                            self.output.push(format!("  {}", variant.name));
                        } else {
                            let fields: Vec<String> = variant
                                .fields
                                .iter()
                                .map(|(n, t)| format!("{}: {}", n, t.display()))
                                .collect();
                            self.output
                                .push(format!("  {}({})", variant.name, fields.join(", ")));
                        }
                    }
                }
                DeclInfo::Unit(info) => {
                    let suffix_str = match &info.suffix {
                        Some(s) => format!(" suffix {}", s),
                        None => String::new(),
                    };
                    self.output.push(format!("unit {}{}", name, suffix_str));
                    for fi in &info.fields {
                        self.output
                            .push(format!("  {}: {}", fi.name, fi.ty.display()));
                    }
                }
            }
        }
        Ok(())
    }

    pub(super) fn cmd_actions(&mut self) -> Result<(), CliError> {
        let mut actions: Vec<_> = self
            .type_env
            .functions
            .values()
            .filter(|fi| matches!(fi.kind, FnKind::Action))
            .collect();
        actions.sort_by(|a, b| a.name.cmp(&b.name));

        if actions.is_empty() {
            self.output.push("no actions".into());
            return Ok(());
        }

        for fi in &actions {
            let receiver = fi
                .receiver
                .as_ref()
                .map(|r| format!("{}: {}", r.name, r.ty.display()))
                .unwrap_or_default();
            let params: Vec<String> = fi
                .params
                .iter()
                .map(|p| format!("{}: {}", p.name, p.ty.display()))
                .collect();
            let all_params = if receiver.is_empty() {
                params.join(", ")
            } else if params.is_empty() {
                receiver
            } else {
                format!("{}, {}", receiver, params.join(", "))
            };
            self.output.push(format!(
                "action {}({}) -> {}",
                fi.name,
                all_params,
                fi.return_type.display()
            ));
        }
        Ok(())
    }

    pub(super) fn cmd_mechanics(&mut self) -> Result<(), CliError> {
        let mut fns: Vec<_> = self
            .type_env
            .functions
            .values()
            .filter(|fi| matches!(fi.kind, FnKind::Mechanic | FnKind::Derive))
            .collect();
        fns.sort_by(|a, b| a.name.cmp(&b.name));

        if fns.is_empty() {
            self.output.push("no mechanics".into());
            return Ok(());
        }

        for fi in &fns {
            let kind_label = match fi.kind {
                FnKind::Derive => "derive",
                FnKind::Mechanic => "mechanic",
                _ => unreachable!(),
            };
            let params: Vec<String> = fi
                .params
                .iter()
                .map(|p| format!("{}: {}", p.name, p.ty.display()))
                .collect();
            self.output.push(format!(
                "{} {}({}) -> {}",
                kind_label,
                fi.name,
                params.join(", "),
                fi.return_type.display()
            ));
        }
        Ok(())
    }

    pub(super) fn cmd_enable(&mut self, name: &str) -> Result<(), CliError> {
        let name = name.trim();
        if !self.type_env.options.contains(name) {
            return Err(CliError::Message(format!(
                "unknown option '{}'",
                name
            )));
        }
        self.game_state.borrow_mut().enable_option(name);
        self.output.push(format!("enabled option '{}'", name));
        Ok(())
    }

    pub(super) fn cmd_disable(&mut self, name: &str) -> Result<(), CliError> {
        let name = name.trim();
        if !self.type_env.options.contains(name) {
            return Err(CliError::Message(format!(
                "unknown option '{}'",
                name
            )));
        }
        self.game_state.borrow_mut().disable_option(name);
        self.output.push(format!("disabled option '{}'", name));
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
                .map(|d| format!(" — {}", d))
                .unwrap_or_default();
            self.output
                .push(format!("  {} [{}]{}", name, status, desc));
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
}
