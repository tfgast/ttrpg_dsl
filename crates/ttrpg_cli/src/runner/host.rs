use std::collections::BTreeMap;

use ttrpg_ast::Name;
use ttrpg_interp::reference_state::GridPosition;
use ttrpg_interp::value::Value;

use super::*;

impl Runner {
    /// `emit EventName(param: expr, param: expr, ...)`
    ///
    /// Fire a DSL event from the host side, executing all matching hooks and
    /// reactions. Arguments are evaluated as normal DSL expressions with handle
    /// resolution. This lets test scripts inject zone events, damage events, etc.
    /// without a full spatial simulation.
    pub(super) fn cmd_emit(&mut self, tail: &str) -> Result<(), CliError> {
        let tail = tail.trim();

        // Parse: EventName(arg1: expr1, arg2: expr2, ...)
        let paren_pos = tail
            .find('(')
            .ok_or_else(|| CliError::Message("usage: emit EventName(param: expr, ...)".into()))?;
        let event_name = tail[..paren_pos].trim();
        if event_name.is_empty() {
            return Err(CliError::Message(
                "usage: emit EventName(param: expr, ...)".into(),
            ));
        }

        // Verify event exists
        if !self.program.events.contains_key(event_name) {
            return Err(CliError::Message(format!("undefined event '{event_name}'")));
        }

        // Extract the args portion (between parens)
        let args_str = tail[paren_pos..]
            .strip_prefix('(')
            .and_then(|s| s.strip_suffix(')'))
            .ok_or_else(|| CliError::Message("unmatched '(' in emit".into()))?;

        // Parse and evaluate named arguments: "param: expr, param: expr"
        let mut param_map = BTreeMap::new();
        let entries = split_top_level_commas(args_str);
        for entry in entries {
            let entry = entry.trim();
            if entry.is_empty() {
                continue;
            }
            let colon_pos = entry.find(':').ok_or_else(|| {
                CliError::Message(format!(
                    "expected 'param: expr' in emit arguments, got: {entry}"
                ))
            })?;
            let param_name = entry[..colon_pos].trim();
            let val_str = entry[colon_pos + 1..].trim();
            if param_name.is_empty() || val_str.is_empty() {
                return Err(CliError::Message(format!(
                    "invalid argument entry: {entry}"
                )));
            }
            let val = self.eval(val_str)?;
            param_map.insert(Name::from(param_name), val);
        }

        // Clone event_decl now (before mutable borrows)
        let event_decl = self.program.events.get(event_name).unwrap().clone();

        // Fill defaults for missing params (using self.eval on default exprs)
        for p in &event_decl.params {
            if !param_map.contains_key(&p.name) {
                if p.default.is_some() {
                    // Evaluate the default expression through the standard eval path
                    let cov_rc = self.coverage_rc();
                    let mut interp = TrackedInterpreter::new(
                        &self.program,
                        &self.type_env,
                        &self.game_state,
                        &self.source_map,
                    )?;
                    if let Some(cov) = cov_rc {
                        interp.interp.set_coverage(cov);
                    }
                    let state = RefCellState(&self.game_state);
                    let mut handler = CliHandler::new(
                        &self.game_state,
                        &self.reverse_handles,
                        &mut self.rng,
                        &mut self.roll_queue,
                        &mut self.prompt_queue,
                        &self.unit_suffixes,
                    )
                    .quiet(self.quiet)
                    .interactive(self.interactive);
                    let bindings: rustc_hash::FxHashMap<Name, Value> = self
                        .variables
                        .iter()
                        .map(|(name, val)| (Name::from(name.as_str()), val.clone()))
                        .chain(self.handles.iter().map(|(name, entity)| {
                            (Name::from(name.as_str()), Value::Entity(*entity))
                        }))
                        .collect();
                    let val = interp
                        .evaluate_expr_with_bindings(
                            &state,
                            &mut handler,
                            p.default.as_ref().unwrap(),
                            bindings,
                        )
                        .map_err(|e| {
                            for line in handler.log.drain(..) {
                                self.output.push(line);
                            }
                            render_runtime_error(&e, &self.source_map)
                        })?;
                    for line in handler.log.drain(..) {
                        self.output.push(line);
                    }
                    param_map.insert(p.name.clone(), val);
                }
            }
        }

        // Evaluate derived fields (event body defaults) with params in scope
        let mut all_fields = param_map.clone();
        for f in &event_decl.fields {
            if !all_fields.contains_key(&f.name) {
                if f.default.is_some() {
                    let cov_rc = self.coverage_rc();
                    let mut interp = TrackedInterpreter::new(
                        &self.program,
                        &self.type_env,
                        &self.game_state,
                        &self.source_map,
                    )?;
                    if let Some(cov) = cov_rc {
                        interp.interp.set_coverage(cov);
                    }
                    let state = RefCellState(&self.game_state);
                    let mut handler = CliHandler::new(
                        &self.game_state,
                        &self.reverse_handles,
                        &mut self.rng,
                        &mut self.roll_queue,
                        &mut self.prompt_queue,
                        &self.unit_suffixes,
                    )
                    .quiet(self.quiet)
                    .interactive(self.interactive);
                    // Include params so derived fields can reference them
                    let mut bindings: rustc_hash::FxHashMap<Name, Value> = self
                        .variables
                        .iter()
                        .map(|(name, val)| (Name::from(name.as_str()), val.clone()))
                        .chain(self.handles.iter().map(|(name, entity)| {
                            (Name::from(name.as_str()), Value::Entity(*entity))
                        }))
                        .collect();
                    for (name, val) in &all_fields {
                        bindings.insert(name.clone(), val.clone());
                    }
                    let val = interp
                        .evaluate_expr_with_bindings(
                            &state,
                            &mut handler,
                            f.default.as_ref().unwrap(),
                            bindings,
                        )
                        .map_err(|e| {
                            for line in handler.log.drain(..) {
                                self.output.push(line);
                            }
                            render_runtime_error(&e, &self.source_map)
                        })?;
                    for line in handler.log.drain(..) {
                        self.output.push(line);
                    }
                    all_fields.insert(f.name.clone(), val);
                }
            }
        }

        // Build the payload struct
        let payload = Value::Struct {
            name: Name::from(format!("__event_{event_name}")),
            fields: all_fields,
        };

        // Fire hooks and reactions
        let cov_rc = self.coverage_rc();
        let mut interp = TrackedInterpreter::new(
            &self.program,
            &self.type_env,
            &self.game_state,
            &self.source_map,
        )?;
        if let Some(cov) = cov_rc {
            interp.interp.set_coverage(cov);
        }
        let state = RefCellState(&self.game_state);
        let mut handler = CliHandler::new(
            &self.game_state,
            &self.reverse_handles,
            &mut self.rng,
            &mut self.roll_queue,
            &mut self.prompt_queue,
            &self.unit_suffixes,
        )
        .quiet(self.quiet)
        .interactive(self.interactive);
        let candidates = state.all_entities();

        let results = interp
            .fire_hooks(
                &state,
                &mut handler,
                event_name,
                payload.clone(),
                &candidates,
            )
            .map_err(|e| {
                for line in handler.log.drain(..) {
                    self.output.push(line);
                }
                render_runtime_error(&e, &self.source_map)
            })?;
        for line in handler.log.drain(..) {
            self.output.push(line);
        }

        // Also fire reactions
        let reaction_result = interp
            .what_triggers(&state, event_name, payload.clone(), &candidates)
            .map_err(|e| render_runtime_error(&e, &self.source_map))?;

        for trigger in &reaction_result.triggerable {
            let _val = interp
                .execute_reaction(
                    &state,
                    &mut handler,
                    &trigger.name,
                    trigger.reactor,
                    payload.clone(),
                )
                .map_err(|e| {
                    for line in handler.log.drain(..) {
                        self.output.push(line);
                    }
                    render_runtime_error(&e, &self.source_map)
                })?;
            for line in handler.log.drain(..) {
                self.output.push(line);
            }
        }

        let hook_count = results.len();
        let reaction_count = reaction_result.triggerable.len();
        if hook_count > 0 || reaction_count > 0 {
            let mut parts = Vec::new();
            if hook_count > 0 {
                parts.push(format!(
                    "{hook_count} hook{}",
                    if hook_count == 1 { "" } else { "s" }
                ));
            }
            if reaction_count > 0 {
                parts.push(format!(
                    "{reaction_count} reaction{}",
                    if reaction_count == 1 { "" } else { "s" }
                ));
            }
            self.output
                .push(format!("emitted {event_name}: fired {}", parts.join(", ")));
        } else {
            self.output
                .push(format!("emitted {event_name}: no handlers matched"));
        }

        Ok(())
    }

    /// `place <handle> <x> <y>` or `place <handle> at <x>,<y>`
    ///
    /// Set an entity's position field to a GridPosition value.
    /// Uses "center" for Zone entities, "position" for others.
    pub(super) fn cmd_place(&mut self, tail: &str) -> Result<(), CliError> {
        let tail = tail.trim();

        // Parse: handle x y  or  handle at x,y
        let (handle, rest) = split_first_token(tail);
        if handle.is_empty() {
            return Err(CliError::Message("usage: place <handle> <x> <y>".into()));
        }
        let rest = rest.trim();

        // Strip optional "at" keyword
        let coords = if rest.starts_with("at ") || rest.starts_with("at\t") {
            rest[2..].trim()
        } else {
            rest
        };

        // Parse x and y — support "x y" or "x,y" or "x, y"
        let (x, y) = parse_coordinates(coords)?;

        let entity = self.resolve_handle(handle)?;

        // Write the position as a GridPosition value
        let pos_value = GridPosition(x, y).to_value();

        // Determine which field to set — use "center" for Zone entities,
        // "position" for anything else
        let type_name = {
            let gs = self.game_state.borrow();
            gs.entity_type_name(&entity)
                .map(|s| s.to_string())
                .unwrap_or_default()
        };

        let field_name = if type_name == "Zone" {
            "center"
        } else {
            let gs = self.game_state.borrow();
            if gs.read_field(&entity, "position").is_some() {
                "position"
            } else if gs.read_field(&entity, "center").is_some() {
                "center"
            } else {
                "position"
            }
        };

        {
            let mut gs = self.game_state.borrow_mut();
            gs.write_field(
                &entity,
                &[ttrpg_interp::effect::FieldPathSegment::Field(Name::from(
                    field_name,
                ))],
                pos_value,
            );
        }

        self.output.push(format!("placed {handle} at ({x}, {y})"));

        Ok(())
    }
}

/// Parse coordinate string like "3 4", "3,4", or "3, 4" into (x, y).
fn parse_coordinates(s: &str) -> Result<(i64, i64), CliError> {
    // Try comma-separated first
    if let Some(comma_pos) = s.find(',') {
        let x_str = s[..comma_pos].trim();
        let y_str = s[comma_pos + 1..].trim();
        let x = x_str
            .parse::<i64>()
            .map_err(|_| CliError::Message(format!("invalid x coordinate: '{x_str}'")))?;
        let y = y_str
            .parse::<i64>()
            .map_err(|_| CliError::Message(format!("invalid y coordinate: '{y_str}'")))?;
        return Ok((x, y));
    }

    // Space-separated
    let parts: Vec<&str> = s.split_whitespace().collect();
    if parts.len() != 2 {
        return Err(CliError::Message("usage: place <handle> <x> <y>".into()));
    }
    let x = parts[0]
        .parse::<i64>()
        .map_err(|_| CliError::Message(format!("invalid x coordinate: '{}'", parts[0])))?;
    let y = parts[1]
        .parse::<i64>()
        .map_err(|_| CliError::Message(format!("invalid y coordinate: '{}'", parts[1])))?;
    Ok((x, y))
}
