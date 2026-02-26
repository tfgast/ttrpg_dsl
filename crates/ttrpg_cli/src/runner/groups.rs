use super::*;

impl Runner {
    /// Validate supplied fields against the optional-group schema, fill
    /// defaults for missing fields, check all required fields are present,
    /// and return the built `Value::Struct`.
    pub(super) fn validate_and_prepare_group(
        &mut self,
        group_name: &str,
        entity_type: &str,
        mut fields: HashMap<String, Value>,
    ) -> Result<Value, CliError> {
        let group_info = self
            .type_env
            .lookup_optional_group(entity_type, group_name)
            .ok_or_else(|| {
                CliError::Message(format!(
                    "unknown group '{}' on entity type '{}'",
                    group_name, entity_type
                ))
            })?
            .clone();

        for (field_name, field_val) in &fields {
            match group_info.fields.iter().find(|f| f.name == field_name.as_str()) {
                None => {
                    return Err(CliError::Message(format!(
                        "unknown field '{}' in group '{}'",
                        field_name, group_name
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

        self.fill_group_defaults(group_name, entity_type, &mut fields)?;

        for fi in &group_info.fields {
            if !fi.has_default && !fields.contains_key(fi.name.as_str()) {
                return Err(CliError::Message(format!(
                    "missing required field '{}' in group '{}'",
                    fi.name, group_name
                )));
            }
        }

        let btree_fields: BTreeMap<Name, Value> = fields.into_iter().map(|(k, v)| (Name::from(k), v)).collect();
        Ok(Value::Struct {
            name: Name::from(group_name),
            fields: btree_fields,
        })
    }

    /// Find resolved AST field defs for an optional group on an entity.
    pub(super) fn find_optional_group_ast_fields(
        &self,
        entity_type: &str,
        group_name: &str,
    ) -> Option<Vec<FieldDef>> {
        for item in &self.program.items {
            if let TopLevel::System(system) = &item.node {
                for decl in &system.decls {
                    if let DeclKind::Entity(entity_decl) = &decl.node {
                        if entity_decl.name == entity_type {
                            for group in &entity_decl.optional_groups {
                                if group.name == group_name {
                                    if group.is_external_ref {
                                        return self.find_group_decl_fields(group_name);
                                    }
                                    return Some(group.fields.clone());
                                }
                            }
                        }
                    }
                }
            }
        }
        None
    }

    fn find_group_decl_fields(&self, group_name: &str) -> Option<Vec<FieldDef>> {
        for item in &self.program.items {
            if let TopLevel::System(system) = &item.node {
                for decl in &system.decls {
                    if let DeclKind::Group(group_decl) = &decl.node {
                        if group_decl.name == group_name {
                            return Some(group_decl.fields.clone());
                        }
                    }
                }
            }
        }
        None
    }

    /// Fill default values for missing fields in a group.
    pub(super) fn fill_group_defaults(
        &mut self,
        group_name: &str,
        entity_type: &str,
        fields: &mut HashMap<String, Value>,
    ) -> Result<(), CliError> {
        let group_fields = match self.find_optional_group_ast_fields(entity_type, group_name) {
            Some(g) => g,
            None => return Ok(()),
        };

        for field_def in &group_fields {
            if fields.contains_key(field_def.name.as_str()) {
                continue;
            }
            if let Some(ref default_expr) = field_def.default {
                let interp = Interpreter::new(&self.program, &self.type_env)
                    .map_err(|e| CliError::Message(format!("interpreter error: {}", e)))?;
                let state = RefCellState(&self.game_state);
                let mut handler = CliHandler::new(
                    &self.game_state,
                    &self.reverse_handles,
                    &mut self.rng,
                    &mut self.roll_queue,
                );
                let val = interp
                    .evaluate_expr(&state, &mut handler, default_expr)
                    .map_err(|e| {
                        for line in handler.log.drain(..) {
                            self.output.push(line);
                        }
                        CliError::Message(format!(
                            "error evaluating default for field '{}': {}",
                            field_def.name, e
                        ))
                    })?;
                for line in handler.log.drain(..) {
                    self.output.push(line);
                }
                fields.insert(field_def.name.to_string(), val);
            }
        }
        Ok(())
    }
}
