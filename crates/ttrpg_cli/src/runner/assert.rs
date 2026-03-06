use super::*;

impl Runner {
    pub(super) fn cmd_assert(&mut self, expr_str: &str) -> Result<(), CliError> {
        let val = self.eval(expr_str)?;
        match val {
            Value::Bool(true) => Ok(()),
            Value::Bool(false) => Err(CliError::Message(format!(
                "assertion failed: {expr_str} evaluated to false"
            ))),
            _ => Err(CliError::Message(format!(
                "assertion error: expected bool, got {}",
                value_type_display(&val)
            ))),
        }
    }

    pub(super) fn cmd_assert_eq(&mut self, tail: &str) -> Result<(), CliError> {
        let parts = split_top_level_commas(tail);
        if parts.len() != 2 {
            return Err(CliError::Message(
                "usage: assert_eq <expr1>, <expr2>".into(),
            ));
        }
        let left_str = parts[0].trim();
        let right_str = parts[1].trim();
        if left_str.is_empty() || right_str.is_empty() {
            return Err(CliError::Message(
                "usage: assert_eq <expr1>, <expr2>".into(),
            ));
        }
        let left = self.eval(left_str)?;
        let right = self.eval(right_str)?;
        if left == right {
            Ok(())
        } else {
            Err(CliError::Message(format!(
                "assertion failed: {} != {}\n  left:  {}\n  right: {}",
                left_str,
                right_str,
                format_value(&left, &self.unit_suffixes),
                format_value(&right, &self.unit_suffixes)
            )))
        }
    }

    pub(super) fn cmd_assert_ne(&mut self, tail: &str) -> Result<(), CliError> {
        let parts = split_top_level_commas(tail);
        if parts.len() != 2 {
            return Err(CliError::Message(
                "usage: assert_ne <expr1>, <expr2>".into(),
            ));
        }
        let left_str = parts[0].trim();
        let right_str = parts[1].trim();
        if left_str.is_empty() || right_str.is_empty() {
            return Err(CliError::Message(
                "usage: assert_ne <expr1>, <expr2>".into(),
            ));
        }
        let left = self.eval(left_str)?;
        let right = self.eval(right_str)?;
        if left != right {
            Ok(())
        } else {
            Err(CliError::Message(format!(
                "assertion failed: {} == {}\n  both: {}",
                left_str,
                right_str,
                format_value(&left, &self.unit_suffixes)
            )))
        }
    }

    pub(super) fn cmd_assert_match(&mut self, tail: &str) -> Result<(), CliError> {
        let parts = split_top_level_commas(tail);
        if parts.len() != 2 {
            return Err(CliError::Message(
                "usage: assert_match <expr>, <EnumName>.<Variant>".into(),
            ));
        }
        let expr_str = parts[0].trim();
        let pattern_str = parts[1].trim();
        if expr_str.is_empty() || pattern_str.is_empty() {
            return Err(CliError::Message(
                "usage: assert_match <expr>, <EnumName>.<Variant>".into(),
            ));
        }

        let Some((enum_name, variant_name)) = pattern_str.split_once('.') else {
            return Err(CliError::Message(format!(
                "invalid pattern: expected EnumName.Variant, got {pattern_str}"
            )));
        };
        let enum_name = enum_name.trim();
        let variant_name = variant_name.trim();
        if enum_name.is_empty() || variant_name.is_empty() {
            return Err(CliError::Message(
                "usage: assert_match <expr>, <EnumName>.<Variant>".into(),
            ));
        }

        let val = self.eval(expr_str)?;
        match &val {
            Value::EnumVariant {
                enum_name: actual_enum,
                variant: actual_variant,
                ..
            } if actual_enum.as_ref() == enum_name
                && actual_variant.as_ref() == variant_name =>
            {
                Ok(())
            }
            _ => Err(CliError::Message(format!(
                "assertion failed: expected {enum_name}.{variant_name}, got {}",
                format_value(&val, &self.unit_suffixes)
            ))),
        }
    }

    pub(super) fn cmd_assert_condition(&mut self, tail: &str) -> Result<(), CliError> {
        let parts = split_top_level_commas(tail);
        if parts.len() != 2 {
            return Err(CliError::Message(
                "usage: assert_condition <handle>, <ConditionName>".into(),
            ));
        }
        let handle = parts[0].trim();
        let condition_name = parts[1].trim();
        if handle.is_empty() || condition_name.is_empty() {
            return Err(CliError::Message(
                "usage: assert_condition <handle>, <ConditionName>".into(),
            ));
        }
        let entity = self.resolve_handle(handle)?;
        let gs = self.game_state.borrow();
        let has_condition = gs
            .read_conditions(&entity)
            .is_some_and(|conds| conds.iter().any(|c| c.name.as_ref() == condition_name));
        if has_condition {
            Ok(())
        } else {
            Err(CliError::Message(format!(
                "assertion failed: {handle} does not have condition '{condition_name}'"
            )))
        }
    }

    pub(super) fn cmd_assert_no_condition(&mut self, tail: &str) -> Result<(), CliError> {
        let parts = split_top_level_commas(tail);
        if parts.len() != 2 {
            return Err(CliError::Message(
                "usage: assert_no_condition <handle>, <ConditionName>".into(),
            ));
        }
        let handle = parts[0].trim();
        let condition_name = parts[1].trim();
        if handle.is_empty() || condition_name.is_empty() {
            return Err(CliError::Message(
                "usage: assert_no_condition <handle>, <ConditionName>".into(),
            ));
        }
        let entity = self.resolve_handle(handle)?;
        let gs = self.game_state.borrow();
        let has_condition = gs
            .read_conditions(&entity)
            .is_some_and(|conds| conds.iter().any(|c| c.name.as_ref() == condition_name));
        if !has_condition {
            Ok(())
        } else {
            Err(CliError::Message(format!(
                "assertion failed: {handle} has condition '{condition_name}'"
            )))
        }
    }

    pub(super) fn cmd_assert_err(&mut self, tail: &str) -> Result<(), CliError> {
        let output_len = self.output.len();
        match self.exec_inner(tail) {
            Err(_) => {
                // Expected error — suppress any output generated by the failed command
                self.output.truncate(output_len);
                Ok(())
            }
            Ok(()) => Err(CliError::Message(format!(
                "assertion failed: expected error from: {tail}"
            ))),
        }
    }
}
