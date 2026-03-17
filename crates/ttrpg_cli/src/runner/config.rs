use ttrpg_interp::effect::EffectKind;

use super::*;

impl Runner {
    pub(super) fn cmd_gm(&mut self, tail: &str) -> Result<(), CliError> {
        let (sub, rest) = split_first_token(tail.trim());
        match sub {
            "gate" => self.cmd_gm_gate(rest),
            "accept" => self.submit_gate(Response::Acknowledged),
            "veto" => self.submit_gate(Response::Vetoed),
            "override" => {
                let rest = rest.trim();
                if rest.is_empty() {
                    return Err(CliError::Message(
                        "gm override requires a value expression".into(),
                    ));
                }
                let val = self.eval(rest)?;
                self.submit_gate(Response::Override(val))
            }
            _ => Err(CliError::Message(format!(
                "unknown gm subcommand: {sub}. Use: gate, accept, veto, override"
            ))),
        }
    }

    fn cmd_gm_gate(&mut self, tail: &str) -> Result<(), CliError> {
        let (kind_str, on_off) = split_first_token(tail.trim());
        let on = match on_off.trim() {
            "on" => true,
            "off" => false,
            other => {
                return Err(CliError::Message(format!(
                    "expected 'on' or 'off', got '{other}'"
                )));
            }
        };

        let kinds: Vec<EffectKind> = match kind_str {
            "actions" => vec![EffectKind::ActionStarted],
            "conditions" => vec![
                EffectKind::ConditionApplyGate,
                EffectKind::ConditionRemovalGate,
            ],
            "all" => vec![
                EffectKind::ActionStarted,
                EffectKind::ConditionApplyGate,
                EffectKind::ConditionRemovalGate,
            ],
            _ => {
                return Err(CliError::Message(format!(
                    "unknown gate kind: {kind_str}. Use: actions, conditions, all"
                )));
            }
        };

        for kind in &kinds {
            if on {
                self.gm_gates.insert(*kind);
            } else {
                self.gm_gates.remove(kind);
            }
        }

        // GM gates require step-based execution to pause mid-action.
        if on && self.exec_mode != super::ExecutionMode::StepBased {
            self.exec_mode = super::ExecutionMode::StepBased;
        }

        let state = if on { "enabled" } else { "disabled" };
        self.output
            .push(format!("gm gate {kind_str} {state}"));
        Ok(())
    }

    pub(super) fn cmd_seed(&mut self, tail: &str) -> Result<(), CliError> {
        let seed: u64 = tail
            .trim()
            .parse()
            .map_err(|_| CliError::Message(format!("invalid seed: {}", tail.trim())))?;
        self.rng = StdRng::seed_from_u64(seed);
        self.output.push(format!("seed set to {seed}"));
        Ok(())
    }

    pub(super) fn cmd_prompts(&mut self, tail: &str) -> Result<(), CliError> {
        let tail = tail.trim();
        if tail == "clear" {
            self.prompt_queue.clear();
            self.output.push("prompt queue cleared".into());
            return Ok(());
        }

        // Parse each token as an expression, evaluating at queue time so
        // syntax errors are reported immediately rather than mid-execution.
        let (parsed, diags) = ttrpg_parser::parse_expr(tail);
        if !diags.is_empty() {
            let msgs: Vec<_> = diags.iter().map(|d| d.message.as_str()).collect();
            return Err(CliError::Message(format!(
                "invalid prompt value: {}",
                msgs.join("; ")
            )));
        }
        let parsed = parsed
            .ok_or_else(|| CliError::Message(format!("failed to parse prompt value: {tail}")))?;

        let interp = ttrpg_interp::Interpreter::new(&self.program, &self.type_env)
            .map_err(|e| render_runtime_error(&e, &self.source_map))?;
        let state = RefCellState(&self.game_state);
        let mut handler = crate::effects::CliHandler::new(
            &self.game_state,
            self.handles.by_entity(),
            &mut self.rng,
            &mut self.roll_queue,
            &mut self.prompt_queue,
            &self.unit_suffixes,
        )
        .quiet(true);
        let bindings: rustc_hash::FxHashMap<Name, Value> = self
            .variables
            .iter()
            .map(|(name, val)| (Name::from(name.as_str()), val.clone()))
            .chain(
                self.handles
                    .iter()
                    .map(|(name, entity)| (Name::from(name), Value::Entity(*entity))),
            )
            .collect();
        let val = interp
            .evaluate_expr_with_bindings(&state, &mut handler, &parsed, bindings)
            .map_err(|e| render_runtime_error(&e, &self.source_map))?;

        self.prompt_queue.push_back(val);
        self.output.push(format!(
            "queued 1 prompt response ({} total)",
            self.prompt_queue.len()
        ));
        Ok(())
    }

    pub(super) fn cmd_rolls(&mut self, tail: &str) -> Result<(), CliError> {
        let tail = tail.trim();
        if tail == "clear" {
            self.roll_queue.clear();
            self.output.push("roll queue cleared".into());
            return Ok(());
        }
        // Parse all values first so a bad token doesn't leave partial state
        let vals: Vec<i64> = tail
            .split_whitespace()
            .map(|token| {
                token
                    .parse()
                    .map_err(|_| CliError::Message(format!("invalid roll value: {token}")))
            })
            .collect::<Result<_, _>>()?;
        let count = vals.len();
        self.roll_queue.extend(vals);
        self.output.push(format!(
            "queued {} roll{} ({} total)",
            count,
            if count == 1 { "" } else { "s" },
            self.roll_queue.len()
        ));
        Ok(())
    }
}
