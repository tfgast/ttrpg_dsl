use crate::effects::RefCellState;

use super::*;

impl Runner {
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
            &self.reverse_handles,
            &mut self.rng,
            &mut self.roll_queue,
            &mut self.prompt_queue,
            &self.unit_suffixes,
        )
        .quiet(true);
        let val = interp
            .evaluate_expr(&state, &mut handler, &parsed)
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
