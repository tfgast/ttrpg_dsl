use super::*;

impl Runner {
    pub(super) fn cmd_seed(&mut self, tail: &str) -> Result<(), CliError> {
        let seed: u64 = tail
            .trim()
            .parse()
            .map_err(|_| CliError::Message(format!("invalid seed: {}", tail.trim())))?;
        self.rng = StdRng::seed_from_u64(seed);
        self.output.push(format!("seed set to {}", seed));
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
                    .map_err(|_| CliError::Message(format!("invalid roll value: {}", token)))
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
