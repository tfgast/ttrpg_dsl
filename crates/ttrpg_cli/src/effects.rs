use ttrpg_interp::effect::{Effect, EffectHandler, Response};

/// A minimal effect handler for the CLI.
///
/// Acknowledges all informational/mutation/gate effects.
/// Returns `RuntimeError`-inducing responses for `RollDice` and `ResolvePrompt`
/// since the CLI has no RNG or user interaction in Phase 1.
pub struct MinimalHandler;

impl EffectHandler for MinimalHandler {
    fn handle(&mut self, effect: Effect) -> Response {
        match &effect {
            Effect::RollDice { .. } | Effect::ResolvePrompt { .. } => {
                // Phase 1: no RNG or interaction support.
                // Return Vetoed — the interpreter will produce a RuntimeError
                // for RollDice (which requires a Rolled response).
                // For ResolvePrompt, Vetoed similarly signals inability.
                Response::Vetoed
            }
            _ => Response::Acknowledged,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ttrpg_interp::value::DiceExpr;

    #[test]
    fn acknowledges_action_started() {
        let mut handler = MinimalHandler;
        let effect = Effect::ActionCompleted {
            name: "Test".into(),
            actor: ttrpg_interp::state::EntityRef(1),
        };
        assert!(matches!(handler.handle(effect), Response::Acknowledged));
    }

    #[test]
    fn vetoes_roll_dice() {
        let mut handler = MinimalHandler;
        let effect = Effect::RollDice {
            expr: DiceExpr {
                count: 1,
                sides: 20,
                filter: None,
                modifier: 0,
            },
        };
        assert!(matches!(handler.handle(effect), Response::Vetoed));
    }
}
