//! Integration tests for condition stacking policies.
//!
//! Runtime stacking coverage has moved to `tests/stacking.ttrpg-cli`.
//! This Rust file now keeps only pipeline coverage for the synthetic source.

use ttrpg_ast::FileId;
use ttrpg_ast::diagnostic::Severity;
use ttrpg_interp::Interpreter;

fn compile(source: &str) -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    let (program, parse_errors) = ttrpg_parser::parse(source, FileId::SYNTH);
    assert!(
        parse_errors.is_empty(),
        "parse errors: {:?}",
        parse_errors.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    let mut lower_diags = Vec::new();
    let program = ttrpg_parser::lower_moves(program, &mut lower_diags);
    assert!(
        lower_diags.is_empty(),
        "lowering errors: {:?}",
        lower_diags.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    let result = ttrpg_checker::check(&program);
    let errors: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .collect();
    assert!(
        errors.is_empty(),
        "checker errors: {:#?}",
        errors.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    (program, result)
}

const STACKING_SOURCE: &str = r#"
system "Stacking" {
    entity Character {
        base_atk: int
        base_def: int
    }

    derive attack_score(target: Character, bonus: int = 0) -> int {
        target.base_atk + bonus
    }

    derive defense_score(target: Character, bonus: int = 0) -> int {
        target.base_def + bonus
    }

    condition Buff on bearer: Character {
        modify attack_score(target: bearer) {
            bonus = bonus + 1
        }
    }

    condition Prone on bearer: Character
        stacking first
    {
        modify attack_score(target: bearer) {
            bonus = bonus - 4
        }
    }

    condition Shield(level: int) on bearer: Character
        stacking best by highest(level) ties oldest
    {
        modify defense_score(target: bearer) {
            bonus = bonus + level
        }
    }

    condition Curse(severity: int) on bearer: Character
        stacking best by lowest(severity) ties oldest
    {
        modify attack_score(target: bearer) {
            bonus = bonus - severity
        }
    }
}
"#;

#[test]
fn pipeline_parses_checks_and_builds_interpreter() {
    let (program, result) = compile(STACKING_SOURCE);
    let interp = Interpreter::new(&program, &result.env);
    assert!(
        interp.is_ok(),
        "interpreter creation failed: {:?}",
        interp.err()
    );
}
