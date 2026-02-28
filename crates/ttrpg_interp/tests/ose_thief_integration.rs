//! OSE thief skills integration test.
//!
//! Verifies that ose/ose_thief.ttrpg (combined with ose/ose_core.ttrpg)
//! parses, lowers, type-checks, and evaluates correctly through the full
//! pipeline: parse → lower → check → interpret.

use std::collections::{BTreeMap, VecDeque};

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_ast::diagnostic::Severity;
use ttrpg_ast::DiceFilter;
use ttrpg_ast::FileId;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::{DiceExpr, RollResult, Value};
use ttrpg_interp::Interpreter;

// ── Setup ──────────────────────────────────────────────────────

/// Test harness derives that wrap table lookups for direct evaluation.
/// Tables can't be called directly via evaluate_derive — they must be
/// invoked from within a derive/mechanic body.
const TEST_HARNESS: &str = r#"
system "OSE" {
    derive test_skill_chance(skill: ThiefSkill, level: int) -> int {
        skill_chance(skill, level)
    }
}
"#;

/// Compile ose_core + ose_thief + test harness as a single combined source.
/// All three declare `system "OSE"`, so their declarations merge.
fn compile_ose_thief() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    let core_source = include_str!("../../../ose/ose_core.ttrpg");
    let thief_source = include_str!("../../../ose/ose_thief.ttrpg");
    let source = format!("{}\n{}\n{}", core_source, thief_source, TEST_HARNESS);

    let (program, parse_errors) = ttrpg_parser::parse(&source, FileId::SYNTH);
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
        "checker errors: {:?}",
        errors.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    (program, result)
}

// ── Helpers ────────────────────────────────────────────────────

struct ScriptedHandler {
    script: VecDeque<Response>,
    log: Vec<Effect>,
}

impl ScriptedHandler {
    fn new() -> Self {
        ScriptedHandler {
            script: VecDeque::new(),
            log: Vec::new(),
        }
    }

    fn with_responses(responses: Vec<Response>) -> Self {
        ScriptedHandler {
            script: responses.into(),
            log: Vec::new(),
        }
    }
}

impl EffectHandler for ScriptedHandler {
    fn handle(&mut self, effect: Effect) -> Response {
        self.log.push(effect);
        self.script.pop_front().unwrap_or(Response::Acknowledged)
    }
}

fn enum_variant(enum_name: &str, variant: &str) -> Value {
    Value::EnumVariant {
        enum_name: ttrpg_ast::Name::from(enum_name),
        variant: ttrpg_ast::Name::from(variant),
        fields: BTreeMap::new(),
    }
}

#[allow(clippy::too_many_arguments)]
fn scripted_roll(
    count: u32,
    sides: u32,
    filter: Option<DiceFilter>,
    modifier: i64,
    dice_vals: Vec<i64>,
    kept_vals: Vec<i64>,
    total: i64,
    unmodified: i64,
) -> Response {
    Response::Rolled(RollResult {
        expr: DiceExpr::single(count, sides, filter, modifier),
        dice: dice_vals,
        kept: kept_vals,
        modifier,
        total,
        unmodified,
    })
}

/// Collect all DeclKind items from all system blocks named "OSE".
fn get_ose_decls(program: &ttrpg_ast::ast::Program) -> Vec<&ttrpg_ast::Spanned<DeclKind>> {
    let mut decls = Vec::new();
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSE" {
                decls.extend(sys.decls.iter());
            }
        }
    }
    decls
}

// ── Parse & typecheck ──────────────────────────────────────────

#[test]
fn ose_thief_parses_and_typechecks() {
    let (program, _) = compile_ose_thief();
    // Should have at least two system "OSE" blocks (core + thief)
    let ose_count = program
        .items
        .iter()
        .filter(|item| matches!(&item.node, TopLevel::System(sys) if sys.name == "OSE"))
        .count();
    assert!(
        ose_count >= 2,
        "expected at least 2 system 'OSE' blocks, got {}",
        ose_count
    );
}

#[test]
fn ose_thief_has_expected_declarations() {
    let (program, _) = compile_ose_thief();
    let decls = get_ose_decls(&program);

    // Count thief-specific declarations (from ose_thief.ttrpg)
    let tables: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Table(t) => Some(&*t.name),
            _ => None,
        })
        .collect();
    assert!(
        tables.contains(&"skill_chance"),
        "missing table skill_chance"
    );

    let mechanics: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Mechanic(m) => Some(&*m.name),
            _ => None,
        })
        .collect();
    assert!(
        mechanics.contains(&"thief_skill_check"),
        "missing mechanic thief_skill_check"
    );
    assert!(
        mechanics.contains(&"hear_noise_check"),
        "missing mechanic hear_noise_check"
    );

    let derives: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Derive(d) => Some(&*d.name),
            _ => None,
        })
        .collect();
    assert!(
        derives.contains(&"backstab_multiplier"),
        "missing derive backstab_multiplier"
    );
    assert!(
        derives.contains(&"has_thief_skills"),
        "missing derive has_thief_skills"
    );
    assert!(
        derives.contains(&"can_backstab"),
        "missing derive can_backstab"
    );
}

// ── Table lookups ──────────────────────────────────────────────

#[test]
fn skill_chance_climb_walls() {
    let (program, result) = compile_ose_thief();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = ScriptedHandler::new();

    // Climb walls level 1 → 87
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "test_skill_chance",
            vec![enum_variant("ThiefSkill", "climb_walls"), Value::Int(1)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(87));

    // Climb walls level 7 → 93
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "test_skill_chance",
            vec![enum_variant("ThiefSkill", "climb_walls"), Value::Int(7)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(93));

    // Climb walls level 14 → 99 (range 13..=14)
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "test_skill_chance",
            vec![enum_variant("ThiefSkill", "climb_walls"), Value::Int(14)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(99));
}

#[test]
fn skill_chance_hear_noise_ranges() {
    let (program, result) = compile_ose_thief();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = ScriptedHandler::new();

    // Hear noise level 1 → 2 (d6 target)
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "test_skill_chance",
            vec![enum_variant("ThiefSkill", "hear_noise"), Value::Int(1)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(2));

    // Hear noise level 5 → 3 (range 3..=6)
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "test_skill_chance",
            vec![enum_variant("ThiefSkill", "hear_noise"), Value::Int(5)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(3));

    // Hear noise level 10 → 4 (range 7..=10)
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "test_skill_chance",
            vec![enum_variant("ThiefSkill", "hear_noise"), Value::Int(10)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(4));

    // Hear noise level 14 → 5 (range 11..=14)
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "test_skill_chance",
            vec![enum_variant("ThiefSkill", "hear_noise"), Value::Int(14)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(5));
}

#[test]
fn skill_chance_read_languages() {
    let (program, result) = compile_ose_thief();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = ScriptedHandler::new();

    // Read languages level 3 → 0 (not available yet)
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "test_skill_chance",
            vec![enum_variant("ThiefSkill", "read_languages"), Value::Int(3)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(0));

    // Read languages level 4 → 80 (acquired at level 4)
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "test_skill_chance",
            vec![enum_variant("ThiefSkill", "read_languages"), Value::Int(4)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(80));
}

#[test]
fn skill_chance_pick_pockets_exceeds_100() {
    let (program, result) = compile_ose_thief();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = ScriptedHandler::new();

    // Pick pockets level 14 → 125 (exceeds 100%)
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "test_skill_chance",
            vec![enum_variant("ThiefSkill", "pick_pockets"), Value::Int(14)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(125));
}

// ── Derive evaluations ────────────────────────────────────────

#[test]
fn backstab_multiplier_by_level() {
    let (program, result) = compile_ose_thief();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = ScriptedHandler::new();

    // Level 1 → ×2
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "backstab_multiplier",
            vec![Value::Int(1)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(2));

    // Level 4 → ×2 (boundary)
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "backstab_multiplier",
            vec![Value::Int(4)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(2));

    // Level 5 → ×3
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "backstab_multiplier",
            vec![Value::Int(5)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(3));

    // Level 9 → ×4
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "backstab_multiplier",
            vec![Value::Int(9)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(4));

    // Level 14 → ×5
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "backstab_multiplier",
            vec![Value::Int(14)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(5));
}

#[test]
fn has_thief_skills_class_check() {
    let (program, result) = compile_ose_thief();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = ScriptedHandler::new();

    // Thief → true
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "has_thief_skills",
            vec![enum_variant("Class", "Thief")],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(true));

    // Acrobat → true
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "has_thief_skills",
            vec![enum_variant("Class", "Acrobat")],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(true));

    // Fighter → false
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "has_thief_skills",
            vec![enum_variant("Class", "Fighter")],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(false));

    // Cleric → false
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "has_thief_skills",
            vec![enum_variant("Class", "Cleric")],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(false));
}

#[test]
fn can_backstab_class_check() {
    let (program, result) = compile_ose_thief();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = ScriptedHandler::new();

    // Thief → true
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "can_backstab",
            vec![enum_variant("Class", "Thief")],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(true));

    // Assassin → true
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "can_backstab",
            vec![enum_variant("Class", "Assassin")],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(true));

    // Acrobat → false (has thief skills but no backstab)
    let val = interp
        .evaluate_derive(
            &state,
            &mut handler,
            "can_backstab",
            vec![enum_variant("Class", "Acrobat")],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(false));
}

// ── Mechanic evaluations ──────────────────────────────────────

#[test]
fn thief_skill_check_success() {
    let (program, result) = compile_ose_thief();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Open locks level 1 chance = 15. Roll 10 → 10 <= 15 → true
    let roll_response = scripted_roll(1, 100, None, 0, vec![10], vec![10], 10, 10);
    let mut handler = ScriptedHandler::with_responses(vec![roll_response]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "thief_skill_check",
            vec![enum_variant("ThiefSkill", "open_locks"), Value::Int(1)],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(true));
}

#[test]
fn thief_skill_check_failure() {
    let (program, result) = compile_ose_thief();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Open locks level 1 chance = 15. Roll 50 → 50 > 15 → false
    let roll_response = scripted_roll(1, 100, None, 0, vec![50], vec![50], 50, 50);
    let mut handler = ScriptedHandler::with_responses(vec![roll_response]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "thief_skill_check",
            vec![enum_variant("ThiefSkill", "open_locks"), Value::Int(1)],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(false));
}

#[test]
fn hear_noise_check_mechanic() {
    let (program, result) = compile_ose_thief();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Level 1 target = 2. Roll 2 → 2 <= 2 → true
    let roll_response = scripted_roll(1, 6, None, 0, vec![2], vec![2], 2, 2);
    let mut handler = ScriptedHandler::with_responses(vec![roll_response]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "hear_noise_check",
            vec![Value::Int(1)],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(true));

    // Level 1 target = 2. Roll 5 → 5 > 2 → false
    let roll_response = scripted_roll(1, 6, None, 0, vec![5], vec![5], 5, 5);
    let mut handler = ScriptedHandler::with_responses(vec![roll_response]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "hear_noise_check",
            vec![Value::Int(1)],
        )
        .unwrap();
    assert_eq!(val, Value::Bool(false));
}
