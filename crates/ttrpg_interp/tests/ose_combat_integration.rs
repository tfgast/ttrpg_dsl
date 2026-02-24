//! OSE Combat & Morale integration tests.
//!
//! Verifies that ose/ose_combat.ttrpg parses, lowers, type-checks, and
//! evaluates correctly through the full pipeline.

use std::collections::{BTreeMap, VecDeque};

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_ast::diagnostic::Severity;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::value::{DiceExpr, RollResult, Value};
use ttrpg_interp::Interpreter;

// ── Setup ──────────────────────────────────────────────────────

fn compile_ose_combat() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    let source = include_str!("../../../ose/ose_combat.ttrpg");
    let (program, parse_errors) = ttrpg_parser::parse(source);
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

fn get_decls(program: &ttrpg_ast::ast::Program) -> &[ttrpg_ast::Spanned<DeclKind>] {
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            return &sys.decls;
        }
    }
    panic!("no system block found");
}

fn enum_variant(enum_name: &str, variant: &str) -> Value {
    Value::EnumVariant {
        enum_name: enum_name.to_string(),
        variant: variant.to_string(),
        fields: BTreeMap::new(),
    }
}

// ── Effect handler ─────────────────────────────────────────────

struct NullHandler;
impl EffectHandler for NullHandler {
    fn handle(&mut self, _effect: Effect) -> Response {
        Response::Acknowledged
    }
}

struct ScriptedHandler {
    script: VecDeque<Response>,
    log: Vec<Effect>,
}

impl ScriptedHandler {
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

fn scripted_roll(
    count: u32,
    sides: u32,
    modifier: i64,
    dice_vals: Vec<i64>,
    kept_vals: Vec<i64>,
    total: i64,
    unmodified: i64,
) -> Response {
    Response::Rolled(RollResult {
        expr: DiceExpr {
            count,
            sides,
            filter: None,
            modifier,
        },
        dice: dice_vals,
        kept: kept_vals,
        modifier,
        total,
        unmodified,
    })
}

// ── Parsing & type checking ────────────────────────────────────

#[test]
fn ose_combat_parses_and_typechecks() {
    let (program, _) = compile_ose_combat();
    let has_system = program.items.iter().any(|item| {
        matches!(&item.node, TopLevel::System(sys) if sys.name == "OSE Combat")
    });
    assert!(has_system, "expected system named 'OSE Combat'");
}

#[test]
fn ose_combat_has_enums() {
    let (program, _) = compile_ose_combat();
    let decls = get_decls(&program);
    let enums: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Enum(e) => Some((&*e.name, e.variants.len())),
            _ => None,
        })
        .collect();
    assert!(enums.contains(&("AttackOutcome", 2)));
    assert!(enums.contains(&("MoraleOutcome", 2)));
    assert!(enums.contains(&("ReactionOutcome", 5)));
    assert_eq!(enums.len(), 3, "expected 3 enums");
}

#[test]
fn ose_combat_has_tables() {
    let (program, _) = compile_ose_combat();
    let decls = get_decls(&program);
    let tables: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Table(t) => Some(&*t.name),
            _ => None,
        })
        .collect();
    assert!(tables.contains(&"monster_thac0"));
    assert!(tables.contains(&"reaction_outcome"));
    assert_eq!(tables.len(), 2, "expected 2 tables");
}

#[test]
fn ose_combat_has_derives() {
    let (program, _) = compile_ose_combat();
    let decls = get_decls(&program);
    let derives: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Derive(d) => Some(&*d.name),
            _ => None,
        })
        .collect();
    assert!(derives.contains(&"target_number"));
    assert!(derives.contains(&"calc_ac"));
    assert!(derives.contains(&"missile_range_mod"));
    assert_eq!(derives.len(), 3, "expected 3 derives");
}

#[test]
fn ose_combat_has_mechanics() {
    let (program, _) = compile_ose_combat();
    let decls = get_decls(&program);
    let mechanics: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Mechanic(m) => Some(&*m.name),
            _ => None,
        })
        .collect();
    assert!(mechanics.contains(&"attack_roll"));
    assert!(mechanics.contains(&"morale_check"));
    assert!(mechanics.contains(&"reaction_roll"));
    assert_eq!(mechanics.len(), 3, "expected 3 mechanics");
}

// ── Derive evaluation ──────────────────────────────────────────

#[test]
fn target_number_unarmoured() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // THAC0 19 vs AC 9 = need 10
    let val = interp
        .evaluate_derive(&state, &mut handler, "target_number", vec![Value::Int(19), Value::Int(9)])
        .unwrap();
    assert_eq!(val, Value::Int(10));
}

#[test]
fn target_number_chain_mail() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // THAC0 19 vs AC 5 = need 14
    let val = interp
        .evaluate_derive(&state, &mut handler, "target_number", vec![Value::Int(19), Value::Int(5)])
        .unwrap();
    assert_eq!(val, Value::Int(14));
}

#[test]
fn target_number_negative_ac() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // THAC0 19 vs AC -3 = need 22 (very hard)
    let val = interp
        .evaluate_derive(&state, &mut handler, "target_number", vec![Value::Int(19), Value::Int(-3)])
        .unwrap();
    assert_eq!(val, Value::Int(22));
}

#[test]
fn calc_ac_unarmoured() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // AC 9 (unarmoured), no shield, DEX mod 0
    let val = interp
        .evaluate_derive(&state, &mut handler, "calc_ac", vec![Value::Int(9), Value::Int(0), Value::Int(0)])
        .unwrap();
    assert_eq!(val, Value::Int(9));
}

#[test]
fn calc_ac_chain_with_shield_and_dex() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Chain mail AC 5, shield (1), DEX mod +1 → 5 - 1 - 1 = 3
    let val = interp
        .evaluate_derive(&state, &mut handler, "calc_ac", vec![Value::Int(5), Value::Int(1), Value::Int(1)])
        .unwrap();
    assert_eq!(val, Value::Int(3));
}

#[test]
fn calc_ac_negative_dex() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Leather AC 7, no shield, DEX mod -1 → 7 - 0 - (-1) = 8
    let val = interp
        .evaluate_derive(&state, &mut handler, "calc_ac", vec![Value::Int(7), Value::Int(0), Value::Int(-1)])
        .unwrap();
    assert_eq!(val, Value::Int(8));
}

#[test]
fn missile_range_short() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Short bow: 50/100/150, distance 30 → +1
    let val = interp
        .evaluate_derive(
            &state, &mut handler, "missile_range_mod",
            vec![Value::Int(30), Value::Int(50), Value::Int(100), Value::Int(150)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(1));
}

#[test]
fn missile_range_short_boundary() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // Exactly at short range boundary → +1
    let val = interp
        .evaluate_derive(
            &state, &mut handler, "missile_range_mod",
            vec![Value::Int(50), Value::Int(50), Value::Int(100), Value::Int(150)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(1));
}

#[test]
fn missile_range_medium() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // distance 75, medium range → 0
    let val = interp
        .evaluate_derive(
            &state, &mut handler, "missile_range_mod",
            vec![Value::Int(75), Value::Int(50), Value::Int(100), Value::Int(150)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(0));
}

#[test]
fn missile_range_long() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    // distance 120, long range → -1
    let val = interp
        .evaluate_derive(
            &state, &mut handler, "missile_range_mod",
            vec![Value::Int(120), Value::Int(50), Value::Int(100), Value::Int(150)],
        )
        .unwrap();
    assert_eq!(val, Value::Int(-1));
}

// ── Table evaluation (via wrapper derives) ─────────────────────

/// Compile a source that adds wrapper derives for table testing.
fn compile_table_test() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    let base = include_str!("../../../ose/ose_combat.ttrpg");
    // Inject wrapper derives inside the system block for table testing.
    // Replace the closing "}" with wrappers + "}".
    let source = base.replace(
        "\n}\n",
        r#"
    // Test wrappers for table access
    derive test_thac0(hd: int) -> int { monster_thac0(hd) }
    derive test_reaction(roll: int) -> ReactionOutcome { reaction_outcome(roll) }
}
"#,
    );
    let (program, parse_errors) = ttrpg_parser::parse(&source);
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

#[test]
fn monster_thac0_normal_human() {
    let (program, result) = compile_table_test();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let val = interp
        .evaluate_derive(&state, &mut handler, "test_thac0", vec![Value::Int(0)])
        .unwrap();
    assert_eq!(val, Value::Int(20));
}

#[test]
fn monster_thac0_all_tiers() {
    let (program, result) = compile_table_test();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let cases = vec![
        (0, 20),  // Normal Human
        (1, 19),  // HD 1-3
        (3, 19),
        (4, 17),  // HD 4-6
        (6, 17),
        (7, 14),  // HD 7-9
        (9, 14),
        (10, 12), // HD 10-12
        (12, 12),
        (13, 10), // HD 13-15
        (15, 10),
        (16, 8),  // HD 16-18
        (18, 8),
        (19, 6),  // HD 19+ (wildcard)
        (25, 6),
    ];

    for (hd, expected_thac0) in cases {
        let val = interp
            .evaluate_derive(&state, &mut handler, "test_thac0", vec![Value::Int(hd)])
            .unwrap();
        assert_eq!(val, Value::Int(expected_thac0), "HD {} should have THAC0 {}", hd, expected_thac0);
    }
}

#[test]
fn reaction_outcome_all_tiers() {
    let (program, result) = compile_table_test();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();
    let mut handler = NullHandler;

    let cases = vec![
        (2, "Hostile"),
        (3, "Unfriendly"),
        (5, "Unfriendly"),
        (6, "Neutral"),
        (8, "Neutral"),
        (9, "Indifferent"),
        (11, "Indifferent"),
        (12, "Friendly"),
    ];

    for (roll, expected_variant) in cases {
        let val = interp
            .evaluate_derive(&state, &mut handler, "test_reaction", vec![Value::Int(roll)])
            .unwrap();
        assert_eq!(
            val,
            enum_variant("ReactionOutcome", expected_variant),
            "roll {} should be {}",
            roll,
            expected_variant
        );
    }
}

// ── Mechanic evaluation ────────────────────────────────────────

#[test]
fn attack_roll_natural_1_always_misses() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Roll a natural 1 — should miss regardless of bonuses
    let roll = scripted_roll(1, 20, 0, vec![1], vec![1], 1, 1);
    let mut handler = ScriptedHandler::with_responses(vec![roll]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "attack_roll",
            vec![Value::Int(19), Value::Int(9), Value::Int(10)], // thac0=19, ac=9, mod=+10
        )
        .unwrap();
    assert_eq!(val, enum_variant("AttackOutcome", "Miss"));
}

#[test]
fn attack_roll_natural_20_always_hits() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Roll a natural 20 — should hit regardless of penalties
    let roll = scripted_roll(1, 20, 0, vec![20], vec![20], 20, 20);
    let mut handler = ScriptedHandler::with_responses(vec![roll]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "attack_roll",
            vec![Value::Int(19), Value::Int(-10), Value::Int(-5)], // thac0=19, ac=-10, mod=-5
        )
        .unwrap();
    assert_eq!(val, enum_variant("AttackOutcome", "Hit"));
}

#[test]
fn attack_roll_standard_hit() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // THAC0 19 vs AC 5 → target 14. Roll 14 + mod 0 = 14, hits.
    let roll = scripted_roll(1, 20, 0, vec![14], vec![14], 14, 14);
    let mut handler = ScriptedHandler::with_responses(vec![roll]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "attack_roll",
            vec![Value::Int(19), Value::Int(5), Value::Int(0)],
        )
        .unwrap();
    assert_eq!(val, enum_variant("AttackOutcome", "Hit"));
}

#[test]
fn attack_roll_standard_miss() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // THAC0 19 vs AC 5 → target 14. Roll 13 + mod 0 = 13, misses.
    let roll = scripted_roll(1, 20, 0, vec![13], vec![13], 13, 13);
    let mut handler = ScriptedHandler::with_responses(vec![roll]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "attack_roll",
            vec![Value::Int(19), Value::Int(5), Value::Int(0)],
        )
        .unwrap();
    assert_eq!(val, enum_variant("AttackOutcome", "Miss"));
}

#[test]
fn attack_roll_with_str_modifier() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // THAC0 19 vs AC 5 → target 14. Roll 12 + mod 2 = 14, hits.
    let roll = scripted_roll(1, 20, 0, vec![12], vec![12], 12, 12);
    let mut handler = ScriptedHandler::with_responses(vec![roll]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "attack_roll",
            vec![Value::Int(19), Value::Int(5), Value::Int(2)],
        )
        .unwrap();
    assert_eq!(val, enum_variant("AttackOutcome", "Hit"));
}

#[test]
fn morale_check_hold() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Morale 7, roll 2d6 = 6 (3+3). 6 <= 7, hold.
    let roll = scripted_roll(2, 6, 0, vec![3, 3], vec![3, 3], 6, 6);
    let mut handler = ScriptedHandler::with_responses(vec![roll]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "morale_check",
            vec![Value::Int(7)],
        )
        .unwrap();
    assert_eq!(val, enum_variant("MoraleOutcome", "Hold"));
}

#[test]
fn morale_check_fail() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Morale 7, roll 2d6 = 9 (5+4). 9 > 7, fail.
    let roll = scripted_roll(2, 6, 0, vec![5, 4], vec![5, 4], 9, 9);
    let mut handler = ScriptedHandler::with_responses(vec![roll]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "morale_check",
            vec![Value::Int(7)],
        )
        .unwrap();
    assert_eq!(val, enum_variant("MoraleOutcome", "Fail"));
}

#[test]
fn morale_check_exact_score_holds() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Morale 7, roll 2d6 = 7. 7 <= 7, hold (equal = hold).
    let roll = scripted_roll(2, 6, 0, vec![4, 3], vec![4, 3], 7, 7);
    let mut handler = ScriptedHandler::with_responses(vec![roll]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "morale_check",
            vec![Value::Int(7)],
        )
        .unwrap();
    assert_eq!(val, enum_variant("MoraleOutcome", "Hold"));
}

#[test]
fn reaction_roll_neutral() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Roll 2d6 = 7 (4+3), CHA mod 0. Clamped 7 → neutral.
    let roll = scripted_roll(2, 6, 0, vec![4, 3], vec![4, 3], 7, 7);
    let mut handler = ScriptedHandler::with_responses(vec![roll]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "reaction_roll",
            vec![Value::Int(0)],
        )
        .unwrap();
    assert_eq!(val, enum_variant("ReactionOutcome", "Neutral"));
}

#[test]
fn reaction_roll_with_cha_bonus() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Roll 2d6 = 8 (5+3), CHA mod +2. Total 10 → indifferent.
    let roll = scripted_roll(2, 6, 0, vec![5, 3], vec![5, 3], 8, 8);
    let mut handler = ScriptedHandler::with_responses(vec![roll]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "reaction_roll",
            vec![Value::Int(2)],
        )
        .unwrap();
    assert_eq!(val, enum_variant("ReactionOutcome", "Indifferent"));
}

#[test]
fn reaction_roll_clamped_low() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Roll 2d6 = 3 (2+1), CHA mod -3. Total 0 → clamped to 2 → hostile.
    let roll = scripted_roll(2, 6, 0, vec![2, 1], vec![2, 1], 3, 3);
    let mut handler = ScriptedHandler::with_responses(vec![roll]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "reaction_roll",
            vec![Value::Int(-3)],
        )
        .unwrap();
    assert_eq!(val, enum_variant("ReactionOutcome", "Hostile"));
}

#[test]
fn reaction_roll_clamped_high() {
    let (program, result) = compile_ose_combat();
    let interp = Interpreter::new(&program, &result.env).unwrap();
    let state = GameState::new();

    // Roll 2d6 = 11 (6+5), CHA mod +3. Total 14 → clamped to 12 → friendly.
    let roll = scripted_roll(2, 6, 0, vec![6, 5], vec![6, 5], 11, 11);
    let mut handler = ScriptedHandler::with_responses(vec![roll]);

    let val = interp
        .evaluate_mechanic(
            &state,
            &mut handler,
            "reaction_roll",
            vec![Value::Int(3)],
        )
        .unwrap();
    assert_eq!(val, enum_variant("ReactionOutcome", "Friendly"));
}
