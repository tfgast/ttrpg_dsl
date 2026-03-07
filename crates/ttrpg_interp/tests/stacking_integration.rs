//! Integration tests for condition stacking policies.
//!
//! Tests all three stacking modes: `all` (default), `first`, and `best by`.

use std::collections::BTreeMap;

use rustc_hash::FxHashMap;
use ttrpg_ast::diagnostic::Severity;
use ttrpg_ast::FileId;
use ttrpg_ast::Name;
use ttrpg_interp::effect::{Effect, EffectHandler, Response};
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::EntityRef;
use ttrpg_interp::value::{duration_variant, Value};
use ttrpg_interp::Interpreter;

// ── Setup helpers ────────────────────────────────────────────

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

struct LogHandler {
    log: Vec<Effect>,
}

impl LogHandler {
    fn new() -> Self {
        Self { log: Vec::new() }
    }
}

impl EffectHandler for LogHandler {
    fn handle(&mut self, effect: Effect) -> Response {
        self.log.push(effect);
        Response::Acknowledged
    }
}

fn forever() -> Value {
    duration_variant("Forever")
}

fn make_char(state: &mut GameState, base_atk: i64, base_def: i64) -> EntityRef {
    let mut fields = FxHashMap::default();
    fields.insert(Name::from("base_atk"), Value::Int(base_atk));
    fields.insert(Name::from("base_def"), Value::Int(base_def));
    state.add_entity("Character", fields)
}

// ── Source ────────────────────────────────────────────────────

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

    // Default stacking (all) — every instance contributes
    condition Buff on bearer: Character {
        modify attack_score(target: bearer) {
            bonus = bonus + 1
        }
    }

    // stacking first — oldest wins, duplicates suppressed
    condition Prone on bearer: Character
        stacking first
    {
        modify attack_score(target: bearer) {
            bonus = bonus - 4
        }
    }

    // stacking best by highest — strongest wins
    condition Shield(level: int) on bearer: Character
        stacking best by highest(level) ties oldest
    {
        modify defense_score(target: bearer) {
            bonus = bonus + level
        }
    }

    // stacking best by lowest — smallest value wins
    condition Curse(severity: int) on bearer: Character
        stacking best by lowest(severity) ties oldest
    {
        modify attack_score(target: bearer) {
            bonus = bonus - severity
        }
    }
}
"#;

// ── Tests ────────────────────────────────────────────────────

fn query_attack(interp: &Interpreter, state: &GameState, entity: EntityRef) -> i64 {
    let mut handler = LogHandler::new();
    let result = interp
        .evaluate_derive(state, &mut handler, "attack_score", vec![Value::Entity(entity)])
        .unwrap();
    match result {
        Value::Int(n) => n,
        other => panic!("expected Int, got {:?}", other),
    }
}

fn query_defense(interp: &Interpreter, state: &GameState, entity: EntityRef) -> i64 {
    let mut handler = LogHandler::new();
    let result = interp
        .evaluate_derive(state, &mut handler, "defense_score", vec![Value::Entity(entity)])
        .unwrap();
    match result {
        Value::Int(n) => n,
        other => panic!("expected Int, got {:?}", other),
    }
}

#[test]
fn stacking_all_multiple_instances_all_contribute() {
    let (program, check) = compile(STACKING_SOURCE);
    let interp = Interpreter::new(&program, &check.env).unwrap();

    let mut state = GameState::new();
    let e1 = make_char(&mut state, 5, 10);

    // Apply 3 Buff conditions (stacking all = default)
    state.apply_condition(&e1, "Buff", BTreeMap::new(), forever(), None);
    state.apply_condition(&e1, "Buff", BTreeMap::new(), forever(), None);
    state.apply_condition(&e1, "Buff", BTreeMap::new(), forever(), None);

    assert_eq!(query_attack(&interp, &state, e1), 8); // 5 + 1 + 1 + 1
}

#[test]
fn stacking_first_oldest_wins() {
    let (program, check) = compile(STACKING_SOURCE);
    let interp = Interpreter::new(&program, &check.env).unwrap();

    let mut state = GameState::new();
    let e1 = make_char(&mut state, 10, 10);

    // Apply 3 Prone conditions (stacking first = only oldest applies)
    state.apply_condition(&e1, "Prone", BTreeMap::new(), forever(), None);
    state.apply_condition(&e1, "Prone", BTreeMap::new(), forever(), None);
    state.apply_condition(&e1, "Prone", BTreeMap::new(), forever(), None);

    // Only one -4, not -12
    assert_eq!(query_attack(&interp, &state, e1), 6); // 10 - 4
}

#[test]
fn stacking_best_by_highest_strongest_wins() {
    let (program, check) = compile(STACKING_SOURCE);
    let interp = Interpreter::new(&program, &check.env).unwrap();

    let mut state = GameState::new();
    let e1 = make_char(&mut state, 5, 10);

    // Apply Shield with different levels — highest should win
    let mut p1 = BTreeMap::new();
    p1.insert(Name::from("level"), Value::Int(2));
    state.apply_condition(&e1, "Shield", p1, forever(), None);

    let mut p2 = BTreeMap::new();
    p2.insert(Name::from("level"), Value::Int(5));
    state.apply_condition(&e1, "Shield", p2, forever(), None);

    let mut p3 = BTreeMap::new();
    p3.insert(Name::from("level"), Value::Int(3));
    state.apply_condition(&e1, "Shield", p3, forever(), None);

    // Only the level=5 instance contributes: 10 + 5
    assert_eq!(query_defense(&interp, &state, e1), 15);
}

#[test]
fn stacking_best_by_lowest_weakest_wins() {
    let (program, check) = compile(STACKING_SOURCE);
    let interp = Interpreter::new(&program, &check.env).unwrap();

    let mut state = GameState::new();
    let e1 = make_char(&mut state, 10, 10);

    // Apply Curse with different severities — lowest wins
    let mut p1 = BTreeMap::new();
    p1.insert(Name::from("severity"), Value::Int(5));
    state.apply_condition(&e1, "Curse", p1, forever(), None);

    let mut p2 = BTreeMap::new();
    p2.insert(Name::from("severity"), Value::Int(1));
    state.apply_condition(&e1, "Curse", p2, forever(), None);

    let mut p3 = BTreeMap::new();
    p3.insert(Name::from("severity"), Value::Int(3));
    state.apply_condition(&e1, "Curse", p3, forever(), None);

    // Only the severity=1 instance contributes: 10 - 1
    assert_eq!(query_attack(&interp, &state, e1), 9);
}

#[test]
fn stacking_first_single_instance_works() {
    let (program, check) = compile(STACKING_SOURCE);
    let interp = Interpreter::new(&program, &check.env).unwrap();

    let mut state = GameState::new();
    let e1 = make_char(&mut state, 10, 10);

    // Single Prone instance still applies
    state.apply_condition(&e1, "Prone", BTreeMap::new(), forever(), None);

    assert_eq!(query_attack(&interp, &state, e1), 6); // 10 - 4
}

#[test]
fn stacking_mixed_conditions_independent() {
    let (program, check) = compile(STACKING_SOURCE);
    let interp = Interpreter::new(&program, &check.env).unwrap();

    let mut state = GameState::new();
    let e1 = make_char(&mut state, 10, 10);

    // Buff (stacking all) + Prone (stacking first) both affect attack_score
    state.apply_condition(&e1, "Buff", BTreeMap::new(), forever(), None);
    state.apply_condition(&e1, "Buff", BTreeMap::new(), forever(), None);
    state.apply_condition(&e1, "Prone", BTreeMap::new(), forever(), None);
    state.apply_condition(&e1, "Prone", BTreeMap::new(), forever(), None);

    // Two buffs (+2) and one prone (-4): 10 + 2 - 4 = 8
    assert_eq!(query_attack(&interp, &state, e1), 8);
}

#[test]
fn stacking_best_by_ties_oldest_wins() {
    let (program, check) = compile(STACKING_SOURCE);
    let interp = Interpreter::new(&program, &check.env).unwrap();

    let mut state = GameState::new();
    let e1 = make_char(&mut state, 5, 10);

    // Two Shield instances with same level — oldest (first applied) should win
    let mut p1 = BTreeMap::new();
    p1.insert(Name::from("level"), Value::Int(3));
    state.apply_condition(&e1, "Shield", p1, forever(), None);

    let mut p2 = BTreeMap::new();
    p2.insert(Name::from("level"), Value::Int(3));
    state.apply_condition(&e1, "Shield", p2, forever(), None);

    // Only one instance contributes: 10 + 3
    assert_eq!(query_defense(&interp, &state, e1), 13);
}
