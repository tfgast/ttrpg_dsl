//! Integration tests for condition state field declarations and inheritance.
//!
//! Verifies the checker's state field type-checking, the post-collect merge
//! pass for inherited state fields, and error detection for conflicts.

use ttrpg_ast::FileId;
use ttrpg_ast::diagnostic::Severity;

fn setup(source: &str) -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
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
        "checker errors: {:?}",
        errors.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    (program, result)
}

fn setup_expect_errors(source: &str) -> Vec<String> {
    let (program, parse_errors) = ttrpg_parser::parse(source, FileId::SYNTH);
    assert!(
        parse_errors.is_empty(),
        "parse errors: {:?}",
        parse_errors.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    let mut lower_diags = Vec::new();
    let program = ttrpg_parser::lower_moves(program, &mut lower_diags);
    let result = ttrpg_checker::check(&program);
    result
        .diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .map(|d| d.message.clone())
        .collect()
}

// ── Basic state field declarations ──────────────────────────────

#[test]
fn condition_own_state_fields_check() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Poisoned(potency: int = 1) on bearer: Character {
        state {
            ticks: int = 0
            total_damage: int = potency
        }
        on_apply {
            state.ticks = 1
            state.total_damage = state.total_damage + 1
        }
    }
}
"#;
    let (_program, result) = setup(source);
    let cond_info = result.env.conditions.get("Poisoned").unwrap();
    assert_eq!(cond_info.own_state_fields.len(), 2);
    assert_eq!(cond_info.merged_state_fields.len(), 2);
}

// ── Inherited state fields ──────────────────────────────────────

#[test]
fn child_inherits_parent_state_fields() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Burning(damage_per_tick: int = 1) on bearer: Character {
        state {
            ticks_elapsed: int = 0
            total_damage: int = 0
        }
    }
    condition IntenseBurning extends Burning on bearer: Character {
        state {
            spread_count: int = 0
        }
    }
}
"#;
    let (_program, result) = setup(source);
    let parent_info = result.env.conditions.get("Burning").unwrap();
    assert_eq!(parent_info.own_state_fields.len(), 2);
    assert_eq!(parent_info.merged_state_fields.len(), 2);

    let child_info = result.env.conditions.get("IntenseBurning").unwrap();
    assert_eq!(child_info.own_state_fields.len(), 1);
    // Merged: 2 from parent + 1 own = 3
    assert_eq!(child_info.merged_state_fields.len(), 3);
    // Ancestor order: parent fields first, then child
    assert_eq!(child_info.merged_state_fields[0].0, "ticks_elapsed");
    assert_eq!(child_info.merged_state_fields[1].0, "total_damage");
    assert_eq!(child_info.merged_state_fields[2].0, "spread_count");
}

#[test]
fn child_accesses_inherited_state_in_lifecycle() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Burning(damage_per_tick: int = 1) on bearer: Character {
        state {
            ticks_elapsed: int = 0
        }
        on_apply {
            state.ticks_elapsed = 1
        }
    }
    condition IntenseBurning extends Burning on bearer: Character {
        state {
            spread_count: int = 0
        }
        on_apply {
            // Can read inherited state field
            state.spread_count = state.ticks_elapsed
        }
    }
}
"#;
    let (_program, _result) = setup(source);
}

#[test]
fn grandchild_inherits_through_chain() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Base on bearer: Character {
        state { a: int = 0 }
    }
    condition Mid extends Base on bearer: Character {
        state { b: int = 0 }
    }
    condition Leaf extends Mid on bearer: Character {
        state { c: int = 0 }
    }
}
"#;
    let (_program, result) = setup(source);
    let leaf = result.env.conditions.get("Leaf").unwrap();
    assert_eq!(leaf.merged_state_fields.len(), 3);
    assert_eq!(leaf.merged_state_fields[0].0, "a");
    assert_eq!(leaf.merged_state_fields[1].0, "b");
    assert_eq!(leaf.merged_state_fields[2].0, "c");
}

// ── Error cases ──────────────────────────────────────────────────

#[test]
fn child_redeclares_parent_state_field_error() {
    let errors = setup_expect_errors(
        r#"
system "test" {
    entity Character { HP: int }
    condition Parent on bearer: Character {
        state { x: int = 0 }
    }
    condition Child extends Parent on bearer: Character {
        state { x: int = 1 }
    }
}
"#,
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("redeclares inherited state field")),
        "expected redeclaration error, got: {:?}",
        errors
    );
}

#[test]
fn sibling_parent_field_conflict_error() {
    let errors = setup_expect_errors(
        r#"
system "test" {
    entity Character { HP: int }
    condition ParentA on bearer: Character {
        state { x: int = 0 }
    }
    condition ParentB on bearer: Character {
        state { x: int = 0 }
    }
    condition Child extends ParentA, ParentB on bearer: Character {}
}
"#,
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("conflicting state field") || e.contains("state field `x`")),
        "expected sibling parent conflict error, got: {:?}",
        errors
    );
}

#[test]
fn disallowed_type_in_state_field_error() {
    let errors = setup_expect_errors(
        r#"
system "test" {
    entity Character { HP: int }
    condition Bad on bearer: Character {
        state { c: Condition = Prone }
    }
    condition Prone on bearer: Character {}
}
"#,
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("cannot have type") && e.contains("disallowed")),
        "expected disallowed type error, got: {:?}",
        errors
    );
}

#[test]
fn state_default_type_mismatch_error() {
    let errors = setup_expect_errors(
        r#"
system "test" {
    entity Character { HP: int }
    condition Bad on bearer: Character {
        state { x: int = "hello" }
    }
}
"#,
    );
    assert!(
        errors.iter().any(|e| e.contains("default has type")),
        "expected type mismatch error, got: {:?}",
        errors
    );
}

#[test]
fn no_state_fields_condition_no_extends() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Prone on bearer: Character {}
}
"#;
    let (_program, result) = setup(source);
    let info = result.env.conditions.get("Prone").unwrap();
    assert!(info.own_state_fields.is_empty());
    assert!(info.merged_state_fields.is_empty());
}

// ── Reserved identifier tests ────────────────────────────────────

#[test]
fn state_as_receiver_name_error() {
    let errors = setup_expect_errors(
        r#"
system "test" {
    entity Character { HP: int }
    condition Bad on state: Character {}
}
"#,
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("state") && e.contains("shadows")),
        "expected reserved name error, got: {:?}",
        errors
    );
}

#[test]
fn state_as_param_name_error() {
    let errors = setup_expect_errors(
        r#"
system "test" {
    entity Character { HP: int }
    condition Bad(state: int) on bearer: Character {}
}
"#,
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("state") && e.contains("shadows")),
        "expected reserved name error, got: {:?}",
        errors
    );
}

#[test]
fn parent_default_params_materialized_in_child() {
    // When IntenseBurning extends Burning(damage_per_tick: int = 3),
    // the child instance should have damage_per_tick=3 available.
    let source = r#"
system "test" {
    entity Character {
        HP: int
        last_damage: int
    }
    condition Burning(damage_per_tick: int = 3) on bearer: Character {
        on_apply {
            bearer.last_damage = damage_per_tick
        }
    }
    condition IntenseBurning extends Burning on bearer: Character {
        on_apply {
            // Parent on_apply already set last_damage to damage_per_tick
            // Child can also access inherited param
            bearer.last_damage = bearer.last_damage + damage_per_tick
        }
    }
}
"#;
    let (_program, _result) = setup(source);
}

#[test]
fn self_as_receiver_name_error() {
    let errors = setup_expect_errors(
        r#"
system "test" {
    entity Character { HP: int }
    condition Bad on self: Character {}
}
"#,
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("self") && e.contains("shadows")),
        "expected reserved name error, got: {:?}",
        errors
    );
}

#[test]
fn state_readable_in_modify_body() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    derive calc_hp(target: Character) -> int { target.HP }
    condition Buffed on bearer: Character {
        state {
            stacks: int = 1
        }
        modify calc_hp(target: bearer) {
            result = result + state.stacks
        }
    }
}
"#;
    let (_program, _result) = setup(source);
}

#[test]
fn state_readable_in_modify_selector() {
    let source = r#"
system "test" {
    tag attack_resolution
    entity Character { HP: int }
    derive base_attack(target: Character) -> int #attack_resolution { target.HP }
    condition Weakened on bearer: Character {
        state {
            penalty: int = 1
        }
        modify [#attack_resolution](target: bearer) {
            result = result - state.penalty
        }
    }
}
"#;
    let (_program, _result) = setup(source);
}

#[test]
fn self_as_param_name_error() {
    let errors = setup_expect_errors(
        r#"
system "test" {
    entity Character { HP: int }
    condition Bad(self: int) on bearer: Character {}
}
"#,
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("self") && e.contains("shadows")),
        "expected reserved name error, got: {:?}",
        errors
    );
}
