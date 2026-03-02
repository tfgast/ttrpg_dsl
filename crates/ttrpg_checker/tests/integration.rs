use ttrpg_ast::ast::DeclKind;
use ttrpg_ast::diagnostic::SourceMap;
use ttrpg_ast::FileId;
use ttrpg_checker::{check, check_with_modules, CheckResult};

fn check_source(source: &str) -> CheckResult {
    let (program, parse_errors) = ttrpg_parser::parse(source, FileId::SYNTH);
    assert!(
        parse_errors.is_empty(),
        "parse errors:\n{}",
        parse_errors
            .iter()
            .map(|d| SourceMap::new(source).render(d))
            .collect::<Vec<_>>()
            .join("\n\n")
    );
    check(&program)
}

/// Parse, lower moves, then check — the full pipeline for move declarations.
fn check_lowered(source: &str) -> (ttrpg_ast::ast::Program, CheckResult) {
    let (program, parse_errors) = ttrpg_parser::parse(source, FileId::SYNTH);
    assert!(
        parse_errors.is_empty(),
        "parse errors:\n{}",
        parse_errors
            .iter()
            .map(|d| SourceMap::new(source).render(d))
            .collect::<Vec<_>>()
            .join("\n\n")
    );
    let mut lower_diags = Vec::new();
    let program = ttrpg_parser::lower_moves(program, &mut lower_diags);
    assert!(
        lower_diags.is_empty(),
        "lowering errors:\n{}",
        lower_diags
            .iter()
            .map(|d| SourceMap::new(source).render(d))
            .collect::<Vec<_>>()
            .join("\n\n")
    );
    let result = check(&program);
    (program, result)
}

/// Parse and lower, returning lowering diagnostics (does not check).
fn lower_source(
    source: &str,
) -> (
    ttrpg_ast::ast::Program,
    Vec<ttrpg_ast::diagnostic::Diagnostic>,
) {
    let (program, parse_errors) = ttrpg_parser::parse(source, FileId::SYNTH);
    assert!(
        parse_errors.is_empty(),
        "parse errors:\n{}",
        parse_errors
            .iter()
            .map(|d| SourceMap::new(source).render(d))
            .collect::<Vec<_>>()
            .join("\n\n")
    );
    let mut lower_diags = Vec::new();
    let program = ttrpg_parser::lower_moves(program, &mut lower_diags);
    (program, lower_diags)
}

fn expect_no_errors(source: &str) {
    let result = check_source(source);
    let errors: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.severity == ttrpg_ast::diagnostic::Severity::Error)
        .collect();
    if !errors.is_empty() {
        let sm = SourceMap::new(source);
        let rendered: Vec<_> = errors.iter().map(|d| sm.render(d)).collect();
        panic!(
            "expected no errors, found {}:\n{}",
            errors.len(),
            rendered.join("\n\n")
        );
    }
}

fn expect_errors(source: &str, expected_fragments: &[&str]) {
    let result = check_source(source);
    let errors: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.severity == ttrpg_ast::diagnostic::Severity::Error)
        .collect();

    for frag in expected_fragments {
        let found = errors.iter().any(|e| e.message.contains(frag));
        if !found {
            let sm = SourceMap::new(source);
            let rendered: Vec<_> = errors.iter().map(|d| sm.render(d)).collect();
            panic!(
                "expected error containing {:?}, but not found in:\n{}",
                frag,
                rendered.join("\n\n")
            );
        }
    }
}

fn expect_error_count(source: &str, expected_count: usize) {
    let result = check_source(source);
    let errors: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.severity == ttrpg_ast::diagnostic::Severity::Error)
        .collect();
    if errors.len() != expected_count {
        let sm = SourceMap::new(source);
        let rendered: Vec<_> = errors.iter().map(|d| sm.render(d)).collect();
        panic!(
            "expected {} error(s), found {}:\n{}",
            expected_count,
            errors.len(),
            rendered.join("\n\n")
        );
    }
}

fn expect_warnings(source: &str, expected_fragments: &[&str]) {
    let result = check_source(source);
    let warnings: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.severity == ttrpg_ast::diagnostic::Severity::Warning)
        .collect();

    for frag in expected_fragments {
        let found = warnings.iter().any(|w| w.message.contains(frag));
        if !found {
            let sm = SourceMap::new(source);
            let rendered: Vec<_> = warnings.iter().map(|d| sm.render(d)).collect();
            panic!(
                "expected warning containing {:?}, but not found in:\n{}",
                frag,
                rendered.join("\n\n")
            );
        }
    }
}

// ═══════════════════════════════════════════════════════════════
// Full example acceptance test
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_full_example_no_errors() {
    let source = include_str!("../../../spec/v0/04_full_example.ttrpg");
    expect_no_errors(source);
}

#[test]
fn test_expanded_example_no_errors() {
    let source = include_str!("../../../examples/dnd5e_expanded.ttrpg");
    expect_no_errors(source);
}

// ═══════════════════════════════════════════════════════════════
// Pass 1: Declaration collection
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_collect_counts() {
    let source = include_str!("../../../spec/v0/04_full_example.ttrpg");
    let result = check_source(source);

    // Enums: Ability, RollMode, DamageType, WeaponProperty, SaveResult, ResolvedDamage + built-in Duration
    assert_eq!(
        result
            .env
            .types
            .values()
            .filter(|d| matches!(d, ttrpg_checker::env::DeclInfo::Enum(_)))
            .count(),
        7
    );
    // Structs: DamageSpec, TurnBudget
    assert_eq!(
        result
            .env
            .types
            .values()
            .filter(|d| matches!(d, ttrpg_checker::env::DeclInfo::Struct(_)))
            .count(),
        2
    );
    // Entities: Weapon, Character
    assert_eq!(
        result
            .env
            .types
            .values()
            .filter(|d| matches!(d, ttrpg_checker::env::DeclInfo::Entity(_)))
            .count(),
        2
    );
    // Events: entity_leaves_reach, turn_start, turn_end, Damaged, ConcentrationStarted + built-in modify_applied
    assert_eq!(result.env.events.len(), 6);
    // Conditions: Prone, Dodging, Disengaging, Hidden, Stunned, Petrified, CunningAction, Blessed, Raging
    assert_eq!(result.env.conditions.len(), 9);
}

#[test]
fn test_duplicate_type_declaration() {
    let source = r#"
system "test" {
    enum Foo { A, B }
    enum Foo { C, D }
}
"#;
    expect_errors(source, &["duplicate type declaration `Foo`"]);
}

#[test]
fn test_duplicate_function_declaration() {
    let source = r#"
system "test" {
    derive foo(x: int) -> int { x }
    derive foo(y: int) -> int { y }
}
"#;
    expect_errors(source, &["duplicate function declaration `foo`"]);
}

// ═══════════════════════════════════════════════════════════════
// Type checking: expressions
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_undefined_variable() {
    let source = r#"
system "test" {
    derive foo(x: int) -> int { y }
}
"#;
    expect_errors(source, &["undefined variable `y`"]);
}

#[test]
fn test_type_mismatch_return() {
    let source = r#"
system "test" {
    derive foo(x: int) -> bool { x }
}
"#;
    expect_errors(
        source,
        &["function body has type int, expected return type bool"],
    );
}

#[test]
fn test_dice_in_comparison_error() {
    let source = r#"
system "test" {
    derive foo() -> bool {
        let x: DiceExpr = 1d20
        x >= 15
    }
}
"#;
    expect_errors(source, &["cannot compare DiceExpr directly"]);
}

#[test]
fn test_dice_multiply_error() {
    let source = r#"
system "test" {
    derive foo() -> DiceExpr {
        let x: DiceExpr = 1d20
        x * 2
    }
}
"#;
    expect_errors(source, &["cannot multiply DiceExpr"]);
}

#[test]
fn test_dice_divide_error() {
    let source = r#"
system "test" {
    derive foo() -> DiceExpr {
        let x: DiceExpr = 1d20
        x / 2
    }
}
"#;
    expect_errors(source, &["cannot divide DiceExpr"]);
}

#[test]
fn test_dice_addition_ok() {
    let source = r#"
system "test" {
    derive foo() -> DiceExpr {
        1d20 + 5
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_dice_combination_ok() {
    let source = r#"
system "test" {
    derive foo() -> DiceExpr {
        1d8 + 1d6
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_dice_constructor_ok() {
    let source = r#"
system "test" {
    derive foo(n: int) -> DiceExpr {
        dice(n, 8)
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_dice_constructor_with_modifier_ok() {
    let source = r#"
system "test" {
    derive foo(n: int, bonus: int) -> DiceExpr {
        dice(n, 8) + bonus
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_dice_constructor_literal_args_ok() {
    let source = r#"
system "test" {
    derive foo() -> DiceExpr {
        dice(3, 6)
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_int_division_yields_float() {
    let source = r#"
system "test" {
    derive foo(x: int) -> int {
        x / 2
    }
}
"#;
    // int / int -> float, so returning float as int should error
    expect_errors(
        source,
        &["function body has type float, expected return type int"],
    );
}

#[test]
fn test_floor_converts_float_to_int() {
    let source = r#"
system "test" {
    derive foo(x: int) -> int {
        floor(x / 2)
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_error_builtin_allows_early_abort_return() {
    let source = r#"
system "test" {
    derive fail_fast() -> int {
        error("boom")
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_error_builtin_unifies_in_if_branch() {
    let source = r#"
system "test" {
    derive pick(flag: bool) -> int {
        if flag { error("bad state") } else { 7 }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_error_builtin_requires_string_message() {
    let source = r#"
system "test" {
    derive bad() -> int {
        error(123)
    }
}
"#;
    expect_errors(
        source,
        &["argument `message` has type int, expected string"],
    );
}

// ═══════════════════════════════════════════════════════════════
// Scope enforcement
// ═══════════════════════════════════════════════════════════════

#[test]
// ═══════════════════════════════════════════════════════════════
// Block categories: scoping and permission audit (02_scoping.ttrpg)
// ═══════════════════════════════════════════════════════════════

// --- emit scope ---

fn test_emit_in_derive_error() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    event Damage(target: Character) {}
    derive foo(target: Character) -> int {
        emit Damage(target: target)
        0
    }
}
"#;
    expect_errors(source, &["emit is only allowed in action, reaction, or hook"]);
}

#[test]
fn test_emit_in_mechanic_error() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    event Damage(target: Character) {}
    mechanic foo(target: Character) -> int {
        emit Damage(target: target)
        0
    }
}
"#;
    expect_errors(source, &["emit is only allowed in action, reaction, or hook"]);
}

#[test]
fn test_emit_in_action_ok() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    event Damage(target: Character) {}
    action Strike on actor: Character (target: Character) {
        resolve {
            target.hp -= 5
            emit Damage(target: target)
        }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_emit_in_reaction_ok() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    event MeleeAttack(reactor: Character) { attacker: Character }
    event Riposte(target: Character) {}
    reaction Parry on defender: Character (trigger: MeleeAttack(reactor: defender)) {
        resolve {
            emit Riposte(target: trigger.attacker)
        }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_emit_in_hook_ok() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    event TurnStart(actor: Character) {}
    event Regenerated(target: Character) {}
    hook Regen on c: Character (trigger: TurnStart(actor: c)) {
        c.hp += 1
        emit Regenerated(target: c)
    }
}
"#;
    expect_no_errors(source);
}

// --- turn keyword scope ---

#[test]
fn test_turn_in_derive_error() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    derive foo(actor: Character) -> int {
        turn.movement
    }
}
"#;
    expect_errors(source, &["undefined variable `turn`"]);
}

#[test]
fn test_turn_in_mechanic_error() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    mechanic foo(actor: Character) -> int {
        turn.movement
    }
}
"#;
    expect_errors(source, &["undefined variable `turn`"]);
}

#[test]
fn test_turn_in_action_ok() {
    let source = r#"
system "test" {
    entity Character { speed: int }
    action Dash on actor: Character () {
        resolve {
            turn.movement += actor.speed
        }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_turn_in_reaction_ok() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    event Attack(reactor: Character) { attacker: Character }
    reaction Dodge on defender: Character (trigger: Attack(reactor: defender)) {
        resolve {
            let budget = turn.movement
        }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_turn_in_hook_ok() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    event TurnStart(actor: Character) {}
    hook MoveReset on c: Character (trigger: TurnStart(actor: c)) {
        turn.movement += 5
    }
}
"#;
    expect_no_errors(source);
}

// --- roll (dice) permission ---

#[test]
fn test_roll_in_derive_error() {
    let source = r#"
system "test" {
    derive foo() -> RollResult {
        roll(1d20)
    }
}
"#;
    expect_errors(
        source,
        &["roll() can only be called in mechanic, action, reaction, or hook"],
    );
}

#[test]
fn test_roll_in_mechanic_ok() {
    let source = r#"
system "test" {
    mechanic foo() -> RollResult {
        roll(1d20)
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_mutation_in_mechanic_error() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
    }
    mechanic foo(target: Character) -> int {
        target.HP -= 5
        0
    }
}
"#;
    expect_errors(
        source,
        &["assignment to entity fields requires action, reaction, or hook"],
    );
}

#[test]
fn test_mutation_in_action_ok() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
    }
    action Heal on actor: Character (target: Character) {
        cost { action }
        resolve {
            target.HP += 5
        }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_apply_condition_in_derive_error() {
    let source = r#"
system "test" {
    entity Character {
        name: string
    }
    condition Foo on bearer: Character {}
    derive foo(target: Character) -> int {
        apply_condition(target, Foo, Duration.indefinite)
        0
    }
}
"#;
    expect_errors(
        source,
        &["apply_condition() can only be called in action, reaction, or hook"],
    );
}

// ═══════════════════════════════════════════════════════════════
// Pattern matching
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_pattern_match_basic() {
    let source = r#"
system "test" {
    enum Color { red, green, blue }
    derive name(c: Color) -> string {
        match c {
            red => "Red",
            green => "Green",
            blue => "Blue"
        }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_guard_match_basic() {
    let source = r#"
system "test" {
    derive classify(x: int) -> string {
        match {
            x > 100 => "high",
            x > 50 => "medium",
            _ => "low"
        }
    }
}
"#;
    expect_no_errors(source);
}

// ═══════════════════════════════════════════════════════════════
// Struct / field access
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_struct_field_access() {
    let source = r#"
system "test" {
    struct Pair {
        a: int
        b: int
    }
    derive sum(p: Pair) -> int { p.a + p.b }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_struct_no_such_field() {
    let source = r#"
system "test" {
    struct Pair {
        a: int
        b: int
    }
    derive bad(p: Pair) -> int { p.c }
}
"#;
    expect_errors(source, &["has no field `c`"]);
}

#[test]
fn test_struct_literal_construction() {
    let source = r#"
system "test" {
    struct Point {
        x: int
        y: int
    }
    derive origin() -> Point {
        Point { x: 0, y: 0 }
    }
}
"#;
    expect_no_errors(source);
}

// ═══════════════════════════════════════════════════════════════
// if/else
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_if_else_type_unification() {
    let source = r#"
system "test" {
    derive foo(x: bool) -> int {
        if x { 1 } else { 2 }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_if_else_type_mismatch() {
    let source = r#"
system "test" {
    derive foo(x: bool) -> int {
        if x { 1 } else { "hello" }
    }
}
"#;
    expect_errors(source, &["incompatible types"]);
}

#[test]
fn test_if_condition_must_be_bool() {
    let source = r#"
system "test" {
    derive foo(x: int) -> int {
        if x { 1 } else { 2 }
    }
}
"#;
    expect_errors(source, &["if condition must be bool"]);
}

// ═══════════════════════════════════════════════════════════════
// Function calls
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_call_wrong_arg_count() {
    let source = r#"
system "test" {
    derive add(a: int, b: int) -> int { a + b }
    derive bad() -> int { add(1) }
}
"#;
    expect_errors(source, &["missing required argument `b` in call to `add`"]);
}

#[test]
fn test_call_arg_type_mismatch() {
    let source = r#"
system "test" {
    derive foo(x: int) -> int { x }
    derive bad() -> int { foo("hello") }
}
"#;
    expect_errors(source, &["argument `x` has type string, expected int"]);
}

#[test]
fn test_call_named_args() {
    let source = r#"
system "test" {
    derive add(a: int, b: int = 0) -> int { a + b }
    derive ok() -> int { add(a: 1, b: 2) }
}
"#;
    expect_no_errors(source);
}

// ═══════════════════════════════════════════════════════════════
// RollResult coercion
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_roll_result_comparison_coercion() {
    let source = r#"
system "test" {
    mechanic foo() -> bool {
        let r = roll(1d20)
        r >= 10
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_roll_result_field_access() {
    let source = r#"
system "test" {
    mechanic foo() -> int {
        let r = roll(1d20)
        r.total
    }
}
"#;
    expect_no_errors(source);
}

// ═══════════════════════════════════════════════════════════════
// Enum variant in set membership
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_enum_in_set() {
    let source = r#"
system "test" {
    enum Color { red, green, blue }
    derive has_red(s: set<Color>) -> bool {
        red in s
    }
}
"#;
    expect_no_errors(source);
}

// ═══════════════════════════════════════════════════════════════
// Map indexing
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_map_index() {
    let source = r#"
system "test" {
    enum Ability { STR, DEX }
    derive get_score(abilities: map<Ability, int>) -> int {
        abilities[STR]
    }
}
"#;
    expect_no_errors(source);
}

// ═══════════════════════════════════════════════════════════════
// Condition modify
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_condition_modify_basic() {
    let source = r#"
system "test" {
    entity Character {
        speed: int
    }
    derive initial_budget(actor: Character) -> int {
        actor.speed
    }
    condition Slow on bearer: Character {
        modify initial_budget(actor: bearer) {
            result = result - 10
        }
    }
}
"#;
    // This should check fine — modify targeting a derive
    // result overrides on int return type
    // Actually: for a derive returning int, `result` should be int
    // `result = result - 10` is a ParamOverride? No, it has no dot.
    // Let me re-check: `result = expr` is a ParamOverride with name "result"
    // But `result.field = expr` is a ResultOverride.
    // For int return type, modifying `result` directly makes sense.
    // Actually the spec shows `result.movement = ...` for TurnBudget fields.
    // But for a plain int return, `result = result - 10` would be a param override on "result".
    // The target function has a param named "actor", not "result".
    // So this might not parse correctly. Let me adjust.
    expect_no_errors(source);
}

#[test]
fn test_condition_modify_undefined_target() {
    let source = r#"
system "test" {
    entity Character { speed: int }
    condition Slow on bearer: Character {
        modify nonexistent_fn(actor: bearer) {
            result = 0
        }
    }
}
"#;
    expect_errors(
        source,
        &["modify target `nonexistent_fn` is not a defined function"],
    );
}

// ═══════════════════════════════════════════════════════════════
// Suppress clause
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_suppress_undefined_event() {
    let source = r#"
system "test" {
    entity Character { name: string }
    condition Foo on bearer: Character {
        suppress nonexistent_event(entity: bearer)
    }
}
"#;
    expect_errors(source, &["undefined event `nonexistent_event`"]);
}

// ═══════════════════════════════════════════════════════════════
// Reaction trigger validation
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_reaction_undefined_event() {
    let source = r#"
system "test" {
    entity Character { name: string }
    reaction Foo on actor: Character (trigger: nonexistent_event(reactor: actor)) {
        cost { reaction }
        resolve {}
    }
}
"#;
    expect_errors(source, &["undefined event `nonexistent_event`"]);
}

// ═══════════════════════════════════════════════════════════════
// let with type annotation
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_let_type_annotation_mismatch() {
    let source = r#"
system "test" {
    derive foo() -> int {
        let x: bool = 42
        0
    }
}
"#;
    expect_errors(
        source,
        &["let `x`: value has type int, annotation says bool"],
    );
}

// ═══════════════════════════════════════════════════════════════
// Boolean operators
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_logical_ops_require_bool() {
    let source = r#"
system "test" {
    derive foo(x: int, y: int) -> bool {
        x && y
    }
}
"#;
    expect_errors(source, &["left operand of logical op must be bool"]);
}

// ═══════════════════════════════════════════════════════════════
// Unary operators
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_negate_non_numeric() {
    let source = r#"
system "test" {
    derive foo(x: string) -> int {
        -x
    }
}
"#;
    expect_errors(source, &["cannot negate string"]);
}

#[test]
fn test_not_non_bool() {
    let source = r#"
system "test" {
    derive foo(x: int) -> bool {
        !x
    }
}
"#;
    expect_errors(source, &["cannot apply `!` to int"]);
}

// ═══════════════════════════════════════════════════════════════
// Fix #1: Unknown type names emit diagnostics
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_unknown_type_in_param() {
    let source = r#"
system "test" {
    derive foo(x: Nonexistent) -> int { 0 }
}
"#;
    expect_errors(source, &["unknown type `Nonexistent`"]);
}

#[test]
fn test_unknown_type_in_return() {
    let source = r#"
system "test" {
    derive foo(x: int) -> Nonexistent { x }
}
"#;
    expect_errors(source, &["unknown type `Nonexistent`"]);
}

#[test]
fn test_unknown_type_in_struct_field() {
    let source = r#"
system "test" {
    struct Foo {
        x: Nonexistent
    }
}
"#;
    expect_errors(source, &["unknown type `Nonexistent`"]);
}

#[test]
fn test_unknown_type_in_generic() {
    let source = r#"
system "test" {
    derive foo(x: list<Nonexistent>) -> int { 0 }
}
"#;
    expect_errors(source, &["unknown type `Nonexistent`"]);
}

// ═══════════════════════════════════════════════════════════════
// Fix #2: Named argument soundness
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_duplicate_named_arg() {
    let source = r#"
system "test" {
    derive add(a: int, b: int) -> int { a + b }
    derive bad() -> int { add(a: 1, a: 2) }
}
"#;
    expect_errors(source, &["duplicate argument for parameter `a`"]);
}

#[test]
fn test_missing_required_param_with_named_args() {
    let source = r#"
system "test" {
    derive add(a: int, b: int, c: int = 0) -> int { a + b + c }
    derive bad() -> int { add(c: 5) }
}
"#;
    expect_errors(
        source,
        &[
            "missing required argument `a`",
            "missing required argument `b`",
        ],
    );
}

#[test]
fn test_too_many_positional_args() {
    let source = r#"
system "test" {
    derive add(a: int, b: int) -> int { a + b }
    derive bad() -> int { add(1, 2, 3) }
}
"#;
    expect_errors(source, &["expects at most 2 argument(s), found 3"]);
}

#[test]
fn test_unknown_named_arg() {
    let source = r#"
system "test" {
    derive add(a: int, b: int) -> int { a + b }
    derive bad() -> int { add(a: 1, z: 2) }
}
"#;
    expect_errors(source, &["has no parameter `z`"]);
}

// ═══════════════════════════════════════════════════════════════
// Fix #3: Binding expression type-checking
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_suppress_binding_type_mismatch() {
    let source = r#"
system "test" {
    entity Character { name: string }
    event leave(actor: Character) {
        target: Character
    }
    condition Foo on bearer: Character {
        suppress leave(target: "not_a_character")
    }
}
"#;
    expect_errors(
        source,
        &["suppress binding `target` has type string, expected Character"],
    );
}

#[test]
fn test_suppress_binding_unknown_param() {
    let source = r#"
system "test" {
    entity Character { name: string }
    event leave(actor: Character) {
        target: Character
    }
    condition Foo on bearer: Character {
        suppress leave(nonexistent: bearer)
    }
}
"#;
    expect_errors(source, &["does not match any parameter or field"]);
}

#[test]
fn test_suppress_binding_unknown_param_still_checks_value() {
    let source = r#"
system "test" {
    entity Character { name: string }
    event leave(actor: Character) {
        target: Character
    }
    condition Foo on bearer: Character {
        suppress leave(nonexistent: undefined_var)
    }
}
"#;
    expect_errors(
        source,
        &[
            "does not match any parameter or field",
            "undefined variable `undefined_var`",
        ],
    );
}

// ═══════════════════════════════════════════════════════════════
// Fix #4: Modify targets must be derive or mechanic
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_modify_target_action_rejected() {
    let source = r#"
system "test" {
    entity Character { speed: int }
    action Sprint on actor: Character () {
        cost { action }
        resolve {
            actor.speed += 10
        }
    }
    condition Slow on bearer: Character {
        modify Sprint(actor: bearer) {
            result = 0
        }
    }
}
"#;
    expect_errors(
        source,
        &["modify target `Sprint` must be a derive or mechanic"],
    );
}

#[test]
fn test_modify_target_derive_ok() {
    let source = r#"
system "test" {
    entity Character { speed: int }
    derive initial_budget(actor: Character) -> int {
        actor.speed
    }
    condition Slow on bearer: Character {
        modify initial_budget(actor: bearer) {
            result = result - 10
        }
    }
}
"#;
    // Should not error — derive is a valid modify target
    expect_no_errors(source);
}

// ═══════════════════════════════════════════════════════════════
// Fix #5: Compound assignment type compatibility
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_int_plus_eq_float_rejected() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
    }
    action Heal on actor: Character (target: Character) {
        cost { action }
        resolve {
            target.HP += 3 / 2
        }
    }
}
"#;
    // int / int -> float, so int += float should be rejected
    expect_errors(source, &["cannot use float in += / -= on int"]);
}

#[test]
fn test_int_plus_eq_int_ok() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
    }
    action Heal on actor: Character (target: Character) {
        cost { action }
        resolve {
            target.HP += 5
        }
    }
}
"#;
    expect_no_errors(source);
}

// ═══════════════════════════════════════════════════════════════
// Fix #6: Positional trigger binding validation
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_positional_trigger_binding_type_mismatch() {
    let source = r#"
system "test" {
    entity Character { name: string }
    event damage(amount: int) {}
    reaction Block on actor: Character (trigger: damage(actor)) {
        cost { reaction }
        resolve {}
    }
}
"#;
    expect_errors(
        source,
        &["positional trigger binding 0 has type Character, expected int"],
    );
}

#[test]
fn test_positional_trigger_binding_too_many() {
    let source = r#"
system "test" {
    entity Character { name: string }
    event flee(actor: Character) {}
    reaction Block on defender: Character (trigger: flee(defender, defender)) {
        cost { reaction }
        resolve {}
    }
}
"#;
    expect_errors(
        source,
        &["too many positional trigger bindings for event `flee`"],
    );
}

#[test]
fn test_positional_trigger_binding_ok() {
    let source = r#"
system "test" {
    entity Character { name: string }
    event flee(actor: Character) {}
    reaction Block on defender: Character (trigger: flee(defender)) {
        cost { reaction }
        resolve {}
    }
}
"#;
    expect_no_errors(source);
}

// ═══════════════════════════════════════════════════════════════
// Fix #7: Parameter default type-checking
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_param_default_type_mismatch() {
    let source = r#"
system "test" {
    derive foo(x: int = "hello") -> int { x }
}
"#;
    expect_errors(
        source,
        &["parameter `x` default has type string, expected int"],
    );
}

#[test]
fn test_param_default_ok() {
    let source = r#"
system "test" {
    derive add(a: int, b: int = 0) -> int { a + b }
}
"#;
    expect_no_errors(source);
}

// ═══════════════════════════════════════════════════════════════
// Fix #8: Guard match wildcard ordering
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_guard_match_wildcard_not_last() {
    let source = r#"
system "test" {
    derive classify(x: int) -> string {
        match {
            _ => "default",
            x > 100 => "high"
        }
    }
}
"#;
    expect_warnings(
        source,
        &["unreachable match arm: wildcard `_` must be last"],
    );
}

#[test]
fn test_guard_match_wildcard_last_ok() {
    let source = r#"
system "test" {
    derive classify(x: int) -> string {
        match {
            x > 100 => "high",
            _ => "low"
        }
    }
}
"#;
    expect_no_errors(source);
}

// ═══════════════════════════════════════════════════════════════
// Fix: Immutable binding enforcement
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_let_reassignment_in_action_rejected() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    action Heal on actor: Character (target: Character) {
        cost { action }
        resolve {
            let x = 1
            x = 2
        }
    }
}
"#;
    expect_errors(source, &["cannot reassign immutable binding `x`"]);
}

#[test]
fn test_let_reassignment_in_derive_rejected() {
    let source = r#"
system "test" {
    derive foo() -> int {
        let x = 1
        x = 2
        x
    }
}
"#;
    expect_errors(source, &["cannot reassign immutable binding `x`"]);
}

#[test]
fn test_param_reassignment_rejected() {
    let source = r#"
system "test" {
    derive foo(x: int) -> int {
        x = 2
        x
    }
}
"#;
    expect_errors(source, &["cannot reassign immutable binding `x`"]);
}

#[test]
fn test_mutable_receiver_field_ok() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    action Heal on actor: Character () {
        cost { action }
        resolve {
            actor.HP += 10
        }
    }
}
"#;
    expect_no_errors(source);
}

// ═══════════════════════════════════════════════════════════════
// Fix: Mixed named + positional arg mapping
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_mixed_named_then_positional_args() {
    let source = r#"
system "test" {
    derive add(a: int, b: int) -> int { a + b }
    derive ok() -> int { add(b: 2, 1) }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_mixed_positional_then_named_args() {
    let source = r#"
system "test" {
    derive add(a: int, b: int) -> int { a + b }
    derive ok() -> int { add(1, b: 2) }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_mixed_args_type_mismatch() {
    let source = r#"
system "test" {
    derive add(a: int, b: int) -> int { a + b }
    derive bad() -> int { add(b: 2, "hello") }
}
"#;
    expect_errors(source, &["argument `a` has type string, expected int"]);
}

// ═══════════════════════════════════════════════════════════════
// Fix: Enum constructor named argument validation
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_enum_constructor_wrong_field_name() {
    let source = r#"
system "test" {
    enum Effect {
        timed(count: int),
        permanent
    }
    derive foo() -> Effect {
        Effect.timed(foo: 1)
    }
}
"#;
    expect_errors(source, &["variant `timed` has no field `foo`"]);
}

#[test]
fn test_enum_constructor_correct_field_name() {
    let source = r#"
system "test" {
    enum Effect {
        timed(count: int),
        permanent
    }
    derive foo() -> Effect {
        Effect.timed(count: 1)
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_enum_constructor_named_type_mismatch() {
    let source = r#"
system "test" {
    enum Effect {
        timed(count: int),
        permanent
    }
    derive foo() -> Effect {
        Effect.timed(count: "hello")
    }
}
"#;
    expect_errors(
        source,
        &["variant field `count` has type int, found string"],
    );
}

#[test]
fn test_enum_constructor_positional_still_works() {
    let source = r#"
system "test" {
    enum Effect {
        timed(count: int),
        permanent
    }
    derive foo() -> Effect {
        Effect.timed(5)
    }
}
"#;
    expect_no_errors(source);
}

// ═══════════════════════════════════════════════════════════════
// Fix: modify-if branch scope isolation
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_modify_if_scope_leak_rejected() {
    let source = r#"
system "test" {
    entity Character { speed: int }
    struct Budget {
        movement: int
    }
    derive initial_budget(actor: Character) -> Budget {
        Budget { movement: actor.speed }
    }
    condition Slow on bearer: Character {
        modify initial_budget(actor: bearer) {
            if true {
                let x = 2
            }
            result.movement = result.movement - x
        }
    }
}
"#;
    expect_errors(source, &["undefined variable `x`"]);
}

#[test]
fn test_modify_if_let_inside_branch_ok() {
    let source = r#"
system "test" {
    entity Character { speed: int }
    struct Budget {
        movement: int
    }
    derive initial_budget(actor: Character) -> Budget {
        Budget { movement: actor.speed }
    }
    condition Slow on bearer: Character {
        modify initial_budget(actor: bearer) {
            if true {
                let x = 2
                result.movement = result.movement - x
            }
        }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_modify_else_scope_leak_rejected() {
    let source = r#"
system "test" {
    entity Character { speed: int }
    struct Budget {
        movement: int
    }
    derive initial_budget(actor: Character) -> Budget {
        Budget { movement: actor.speed }
    }
    condition Slow on bearer: Character {
        modify initial_budget(actor: bearer) {
            if false {
                result.movement = result.movement
            } else {
                let y = 5
            }
            result.movement = result.movement - y
        }
    }
}
"#;
    expect_errors(source, &["undefined variable `y`"]);
}

// ═══════════════════════════════════════════════════════════════
// Duplicate field/param detection
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_duplicate_struct_field() {
    let source = r#"
system "test" {
    struct Pair {
        x: int
        x: int
    }
}
"#;
    expect_errors(source, &["duplicate field `x` in struct `Pair`"]);
}

#[test]
fn test_duplicate_entity_field() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
        HP: int
    }
}
"#;
    expect_errors(source, &["duplicate field `HP` in entity `Character`"]);
}

#[test]
fn test_duplicate_enum_variant_field() {
    let source = r#"
system "test" {
    enum Effect {
        timed(count: int, count: int),
        permanent
    }
}
"#;
    expect_errors(source, &["duplicate field `count` in variant `timed`"]);
}

#[test]
fn test_duplicate_event_field() {
    let source = r#"
system "test" {
    entity Character { name: string }
    event hit(actor: Character) {
        damage: int
        damage: int
    }
}
"#;
    expect_errors(source, &["duplicate field `damage` in event `hit`"]);
}

#[test]
fn test_duplicate_function_param() {
    let source = r#"
system "test" {
    derive foo(x: int, x: int) -> int { x }
}
"#;
    expect_errors(source, &["duplicate parameter `x` in function `foo`"]);
}

// ═══════════════════════════════════════════════════════════════
// Enum constructor: duplicate & missing field validation
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_enum_constructor_duplicate_named_arg() {
    let source = r#"
system "test" {
    enum Effect {
        timed(count: int),
        permanent
    }
    derive foo() -> Effect {
        Effect.timed(count: 1, count: 2)
    }
}
"#;
    expect_errors(source, &["duplicate argument for variant field `count`"]);
}

#[test]
fn test_enum_constructor_missing_required_field() {
    let source = r#"
system "test" {
    enum Pair {
        both(a: int, b: int)
    }
    derive foo() -> Pair {
        Pair.both(a: 1)
    }
}
"#;
    expect_errors(source, &["missing required field `b` in variant `both`"]);
}

// ═══════════════════════════════════════════════════════════════
// Struct literal: duplicate & missing field validation
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_struct_literal_duplicate_field() {
    let source = r#"
system "test" {
    struct Point {
        x: int
        y: int
    }
    derive foo() -> Point {
        Point { x: 1, y: 2, x: 3 }
    }
}
"#;
    expect_errors(source, &["duplicate field `x` in struct literal"]);
}

#[test]
fn test_struct_literal_missing_required_field() {
    let source = r#"
system "test" {
    struct Point {
        x: int
        y: int
    }
    derive foo() -> Point {
        Point { x: 1 }
    }
}
"#;
    expect_errors(source, &["missing required field `y` in `Point` literal"]);
}

#[test]
fn test_struct_literal_missing_field_with_default_ok() {
    let source = r#"
system "test" {
    struct Config {
        x: int
        y: int = 0
    }
    derive foo() -> Config {
        Config { x: 1 }
    }
}
"#;
    expect_no_errors(source);
}

// ═══════════════════════════════════════════════════════════════
// Struct spread / base expression (..base)
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_struct_spread_base_valid() {
    let source = r#"
system "test" {
    struct Point {
        x: int
        y: int
    }
    derive shifted(p: Point) -> Point {
        Point { x: p.x + 1, ..p }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_struct_spread_base_suppresses_missing_fields() {
    let source = r#"
system "test" {
    struct Point {
        x: int
        y: int
        z: int
    }
    derive update_x(p: Point) -> Point {
        Point { x: 99, ..p }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_struct_spread_base_wrong_type() {
    let source = r#"
system "test" {
    struct Point { x: int, y: int }
    struct Color { r: int, g: int }
    derive bad(c: Color) -> Point {
        Point { x: 1, ..c }
    }
}
"#;
    expect_errors(source, &["base expression has type Color, expected Point"]);
}

#[test]
fn test_struct_spread_base_no_fields_ok() {
    let source = r#"
system "test" {
    struct Point { x: int, y: int }
    derive clone(p: Point) -> Point {
        Point { ..p }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_struct_spread_base_field_type_still_checked() {
    let source = r#"
system "test" {
    struct Point { x: int, y: int }
    derive bad(p: Point) -> Point {
        Point { x: "oops", ..p }
    }
}
"#;
    expect_errors(source, &["field `x` has type string, expected int"]);
}

// ═══════════════════════════════════════════════════════════════
// Payload enum variant without constructor args
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_payload_variant_requires_constructor() {
    let source = r#"
system "test" {
    enum Effect { timed(count: int), permanent }
    derive foo() -> Effect { Effect.timed }
}
"#;
    expect_errors(
        source,
        &["variant `timed` has payload fields and must be called as a constructor"],
    );
}

#[test]
fn test_simple_variant_field_access_ok() {
    let source = r#"
system "test" {
    enum Effect { timed(count: int), permanent }
    derive foo() -> Effect { Effect.permanent }
}
"#;
    expect_no_errors(source);
}

// ═══════════════════════════════════════════════════════════════
// Action/reaction receiver enforcement
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_action_call_from_derive_rejected() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    action Heal on actor: Character (target: Character) {
        resolve { target.hp = target.hp + 10 }
    }
    derive foo(target: Character) -> int {
        Heal(actor: target, target: target)
        0
    }
}
"#;
    expect_errors(
        source,
        &["is an action and can only be called from action, reaction, or hook context"],
    );
}

#[test]
fn test_action_call_missing_receiver_arg() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    event combat(actor: Character) {}
    action Heal on actor: Character (target: Character) {
        resolve { target.hp = target.hp + 10 }
    }
    reaction Counter on reactor: Character (trigger: combat(actor: reactor)) {
        cost { reaction }
        resolve { Heal(target: reactor) }
    }
}
"#;
    expect_errors(source, &["missing required argument `actor`"]);
}

// ═══════════════════════════════════════════════════════════════
// Duplicate event parameter names
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_duplicate_event_param() {
    let source = r#"
system "test" {
    entity Character {}
    event hit(actor: Character, actor: Character) {}
}
"#;
    expect_errors(source, &["duplicate parameter `actor` in event `hit`"]);
}

// ═══════════════════════════════════════════════════════════════
// Fix: none assignable to option<T>
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_none_assignable_to_option_int() {
    let source = r#"
system "test" {
    derive foo() -> option<int> { none }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_none_assignable_to_option_string() {
    let source = r#"
system "test" {
    derive foo() -> option<string> { none }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_none_in_let_with_option_annotation() {
    let source = r#"
system "test" {
    derive foo() -> option<int> {
        let x: option<int> = none
        x
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_none_not_assignable_to_int() {
    let source = r#"
system "test" {
    derive foo() -> int { none }
}
"#;
    expect_errors(source, &["function body has type option"]);
}

// ═══════════════════════════════════════════════════════════════
// Fix: Duplicate bindings in trigger/modify/suppress
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_duplicate_trigger_binding() {
    let source = r#"
system "test" {
    entity Character { name: string }
    event hit(actor: Character) {
        damage: int
    }
    reaction Block on reactor: Character (trigger: hit(actor: reactor, actor: reactor)) {
        cost { reaction }
        resolve {}
    }
}
"#;
    expect_errors(source, &["duplicate trigger binding `actor`"]);
}

#[test]
fn test_trigger_unknown_binding_still_checks_value() {
    let source = r#"
system "test" {
    entity Character { name: string }
    event hit(actor: Character) {
        damage: int
    }
    reaction Block on reactor: Character (trigger: hit(nonexistent: undefined_var)) {
        cost { reaction }
        resolve {}
    }
}
"#;
    expect_errors(
        source,
        &[
            "does not match any parameter of event",
            "undefined variable `undefined_var`",
        ],
    );
}

#[test]
fn test_duplicate_modify_binding() {
    let source = r#"
system "test" {
    entity Character { speed: int }
    derive initial_budget(actor: Character) -> int {
        actor.speed
    }
    condition Slow on bearer: Character {
        modify initial_budget(actor: bearer, actor: bearer) {
            result = result - 10
        }
    }
}
"#;
    expect_errors(source, &["duplicate modify binding `actor`"]);
}

#[test]
fn test_modify_unknown_binding_still_checks_value() {
    let source = r#"
system "test" {
    entity Character { speed: int }
    derive initial_budget(actor: Character) -> int {
        actor.speed
    }
    condition Slow on bearer: Character {
        modify initial_budget(nonexistent: undefined_var) {
            result = result - 10
        }
    }
}
"#;
    expect_errors(
        source,
        &[
            "does not match any parameter",
            "undefined variable `undefined_var`",
        ],
    );
}

#[test]
fn test_modify_unknown_param_override_still_checks_value() {
    let source = r#"
system "test" {
    entity Character { speed: int }
    derive initial_budget(actor: Character) -> int {
        actor.speed
    }
    condition Slow on bearer: Character {
        modify initial_budget(actor: bearer) {
            nonexistent_param = undefined_var
        }
    }
}
"#;
    expect_errors(
        source,
        &[
            "has no parameter `nonexistent_param`",
            "undefined variable `undefined_var`",
        ],
    );
}

#[test]
fn test_duplicate_suppress_binding() {
    let source = r#"
system "test" {
    entity Character { name: string }
    event leave(actor: Character) {
        target: Character
    }
    condition Foo on bearer: Character {
        suppress leave(actor: bearer, actor: bearer)
    }
}
"#;
    expect_errors(source, &["duplicate suppress binding `actor`"]);
}

// ═══════════════════════════════════════════════════════════════
// Fix: Event param/field name collisions
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_event_param_field_collision() {
    let source = r#"
system "test" {
    entity Character { name: string }
    event hit(actor: Character) {
        actor: int
    }
}
"#;
    expect_errors(source, &["field `actor` collides with a parameter"]);
}

#[test]
fn test_event_no_collision_different_names() {
    let source = r#"
system "test" {
    entity Character { name: string }
    event hit(actor: Character) {
        damage: int
    }
}
"#;
    expect_no_errors(source);
}

// ═══════════════════════════════════════════════════════════════
// Fix: Unknown types in local let annotations
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_unknown_type_in_let_annotation() {
    let source = r#"
system "test" {
    derive foo() -> int {
        let x: MissingType = 42
        0
    }
}
"#;
    expect_errors(source, &["unknown type `MissingType`"]);
}

#[test]
fn test_unknown_type_in_modify_let_annotation() {
    let source = r#"
system "test" {
    entity Character { speed: int }
    derive initial_budget(actor: Character) -> int {
        actor.speed
    }
    condition Slow on bearer: Character {
        modify initial_budget(actor: bearer) {
            let x: MissingType = 42
            result = 0
        }
    }
}
"#;
    expect_errors(source, &["unknown type `MissingType`"]);
}

#[test]
fn test_unknown_type_in_let_is_sole_error() {
    // Ensure the unknown type is reported even when the value is well-typed
    let source = r#"
system "test" {
    derive foo() -> int {
        let x: MissingType = 42
        0
    }
}
"#;
    expect_error_count(source, 1);
    expect_errors(source, &["unknown type `MissingType`"]);
}

// ═══════════════════════════════════════════════════════════════
// Mixed named+positional trigger bindings
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_mixed_named_then_positional_trigger_binding() {
    // named `actor:` consumes param 0, positional should resolve to param 1 (target)
    let source = r#"
system "test" {
    entity Character { name: string }
    event damage(actor: Character, target: Character) {}
    reaction Block on defender: Character (trigger: damage(actor: defender, defender)) {
        cost { reaction }
        resolve {}
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_mixed_positional_then_named_trigger_binding() {
    // positional should fill param 0 (actor), named `amount:` fills param 1
    let source = r#"
system "test" {
    entity Character { name: string }
    event damage(actor: Character, amount: int) {}
    reaction Block on defender: Character (trigger: damage(defender, amount: 42)) {
        cost { reaction }
        resolve {}
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_mixed_named_positional_trigger_type_mismatch() {
    // named binds param 0 (actor); positional should check against param 1 (amount: int), not param 0
    let source = r#"
system "test" {
    entity Character { name: string }
    event damage(actor: Character, amount: int) {}
    reaction Block on defender: Character (trigger: damage(actor: defender, defender)) {
        cost { reaction }
        resolve {}
    }
}
"#;
    expect_errors(
        source,
        &["positional trigger binding 1 has type Character, expected int"],
    );
}

// ═══════════════════════════════════════════════════════════════
// Implicit name shadowing in actions/reactions
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_action_receiver_shadows_turn() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    action Heal on turn: Character () {
        cost { action }
        resolve {}
    }
}
"#;
    expect_errors(
        source,
        &["receiver `turn` shadows the implicit turn budget binding"],
    );
}

#[test]
fn test_action_param_shadows_turn() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    action Heal on target: Character (turn: int) {
        cost { action }
        resolve {}
    }
}
"#;
    expect_errors(
        source,
        &["parameter `turn` shadows the implicit turn budget binding"],
    );
}

#[test]
fn test_action_param_shadows_receiver() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    action Heal on target: Character (target: int) {
        cost { action }
        resolve {}
    }
}
"#;
    expect_errors(source, &["parameter `target` shadows the receiver binding"]);
}

#[test]
fn test_reaction_receiver_shadows_trigger() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    event damage(actor: Character) {}
    reaction Block on trigger: Character (trigger: damage(trigger)) {
        cost { reaction }
        resolve {}
    }
}
"#;
    expect_errors(
        source,
        &["receiver `trigger` shadows the implicit trigger binding"],
    );
}

#[test]
fn test_reaction_receiver_shadows_turn() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    event damage(actor: Character) {}
    reaction Block on turn: Character (trigger: damage(turn)) {
        cost { reaction }
        resolve {}
    }
}
"#;
    expect_errors(
        source,
        &["receiver `turn` shadows the implicit turn budget binding"],
    );
}

// ═══════════════════════════════════════════════════════════════
// Regression: type/value namespace separation
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_bare_struct_name_is_not_a_value() {
    // Struct type names must not be usable as values — instances come from
    // struct literals or function parameters, not from the type name itself.
    let source = r#"
system "test" {
    struct Pair {
        a: int
        b: int
    }
    derive foo() -> int {
        let x = Pair
        0
    }
}
"#;
    expect_errors(source, &["type `Pair` cannot be used as a value"]);
}

#[test]
fn test_bare_entity_name_is_not_a_value() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    derive foo() -> int {
        let x = Character
        0
    }
}
"#;
    expect_errors(source, &["type `Character` cannot be used as a value"]);
}

#[test]
fn test_bare_struct_field_access_rejected() {
    // Character.hp should not type-check without a Character instance
    let source = r#"
system "test" {
    entity Character { HP: int }
    derive foo() -> int {
        Character.HP
    }
}
"#;
    expect_errors(source, &["type `Character` cannot be used as a value"]);
}

#[test]
fn test_enum_qualified_access_still_works() {
    // Enum qualified variant access should still work
    let source = r#"
system "test" {
    entity Character { HP: int }
    enum DamageType { fire, cold, lightning }
    derive foo() -> DamageType {
        DamageType.fire
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_local_variable_shadows_enum_constructor() {
    // A local variable named after an enum type should shadow the enum
    // for constructor calls — the fallback to env.types must not bypass scope.
    let source = r#"
system "test" {
    enum Effect {
        timed(count: int)
        permanent
    }
    derive foo() -> int {
        let Effect = 5
        Effect.timed(count: 1)
        0
    }
}
"#;
    expect_errors(source, &["has no methods"]);
}

// ═══════════════════════════════════════════════════════════════
// Regression: none should not collapse option types
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_none_if_else_prefers_concrete_type() {
    // When both branches are `none`, the result is option<error> which is
    // compatible with any option<T> return type.
    let source = r#"
system "test" {
    derive foo(x: bool) -> option<int> {
        if x { none } else { none }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_none_then_concrete_option_unifies() {
    let source = r#"
system "test" {
    derive foo(x: bool, y: option<int>) -> option<int> {
        if x { none } else { y }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_concrete_option_then_none_unifies() {
    let source = r#"
system "test" {
    derive foo(x: bool, y: option<int>) -> option<int> {
        if x { y } else { none }
    }
}
"#;
    expect_no_errors(source);
}

// ═══════════════════════════════════════════════════════════════
// Fix: Receiver type must be entity
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_action_struct_receiver_rejected() {
    let source = r#"
system "test" {
    struct Stats { hp: int }
    action Heal on actor: Stats () {
        cost { action }
        resolve {}
    }
}
"#;
    expect_errors(
        source,
        &["action `Heal` receiver type must be an entity, found Stats"],
    );
}

#[test]
fn test_reaction_struct_receiver_rejected() {
    let source = r#"
system "test" {
    struct Stats { hp: int }
    entity Character { hp: int }
    event damage(actor: Character) {}
    reaction Block on actor: Stats (trigger: damage(actor)) {
        cost { reaction }
        resolve {}
    }
}
"#;
    expect_errors(
        source,
        &["reaction `Block` receiver type must be an entity, found Stats"],
    );
}

#[test]
fn test_condition_struct_receiver_rejected() {
    let source = r#"
system "test" {
    struct Stats { hp: int }
    condition Slow on bearer: Stats {}
}
"#;
    expect_errors(
        source,
        &["condition `Slow` receiver type must be an entity, found Stats"],
    );
}

#[test]
fn test_action_enum_receiver_rejected() {
    let source = r#"
system "test" {
    enum Color { red, green }
    action Paint on actor: Color () {
        cost { action }
        resolve {}
    }
}
"#;
    expect_errors(
        source,
        &["action `Paint` receiver type must be an entity, found Color"],
    );
}

#[test]
fn test_action_entity_receiver_ok() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    action Heal on actor: Character () {
        cost { action }
        resolve { actor.hp += 10 }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_action_any_entity_receiver_ok() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    action Heal on actor: entity () {
        cost { action }
        resolve {}
    }
}
"#;
    expect_no_errors(source);
}

// ═══════════════════════════════════════════════════════════════
// Fix: Entity-generic builtins (apply_condition, remove_condition)
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_apply_condition_with_non_character_entity() {
    let source = r#"
system "test" {
    entity Monster {
        hp: int
    }
    condition Stunned on bearer: Monster {}
    action Bash on actor: Monster (target: Monster) {
        cost { action }
        resolve {
            apply_condition(target, Stunned, Duration.indefinite)
        }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_remove_condition_with_non_character_entity() {
    let source = r#"
system "test" {
    entity Monster {
        hp: int
    }
    condition Stunned on bearer: Monster {}
    action Cleanse on actor: Monster (target: Monster) {
        cost { action }
        resolve {
            remove_condition(target, Stunned)
        }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_apply_condition_with_struct_rejected() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    struct Stats { hp: int }
    condition Stunned on bearer: Character {}
    action Bash on actor: Character (target: Character) {
        cost { action }
        resolve {
            let s = Stats { hp: 10 }
            apply_condition(s, Stunned, Duration.indefinite)
        }
    }
}
"#;
    expect_errors(
        source,
        &["argument `target` has type Stats, expected entity"],
    );
}

// ── Issue 1: Immutable let bindings reject field/index mutation ──

#[test]
fn test_let_field_mutation_rejected_in_action() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
    }
    action Foo on actor: Character () {
        cost { action }
        resolve {
            let s = Character {
                HP: 10
            }
            s.HP = 5
        }
    }
}
"#;
    expect_errors(
        source,
        &["cannot mutate field/index of immutable binding `s`"],
    );
}

#[test]
fn test_let_index_mutation_rejected() {
    let source = r#"
system "test" {
    derive foo() -> int {
        let xs = [1, 2, 3]
        xs[0] = 99
        0
    }
}
"#;
    expect_errors(
        source,
        &["cannot mutate field/index of immutable binding `xs`"],
    );
}

#[test]
fn test_action_receiver_field_mutation_still_ok() {
    // Receiver is explicitly mutable — field mutation should work
    let source = r#"
system "test" {
    entity Character { HP: int }
    action Heal on actor: Character (target: Character) {
        cost { action }
        resolve {
            actor.HP += 5
            target.HP += 5
        }
    }
}
"#;
    expect_no_errors(source);
}

// ── Issue 2: Variant/function name collision warning ──

#[test]
fn test_variant_shadows_function_warning() {
    let source = r#"
system "test" {
    derive foo() -> int { 0 }
    enum MyEnum { foo }
}
"#;
    expect_warnings(source, &["enum variant `foo` shadows function"]);
}

#[test]
fn test_function_shadows_variant_warning() {
    let source = r#"
system "test" {
    enum MyEnum { bar }
    derive bar() -> int { 0 }
}
"#;
    expect_warnings(
        source,
        &["function `bar` has the same name as an enum variant"],
    );
}

// ── Issue 3: Ordering ops restricted to orderable types ──

#[test]
fn test_bool_ordering_rejected() {
    let source = r#"
system "test" {
    derive foo(a: bool, b: bool) -> bool {
        a < b
    }
}
"#;
    expect_errors(source, &["cannot order bool and bool"]);
}

#[test]
fn test_struct_ordering_rejected() {
    let source = r#"
system "test" {
    struct S { x: int }
    derive foo(a: S, b: S) -> bool {
        a < b
    }
}
"#;
    expect_errors(source, &["cannot order S and S"]);
}

#[test]
fn test_bool_equality_still_ok() {
    let source = r#"
system "test" {
    derive foo(a: bool, b: bool) -> bool {
        a == b
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_int_ordering_still_ok() {
    let source = r#"
system "test" {
    derive foo(a: int, b: int) -> bool {
        a < b
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_string_ordering_ok() {
    let source = r#"
system "test" {
    derive foo(a: string, b: string) -> bool {
        a >= b
    }
}
"#;
    expect_no_errors(source);
}

// ── Issue 4: Prompt suggest expressions are checked ──

#[test]
fn test_prompt_suggest_type_mismatch() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    prompt ChooseTarget(options: list<Character>) -> Character {
        hint: "Pick a target"
        suggest: "not a character"
    }
}
"#;
    expect_errors(
        source,
        &["suggest expression has type string, expected Character"],
    );
}

#[test]
fn test_prompt_suggest_undefined_var() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    prompt ChooseTarget(options: list<Character>) -> Character {
        hint: "Pick a target"
        suggest: nonexistent
    }
}
"#;
    expect_errors(source, &["undefined variable `nonexistent`"]);
}

#[test]
fn test_prompt_suggest_ok() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    prompt ChooseTarget(options: list<Character>) -> Character {
        hint: "Pick a target"
        suggest: options[0]
    }
}
"#;
    expect_no_errors(source);
}

// ═══════════════════════════════════════════════════════════════
// Fix: Trigger payload direct field mutation is blocked
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_trigger_direct_field_mutation_rejected() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    event damage(actor: Character, target: Character) {}
    reaction Block on reactor: Character (trigger: damage(reactor)) {
        cost { reaction }
        resolve { trigger.target = reactor }
    }
}
"#;
    expect_errors(source, &["cannot mutate field of trigger payload"]);
}

#[test]
fn test_trigger_deep_field_mutation_ok() {
    // trigger.entity.HP goes through an entity reference — allowed
    let source = r#"
system "test" {
    entity Character { HP: int }
    event damage(actor: Character, target: Character) {}
    reaction Block on reactor: Character (trigger: damage(reactor)) {
        cost { reaction }
        resolve { trigger.target.HP = trigger.target.HP - 1 }
    }
}
"#;
    expect_no_errors(source);
}

// ═══════════════════════════════════════════════════════════════
// Fix: Receiver rebinding is blocked
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_receiver_reassignment_rejected() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    action Heal on actor: Character (target: Character) {
        cost { action }
        resolve { actor = target }
    }
}
"#;
    expect_errors(source, &["cannot reassign immutable binding `actor`"]);
}

#[test]
fn test_receiver_field_mutation_still_ok() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    action Heal on actor: Character (target: Character) {
        cost { action }
        resolve { actor.HP = actor.HP + 10 }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_reaction_receiver_reassignment_rejected() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    event damage(actor: Character) {}
    reaction Block on reactor: Character (trigger: damage(reactor)) {
        cost { reaction }
        resolve { reactor = trigger.actor }
    }
}
"#;
    expect_errors(source, &["cannot reassign immutable binding `reactor`"]);
}

// ═══════════════════════════════════════════════════════════════
// Fix: Duplicate pattern bindings
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_duplicate_pattern_binding_rejected() {
    let source = r#"
system "test" {
    enum Outcome { hit(amount: int, target: int), miss }
    derive check(x: Outcome) -> int {
        match x {
            Outcome.hit(a, a) => a
            miss => 0
        }
    }
}
"#;
    expect_errors(source, &["duplicate binding `a` in pattern"]);
}

// ═══════════════════════════════════════════════════════════════
// Option declarations
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_option_with_modify_clause_ok() {
    let source = r#"
system "test" {
    derive base_modifier(x: int) -> int { x + 2 }
    option generous {
        description: "Increases base modifier"
        default: off
        when enabled {
            modify base_modifier(x: 10) {
                result = result + 5
            }
        }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_option_modify_undefined_target() {
    let source = r#"
system "test" {
    option flanking {
        when enabled {
            modify nonexistent_fn(actor: 1) {
                result = 0
            }
        }
    }
}
"#;
    expect_errors(
        source,
        &["modify target `nonexistent_fn` is not a defined function"],
    );
}

#[test]
fn test_option_modify_wrong_target_kind() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    action Heal on actor: Character () {
        cost { action }
        resolve { actor.hp += 10 }
    }
    option flanking {
        when enabled {
            modify Heal(actor: 1) {
                result = 0
            }
        }
    }
}
"#;
    expect_errors(
        source,
        &["modify target `Heal` must be a derive or mechanic"],
    );
}

#[test]
fn test_option_modify_binding_type_mismatch() {
    let source = r#"
system "test" {
    entity Character { speed: int }
    derive initial_budget(actor: Character) -> int {
        actor.speed
    }
    option flanking {
        when enabled {
            modify initial_budget(actor: "not_a_character") {
                result = result + 5
            }
        }
    }
}
"#;
    expect_errors(
        source,
        &["modify binding `actor` has type string, expected Character"],
    );
}

#[test]
fn test_option_with_modify_clause_with_receiver_in_condition() {
    // Verify condition modify still works after refactor
    let source = r#"
system "test" {
    entity Character { speed: int }
    derive initial_budget(actor: Character) -> int {
        actor.speed
    }
    condition Slow on bearer: Character {
        modify initial_budget(actor: bearer) {
            result = result - 10
        }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_duplicate_option_name() {
    let source = r#"
system "test" {
    option flanking {
        description: "First"
    }
    option flanking {
        description: "Second"
    }
}
"#;
    expect_errors(source, &["duplicate option declaration `flanking`"]);
}

#[test]
fn test_option_empty_no_errors() {
    let source = r#"
system "test" {
    option flanking {
        description: "Flanking gives advantage"
        default: on
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_option_extends_unknown_parent() {
    let source = r#"
system "test" {
    option flanking extends "Some System" {
        description: "Flanking gives advantage"
        default: on
    }
}
"#;
    expect_errors(
        source,
        &["option \"flanking\" extends unknown option \"Some System\""],
    );
}

#[test]
fn test_option_extends_valid_parent() {
    let source = r#"
system "test" {
    option base_flanking {
        description: "Base flanking rules"
        default: on
    }
    option flanking extends "base_flanking" {
        description: "Extended flanking"
        default: on
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_option_extends_system_name() {
    let source = r#"
system "D&D 5e Combat" {
    option flanking extends "D&D 5e Combat" {
        description: "Flanking gives advantage"
        default: off
    }
}
"#;
    expect_no_errors(source);
}

// ═══════════════════════════════════════════════════════════════
// Move declarations (must be lowered before checking)
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_unlowered_move_rejected() {
    let source = r#"
system "test" {
    entity Character { stat: int }
    move Hack on actor: Character () {
        trigger: "When you hack and slash"
        roll: 2d6 + actor.stat
        on success {
            actor.stat += 1
        }
        on failure {
            actor.stat -= 1
        }
    }
}
"#;
    expect_errors(
        source,
        &["move declarations must be lowered before type-checking"],
    );
}

// ── Bare-call shadowing by local bindings ────────────────────────────

#[test]
fn local_binding_shadows_enum_variant_constructor() {
    let source = r#"
system "test" {
    enum Effect { timed(count: int), permanent }
    derive foo() -> int {
        let timed = 5
        timed(count: 1)
        0
    }
}
"#;
    expect_errors(
        source,
        &["is a local binding of type int, not a callable function"],
    );
}

#[test]
fn local_binding_shadows_function() {
    let source = r#"
system "test" {
    derive bar() -> int { 1 }
    derive foo() -> int {
        let bar = 5
        bar()
    }
}
"#;
    expect_errors(
        source,
        &["is a local binding of type int, not a callable function"],
    );
}

#[test]
fn local_binding_as_callee_still_checks_args() {
    let source = r#"
system "test" {
    derive bar() -> int { 1 }
    derive foo() -> int {
        let bar = 5
        bar(undefined_var)
    }
}
"#;
    expect_errors(
        source,
        &[
            "is a local binding of type int, not a callable function",
            "undefined variable `undefined_var`",
        ],
    );
}

#[test]
fn undefined_function_still_checks_args() {
    let source = r#"
system "test" {
    derive foo() -> int {
        nonexistent(undefined_var)
    }
}
"#;
    expect_errors(
        source,
        &[
            "undefined function `nonexistent`",
            "undefined variable `undefined_var`",
        ],
    );
}

#[test]
fn local_binding_does_not_shadow_qualified_call() {
    // Qualified calls go through check_expr on the object, so a local
    // variable with the same name as an enum variant should NOT interfere
    // with Type.variant() syntax.
    let source = r#"
system "test" {
    enum Effect { timed(count: int), permanent }
    derive foo() -> Effect {
        let timed = 5
        Effect.timed(count: timed)
    }
}
"#;
    expect_no_errors(source);
}

// ── List literal typing with none ────────────────────────────────────

#[test]
fn list_literal_none_first_element() {
    let source = r#"
system "test" {
    derive foo(y: option<int>) -> list<option<int>> {
        [none, y]
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn list_literal_none_later_element() {
    let source = r#"
system "test" {
    derive foo(y: option<int>) -> list<option<int>> {
        [y, none]
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn list_literal_all_none_needs_context() {
    // All none — inferred as list<option<error>>; no concrete type to unify
    // against, so it cannot satisfy a concrete return type.
    let source = r#"
system "test" {
    derive foo() -> list<option<int>> {
        [none, none]
    }
}
"#;
    expect_errors(source, &["expected return type"]);
}

#[test]
fn list_literal_mixed_type_still_errors() {
    let source = r#"
system "test" {
    derive foo() -> list<int> {
        [1, "hello"]
    }
}
"#;
    expect_errors(source, &["list element has type string, expected int"]);
}

// ═══════════════════════════════════════════════════════════════
// Fix: Enum values must not behave as enum namespaces
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_enum_value_field_access_rejected() {
    // c is a Color value — c.red should be rejected
    let source = r#"
system "test" {
    enum Color { red, green, blue }
    derive bad(c: Color) -> Color { c.red }
}
"#;
    expect_errors(source, &["cannot access field `red` on enum value"]);
}

#[test]
fn test_enum_value_variant_call_rejected() {
    // c is a Color value — c.red() should be rejected
    let source = r#"
system "test" {
    enum Effect { timed(count: int), permanent }
    derive bad(e: Effect) -> Effect { e.timed(count: 1) }
}
"#;
    expect_errors(source, &["has no methods"]);
}

#[test]
fn test_enum_namespace_qualified_access_still_works() {
    let source = r#"
system "test" {
    enum Color { red, green, blue }
    derive foo() -> Color { Color.red }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_enum_namespace_constructor_still_works() {
    let source = r#"
system "test" {
    enum Effect { timed(count: int), permanent }
    derive foo() -> Effect { Effect.timed(count: 1) }
}
"#;
    expect_no_errors(source);
}

// ═══════════════════════════════════════════════════════════════
// Fix: Trigger binding cannot reference trigger itself
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_trigger_binding_self_reference_rejected() {
    let source = r#"
system "test" {
    entity Character { name: string }
    event damage(actor: Character) {}
    reaction Block on reactor: Character (trigger: damage(actor: trigger.actor)) {
        cost { reaction }
        resolve {}
    }
}
"#;
    expect_errors(source, &["undefined variable `trigger`"]);
}

#[test]
fn test_trigger_available_in_resolve_block() {
    // trigger should still be available in the resolve block
    let source = r#"
system "test" {
    entity Character { HP: int }
    event damage(actor: Character, target: Character) {}
    reaction Block on reactor: Character (trigger: damage(reactor)) {
        cost { reaction }
        resolve {
            trigger.target.HP = trigger.target.HP - 1
        }
    }
}
"#;
    expect_no_errors(source);
}

// ═══════════════════════════════════════════════════════════════
// Fix: TurnBudget uses user-defined fields when present
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_turn_budget_user_defined_fields() {
    // User-defined TurnBudget fields are valid cost tokens.
    let source = r#"
system "test" {
    entity Character { HP: int }
    struct TurnBudget {
        foo: int
    }
    action Foo on actor: Character () {
        cost { foo }
        resolve {
            turn.foo += 1
        }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_turn_budget_user_defined_rejects_unknown_field() {
    // When user defines TurnBudget, hardcoded fields should not be available
    let source = r#"
system "test" {
    entity Character { HP: int }
    struct TurnBudget {
        foo: int
    }
    action Foo on actor: Character () {
        cost { action }
        resolve {
            turn.actions += 1
        }
    }
}
"#;
    expect_errors(source, &["TurnBudget has no field `actions`"]);
}

#[test]
fn test_turn_budget_hardcoded_fields_without_user_definition() {
    // Without user-defined TurnBudget, hardcoded fields should work
    let source = r#"
system "test" {
    entity Character { HP: int }
    action Foo on actor: Character () {
        cost { action }
        resolve {
            turn.actions += 1
        }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_turn_budget_custom_cost_token_forward_decl() {
    // Cost token validation runs after all type collection, so this is valid
    // even though TurnBudget is declared after the action.
    let source = r#"
system "test" {
    entity Character { HP: int }
    action Step on actor: Character () {
        cost { stamina }
        resolve {}
    }
    struct TurnBudget {
        stamina: int
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_turn_budget_invalid_custom_cost_token() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    struct TurnBudget {
        stamina: int
    }
    action Step on actor: Character () {
        cost { unknown_token }
        resolve {}
    }
}
"#;
    expect_errors(source, &["invalid cost token `unknown_token`"]);
}

// ═══════════════════════════════════════════════════════════════
// Fix: none comparison with option<T>
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_none_eq_option_int() {
    let source = r#"
system "test" {
    derive foo(x: option<int>) -> bool {
        x == none
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_none_neq_option_string() {
    let source = r#"
system "test" {
    derive foo(x: option<string>) -> bool {
        none != x
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_none_eq_int_still_rejected() {
    let source = r#"
system "test" {
    derive foo(x: int) -> bool {
        x == none
    }
}
"#;
    expect_errors(source, &["cannot compare"]);
}

// ═══════════════════════════════════════════════════════════════
// Phase 0: Move lowering tests
// ═══════════════════════════════════════════════════════════════

#[test]
fn lower_move_roundtrip_no_move_decls_remain() {
    let source = r#"
system "test" {
    entity Character {
        stat: int
    }
    move GoAggro on actor: Character () {
        trigger: "When you threaten with force"
        roll: 2d6 + actor.stat
        on strong_hit {
            actor.stat += 1
        }
        on weak_hit {
            actor.stat += 0
        }
        on miss {
            actor.stat -= 1
        }
    }
}
"#;
    let (program, result) = check_lowered(source);
    // No checker errors
    let errors: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.severity == ttrpg_ast::diagnostic::Severity::Error)
        .collect();
    if !errors.is_empty() {
        let sm = SourceMap::new(source);
        let rendered: Vec<_> = errors.iter().map(|d| sm.render(d)).collect();
        panic!(
            "expected no errors after lowering, found {}:\n{}",
            errors.len(),
            rendered.join("\n\n")
        );
    }
    // No DeclKind::Move remains
    for item in &program.items {
        if let ttrpg_ast::ast::TopLevel::System(system) = &item.node {
            for decl in &system.decls {
                assert!(
                    !matches!(decl.node, DeclKind::Move(_)),
                    "DeclKind::Move should not remain after lowering"
                );
            }
        }
    }
}

#[test]
fn lower_move_preserves_trigger_text() {
    let source = r#"
system "test" {
    entity Character {
        stat: int
    }
    move GoAggro on actor: Character () {
        trigger: "When you threaten with force"
        roll: 2d6 + actor.stat
        on strong_hit {}
        on weak_hit {}
        on miss {}
    }
}
"#;
    let (program, _) = check_lowered(source);
    // Find the synthesized action and verify trigger_text
    for item in &program.items {
        if let ttrpg_ast::ast::TopLevel::System(system) = &item.node {
            for decl in &system.decls {
                if let DeclKind::Action(a) = &decl.node {
                    assert_eq!(a.name, "GoAggro");
                    assert_eq!(
                        a.trigger_text,
                        Some("When you threaten with force".to_string())
                    );
                    assert!(a.synthetic);
                    return;
                }
            }
        }
    }
    panic!("synthesized action not found");
}

#[test]
fn lower_move_missing_outcome_produces_diagnostic() {
    let source = r#"
system "test" {
    entity Character { stat: int }
    move Hack on actor: Character () {
        trigger: "hack"
        roll: 2d6
        on strong_hit {}
        on weak_hit {}
    }
}
"#;
    let (_, diags) = lower_source(source);
    assert!(
        diags
            .iter()
            .any(|d| d.message.contains("missing required outcome `miss`")),
        "expected diagnostic about missing 'miss' outcome, got: {:?}",
        diags.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

#[test]
fn lower_move_extra_outcome_produces_diagnostic() {
    let source = r#"
system "test" {
    entity Character { stat: int }
    move Hack on actor: Character () {
        trigger: "hack"
        roll: 2d6
        on strong_hit {}
        on weak_hit {}
        on miss {}
        on critical {}
    }
}
"#;
    let (_, diags) = lower_source(source);
    assert!(
        diags
            .iter()
            .any(|d| d.message.contains("invalid outcome `critical`")),
        "expected diagnostic about invalid outcome, got: {:?}",
        diags.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

#[test]
fn lower_move_duplicate_outcome_produces_diagnostic() {
    let source = r#"
system "test" {
    entity Character { stat: int }
    move Hack on actor: Character () {
        trigger: "hack"
        roll: 2d6
        on strong_hit {}
        on strong_hit {}
        on weak_hit {}
        on miss {}
    }
}
"#;
    let (_, diags) = lower_source(source);
    assert!(
        diags
            .iter()
            .any(|d| d.message.contains("duplicate outcome `strong_hit`")),
        "expected diagnostic about duplicate outcome, got: {:?}",
        diags.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

#[test]
fn lower_move_synthetic_name_collision_produces_diagnostic() {
    let source = r#"
system "test" {
    entity Character { stat: int }
    mechanic __hack_roll(c: Character) -> RollResult {
        roll(2d6)
    }
    move Hack on actor: Character () {
        trigger: "hack"
        roll: 2d6
        on strong_hit {}
        on weak_hit {}
        on miss {}
    }
}
"#;
    let (_, diags) = lower_source(source);
    assert!(
        diags
            .iter()
            .any(|d| d.message.contains("collides with an existing declaration")),
        "expected diagnostic about synthetic name collision, got: {:?}",
        diags.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

// ── Checker prerequisite tests ──────────────────────────────────

#[test]
fn test_reserved_prefix_rejected_on_user_declarations() {
    let source = r#"
system "test" {
    derive __my_func() -> int { 0 }
}
"#;
    expect_errors(source, &["names starting with `__` are reserved"]);
}

#[test]
fn test_reserved_prefix_accepted_on_synthetic_declarations() {
    // Moves lower to synthetic names starting with __; these must be accepted
    let source = r#"
system "test" {
    entity Character { stat: int }
    move GoAggro on actor: Character () {
        trigger: "threaten"
        roll: 2d6 + actor.stat
        on strong_hit {}
        on weak_hit {}
        on miss {}
    }
}
"#;
    let (_, result) = check_lowered(source);
    let errors: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.severity == ttrpg_ast::diagnostic::Severity::Error)
        .collect();
    assert!(
        errors.is_empty(),
        "synthetic __ names should be accepted, but got errors: {:?}",
        errors.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

#[test]
fn test_direct_reaction_call_rejected() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    event TakeDamage(target: Character) {}
    reaction Parry on reactor: Character (
        trigger: TakeDamage(reactor)
    ) {
        resolve {}
    }
    action Attack on actor: Character () {
        resolve {
            Parry(actor)
        }
    }
}
"#;
    expect_errors(source, &["reactions cannot be called directly"]);
}

#[test]
fn test_set_position_rejected() {
    let source = r#"
system "test" {
    derive foo(s: set<Position>) -> int { 0 }
}
"#;
    expect_errors(source, &["Position cannot be used as a set element type"]);
}

// ── set methods ──────────────────────────────────────────────

#[test]
fn test_set_add_typechecks() {
    let source = r#"
system "test" {
    enum Color { red, green, blue }
    derive f(s: set<Color>) -> set<Color> {
        s.add(red)
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_set_remove_typechecks() {
    let source = r#"
system "test" {
    enum Color { red, green, blue }
    derive f(s: set<Color>) -> set<Color> {
        s.remove(green)
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_set_union_typechecks() {
    let source = r#"
system "test" {
    derive f(a: set<int>, b: set<int>) -> set<int> {
        a.union(b)
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_set_intersection_typechecks() {
    let source = r#"
system "test" {
    derive f(a: set<int>, b: set<int>) -> set<int> {
        a.intersection(b)
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_set_difference_typechecks() {
    let source = r#"
system "test" {
    derive f(a: set<int>, b: set<int>) -> set<int> {
        a.difference(b)
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_set_to_list_typechecks() {
    let source = r#"
system "test" {
    derive f(s: set<int>) -> list<int> {
        s.to_list()
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_set_contains_typechecks() {
    let source = r#"
system "test" {
    derive f(s: set<int>, x: int) -> bool {
        s.contains(x)
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_list_to_set_typechecks() {
    let source = r#"
system "test" {
    derive f(xs: list<int>) -> set<int> {
        xs.to_set()
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_set_add_wrong_element_type() {
    let source = r#"
system "test" {
    derive f(s: set<int>) -> set<int> {
        s.add("hello")
    }
}
"#;
    expect_errors(source, &["element type mismatch"]);
}

#[test]
fn test_set_remove_wrong_element_type() {
    let source = r#"
system "test" {
    derive f(s: set<int>) -> set<int> {
        s.remove("hello")
    }
}
"#;
    expect_errors(source, &["element type mismatch"]);
}

#[test]
fn test_set_union_wrong_arg_type() {
    let source = r#"
system "test" {
    derive f(a: set<int>, b: list<int>) -> set<int> {
        a.union(b)
    }
}
"#;
    expect_errors(source, &["type mismatch"]);
}

#[test]
fn test_set_contains_wrong_element_type() {
    let source = r#"
system "test" {
    derive f(s: set<int>) -> bool {
        s.contains("hello")
    }
}
"#;
    expect_errors(source, &["element type mismatch"]);
}

// ── set += / -= ──────────────────────────────────────────────

#[test]
fn test_set_pluseq_typechecks() {
    let source = r#"
system "test" {
    enum DamageType { fire, cold, lightning }
    entity Character {
        resistances: set<DamageType>
    }
    action GainResist on actor: Character () {
        resolve {
            actor.resistances += fire
        }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_set_minuseq_typechecks() {
    let source = r#"
system "test" {
    enum DamageType { fire, cold, lightning }
    entity Character {
        resistances: set<DamageType>
    }
    action LoseResist on actor: Character () {
        resolve {
            actor.resistances -= fire
        }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_set_pluseq_wrong_element_type() {
    let source = r#"
system "test" {
    entity Character {
        tags: set<int>
    }
    action Foo on actor: Character () {
        resolve {
            actor.tags += "hello"
        }
    }
}
"#;
    expect_errors(source, &["right side of += on set<int>"]);
}

#[test]
fn test_set_minuseq_wrong_element_type() {
    let source = r#"
system "test" {
    entity Character {
        tags: set<int>
    }
    action Foo on actor: Character () {
        resolve {
            actor.tags -= "hello"
        }
    }
}
"#;
    expect_errors(source, &["right side of -= on set<int>"]);
}

#[test]
fn test_set_pluseq_local_variable_immutable() {
    // Local let bindings are immutable — += on a local set should be rejected
    let source = r#"
system "test" {
    derive f(s: set<int>) -> set<int> {
        let result = s
        result += 42
        result
    }
}
"#;
    expect_errors(source, &["cannot reassign immutable binding"]);
}

#[test]
fn test_map_position_key_rejected() {
    let source = r#"
system "test" {
    derive foo(m: map<Position, int>) -> int { 0 }
}
"#;
    expect_errors(source, &["Position cannot be used as a map key type"]);
}

#[test]
fn test_trigger_binding_rejects_effectful_calls() {
    // Mechanic call in trigger binding should be rejected
    let source = r#"
system "test" {
    entity Character { hp: int }
    mechanic do_roll(c: Character) -> RollResult {
        roll(2d6)
    }
    event TakeDamage(target: Character, amount: int) {}
    reaction Parry on reactor: Character (
        trigger: TakeDamage(target: reactor, amount: do_roll(reactor).total)
    ) {
        resolve {}
    }
}
"#;
    expect_errors(
        source,
        &["cannot be called in trigger/suppress binding context"],
    );
}

#[test]
fn test_trigger_binding_allows_receiver_identity() {
    // Simple receiver identity in trigger binding should pass
    let source = r#"
system "test" {
    entity Character { hp: int }
    event TakeDamage(target: Character) {}
    reaction Parry on reactor: Character (
        trigger: TakeDamage(target: reactor)
    ) {
        resolve {}
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_trigger_binding_rejects_dice_literals() {
    // Dice literals in trigger binding should be rejected
    let source = r#"
system "test" {
    entity Character { hp: int }
    event TakeDamage(amount: int) {}
    reaction Parry on reactor: Character (
        trigger: TakeDamage(amount: 2d6)
    ) {
        resolve {}
    }
}
"#;
    expect_errors(
        source,
        &["dice literals are not allowed in trigger/suppress binding context"],
    );
}

#[test]
fn test_trigger_binding_allows_pure_builtins() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    event TakeDamage(amount: int) {}
    reaction Guard on reactor: Character (
        trigger: TakeDamage(amount: max(0, 1))
    ) {
        resolve {}
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn lower_move_with_params_roundtrip() {
    let source = r#"
system "test" {
    entity Character { stat: int }
    move GoAggro on actor: Character (target: Character) {
        trigger: "threaten with force"
        roll: 2d6 + actor.stat
        on strong_hit {
            target.stat -= 1
        }
        on weak_hit {}
        on miss {
            actor.stat -= 1
        }
    }
}
"#;
    let (program, result) = check_lowered(source);
    let errors: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.severity == ttrpg_ast::diagnostic::Severity::Error)
        .collect();
    if !errors.is_empty() {
        let sm = SourceMap::new(source);
        let rendered: Vec<_> = errors.iter().map(|d| sm.render(d)).collect();
        panic!(
            "expected no errors, found {}:\n{}",
            errors.len(),
            rendered.join("\n\n")
        );
    }
    // Verify no DeclKind::Move remains
    for item in &program.items {
        if let ttrpg_ast::ast::TopLevel::System(system) = &item.node {
            for decl in &system.decls {
                assert!(!matches!(decl.node, DeclKind::Move(_)));
            }
        }
    }
}

#[test]
fn test_some_pattern_type_checks() {
    let source = r#"
system "test" {
    derive f(x: option<int>) -> int {
        match x {
            some(n) => n,
            none => 0
        }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_some_pattern_wrong_scrutinee() {
    let source = r#"
system "test" {
    derive f(x: int) -> int {
        match x {
            some(n) => n,
            _ => 0
        }
    }
}
"#;
    expect_errors(source, &["`some(...)` pattern cannot match type int"]);
}

// ── option method tests ──────────────────────────────────────────

#[test]
fn test_option_unwrap_valid() {
    let source = r#"
system "test" {
    derive f(x: option<int>) -> int {
        x.unwrap()
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_option_unwrap_or_valid() {
    let source = r#"
system "test" {
    derive f(x: option<int>) -> int {
        x.unwrap_or(0)
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_option_unwrap_wrong_arg_count() {
    let source = r#"
system "test" {
    derive f(x: option<int>) -> int {
        x.unwrap(42)
    }
}
"#;
    expect_errors(source, &["unwrap() takes no arguments"]);
}

#[test]
fn test_option_unwrap_or_missing_arg() {
    let source = r#"
system "test" {
    derive f(x: option<int>) -> int {
        x.unwrap_or()
    }
}
"#;
    expect_errors(source, &["unwrap_or() takes exactly 1 argument"]);
}

#[test]
fn test_option_unwrap_or_type_mismatch() {
    let source = r#"
system "test" {
    derive f(x: option<int>) -> int {
        x.unwrap_or("hello")
    }
}
"#;
    expect_errors(
        source,
        &["unwrap_or() default has type string, expected int"],
    );
}

#[test]
fn test_option_unknown_method() {
    let source = r#"
system "test" {
    derive f(x: option<int>) -> int {
        x.foo()
    }
}
"#;
    expect_errors(source, &["option type has no method `foo`"]);
}

#[test]
fn test_option_method_no_parens() {
    let source = r#"
system "test" {
    derive f(x: option<int>) -> int {
        x.unwrap
    }
}
"#;
    expect_errors(
        source,
        &["`.unwrap` is a method on option; call it as `.unwrap()`"],
    );
}

#[test]
fn test_option_unwrap_chained_arithmetic() {
    let source = r#"
system "test" {
    derive f(x: option<int>) -> int {
        x.unwrap() + 5
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_some_pattern_nested_option() {
    let source = r#"
system "test" {
    derive f(x: option<option<int>>) -> int {
        match x {
            some(some(n)) => n,
            some(none) => -1,
            none => 0
        }
    }
}
"#;
    expect_no_errors(source);
}

// ── For-loop type checking ──────────────────────────────────────

#[test]
fn test_for_over_list() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    action AoE on caster: Character (targets: list<Character>, damage: int) {
        resolve {
            for target in targets {
                target.HP -= damage
            }
        }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_for_over_set() {
    let source = r#"
system "test" {
    enum DamageType { fire, cold }
    derive f(types: set<DamageType>) -> int {
        for _ in types {
            0
        }
        0
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_for_range() {
    let source = r#"
system "test" {
    derive f(n: int) -> int {
        for i in 0..n {
            i
        }
        0
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_for_range_with_expressions() {
    let source = r#"
system "test" {
    derive f(a: int, b: int) -> int {
        for i in a + 1..b * 2 {
            i
        }
        0
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_for_pattern_destructure() {
    let source = r#"
system "test" {
    enum Outcome { hit(amount: int), miss }
    derive f(results: list<Outcome>) -> int {
        for hit(amount) in results {
            amount
        }
        0
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_for_error_not_iterable() {
    let source = r#"
system "test" {
    derive f(x: int) -> int {
        for i in x { i }
        0
    }
}
"#;
    expect_errors(source, &["expected list or set, found int"]);
}

#[test]
fn test_for_error_map_not_iterable() {
    let source = r#"
system "test" {
    enum Ability { STR, DEX }
    derive f(m: map<Ability, int>) -> int {
        for x in m { 0 }
        0
    }
}
"#;
    expect_errors(source, &["map iteration is not supported"]);
}

#[test]
fn test_for_error_range_not_int() {
    let source = r#"
system "test" {
    derive f(x: bool) -> int {
        for i in x..10 { i }
        0
    }
}
"#;
    expect_errors(source, &["range start must be int, found bool"]);
}

#[test]
fn test_for_returns_unit() {
    let source = r#"
system "test" {
    derive f(xs: list<int>) -> int {
        for x in xs { x }
    }
}
"#;
    expect_errors(source, &["expected return type int"]);
}

#[test]
fn test_for_entity_binding_allows_field_mutation() {
    // Entity-typed loop vars should be non-local (field mutation allowed)
    let source = r#"
system "test" {
    entity Character { HP: int }
    action AoE on caster: Character (targets: list<Character>, damage: int) {
        resolve {
            for target in targets {
                target.HP -= damage
            }
        }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_for_non_entity_binding_rejects_field_mutation() {
    // Non-entity loop vars (structs) should stay local — field mutation is rejected
    let source = r#"
system "test" {
    entity Character { HP: int }
    struct Stats { value: int }
    action Foo on caster: Character (xs: list<Stats>) {
        resolve {
            for s in xs {
                s.value += 1
            }
        }
    }
}
"#;
    expect_errors(source, &["cannot mutate field/index of immutable binding"]);
}

// ═══════════════════════════════════════════════════════════════
// Optional groups: collection & declaration validation
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_optional_group_basic_declaration() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Spellcasting {
            spell_save_DC: int
        }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_top_level_group_external_attachment() {
    let source = r#"
system "test" {
    group Spellcasting {
        spell_save_DC: int = 10
        spell_slots: int
    }
    entity Character {
        HP: int
        optional Spellcasting
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_top_level_group_include_attachment() {
    let source = r#"
system "test" {
    group CombatStats {
        ac: int = 10
    }
    entity Monster {
        HP: int
        include CombatStats
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_external_attachment_unknown_group_rejected() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Spellcasting
    }
}
"#;
    expect_errors(source, &["unknown group `Spellcasting`"]);
}

#[test]
fn test_optional_group_duplicate_group_name() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Rage {
            uses: int
        }
        optional Rage {
            damage: int
        }
    }
}
"#;
    expect_errors(source, &["duplicate group `Rage` in entity `Character`"]);
}

#[test]
fn test_optional_group_duplicate_field_in_group() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Spellcasting {
            dc: int
            dc: int
        }
    }
}
"#;
    expect_errors(source, &["duplicate field `dc` in group `Spellcasting`"]);
}

#[test]
fn test_optional_group_field_default() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Rage {
            damage: int = 2
        }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_optional_group_field_default_type_mismatch() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Rage {
            damage: int = "not a number"
        }
    }
}
"#;
    expect_errors(source, &["default has type string, expected int"]);
}

#[test]
fn test_optional_group_name_conflicts_with_field() {
    let source = r#"
system "test" {
    entity Character {
        Spellcasting: int
        optional Spellcasting {
            dc: int
        }
    }
}
"#;
    expect_errors(
        source,
        &["group `Spellcasting` conflicts with field of the same name in entity `Character`"],
    );
}

#[test]
fn test_optional_group_name_conflicts_with_field_reverse_order() {
    // Group declared before field in source — still caught because
    // the parser separates fields and groups into two vecs.
    let source = r#"
system "test" {
    entity Character {
        optional HP {
            recovery: int
        }
        HP: int
    }
}
"#;
    expect_errors(
        source,
        &["group `HP` conflicts with field of the same name in entity `Character`"],
    );
}

// ═══════════════════════════════════════════════════════════════
// Optional groups: `has` expression type checking
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_has_returns_bool() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Spellcasting {
            dc: int
        }
    }
    derive check(actor: Character) -> bool {
        actor has Spellcasting
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_has_unknown_group_rejected() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
    }
    derive check(actor: Character) -> bool {
        actor has Nonexistent
    }
}
"#;
    expect_errors(
        source,
        &["entity `Character` has no optional group `Nonexistent`"],
    );
}

#[test]
fn test_has_on_non_entity_rejected() {
    let source = r#"
system "test" {
    derive check(x: int) -> bool {
        x has Something
    }
}
"#;
    expect_errors(
        source,
        &["`has` can only be used with entity types, found int"],
    );
}

#[test]
fn test_has_on_any_entity_with_known_group() {
    let source = r#"
system "test" {
    entity Character {
        optional Spellcasting { dc: int }
    }
    derive check(x: entity) -> bool {
        x has Spellcasting
    }
}
"#;
    expect_no_errors(source);
}

// ═══════════════════════════════════════════════════════════════
// Optional groups: field access requires narrowing
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_unguarded_group_access_rejected() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Spellcasting {
            dc: int
        }
    }
    derive check(actor: Character) -> int {
        actor.Spellcasting.dc
    }
}
"#;
    expect_errors(source, &["access to optional group `Spellcasting` on `actor` requires a `has` guard or `with` constraint"]);
}

#[test]
fn test_guarded_group_access_with_has() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Spellcasting {
            dc: int
        }
    }
    derive check(actor: Character) -> int {
        if actor has Spellcasting {
            actor.Spellcasting.dc
        } else {
            0
        }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_guarded_group_access_with_constraint() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Spellcasting {
            dc: int
        }
    }
    derive spell_dc(actor: Character with Spellcasting) -> int {
        actor.Spellcasting.dc
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_included_group_access_without_guard_allowed() {
    let source = r#"
system "test" {
    group CombatStats {
        ac: int
    }
    entity Monster {
        HP: int
        include CombatStats
    }
    derive ac_of(mon: Monster) -> int {
        mon.CombatStats.ac
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_guard_and_composition() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Spellcasting {
            dc: int
        }
        optional Rage {
            damage: int
        }
    }
    derive check(actor: Character) -> int {
        if actor has Spellcasting && actor has Rage {
            actor.Spellcasting.dc + actor.Rage.damage
        } else {
            0
        }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_group_field_not_found() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Spellcasting {
            dc: int
        }
    }
    derive check(actor: Character with Spellcasting) -> int {
        actor.Spellcasting.nonexistent
    }
}
"#;
    expect_errors(
        source,
        &["optional group `Spellcasting` has no field `nonexistent`"],
    );
}

// ═══════════════════════════════════════════════════════════════
// Optional groups: `with` constraint validation
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_with_constraint_unknown_group() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
    }
    derive check(actor: Character with Nonexistent) -> int {
        0
    }
}
"#;
    expect_errors(
        source,
        &["entity `Character` has no optional group `Nonexistent`"],
    );
}

#[test]
fn test_with_constraint_on_non_entity() {
    let source = r#"
system "test" {
    derive check(x: int with Something) -> int {
        0
    }
}
"#;
    expect_errors(
        source,
        &["`with` constraint on `x` requires entity type, found int"],
    );
}

#[test]
fn test_with_constraint_on_any_entity() {
    let source = r#"
system "test" {
    entity Character {
        optional Spellcasting {
            dc: int
        }
    }
    derive spell_dc(x: entity with Spellcasting) -> int {
        x.Spellcasting.dc
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_with_constraint_multiple_groups() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Spellcasting {
            dc: int
        }
        optional Rage {
            damage: int
        }
    }
    derive check(actor: Character with Spellcasting, Rage) -> int {
        actor.Spellcasting.dc + actor.Rage.damage
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_with_constraint_on_action_receiver() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Spellcasting {
            dc: int
        }
    }
    action CastSpell on caster: Character with Spellcasting () {
        resolve {
            caster.Spellcasting.dc += 1
        }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_with_constraint_on_reaction_receiver() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Spellcasting {
            dc: int
        }
    }
    event attack(attacker: Character) {}
    reaction Counterspell on caster: Character with Spellcasting (trigger: attack(caster)) {
        cost { reaction }
        resolve {
            caster.Spellcasting.dc += 1
        }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_with_constraint_on_action_param() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Spellcasting {
            dc: int
        }
    }
    action Dispel on caster: Character (target: Character with Spellcasting) {
        resolve {
            target.Spellcasting.dc -= 1
        }
    }
}
"#;
    expect_no_errors(source);
}

// ═══════════════════════════════════════════════════════════════
// Optional groups: grant/revoke type checking
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_grant_in_action_ok() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Spellcasting {
            dc: int
        }
    }
    action GainMagic on actor: Character () {
        resolve {
            grant actor.Spellcasting { dc: 15 }
        }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_revoke_in_action_ok() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Spellcasting {
            dc: int
        }
    }
    action LoseMagic on actor: Character () {
        resolve {
            revoke actor.Spellcasting
        }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_grant_required_group_rejected() {
    let source = r#"
system "test" {
    group CombatStats {
        ac: int = 10
    }
    entity Monster {
        HP: int
        include CombatStats
    }
    action Touch on actor: Monster () {
        resolve {
            grant actor.CombatStats { ac: 12 }
        }
    }
}
"#;
    expect_errors(
        source,
        &["group `CombatStats` is required on this entity and cannot be granted"],
    );
}

#[test]
fn test_revoke_required_group_rejected() {
    let source = r#"
system "test" {
    group CombatStats {
        ac: int = 10
    }
    entity Monster {
        HP: int
        include CombatStats
    }
    action Touch on actor: Monster () {
        resolve {
            revoke actor.CombatStats
        }
    }
}
"#;
    expect_errors(
        source,
        &["group `CombatStats` is required on this entity and cannot be revoked"],
    );
}

#[test]
fn test_grant_required_group_on_any_entity_rejected() {
    let source = r#"
system "test" {
    group CombatStats {
        ac: int = 10
    }
    entity Monster {
        HP: int
        include CombatStats
    }
    action Touch on actor: entity () {
        resolve {
            grant actor.CombatStats { ac: 12 }
        }
    }
}
"#;
    expect_errors(
        source,
        &["group `CombatStats` is required on some entity types and cannot be granted on type `entity`; use a concrete entity type"],
    );
}

#[test]
fn test_grant_in_derive_rejected() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Spellcasting {
            dc: int
        }
    }
    derive bad(actor: Character) -> int {
        grant actor.Spellcasting { dc: 15 }
        0
    }
}
"#;
    expect_errors(
        source,
        &["grant is only allowed in action, reaction, or hook context"],
    );
}

#[test]
fn test_revoke_in_derive_rejected() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Spellcasting {
            dc: int
        }
    }
    derive bad(actor: Character) -> int {
        revoke actor.Spellcasting
        0
    }
}
"#;
    expect_errors(
        source,
        &["revoke is only allowed in action, reaction, or hook context"],
    );
}

#[test]
fn test_grant_unknown_group_rejected() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
    }
    action Bad on actor: Character () {
        resolve {
            grant actor.Nonexistent { x: 1 }
        }
    }
}
"#;
    expect_errors(
        source,
        &["entity `Character` has no optional group `Nonexistent`"],
    );
}

#[test]
fn test_grant_field_type_mismatch() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Spellcasting {
            dc: int
        }
    }
    action GainMagic on actor: Character () {
        resolve {
            grant actor.Spellcasting { dc: "not a number" }
        }
    }
}
"#;
    expect_errors(source, &["field `dc` has type string, expected int"]);
}

#[test]
fn test_grant_missing_required_field() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Spellcasting {
            dc: int
            ability: string
        }
    }
    action GainMagic on actor: Character () {
        resolve {
            grant actor.Spellcasting { dc: 15 }
        }
    }
}
"#;
    expect_errors(
        source,
        &["missing required field `ability` in grant of `Spellcasting`"],
    );
}

#[test]
fn test_grant_unknown_field_rejected() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Spellcasting {
            dc: int
        }
    }
    action GainMagic on actor: Character () {
        resolve {
            grant actor.Spellcasting { dc: 15, nonexistent: 1 }
        }
    }
}
"#;
    expect_errors(
        source,
        &["optional group `Spellcasting` has no field `nonexistent`"],
    );
}

#[test]
fn test_grant_with_default_field_ok() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Rage {
            damage: int = 2
            uses: int
        }
    }
    action Enrage on actor: Character () {
        resolve {
            grant actor.Rage { uses: 3 }
        }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_grant_on_non_entity_rejected() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    action Bad on actor: Character () {
        resolve {
            let x = 5
            grant x.Something { a: 1 }
        }
    }
}
"#;
    expect_errors(source, &["grant requires an entity, found int"]);
}

#[test]
fn test_revoke_on_non_entity_rejected() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    action Bad on actor: Character () {
        resolve {
            let x = 5
            revoke x.Something
        }
    }
}
"#;
    expect_errors(source, &["revoke requires an entity, found int"]);
}

// ═══════════════════════════════════════════════════════════════
// Optional groups: lvalue narrowing
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_lvalue_group_access_with_constraint() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Spellcasting {
            dc: int
        }
    }
    action BoostDC on caster: Character with Spellcasting () {
        resolve {
            caster.Spellcasting.dc += 1
        }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_lvalue_group_access_unguarded_rejected() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Spellcasting {
            dc: int
        }
    }
    action Bad on caster: Character () {
        resolve {
            caster.Spellcasting.dc += 1
        }
    }
}
"#;
    expect_errors(source, &["access to optional group `Spellcasting` on `caster` requires a `has` guard or `with` constraint"]);
}

// ═══════════════════════════════════════════════════════════════
// Optional groups: condition with_groups on receiver
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_condition_with_groups_on_receiver() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Spellcasting {
            dc: int
        }
    }
    derive spell_dc(actor: Character with Spellcasting) -> int {
        actor.Spellcasting.dc
    }
    condition Silenced on bearer: Character with Spellcasting {
        modify spell_dc(actor: bearer) {
            result = 0
        }
    }
}
"#;
    expect_no_errors(source);
}

// ═══════════════════════════════════════════════════════════════
// Bug fix: `has` narrowing keyed by full path (ttrpg_dsl-x0y)
// Previously extract_root_var collapsed `actor.friend` to `actor`,
// so narrowing on one path leaked to another. Now extract_path_key
// returns the full dot-separated path.
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_has_narrowing_different_paths_no_leak() {
    // Narrowing `actor.friend has Spellcasting` should NOT allow access via
    // `actor.target.Spellcasting` — these are different paths.
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Spellcasting {
            spell_slots: int = 3
            dc: int
        }
    }
    entity Monster {
        HP: int
        friend: Character
        target: Character
    }
    derive bad(actor: Monster) -> int {
        if actor.friend has Spellcasting {
            actor.target.Spellcasting.dc
        } else {
            0
        }
    }
}
"#;
    expect_errors(
        source,
        &["access to optional group `Spellcasting` on `actor.target` requires a `has` guard or `with` constraint"],
    );
}

#[test]
fn test_has_narrowing_full_path_works() {
    // Narrowing `actor.friend has Spellcasting` should allow access via
    // `actor.friend.Spellcasting` — same full path.
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Spellcasting {
            spell_slots: int = 3
            dc: int
        }
    }
    entity Monster {
        HP: int
        friend: Character
        target: Character
    }
    derive good(actor: Monster) -> int {
        if actor.friend has Spellcasting {
            actor.friend.Spellcasting.dc
        } else {
            0
        }
    }
}
"#;
    expect_no_errors(source);
}

// ═══════════════════════════════════════════════════════════════
// Bug fix: `with` constraints enforced at call sites (ttrpg_dsl-gwr)
// Previously `with` on action receivers was only used for body
// narrowing, not checked at call sites.
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_with_constraint_enforced_at_call_site() {
    // Calling an action `with Spellcasting` on a receiver that has not
    // been proven to have the group should produce an error.
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Spellcasting {
            spell_slots: int = 3
            dc: int
        }
    }
    action CastSpell on caster: Character with Spellcasting () {
        resolve {
            caster.Spellcasting.spell_slots -= 1
        }
    }
    action Orchestrate on actor: Character (target: Character) {
        resolve {
            CastSpell(target)
        }
    }
}
"#;
    expect_errors(
        source,
        &["requires `target` to have group `Spellcasting` proven active"],
    );
}

#[test]
fn test_with_constraint_satisfied_at_call_site() {
    // Calling an action `with Spellcasting` after a `has` guard should pass.
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Spellcasting {
            spell_slots: int = 3
            dc: int
        }
    }
    action CastSpell on caster: Character with Spellcasting () {
        resolve {
            caster.Spellcasting.spell_slots -= 1
        }
    }
    action Orchestrate on actor: Character (target: Character) {
        resolve {
            if target has Spellcasting {
                CastSpell(target)
            }
        }
    }
}
"#;
    expect_no_errors(source);
}

// ── Hook declaration checker tests ──────────────────────────────

#[test]
fn test_hook_basic_valid() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    event damage(actor: Character, target: Character) {}
    hook OnDamage on target: Character (trigger: damage(target: target)) {
        target.HP -= 1
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_hook_undefined_event() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    hook OnFoo on actor: Character (trigger: nonexistent_event(actor: actor)) {
        0
    }
}
"#;
    expect_errors(source, &["undefined event `nonexistent_event`"]);
}

#[test]
fn test_hook_receiver_shadows_trigger() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    event damage(actor: Character) {}
    hook OnDamage on trigger: Character (trigger: damage(trigger)) {
        0
    }
}
"#;
    expect_errors(
        source,
        &["receiver `trigger` shadows the implicit trigger binding"],
    );
}

#[test]
fn test_hook_receiver_shadows_turn() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    event damage(actor: Character) {}
    hook OnDamage on turn: Character (trigger: damage(turn)) {
        0
    }
}
"#;
    expect_errors(
        source,
        &["receiver `turn` shadows the implicit turn budget binding"],
    );
}

#[test]
fn test_hook_struct_receiver_rejected() {
    let source = r#"
system "test" {
    struct Stats { hp: int }
    entity Character { HP: int }
    event damage(actor: Character) {}
    hook OnDamage on actor: Stats (trigger: damage(actor)) {
        0
    }
}
"#;
    expect_errors(
        source,
        &["hook `OnDamage` receiver type must be an entity, found Stats"],
    );
}

#[test]
fn test_hook_direct_call_rejected() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    event damage(actor: Character) {}
    hook OnDamage on actor: Character (trigger: damage(actor: actor)) {
        0
    }
    derive test_call(c: Character) -> int {
        OnDamage(c)
    }
}
"#;
    expect_errors(source, &["hooks cannot be called directly"]);
}

#[test]
fn test_hook_trigger_binding_type_mismatch() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    event damage(actor: Character, amount: int) {}
    hook OnDamage on target: Character (trigger: damage(amount: target)) {
        0
    }
}
"#;
    expect_errors(
        source,
        &["trigger binding `amount` has type Character, expected int"],
    );
}

#[test]
fn test_hook_trigger_available_in_resolve() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    event damage(actor: Character, target: Character) {}
    hook OnDamage on reactor: Character (trigger: damage(target: reactor)) {
        trigger.actor.HP -= 1
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_hook_with_group_constraint() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Spellcasting { dc: int }
    }
    event spell_cast(caster: Character) {}
    hook TrackCasting on caster: Character with Spellcasting (
        trigger: spell_cast(caster: caster)
    ) {
        caster.Spellcasting.dc
    }
}
"#;
    expect_no_errors(source);
}

// ── resource-valued maps ──────────────────────────────────────────────

#[test]
fn test_resource_map_declaration() {
    let source = r#"
system "test" {
    entity Character {
        max_slots: int = 4
        spell_slots: map<int, resource(0..=max_slots)>
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_resource_map_read_is_int_like() {
    let source = r#"
system "test" {
    entity Character {
        spell_slots: map<int, resource(0..=9)>
    }
    derive check(actor: Character) -> int {
        let x: int = actor.spell_slots[1]
        x + actor.spell_slots[2]
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_resource_map_mutation() {
    let source = r#"
system "test" {
    entity Character {
        spell_slots: map<int, resource(0..=9)>
    }
    action CastSpell on caster: Character (level: int) {
        cost { action }
        resolve {
            caster.spell_slots[level] -= 1
        }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_resource_map_in_optional_group() {
    let source = r#"
system "test" {
    entity Character {
        optional Spellcasting {
            spell_slots: map<int, resource(0..=9)>
        }
    }
    action CastSpell on caster: Character with Spellcasting (level: int) {
        cost { action }
        resolve {
            caster.Spellcasting.spell_slots[level] -= 1
        }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_resource_map_wrong_key_type() {
    let source = r#"
system "test" {
    entity Character {
        spell_slots: map<int, resource(0..=9)>
    }
    action Bad on actor: Character () {
        cost { action }
        resolve {
            actor.spell_slots["abc"] -= 1
        }
    }
}
"#;
    expect_errors(source, &["map key type is int, found string"]);
}

#[test]
fn test_resource_map_assign_string_to_entry() {
    let source = r#"
system "test" {
    entity Character {
        spell_slots: map<int, resource(0..=9)>
    }
    action Bad on actor: Character () {
        cost { action }
        resolve {
            actor.spell_slots[1] = "hello"
        }
    }
}
"#;
    expect_errors(source, &["cannot assign string to resource"]);
}

#[test]
fn test_resource_map_pluseq_with_string() {
    let source = r#"
system "test" {
    entity Character {
        spell_slots: map<int, resource(0..=9)>
    }
    action Bad on actor: Character () {
        cost { action }
        resolve {
            actor.spell_slots[1] += "x"
        }
    }
}
"#;
    expect_errors(source, &["right side of += / -= must be numeric"]);
}

#[test]
fn test_resource_map_pluseq_with_float() {
    let source = r#"
system "test" {
    entity Character {
        spell_slots: map<int, resource(0..=9)>
    }
    action Bad on actor: Character () {
        cost { action }
        resolve {
            actor.spell_slots[1] += 3 / 2
        }
    }
}
"#;
    expect_errors(source, &["cannot use float in += / -= on resource"]);
}

#[test]
fn test_resource_map_enum_key_type() {
    let source = r#"
system "test" {
    enum Ability { STR, DEX, CON, INT, WIS, CHA }
    entity Character {
        abilities: map<Ability, resource(1..=20)>
    }
    action Buff on actor: Character (stat: Ability) {
        cost { action }
        resolve {
            actor.abilities[stat] += 1
        }
    }
    derive check_stat(actor: Character, stat: Ability) -> int {
        actor.abilities[stat] + 0
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_resource_map_entry_in_arithmetic() {
    let source = r#"
system "test" {
    entity Character {
        spell_slots: map<int, resource(0..=9)>
    }
    derive total_low_slots(c: Character) -> int {
        c.spell_slots[1] + c.spell_slots[2] + c.spell_slots[3]
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_resource_map_entry_in_comparison() {
    let source = r#"
system "test" {
    entity Character {
        spell_slots: map<int, resource(0..=9)>
    }
    derive has_slots(c: Character, level: int) -> bool {
        c.spell_slots[level] > 0
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_resource_map_nonzero_min_declaration() {
    let source = r#"
system "test" {
    entity Character {
        abilities: map<int, resource(1..=20)>
    }
    derive modifier(c: Character, stat: int) -> float {
        (c.abilities[stat] - 10) / 2
    }
}
"#;
    expect_no_errors(source);
}

// ═══════════════════════════════════════════════════════════════
// Parameterized conditions
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_parameterized_condition_basic() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
    }
    derive skill_check(actor: Character) -> string { "normal" }
    condition Frightened(source: Character) on bearer: Character {
        modify skill_check(actor: bearer) {
            result = "disadvantage"
        }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_parameterized_condition_params_in_scope() {
    // Condition params should be accessible in modify clause bodies
    let source = r#"
system "test" {
    entity Character {
        HP: int
    }
    derive speed(actor: Character) -> int { 30 }
    condition Frightened(source: Character) on bearer: Character {
        modify speed(actor: bearer) {
            let src: Character = source
            result = 0
        }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_parameterized_condition_call_type_checks() {
    // Calling a parameterized condition with wrong type should error
    let source = r#"
system "test" {
    entity Character {
        HP: int
    }
    condition Frightened(source: Character) on bearer: Character {}
    mechanic scare(actor: Character) -> Condition {
        Frightened(42)
    }
}
"#;
    expect_errors(source, &["parameter `source` has type Character, got int"]);
}

#[test]
fn test_parameterized_condition_bare_use_errors() {
    // Using a parameterized condition bare should error
    let source = r#"
system "test" {
    entity Character {
        HP: int
    }
    condition Frightened(source: Character) on bearer: Character {}
    mechanic scare(actor: Character) -> Condition {
        Frightened
    }
}
"#;
    expect_errors(source, &["requires 1 parameter"]);
}

#[test]
fn test_parameterized_condition_too_many_args() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
    }
    condition Frightened(source: Character) on bearer: Character {}
    mechanic scare(actor: Character) -> Condition {
        Frightened(actor, actor)
    }
}
"#;
    expect_errors(source, &["accepts at most 1 argument"]);
}

#[test]
fn test_parameterized_condition_named_arg_wrong_name() {
    // Named arg with wrong name should produce a clear error
    let source = r#"
system "test" {
    entity Character {
        HP: int
    }
    condition Frightened(source: Character) on bearer: Character {}
    mechanic scare(actor: Character) -> Condition {
        Frightened(src: actor)
    }
}
"#;
    expect_errors(source, &["has no parameter `src`"]);
}

#[test]
fn test_parameterized_condition_named_arg_valid() {
    // Named arg with correct name should pass
    let source = r#"
system "test" {
    entity Character {
        HP: int
    }
    condition Frightened(source: Character) on bearer: Character {}
    mechanic scare(actor: Character) -> Condition {
        Frightened(source: actor)
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_parameterized_condition_duplicate_named_arg() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
    }
    condition Frightened(source: Character) on bearer: Character {}
    mechanic scare(actor: Character) -> Condition {
        Frightened(source: actor, source: actor)
    }
}
"#;
    expect_errors(source, &["duplicate argument for parameter `source`"]);
}

#[test]
fn test_parameterized_condition_with_default() {
    // Condition with default param should allow bare use and call use
    let source = r#"
system "test" {
    entity Character {
        HP: int
    }
    derive speed(actor: Character) -> int { 30 }
    condition Weakened(level: int = 1) on bearer: Character {
        modify speed(actor: bearer) {
            result = result - level
        }
    }
    mechanic weaken(actor: Character) -> Condition {
        Weakened
    }
    mechanic weaken_hard(actor: Character) -> Condition {
        Weakened(3)
    }
    mechanic weaken_named(actor: Character) -> Condition {
        Weakened(level: 2)
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_parameterized_condition_missing_required_arg() {
    // Calling with too few args should report the missing required param by name
    let source = r#"
system "test" {
    entity Character {
        HP: int
    }
    condition Frightened(source: Character) on bearer: Character {}
    mechanic scare() -> Condition {
        Frightened()
    }
}
"#;
    expect_errors(source, &["missing required argument `source`"]);
}

// ── P2: Duplicate condition parameter names ──────────────────────────────

#[test]
fn test_parameterized_condition_duplicate_param_names() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Cursed(level: int, level: int) on bearer: Character {}
}
"#;
    expect_errors(
        source,
        &["duplicate parameter `level` in condition `Cursed`"],
    );
}

// ── P2: Condition parameter default type mismatch ────────────────────────

#[test]
fn test_parameterized_condition_default_type_mismatch() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Weakened(level: int = "oops") on bearer: Character {}
}
"#;
    expect_errors(source, &["default has type string, expected int"]);
}

#[test]
fn test_parameterized_condition_default_type_valid() {
    let source = r#"
system "test" {
    entity Character { HP: int }
    condition Weakened(level: int = 1) on bearer: Character {}
}
"#;
    expect_no_errors(source);
}

// ── P2: With-group enforcement on condition call args ────────────────────

#[test]
fn test_parameterized_condition_with_group_not_proven() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Spellcasting { dc: int }
    }
    condition Hexed(source: Character with Spellcasting) on bearer: Character {}
    mechanic hex(actor: Character) -> Condition {
        Hexed(source: actor)
    }
}
"#;
    expect_errors(
        source,
        &["requires `actor` to have group `Spellcasting` proven active"],
    );
}

#[test]
fn test_parameterized_condition_with_group_proven() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Spellcasting { dc: int }
    }
    condition Hexed(source: Character with Spellcasting) on bearer: Character {}
    mechanic hex(actor: Character with Spellcasting) -> Condition {
        Hexed(source: actor)
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_parameterized_condition_with_group_positional() {
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Spellcasting { dc: int }
    }
    condition Hexed(source: Character with Spellcasting) on bearer: Character {}
    mechanic hex(actor: Character) -> Condition {
        Hexed(actor)
    }
}
"#;
    expect_errors(
        source,
        &["requires `actor` to have group `Spellcasting` proven active"],
    );
}

// ── Ordered enums ────────────────────────────────────────────────

#[test]
fn test_ordered_enum_comparison_accepted() {
    let source = r#"
system "test" {
    enum Size ordered { small, medium, large }
    entity Character { size: Size }
    derive bigger(a: Character, b: Character) -> bool {
        a.size > b.size
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_plain_enum_comparison_rejected() {
    let source = r#"
system "test" {
    enum Color { red, green, blue }
    entity Character { color: Color }
    derive brighter(a: Character, b: Character) -> bool {
        a.color > b.color
    }
}
"#;
    expect_errors(source, &["cannot order"]);
}

#[test]
fn test_plain_enum_equality_still_works() {
    let source = r#"
system "test" {
    enum Color { red, green, blue }
    entity Character { color: Color }
    derive same_color(a: Character, b: Character) -> bool {
        a.color == b.color
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_ordinal_type_checked() {
    let source = r#"
system "test" {
    enum Size ordered { small, medium, large }
    derive size_index(s: Size) -> int {
        ordinal(s)
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_ordinal_rejects_non_ordered() {
    let source = r#"
system "test" {
    enum Color { red, green, blue }
    derive color_index(c: Color) -> int {
        ordinal(c)
    }
}
"#;
    expect_errors(source, &["not ordered"]);
}

#[test]
fn test_ordinal_rejects_non_enum() {
    let source = r#"
system "test" {
    derive bad(x: int) -> int {
        ordinal(x)
    }
}
"#;
    expect_errors(source, &["expects an enum value"]);
}

#[test]
fn test_ordinal_arity_error() {
    let source = r#"
system "test" {
    enum Size ordered { small, medium, large }
    derive bad(a: Size, b: Size) -> int {
        ordinal(a, b)
    }
}
"#;
    expect_errors(source, &["expects 1 argument"]);
}

#[test]
fn test_from_ordinal_type_checked() {
    let source = r#"
system "test" {
    enum Size ordered { small, medium, large }
    derive size_at(i: int) -> Size {
        from_ordinal(Size, i)
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_from_ordinal_rejects_non_ordered() {
    let source = r#"
system "test" {
    enum Color { red, green, blue }
    derive bad(i: int) -> Color {
        from_ordinal(Color, i)
    }
}
"#;
    expect_errors(source, &["not ordered"]);
}

#[test]
fn test_from_ordinal_rejects_wrong_types() {
    let source = r#"
system "test" {
    enum Size ordered { small, medium, large }
    derive bad(s: Size) -> Size {
        from_ordinal(s, 0)
    }
}
"#;
    expect_errors(source, &["must be an enum type"]);
}

#[test]
fn test_from_ordinal_arity_error() {
    let source = r#"
system "test" {
    enum Size ordered { small, medium, large }
    derive bad() -> Size {
        from_ordinal(Size)
    }
}
"#;
    expect_errors(source, &["expects 2 arguments"]);
}

#[test]
fn test_try_from_ordinal_returns_option() {
    let source = r#"
system "test" {
    enum Size ordered { small, medium, large }
    derive maybe_size(i: int) -> option<Size> {
        try_from_ordinal(Size, i)
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_try_from_ordinal_rejects_non_ordered() {
    let source = r#"
system "test" {
    enum Color { red, green, blue }
    derive bad(i: int) -> option<Color> {
        try_from_ordinal(Color, i)
    }
}
"#;
    expect_errors(source, &["not ordered"]);
}

#[test]
fn test_try_from_ordinal_arity_error() {
    let source = r#"
system "test" {
    enum Size ordered { small, medium, large }
    derive bad() -> option<Size> {
        try_from_ordinal(Size)
    }
}
"#;
    expect_errors(source, &["expects 2 arguments"]);
}

// ── Module visibility tests ────────────────────────────────────────────

/// Parse multiple source files and run the module-aware checker.
fn check_multi_source(sources: &[(&str, &str)]) -> CheckResult {
    let owned: Vec<(String, String)> = sources
        .iter()
        .map(|(name, src)| (name.to_string(), src.to_string()))
        .collect();
    let result = ttrpg_parser::parse_multi(&owned);
    assert!(
        !result.has_errors,
        "parse errors:\n{}",
        result
            .diagnostics
            .iter()
            .map(|d| format!("{:?}", d))
            .collect::<Vec<_>>()
            .join("\n")
    );
    check_with_modules(&result.program, &result.module_map)
}

/// Helper: check that multi-source produces no errors.
fn expect_multi_no_errors(sources: &[(&str, &str)]) {
    let result = check_multi_source(sources);
    let errors: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.severity == ttrpg_ast::diagnostic::Severity::Error)
        .collect();
    if !errors.is_empty() {
        let rendered: Vec<_> = errors
            .iter()
            .map(|d| format!("{:?}: {}", d.span, d.message))
            .collect();
        panic!(
            "expected no errors, found {}:\n{}",
            errors.len(),
            rendered.join("\n")
        );
    }
}

/// Helper: check that multi-source produces errors containing the given fragments.
fn expect_multi_errors(sources: &[(&str, &str)], expected_fragments: &[&str]) {
    let result = check_multi_source(sources);
    let errors: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.severity == ttrpg_ast::diagnostic::Severity::Error)
        .collect();

    for frag in expected_fragments {
        let found = errors.iter().any(|e| e.message.contains(frag));
        if !found {
            let rendered: Vec<_> = errors
                .iter()
                .map(|d| format!("{:?}: {}", d.span, d.message))
                .collect();
            panic!(
                "expected error containing {:?}, but not found in:\n{}",
                frag,
                rendered.join("\n")
            );
        }
    }
}

#[test]
fn test_visibility_own_system_visible() {
    // A derive defined in Core is visible from within Core
    expect_multi_no_errors(&[(
        "core.ttrpg",
        r#"
system "Core" {
    entity Character { HP: int = 10 }
    derive max_hp(c: Character) -> int { c.HP }
    derive double_hp(c: Character) -> int { max_hp(c) * 2 }
}
"#,
    )]);
}

#[test]
fn test_visibility_imported_system_visible() {
    // Core defines a derive; Main imports Core and calls it
    expect_multi_no_errors(&[
        (
            "core.ttrpg",
            r#"
system "Core" {
    entity Character { HP: int = 10 }
    derive max_hp(c: Character) -> int { c.HP }
}
"#,
        ),
        (
            "main.ttrpg",
            r#"
use "Core"
system "Main" {
    derive double_hp(c: Character) -> int { max_hp(c) * 2 }
}
"#,
        ),
    ]);
}

#[test]
fn test_visibility_missing_import_function() {
    // Core defines a derive; Main does NOT import Core — should error
    expect_multi_errors(
        &[
            (
                "core.ttrpg",
                r#"
system "Core" {
    entity Character { HP: int = 10 }
    derive helper(c: Character) -> int { c.HP }
}
"#,
            ),
            (
                "main.ttrpg",
                r#"
system "Main" {
    derive caller(c: Character) -> int { helper(c) }
}
"#,
            ),
        ],
        &[r#"`helper` is defined in system "Core""#],
    );
}

#[test]
fn test_visibility_builtins_always_visible() {
    // Builtins like floor() work without any imports
    expect_multi_no_errors(&[(
        "main.ttrpg",
        r#"
system "Main" {
    derive rounded(x: float) -> int { floor(x) }
}
"#,
    )]);
}

#[test]
fn test_visibility_single_file_no_op() {
    // Single-file check() never produces visibility errors
    expect_no_errors(
        r#"
system "Core" {
    entity Character { HP: int = 10 }
    derive helper(c: Character) -> int { c.HP }
}
system "Main" {
    derive caller(c: Character) -> int { helper(c) }
}
"#,
    );
}

#[test]
fn test_visibility_variant_missing_import() {
    // Bare variant from non-imported system → error
    expect_multi_errors(
        &[
            (
                "core.ttrpg",
                r#"
system "Core" {
    enum DamageType { fire, cold, lightning }
}
"#,
            ),
            (
                "main.ttrpg",
                r#"
system "Main" {
    derive get_type() -> DamageType { fire }
}
"#,
            ),
        ],
        &[r#"`fire` is defined in system "Core""#],
    );
}

#[test]
fn test_visibility_condition_missing_import() {
    // Condition from non-imported system → error
    expect_multi_errors(
        &[
            (
                "core.ttrpg",
                r#"
system "Core" {
    entity Character { HP: int = 10 }
    condition Frightened on bearer: Character { }
}
"#,
            ),
            (
                "main.ttrpg",
                r#"
system "Main" {
    derive is_scared() -> Condition { Frightened }
}
"#,
            ),
        ],
        &[r#"`Frightened` is defined in system "Core""#],
    );
}

#[test]
fn test_visibility_type_in_struct_lit_missing_import() {
    // Struct literal construction from non-imported system → error
    expect_multi_errors(
        &[
            (
                "core.ttrpg",
                r#"
system "Core" {
    struct Stats {
        strength: int
        dexterity: int
    }
}
"#,
            ),
            (
                "main.ttrpg",
                r#"
system "Main" {
    derive make_stats() -> Stats { Stats { strength: 10, dexterity: 12 } }
}
"#,
            ),
        ],
        &[r#"`Stats` is defined in system "Core""#],
    );
}

#[test]
fn test_visibility_event_in_trigger_missing_import() {
    // Hook in "Events" system references event from "Core" without importing → error
    expect_multi_errors(
        &[
            (
                "core.ttrpg",
                r#"
system "Core" {
    entity Character { HP: int = 10 }
    event damage(target: Character) { amount: int }
}
"#,
            ),
            (
                "events.ttrpg",
                r#"
system "Events" {
    hook on_damage on self: Character (trigger: damage(target: self)) {
        resolve {}
    }
}
"#,
            ),
        ],
        &[r#"`damage` is defined in system "Core""#],
    );
}

#[test]
fn test_visibility_variant_in_pattern_missing_import() {
    // Variant used in pattern from non-imported system → error
    expect_multi_errors(
        &[
            (
                "core.ttrpg",
                r#"
system "Core" {
    enum Color { red, green, blue }
}
"#,
            ),
            (
                "main.ttrpg",
                r#"
system "Main" {
    derive is_red(c: Color) -> bool {
        match c {
            red => true
            _ => false
        }
    }
}
"#,
            ),
        ],
        &[r#"`red` is defined in system "Core""#],
    );
}

#[test]
fn test_visibility_modify_target_missing_import() {
    // Modify clause targeting a derive from non-imported system → error
    expect_multi_errors(
        &[
            (
                "core.ttrpg",
                r#"
system "Core" {
    entity Character { HP: int = 10 }
    derive max_hp(c: Character) -> int { c.HP }
}
"#,
            ),
            (
                "main.ttrpg",
                r#"
system "Main" {
    condition Strong on bearer: Character {
        modify max_hp(c: bearer) {
            result = result + 5
        }
    }
}
"#,
            ),
        ],
        &[r#"`max_hp` is defined in system "Core""#],
    );
}

// ── Alias-qualified expression tests ───────────────────────────────────

#[test]
fn test_alias_qualified_enum_type() {
    // Core.Ability → EnumType
    expect_multi_no_errors(&[
        (
            "core.ttrpg",
            r#"
system "Core" {
    enum Ability { STR, DEX, CON }
}
"#,
        ),
        (
            "main.ttrpg",
            r#"
use "Core" as Core
system "Main" {
    derive get_ability() -> Ability { Core.Ability.STR }
}
"#,
        ),
    ]);
}

#[test]
fn test_alias_qualified_enum_variant() {
    // Core.Ability.STR → enum variant through alias
    expect_multi_no_errors(&[
        (
            "core.ttrpg",
            r#"
system "Core" {
    enum DamageType { fire, cold, lightning }
}
"#,
        ),
        (
            "main.ttrpg",
            r#"
use "Core" as Core
system "Main" {
    derive get_dmg() -> DamageType { Core.DamageType.fire }
}
"#,
        ),
    ]);
}

#[test]
fn test_alias_qualified_bare_variant() {
    // Core.fire → bare variant through alias
    expect_multi_no_errors(&[
        (
            "core.ttrpg",
            r#"
system "Core" {
    enum DamageType { fire, cold, lightning }
}
"#,
        ),
        (
            "main.ttrpg",
            r#"
use "Core" as Core
system "Main" {
    derive get_dmg() -> DamageType { Core.fire }
}
"#,
        ),
    ]);
}

#[test]
fn test_alias_qualified_function_call() {
    // Core.modifier(10) → function call through alias
    expect_multi_no_errors(&[
        (
            "core.ttrpg",
            r#"
system "Core" {
    derive modifier(score: int) -> float { (score - 10) / 2 }
}
"#,
        ),
        (
            "main.ttrpg",
            r#"
use "Core" as Core
system "Main" {
    derive double_mod(score: int) -> float { Core.modifier(score) * 2 }
}
"#,
        ),
    ]);
}

#[test]
fn test_alias_qualified_condition_ref() {
    // Core.Prone → condition reference through alias
    expect_multi_no_errors(&[
        (
            "core.ttrpg",
            r#"
system "Core" {
    entity Character { HP: int = 10 }
    condition Prone on bearer: Character { }
}
"#,
        ),
        (
            "main.ttrpg",
            r#"
use "Core" as Core
system "Main" {
    derive get_cond() -> Condition { Core.Prone }
}
"#,
        ),
    ]);
}

#[test]
fn test_alias_qualified_condition_call() {
    // Core.Frightened(source: attacker) → parameterized condition through alias
    expect_multi_no_errors(&[
        (
            "core.ttrpg",
            r#"
system "Core" {
    entity Character { HP: int = 10 }
    condition Frightened(source: Character) on bearer: Character { }
}
"#,
        ),
        (
            "main.ttrpg",
            r#"
use "Core" as Core
system "Main" {
    derive get_scared(attacker: Character) -> Condition {
        Core.Frightened(source: attacker)
    }
}
"#,
        ),
    ]);
}

#[test]
fn test_alias_qualified_nonexistent_name() {
    // Core.nonexistent → error
    expect_multi_errors(
        &[
            (
                "core.ttrpg",
                r#"
system "Core" {
    enum Ability { STR, DEX }
}
"#,
            ),
            (
                "main.ttrpg",
                r#"
use "Core" as Core
system "Main" {
    derive bad() -> int { Core.nonexistent }
}
"#,
            ),
        ],
        &["no type, variant, or condition `nonexistent`"],
    );
}

#[test]
fn test_alias_qualified_nonexistent_call() {
    // Core.nonexistent(1) → error
    expect_multi_errors(
        &[
            (
                "core.ttrpg",
                r#"
system "Core" {
    enum Ability { STR, DEX }
}
"#,
            ),
            (
                "main.ttrpg",
                r#"
use "Core" as Core
system "Main" {
    derive bad() -> int { Core.nonexistent(1) }
}
"#,
            ),
        ],
        &["no function, condition, or variant `nonexistent`"],
    );
}

#[test]
fn test_alias_qualified_struct_not_value() {
    // Core.Stats → error (structs cannot be used as values)
    expect_multi_errors(
        &[
            (
                "core.ttrpg",
                r#"
system "Core" {
    struct Stats { strength: int }
}
"#,
            ),
            (
                "main.ttrpg",
                r#"
use "Core" as Core
system "Main" {
    derive bad() -> int { Core.Stats }
}
"#,
            ),
        ],
        &["cannot be used as a value"],
    );
}

#[test]
fn test_alias_qualified_function_type_error() {
    // Core.modifier("string") → type error
    expect_multi_errors(
        &[
            (
                "core.ttrpg",
                r#"
system "Core" {
    derive modifier(score: int) -> int { (score - 10) / 2 }
}
"#,
            ),
            (
                "main.ttrpg",
                r#"
use "Core" as Core
system "Main" {
    derive bad() -> float { Core.modifier("hello") }
}
"#,
            ),
        ],
        &["has type string, expected int"],
    );
}

// ── Alias-qualified with-group enforcement ─────────────────────────────

#[test]
fn test_alias_qualified_condition_call_with_group_not_proven() {
    // Core.Hexed(source: actor) should error when actor lacks Spellcasting
    expect_multi_errors(
        &[
            (
                "core.ttrpg",
                r#"
system "Core" {
    entity Character {
        HP: int
        optional Spellcasting { dc: int }
    }
    condition Hexed(source: Character with Spellcasting) on bearer: Character {}
}
"#,
            ),
            (
                "main.ttrpg",
                r#"
use "Core" as Core
system "Main" {
    mechanic hex(actor: Character) -> Condition {
        Core.Hexed(source: actor)
    }
}
"#,
            ),
        ],
        &["requires `actor` to have group `Spellcasting` proven active"],
    );
}

#[test]
fn test_alias_qualified_condition_call_with_group_proven() {
    // Core.Hexed(source: actor) should pass when actor has Spellcasting
    expect_multi_no_errors(&[
        (
            "core.ttrpg",
            r#"
system "Core" {
    entity Character {
        HP: int
        optional Spellcasting { dc: int }
    }
    condition Hexed(source: Character with Spellcasting) on bearer: Character {}
}
"#,
        ),
        (
            "main.ttrpg",
            r#"
use "Core" as Core
system "Main" {
    mechanic hex(actor: Character with Spellcasting) -> Condition {
        Core.Hexed(source: actor)
    }
}
"#,
        ),
    ]);
}

#[test]
fn test_alias_qualified_function_call_with_group_not_proven() {
    // Core.needs_rage(c) should error when c lacks Rage
    expect_multi_errors(
        &[
            (
                "core.ttrpg",
                r#"
system "Core" {
    entity Character {
        HP: int
        optional Rage { damage_bonus: int }
    }
    derive needs_rage(c: Character with Rage) -> int { c.HP }
}
"#,
            ),
            (
                "main.ttrpg",
                r#"
use "Core" as Core
system "Main" {
    derive try_rage(c: Character) -> int {
        Core.needs_rage(c)
    }
}
"#,
            ),
        ],
        &["requires `c` to have group `Rage` proven active"],
    );
}

#[test]
fn test_alias_qualified_function_call_with_group_proven() {
    // Core.needs_rage(c) should pass when c has Rage
    expect_multi_no_errors(&[
        (
            "core.ttrpg",
            r#"
system "Core" {
    entity Character {
        HP: int
        optional Rage { damage_bonus: int }
    }
    derive needs_rage(c: Character with Rage) -> int { c.HP }
}
"#,
        ),
        (
            "main.ttrpg",
            r#"
use "Core" as Core
system "Main" {
    derive try_rage(c: Character with Rage) -> int {
        Core.needs_rage(c)
    }
}
"#,
        ),
    ]);
}

// ── Alias-qualified variant ambiguity (beads-rw6) ──────────────────────

#[test]
fn test_alias_bare_variant_not_in_target_system() {
    // Variant exists globally but not in the aliased system — must error (not resolve to wrong enum)
    expect_multi_errors(
        &[
            (
                "core.ttrpg",
                r#"
system "Core" {
    enum Ability { STR, DEX }
}
"#,
            ),
            (
                "combat.ttrpg",
                r#"
system "Combat" {
    enum DamageType { fire, cold }
}
"#,
            ),
            (
                "main.ttrpg",
                r#"
use "Core" as Core
use "Combat" as Combat
system "Main" {
    derive pick() -> DamageType { Core.fire }
}
"#,
            ),
        ],
        &["no type, variant, or condition `fire` in system \"Core\""],
    );
}

#[test]
fn test_alias_variant_constructor_not_in_target_system() {
    // Variant constructor exists globally but not in the aliased system
    expect_multi_errors(
        &[
            (
                "core.ttrpg",
                r#"
system "Core" {
    enum Ability { STR, DEX }
}
"#,
            ),
            (
                "combat.ttrpg",
                r#"
system "Combat" {
    enum Effect { damage(amount: int) }
}
"#,
            ),
            (
                "main.ttrpg",
                r#"
use "Core" as Core
use "Combat" as Combat
system "Main" {
    derive pick() -> Effect { Core.damage(amount: 5) }
}
"#,
            ),
        ],
        &["no function, condition, or variant `damage` in system \"Core\""],
    );
}

#[test]
fn test_alias_bare_variant_unique_in_system_ok() {
    // Variant is unique within the aliased system — should resolve fine
    expect_multi_no_errors(&[
        (
            "core.ttrpg",
            r#"
system "Core" {
    enum Color { red, blue }
    enum Alert { yellow, green }
}
"#,
        ),
        (
            "main.ttrpg",
            r#"
use "Core" as Core
system "Main" {
    derive pick() -> Color { Core.red }
}
"#,
        ),
    ]);
}

#[test]
fn test_alias_variant_constructor_in_target_system_ok() {
    // Variant constructor from correct aliased system — should resolve fine
    expect_multi_no_errors(&[
        (
            "core.ttrpg",
            r#"
system "Core" {
    enum Effect { damage(amount: int), heal(amount: int) }
}
"#,
        ),
        (
            "main.ttrpg",
            r#"
use "Core" as Core
system "Main" {
    derive pick() -> Effect { Core.damage(amount: 5) }
}
"#,
        ),
    ]);
}

// ── Type visibility in signatures ──────────────────────────────────────

#[test]
fn test_visibility_type_in_param_missing_import() {
    // Parameter type from non-imported system → error
    expect_multi_errors(
        &[
            (
                "core.ttrpg",
                r#"
system "Core" {
    entity Character { HP: int = 10 }
}
"#,
            ),
            (
                "main.ttrpg",
                r#"
system "Main" {
    derive get_hp(c: Character) -> int { 0 }
}
"#,
            ),
        ],
        &["add `use \"Core\"`"],
    );
}

#[test]
fn test_visibility_type_in_return_missing_import() {
    // Return type from non-imported system → error
    expect_multi_errors(
        &[
            (
                "core.ttrpg",
                r#"
system "Core" {
    struct Stats { hp: int }
}
"#,
            ),
            (
                "main.ttrpg",
                r#"
system "Main" {
    derive make_stats() -> Stats { Stats { hp: 10 } }
}
"#,
            ),
        ],
        &["add `use \"Core\"`"],
    );
}

#[test]
fn test_visibility_type_in_receiver_missing_import() {
    // Action receiver type from non-imported system → error
    expect_multi_errors(
        &[
            (
                "core.ttrpg",
                r#"
system "Core" {
    entity Character { HP: int = 10 }
}
"#,
            ),
            (
                "main.ttrpg",
                r#"
system "Main" {
    action attack on attacker: Character () {
        resolve { }
    }
}
"#,
            ),
        ],
        &["add `use \"Core\"`"],
    );
}

#[test]
fn test_visibility_type_in_struct_field_missing_import() {
    // Struct field type from non-imported system → error
    expect_multi_errors(
        &[
            (
                "core.ttrpg",
                r#"
system "Core" {
    enum Color { red, green, blue }
}
"#,
            ),
            (
                "main.ttrpg",
                r#"
system "Main" {
    struct Item { color: Color }
}
"#,
            ),
        ],
        &["add `use \"Core\"`"],
    );
}

#[test]
fn test_visibility_type_in_entity_field_missing_import() {
    // Entity field type from non-imported system → error
    expect_multi_errors(
        &[
            (
                "core.ttrpg",
                r#"
system "Core" {
    enum Size ordered { small, medium, large }
}
"#,
            ),
            (
                "main.ttrpg",
                r#"
system "Main" {
    entity Monster { size: Size = small }
}
"#,
            ),
        ],
        &["add `use \"Core\"`"],
    );
}

#[test]
fn test_visibility_type_in_enum_variant_field_missing_import() {
    // Enum variant field type from non-imported system → error
    expect_multi_errors(
        &[
            (
                "core.ttrpg",
                r#"
system "Core" {
    entity Character { HP: int = 10 }
}
"#,
            ),
            (
                "main.ttrpg",
                r#"
system "Main" {
    enum Effect { damage(target: Character, amount: int) }
}
"#,
            ),
        ],
        &["add `use \"Core\"`"],
    );
}

#[test]
fn test_visibility_type_in_condition_receiver_missing_import() {
    // Condition receiver type from non-imported system → error
    expect_multi_errors(
        &[
            (
                "core.ttrpg",
                r#"
system "Core" {
    entity Character { HP: int = 10 }
}
"#,
            ),
            (
                "main.ttrpg",
                r#"
system "Main" {
    condition Stunned on bearer: Character { }
}
"#,
            ),
        ],
        &["add `use \"Core\"`"],
    );
}

#[test]
fn test_visibility_type_in_event_param_missing_import() {
    // Event parameter type from non-imported system → error
    expect_multi_errors(
        &[
            (
                "core.ttrpg",
                r#"
system "Core" {
    entity Character { HP: int = 10 }
}
"#,
            ),
            (
                "main.ttrpg",
                r#"
system "Main" {
    event attack(attacker: Character, target: Character) {}
}
"#,
            ),
        ],
        &["add `use \"Core\"`"],
    );
}

#[test]
fn test_visibility_type_in_let_annotation_missing_import() {
    // Type annotation on let binding from non-imported system → error
    expect_multi_errors(
        &[
            (
                "core.ttrpg",
                r#"
system "Core" {
    struct Stats { hp: int }
}
"#,
            ),
            (
                "main.ttrpg",
                r#"
system "Main" {
    derive test() -> int {
        let s: Stats = Stats { hp: 5 }
        s.hp
    }
}
"#,
            ),
        ],
        &["add `use \"Core\"`"],
    );
}

#[test]
fn test_visibility_container_inner_type_missing_import() {
    // Named type inside a container (list<T>) from non-imported system → error
    expect_multi_errors(
        &[
            (
                "core.ttrpg",
                r#"
system "Core" {
    struct Item { name: string }
}
"#,
            ),
            (
                "main.ttrpg",
                r#"
system "Main" {
    derive count_items(items: list<Item>) -> int { 0 }
}
"#,
            ),
        ],
        &["add `use \"Core\"`"],
    );
}

#[test]
fn test_visibility_type_in_signature_with_import_ok() {
    // Same scenario as param test but WITH import → no error
    expect_multi_no_errors(&[
        (
            "core.ttrpg",
            r#"
system "Core" {
    entity Character { HP: int = 10 }
    struct Stats { hp: int }
    enum Color { red, green, blue }
}
"#,
        ),
        (
            "main.ttrpg",
            r#"
use "Core"
system "Main" {
    derive get_hp(c: Character) -> int { c.HP }
    derive make_stats() -> Stats { Stats { hp: 10 } }
    struct Palette { primary: Color }
}
"#,
        ),
    ]);
}

#[test]
fn test_visibility_own_type_in_signature_ok() {
    // Types defined in the same system are always visible
    expect_multi_no_errors(&[(
        "main.ttrpg",
        r#"
system "Main" {
    entity Character { HP: int = 10 }
    struct Stats { hp: int }
    derive get_hp(c: Character) -> Stats { Stats { hp: c.HP } }
}
"#,
    )]);
}

#[test]
fn test_visibility_builtin_types_in_signature_always_ok() {
    // Builtin type keywords (int, float, bool, string, etc.) need no imports
    expect_multi_no_errors(&[(
        "main.ttrpg",
        r#"
system "Main" {
    derive identity(x: int) -> int { x }
    derive to_string(x: float) -> string { "hello" }
}
"#,
    )]);
}

// ═══════════════════════════════════════════════════════════════
// Multi-owner enum variants
// ═══════════════════════════════════════════════════════════════

#[test]
fn shared_variant_ambiguous_bare_use_is_error() {
    // Return type hint disambiguates: `red` resolves to `Color.red` via -> Color
    expect_no_errors(
        r#"
system "test" {
    enum Color { red, blue }
    enum Alert { red, yellow }
    derive test() -> Color { red }
}
"#,
    );
}

#[test]
fn shared_variant_qualified_form_works() {
    expect_no_errors(
        r#"
system "test" {
    enum Color { red, blue }
    enum Alert { red, yellow }
    derive test() -> Color { Color.red }
}
"#,
    );
}

#[test]
fn shared_variant_unique_still_bare_accessible() {
    // `blue` belongs only to Color, `yellow` belongs only to Alert — both should work bare
    expect_no_errors(
        r#"
system "test" {
    enum Color { red, blue }
    enum Alert { red, yellow }
    derive test_blue() -> Color { blue }
    derive test_yellow() -> Alert { yellow }
}
"#,
    );
}

#[test]
fn shared_variant_pattern_scrutinee_disambiguates() {
    expect_no_errors(
        r#"
system "test" {
    enum Color { red, blue }
    enum Alert { red, yellow }
    derive test(c: Color) -> int {
        match c {
            red => 1,
            blue => 2,
        }
    }
}
"#,
    );
}

#[test]
fn shared_variant_pattern_wrong_enum_is_error() {
    expect_errors(
        r#"
system "test" {
    enum Color { red, blue }
    enum Alert { red, yellow }
    derive test(a: Alert) -> int {
        match a {
            blue => 1,
            _ => 0,
        }
    }
}
"#,
        &["variant `blue` belongs to"],
    );
}

#[test]
fn shared_variant_constructor_ambiguous_is_error() {
    // Return type hint disambiguates: `red(intensity: 5)` resolves to `Color.red` via -> Color
    expect_no_errors(
        r#"
system "test" {
    enum Color { red(intensity: int) }
    enum Alert { red(level: int) }
    derive test() -> Color { red(intensity: 5) }
}
"#,
    );
}

#[test]
fn shared_variant_constructor_qualified_works() {
    expect_no_errors(
        r#"
system "test" {
    enum Color { red(intensity: int) }
    enum Alert { red(level: int) }
    derive test() -> Color { Color.red(intensity: 5) }
}
"#,
    );
}

#[test]
fn shared_variant_bare_destructure_scrutinee_disambiguates() {
    expect_no_errors(
        r#"
system "test" {
    enum Color { red(intensity: int) }
    enum Alert { red(level: int) }
    derive test(c: Color) -> int {
        match c {
            red(i) => i,
        }
    }
}
"#,
    );
}

// ═══════════════════════════════════════════════════════════════
// Phase B: Expected-type hint disambiguation
// ═══════════════════════════════════════════════════════════════

#[test]
fn hint_function_param_disambiguates_bare_variant() {
    expect_no_errors(
        r#"
system "test" {
    enum Color { red, blue }
    enum Alert { red, yellow }
    derive paint(c: Color) -> int { 1 }
    derive test() -> int { paint(red) }
}
"#,
    );
}

#[test]
fn hint_named_param_disambiguates_bare_variant() {
    expect_no_errors(
        r#"
system "test" {
    enum Color { red, blue }
    enum Alert { red, yellow }
    derive paint(c: Color) -> int { 1 }
    derive test() -> int { paint(c: red) }
}
"#,
    );
}

#[test]
fn hint_condition_param_disambiguates_bare_variant() {
    expect_no_errors(
        r#"
system "test" {
    entity Character { HP: int }
    enum Color { red, blue }
    enum Alert { red, yellow }
    condition Painted(c: Color) on bearer: Character {
    }
    derive test() -> Condition { Painted(red) }
}
"#,
    );
}

#[test]
fn hint_enum_constructor_field_disambiguates_bare_variant() {
    expect_no_errors(
        r#"
system "test" {
    enum Color { red, blue }
    enum Alert { red, yellow }
    enum Painted { colored(c: Color) }
    derive test() -> Painted { colored(c: red) }
}
"#,
    );
}

#[test]
fn hint_struct_field_disambiguates_bare_variant() {
    expect_no_errors(
        r#"
system "test" {
    enum Color { red, blue }
    enum Alert { red, yellow }
    struct Brush { color: Color }
    derive test() -> Brush { Brush { color: red } }
}
"#,
    );
}

#[test]
fn hint_comparison_rhs_disambiguates_bare_variant() {
    expect_no_errors(
        r#"
system "test" {
    enum Color { red, blue }
    enum Alert { red, yellow }
    derive test(c: Color) -> bool { c == red }
}
"#,
    );
}

#[test]
fn hint_let_annotation_disambiguates_bare_variant() {
    expect_no_errors(
        r#"
system "test" {
    enum Color { red, blue }
    enum Alert { red, yellow }
    derive test() -> int {
        let c: Color = red
        1
    }
}
"#,
    );
}

#[test]
fn hint_assignment_disambiguates_bare_variant() {
    expect_no_errors(
        r#"
system "test" {
    entity Character { HP: int, color: Color }
    enum Color { red, blue }
    enum Alert { red, yellow }
    action paint on self: Character () {
        cost { action }
        resolve {
            self.color = red
        }
    }
}
"#,
    );
}

#[test]
fn hint_list_element_disambiguates_bare_variant() {
    expect_no_errors(
        r#"
system "test" {
    enum Color { red, blue }
    enum Alert { red, yellow }
    derive test() -> list<Color> { [blue, red] }
}
"#,
    );
}

#[test]
fn hint_no_match_still_errors() {
    // `red` is ambiguous between Color and Alert; hint is `Size` which matches neither
    expect_errors(
        r#"
system "test" {
    enum Color { red, blue }
    enum Alert { red, yellow }
    enum Size { small, large }
    derive paint(s: Size) -> int { 1 }
    derive test() -> int { paint(red) }
}
"#,
        &["ambiguous variant `red`"],
    );
}

#[test]
fn hint_existing_unique_variant_still_works() {
    // `blue` is unique to Color — no hint needed, should work as before
    expect_no_errors(
        r#"
system "test" {
    enum Color { red, blue }
    enum Alert { red, yellow }
    derive test() -> Color { blue }
}
"#,
    );
}

#[test]
fn hint_paren_passes_through() {
    expect_no_errors(
        r#"
system "test" {
    enum Color { red, blue }
    enum Alert { red, yellow }
    derive paint(c: Color) -> int { 1 }
    derive test() -> int { paint((red)) }
}
"#,
    );
}

#[test]
fn hint_table_key_disambiguates_bare_variant() {
    expect_no_errors(
        r#"
system "test" {
    enum Color { red, blue }
    enum Alert { red, yellow }
    table paint(c: Color) -> int {
        red => 1,
        blue => 2,
    }
}
"#,
    );
}

#[test]
fn hint_table_value_disambiguates_bare_variant() {
    expect_no_errors(
        r#"
system "test" {
    enum Color { red, blue }
    enum Alert { red, yellow }
    table pick(x: int) -> Color {
        1 => red,
        _ => blue,
    }
}
"#,
    );
}

// ── Default expression type hint disambiguation ──────────────────────

#[test]
fn hint_struct_field_default_disambiguates_bare_variant() {
    expect_no_errors(
        r#"
system "test" {
    enum Color { red, blue }
    enum Alert { red, yellow }
    struct Brush { color: Color = red }
}
"#,
    );
}

#[test]
fn hint_entity_field_default_disambiguates_bare_variant() {
    expect_no_errors(
        r#"
system "test" {
    enum Color { red, blue }
    enum Alert { red, yellow }
    entity Painter { color: Color = red }
}
"#,
    );
}

#[test]
fn hint_entity_optional_group_default_disambiguates_bare_variant() {
    expect_no_errors(
        r#"
system "test" {
    enum Color { red, blue }
    enum Alert { red, yellow }
    entity Painter {
        HP: int
        optional appearance {
            color: Color = red
        }
    }
}
"#,
    );
}

#[test]
fn hint_param_default_disambiguates_bare_variant() {
    expect_no_errors(
        r#"
system "test" {
    enum Color { red, blue }
    enum Alert { red, yellow }
    derive paint(c: Color = red) -> int { 1 }
}
"#,
    );
}

#[test]
fn hint_condition_param_default_disambiguates_bare_variant() {
    expect_no_errors(
        r#"
system "test" {
    entity Character { HP: int }
    enum Color { red, blue }
    enum Alert { red, yellow }
    condition Painted(c: Color = red) on bearer: Character {
    }
}
"#,
    );
}

#[test]
fn hint_event_param_default_disambiguates_bare_variant() {
    expect_no_errors(
        r#"
system "test" {
    enum Color { red, blue }
    enum Alert { red, yellow }
    event Splash(c: Color = red) {
    }
}
"#,
    );
}

#[test]
fn default_wrong_type_still_errors_with_hint() {
    expect_errors(
        r#"
system "test" {
    enum Color { red, blue }
    enum Alert { red, yellow }
    struct Brush { color: Color = yellow }
}
"#,
        &["default has type Alert, expected Color"],
    );
}

#[test]
fn qualified_variant_in_default_works() {
    expect_no_errors(
        r#"
system "test" {
    enum Color { red, blue }
    enum Alert { red, yellow }
    struct Brush { color: Color = Color.red }
}
"#,
    );
}

// ── Single-owner variant pattern vs non-enum scrutinee (tdsl-65cb) ──

#[test]
fn single_owner_variant_pattern_rejects_non_enum_scrutinee() {
    expect_errors(
        r#"
system "test" {
    enum Status { active, inactive }
    derive test(x: int) -> int {
        match x {
            active => 1,
            _ => 0,
        }
    }
}
"#,
        &["cannot match type"],
    );
}

#[test]
fn single_owner_variant_destructure_rejects_non_enum_scrutinee() {
    expect_errors(
        r#"
system "test" {
    enum Result { success(val: int), failure(code: int) }
    derive test(x: string) -> int {
        match x {
            success(v) => v,
            _ => 0,
        }
    }
}
"#,
        &["cannot match type"],
    );
}

#[test]
fn single_owner_variant_pattern_still_works_with_correct_enum() {
    expect_no_errors(
        r#"
system "test" {
    enum Status { active, inactive }
    derive test(x: Status) -> int {
        match x {
            active => 1,
            inactive => 0,
        }
    }
}
"#,
    );
}

// ═══════════════════════════════════════════════════════════════
// Bare identifier in enum match → error (tdsl-8x4q)
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_bare_ident_in_enum_match_is_error() {
    // A bare name that is not a known variant should error when matching an enum.
    let source = r#"
system "test" {
    enum Color { red, green, blue }
    derive name(c: Color) -> string {
        match c {
            red => "Red",
            gren => "Green",
            blue => "Blue"
        }
    }
}
"#;
    expect_errors(source, &["unknown identifier `gren` in match on enum `Color`"]);
}

// ═══════════════════════════════════════════════════════════════
// Bare identifier in for-loop pattern → binding (tdsl-v20v)
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_bare_ident_in_enum_for_loop_binds() {
    // Iterating over a list of enum values should allow binding each element.
    let source = r#"
system "test" {
    enum Color { red, green, blue }
    derive reds(colors: list<Color>) -> list<Color> {
        [c for c in colors if c == red]
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_bare_ident_in_non_enum_match_still_binds() {
    // Bare names in non-enum matches should still work as bindings.
    let source = r#"
system "test" {
    derive describe(x: option<int>) -> int {
        match x {
            some(n) => n,
            none => 0
        }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_bare_ident_typo_in_enum_match_suggests_wildcard() {
    // The error message should suggest using `_` for a catch-all.
    let source = r#"
system "test" {
    enum Direction { north, south, east, west }
    derive is_vertical(d: Direction) -> bool {
        match d {
            north => true,
            south => true,
            other => false
        }
    }
}
"#;
    expect_errors(source, &["use `_`"]);
}

// ═══════════════════════════════════════════════════════════════
// P1 Bug repro tests
// ═══════════════════════════════════════════════════════════════

/// Bug tdsl-ehjf: option extends validation checks env.options.contains()
/// at insert time, so a child option declared before its parent is rejected
/// with "extends unknown option" even though the parent is defined later in
/// the same system. The later validate_option_extends only checks circularity.
#[test]
fn option_extends_forward_reference_accepted() {
    // Child declared before parent — should be valid.
    expect_no_errors(
        r#"
system "test" {
    option flanking extends "base_flanking" {
        description: "Extended flanking"
        default: on
    }
    option base_flanking {
        description: "Base flanking rules"
        default: on
    }
}
"#,
    );
}

/// Bug tdsl-01n: move lowering synthesizes bare calls to `roll(...)` and to
/// the generated mechanic name. If a move parameter is named `roll`, the
/// local binding shadows the builtin, making the generated mechanic body
/// uncallable after lowering.
#[test]
fn move_with_param_named_roll_does_not_shadow_builtin() {
    let source = r#"
system "test" {
    entity Character {
        stat: int
    }
    move GoAggro on actor: Character (roll: int) {
        trigger: "When you threaten with force"
        roll: 2d6 + actor.stat
        on strong_hit {
            actor.stat += 1
        }
        on weak_hit {
            actor.stat += 0
        }
        on miss {
            actor.stat -= 1
        }
    }
}
"#;
    // Fix: lowering now rejects moves with params that conflict with
    // synthesized names ('roll', 'result').
    let (_, lower_diags) = lower_source(source);
    assert!(
        !lower_diags.is_empty(),
        "expected a lowering diagnostic about 'roll' parameter conflict"
    );
    assert!(
        lower_diags
            .iter()
            .any(|d| d.message.contains("roll") && d.message.contains("conflicts")),
        "expected diagnostic mentioning 'roll' conflict, got: {:?}",
        lower_diags.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

/// Bug tdsl-bw0: move lowering introduces a hard-coded `let result = ...`
/// binding and references it in guard arms. If a move parameter is named
/// `result`, the synthetic `let result = __mechanic(...)` shadows it, so
/// outcome bodies that try to use the `result` parameter get the roll result
/// instead, silently changing behavior or causing type errors.
#[test]
fn move_param_named_result_not_captured_by_lowering() {
    let source = r#"
system "test" {
    entity Character {
        stat: int
    }
    move GoAggro on actor: Character (result: int) {
        trigger: "When you threaten"
        roll: 2d6 + actor.stat
        on strong_hit {
            actor.stat += result
        }
        on weak_hit {
            actor.stat += 0
        }
        on miss {
            actor.stat -= result
        }
    }
}
"#;
    // Fix: lowering now rejects moves with params that conflict with
    // synthesized names ('roll', 'result').
    let (_, lower_diags) = lower_source(source);
    assert!(
        !lower_diags.is_empty(),
        "expected a lowering diagnostic about 'result' parameter conflict"
    );
    assert!(
        lower_diags
            .iter()
            .any(|d| d.message.contains("result") && d.message.contains("conflicts")),
        "expected diagnostic mentioning 'result' conflict, got: {:?}",
        lower_diags.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

// ── Regression: tdsl-7rw — narrowing leaks across shadowed bindings ──

#[test]
fn test_narrowing_does_not_leak_across_shadowed_binding() {
    // The parameter `actor` is narrowed with Spellcasting. The for-loop
    // rebinds `actor` to each Character from `targets` (no narrowing proof).
    // Accessing actor.Spellcasting inside the for-loop should be an error
    // because the inner `actor` has no proof. The bug in is_group_narrowed
    // causes it to find the outer scope's proof for the shadowed name.
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Spellcasting {
            spell_slots: int
        }
    }
    action Buff on actor: Character with Spellcasting (targets: list<Character>) {
        resolve {
            for actor in targets {
                actor.Spellcasting.spell_slots
            }
        }
    }
}
"#;
    expect_errors(source, &["requires a `has` guard"]);
}

#[test]
fn test_narrowing_valid_with_proof_still_works() {
    // Sanity check: narrowing via `has` guard should allow access
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Spellcasting {
            spell_slots: int
        }
    }
    derive check_narrowing(actor: Character) -> int {
        if actor has Spellcasting {
            actor.Spellcasting.spell_slots
        } else {
            0
        }
    }
}
"#;
    expect_no_errors(source);
}

// ── Regression: tdsl-a623 — Position/Condition type override ─────────

#[test]
fn test_user_defined_position_type_accepted() {
    // User declares their own Position type. It should be usable in annotations,
    // just like TurnBudget and Duration can be overridden.
    let source = r#"
system "test" {
    entity Character { HP: int }

    struct Position {
        x: int
        y: int
    }

    derive get_origin() -> Position {
        Position { x: 0, y: 0 }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_user_defined_position_rejects_unknown_field() {
    // User overrides Position — accessing a non-existent field should error
    let source = r#"
system "test" {
    entity Character { HP: int }

    struct Position {
        x: int
        y: int
    }

    derive bad_access() -> int {
        let p = Position { x: 0, y: 0 }
        p.z
    }
}
"#;
    expect_errors(source, &["no field `z`"]);
}

#[test]
fn test_user_defined_condition_enum_field_type() {
    // User declares an enum named Condition. Using it as a field type
    // should resolve to the user-defined enum, not the builtin Ty::Condition.
    // If the bug is present, the return type `Condition` resolves to
    // Ty::Condition (builtin) while the body produces Ty::Enum("Condition"),
    // causing a type mismatch.
    let source = r#"
system "test" {
    entity Character { HP: int }
    enum Condition {
        poisoned
        paralyzed
        stunned
    }
    derive get_status() -> Condition {
        poisoned
    }
}
"#;
    expect_no_errors(source);
}

// ── Regression: tdsl-ky7v — direct turn reassignment should be rejected ──

#[test]
fn test_turn_direct_reassignment_rejected() {
    // turn = ... should be a checker error. Only turn.field mutations are allowed.
    // Bug: check_assign allows this because turn binding is mutable; it should
    // specifically forbid direct reassignment of the implicit turn binding.
    let source = r#"
system "test" {
    entity Character { HP: int }
    action Reset on actor: Character () {
        cost { action }
        resolve {
            turn = turn
        }
    }
}
"#;
    expect_errors(source, &["cannot reassign `turn`"]);
}

// ── Regression: tdsl-nmfv — variant ambiguity ignores system visibility ──

#[test]
fn test_variant_ambiguity_respects_system_visibility() {
    // A defines 'short' in Size, B defines 'short' in Length.
    // C imports only A. Using bare 'short' should resolve to A's Size::short
    // (unique within C's visibility), not report ambiguous.
    expect_multi_no_errors(&[
        (
            "a.ttrpg",
            r#"
system "A" {
    enum Size { short, tall }
}
"#,
        ),
        (
            "b.ttrpg",
            r#"
system "B" {
    enum Length { short, long }
}
"#,
        ),
        (
            "c.ttrpg",
            r#"
use "A"
system "C" {
    derive get_size() -> Size { short }
}
"#,
        ),
    ]);
}

// ── Regression: tdsl-5vjs — qualified pattern on non-enum type says "undefined" ──

#[test]
fn test_qualified_pattern_non_enum_says_not_enum() {
    // Using a struct type in a qualified variant pattern should say the type
    // is not an enum, not that it's "undefined".
    let source = r#"
system "test" {
    struct Point { x: int, y: int }
    derive test(v: int) -> int {
        match v {
            Point.origin => 1
            _ => 0
        }
    }
}
"#;
    expect_errors(source, &["not an enum"]);
}

// ── Regression: tdsl-ysqd — typed let in modify body skips visibility check ──

#[test]
fn test_modify_body_typed_let_checks_type_visibility() {
    // Ext does NOT import Core. A typed let `let r: Rarity = ...` inside a
    // modify body should error about Rarity not being visible, just like a
    // regular let statement would.
    expect_multi_errors(
        &[
            (
                "core.ttrpg",
                r#"
system "Core" {
    enum Rarity { common, rare }
}
"#,
            ),
            (
                "ext.ttrpg",
                r#"
system "Ext" {
    entity Character { HP: int }
    derive base_hp(c: Character) -> int { c.HP }
    condition Buff on bearer: Character {
        modify base_hp(actor: bearer) {
            let r: Rarity = common
            result = result + 1
        }
    }
}
"#,
            ),
        ],
        &[r#"`Rarity` is defined in system "Core""#],
    );
}

// ── Regression: tdsl-p0bd — suppress clauses skip receiver with-group narrowing ──

#[test]
fn test_suppress_clause_narrows_receiver_with_groups() {
    // A condition with `on bearer: Character with Spellcasting` should narrow
    // the bearer's Spellcasting group in suppress clause bindings, allowing
    // access to optional group fields.
    let source = r#"
system "test" {
    entity Character {
        HP: int
        optional Spellcasting {
            spell_slots: int
        }
    }
    event cast_spell(actor: Character) {
        slots_used: int
    }
    condition Silenced on bearer: Character with Spellcasting {
        suppress cast_spell(slots_used: bearer.Spellcasting.spell_slots)
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_suppress_clause_validates_invalid_with_group() {
    // A condition-only suppress clause with an invalid with-group name
    // should produce a diagnostic about the invalid group.
    let source = r#"
system "test" {
    entity Character {
        HP: int
    }
    event take_damage(actor: Character) {
        amount: int
    }
    condition Protected on bearer: Character with NonexistentGroup {
        suppress take_damage(actor: bearer)
    }
}
"#;
    expect_errors(source, &["NonexistentGroup"]);
}

// ── Regression: tdsl-qkkn — map index key gets map key type hint ──

#[test]
fn hint_map_index_key_disambiguates_bare_variant() {
    let source = r#"
system "test" {
    enum Color { red, blue }
    enum Alert { red, yellow }
    derive lookup(m: map<Color, int>) -> int {
        m[red]
    }
}
"#;
    expect_no_errors(source);
}

// ── Regression: tdsl-6ut3 — append element gets list element type hint ──

#[test]
fn hint_append_element_disambiguates_bare_variant() {
    let source = r#"
system "test" {
    enum Color { red, blue }
    enum Alert { red, yellow }
    derive add_color(colors: list<Color>) -> list<Color> {
        append(colors, red)
    }
}
"#;
    expect_no_errors(source);
}

// ── Regression: tdsl-1qvb — unwrap_or default gets option inner type hint ──

#[test]
fn hint_unwrap_or_default_disambiguates_bare_variant() {
    let source = r#"
system "test" {
    enum Color { red, blue }
    enum Alert { red, yellow }
    derive get_color(opt: option<Color>) -> Color {
        opt.unwrap_or(red)
    }
}
"#;
    expect_no_errors(source);
}

// ── Regression: tdsl-1cyf — concat second list misses element type hint ──

#[test]
fn test_concat_second_arg_gets_element_type_hint() {
    // The second argument to concat should use the first list's element type
    // as a hint, so ambiguous bare variants can be disambiguated.
    let source = r#"
system "test" {
    enum DamageType { fire, cold, lightning }
    enum Element { fire, water, earth }
    derive combined() -> list<DamageType> {
        concat([DamageType.fire], [fire])
    }
}
"#;
    expect_no_errors(source);
}

// ── Load order independence tests ───────────────────────────────────────
//
// These tests verify that reversing the order of source files does not
// change whether the pipeline produces errors.  They guard against
// refactoring hazards such as:
//   - pass_1a / pass_1b being fused per-system instead of globally staged
//   - processed_types being reset per-system instead of shared
//   - HashMap iteration order affecting collision or visibility logic
//   - import/visibility unions becoming order-dependent

/// Helper: check multi-source and return whether any errors were produced.
fn multi_has_errors(sources: &[(&str, &str)]) -> bool {
    let owned: Vec<(String, String)> = sources
        .iter()
        .map(|(name, src)| (name.to_string(), src.to_string()))
        .collect();
    let parse_result = ttrpg_parser::parse_multi(&owned);
    if parse_result.has_errors {
        return true;
    }
    let check_result = check_with_modules(&parse_result.program, &parse_result.module_map);
    check_result
        .diagnostics
        .iter()
        .any(|d| d.severity == ttrpg_ast::diagnostic::Severity::Error)
}

#[test]
fn test_load_order_forward_type_ref_across_systems() {
    // Hazard: if pass_1a and pass_1b are fused per-system, the second
    // system's signature can't reference the first system's types.
    // Here system A uses type Character defined in system B.
    let sources_ab: &[(&str, &str)] = &[
        (
            "a.ttrpg",
            r#"
use "B"
system "A" {
    derive hp(c: Character) -> int { c.HP }
}
"#,
        ),
        (
            "b.ttrpg",
            r#"
system "B" {
    entity Character { HP: int = 10 }
}
"#,
        ),
    ];
    let sources_ba: &[(&str, &str)] = &[sources_ab[1], sources_ab[0]];
    expect_multi_no_errors(sources_ab);
    expect_multi_no_errors(sources_ba);
}

#[test]
fn test_load_order_forward_fn_ref_across_systems() {
    // Hazard: if pass_1b processes systems sequentially and a later
    // system's function isn't registered yet, calls from an earlier
    // system would fail.
    let sources_ab: &[(&str, &str)] = &[
        (
            "a.ttrpg",
            r#"
use "B"
system "A" {
    entity Character { HP: int = 10 }
    derive double_hp(c: Character) -> int { base_hp(c) * 2 }
}
"#,
        ),
        (
            "b.ttrpg",
            r#"
use "A"
system "B" {
    derive base_hp(c: Character) -> int { c.HP }
}
"#,
        ),
    ];
    let sources_ba: &[(&str, &str)] = &[sources_ab[1], sources_ab[0]];
    expect_multi_no_errors(sources_ab);
    expect_multi_no_errors(sources_ba);
}

#[test]
fn test_load_order_cross_system_collision_both_orderings() {
    // Hazard: collision detection iterates HashMaps. Both file orderings
    // must produce the collision error.
    let sources_ab: &[(&str, &str)] = &[
        (
            "a.ttrpg",
            r#"
system "A" {
    enum Color { red, blue }
}
"#,
        ),
        (
            "b.ttrpg",
            r#"
system "B" {
    enum Color { green, yellow }
}
"#,
        ),
    ];
    let sources_ba: &[(&str, &str)] = &[sources_ab[1], sources_ab[0]];
    assert!(
        multi_has_errors(sources_ab),
        "A-first should detect collision"
    );
    assert!(
        multi_has_errors(sources_ba),
        "B-first should detect collision"
    );
}

#[test]
fn test_load_order_builtin_override() {
    // Hazard: register_builtin_types runs after pass_1a. If the user-
    // defined Duration enum is in a later file, it must still take
    // precedence over the builtin.
    let sources_ab: &[(&str, &str)] = &[
        (
            "a.ttrpg",
            r#"
use "B"
system "A" {
    entity Character { HP: int = 10 }
    condition Burning on bearer: Character {}
}
"#,
        ),
        (
            "b.ttrpg",
            r#"
system "B" {
    enum Duration { rounds(count: int), minutes(count: int), indefinite }
}
"#,
        ),
    ];
    let sources_ba: &[(&str, &str)] = &[sources_ab[1], sources_ab[0]];
    expect_multi_no_errors(sources_ab);
    expect_multi_no_errors(sources_ba);
}

#[test]
fn test_load_order_cross_file_variant_resolution() {
    // Hazard: variant_to_enums is populated in pass_1b. If the enum is
    // in a later file, its variants must still be resolvable.
    let sources_ab: &[(&str, &str)] = &[
        (
            "a.ttrpg",
            r#"
use "B"
system "A" {
    derive is_fire(dt: DamageType) -> bool {
        match dt {
            fire => true
            _ => false
        }
    }
}
"#,
        ),
        (
            "b.ttrpg",
            r#"
system "B" {
    enum DamageType { fire, cold, lightning }
}
"#,
        ),
    ];
    let sources_ba: &[(&str, &str)] = &[sources_ab[1], sources_ab[0]];
    expect_multi_no_errors(sources_ab);
    expect_multi_no_errors(sources_ba);
}

#[test]
fn test_load_order_merged_system_across_files() {
    // Hazard: the same system is split across two files. Types defined
    // in one file must be usable in signatures in the other file,
    // regardless of file ordering.
    let sources_ab: &[(&str, &str)] = &[
        (
            "types.ttrpg",
            r#"
system "Core" {
    entity Character { HP: int = 10 }
    enum DamageType { fire, cold }
}
"#,
        ),
        (
            "fns.ttrpg",
            r#"
system "Core" {
    derive max_hp(c: Character) -> int { c.HP }
    derive get_type() -> DamageType { fire }
}
"#,
        ),
    ];
    let sources_ba: &[(&str, &str)] = &[sources_ab[1], sources_ab[0]];
    expect_multi_no_errors(sources_ab);
    expect_multi_no_errors(sources_ba);
}

#[test]
fn test_load_order_condition_modify_cross_system() {
    // Hazard: condition and its modify target are in different systems.
    // Both orderings must typecheck.
    let sources_ab: &[(&str, &str)] = &[
        (
            "core.ttrpg",
            r#"
system "Core" {
    entity Character { HP: int = 10 }
    derive max_hp(c: Character) -> int { c.HP }
}
"#,
        ),
        (
            "conditions.ttrpg",
            r#"
use "Core"
system "Conditions" {
    condition Strong on bearer: Character {
        modify max_hp(c: bearer) {
            result = result + 5
        }
    }
}
"#,
        ),
    ];
    let sources_ba: &[(&str, &str)] = &[sources_ab[1], sources_ab[0]];
    expect_multi_no_errors(sources_ab);
    expect_multi_no_errors(sources_ba);
}

#[test]
fn test_load_order_three_systems_import_chain() {
    // Hazard: three systems with imports. All 6 file orderings should
    // typecheck without errors. Each system imports what it needs.
    let a = (
        "a.ttrpg",
        r#"
use "B"
use "C"
system "A" {
    derive total_hp(c: Character) -> int { base_hp(c) * 2 }
}
"#,
    );
    let b = (
        "b.ttrpg",
        r#"
use "C"
system "B" {
    derive base_hp(c: Character) -> int { c.HP }
}
"#,
    );
    let c = (
        "c.ttrpg",
        r#"
system "C" {
    entity Character { HP: int = 10 }
}
"#,
    );

    // Test all 6 permutations
    let permutations: &[&[(&str, &str)]] = &[
        &[a, b, c],
        &[a, c, b],
        &[b, a, c],
        &[b, c, a],
        &[c, a, b],
        &[c, b, a],
    ];
    for (i, perm) in permutations.iter().enumerate() {
        expect_multi_no_errors(perm);
        // Verify we didn't silently skip the check
        assert!(
            !multi_has_errors(perm),
            "permutation {} should not have errors",
            i
        );
    }
}

#[test]
fn test_load_order_duplicate_type_first_definition_wins() {
    // Hazard: processed_types ensures first definition wins. If someone
    // resets it per-system, the second definition would overwrite.
    // Both orderings should produce a collision error but the first
    // definition's variants should still be usable.
    let check_dup = |sources: &[(&str, &str)]| -> Vec<String> {
        let owned: Vec<(String, String)> = sources
            .iter()
            .map(|(n, s)| (n.to_string(), s.to_string()))
            .collect();
        let parse_result = ttrpg_parser::parse_multi(&owned);
        // Collision is detected at parse/resolve level — collect all diagnostics
        let mut all_diags: Vec<String> = parse_result
            .diagnostics
            .iter()
            .filter(|d| d.severity == ttrpg_ast::diagnostic::Severity::Error)
            .map(|d| d.message.clone())
            .collect();
        if !parse_result.has_errors {
            let check_result = check_with_modules(&parse_result.program, &parse_result.module_map);
            all_diags.extend(
                check_result
                    .diagnostics
                    .iter()
                    .filter(|d| d.severity == ttrpg_ast::diagnostic::Severity::Error)
                    .map(|d| d.message.clone()),
            );
        }
        all_diags
    };

    let sources_ab: &[(&str, &str)] = &[
        (
            "a.ttrpg",
            r#"
system "A" {
    enum Color { red, blue, green }
    derive get_red() -> Color { red }
}
"#,
        ),
        (
            "b.ttrpg",
            r#"
system "B" {
    enum Color { cyan, magenta, yellow }
}
"#,
        ),
    ];
    let sources_ba: &[(&str, &str)] = &[sources_ab[1], sources_ab[0]];

    let errors_ab = check_dup(sources_ab);
    let errors_ba = check_dup(sources_ba);

    // Both orderings must detect the collision
    assert!(
        errors_ab.iter().any(|m| m.contains("duplicate")),
        "AB should detect collision: {:?}",
        errors_ab
    );
    assert!(
        errors_ba.iter().any(|m| m.contains("duplicate")),
        "BA should detect collision: {:?}",
        errors_ba
    );
}

#[test]
fn test_load_order_event_cross_system() {
    // Hazard: event defined in one system, referenced in another.
    // Both file orderings must typecheck.
    let sources_ab: &[(&str, &str)] = &[
        (
            "core.ttrpg",
            r#"
system "Core" {
    entity Character { HP: int = 10 }
    event damage(target: Character) { amount: int }
    hook on_damage on self: Character (trigger: damage(target: self)) {
        self.HP -= trigger.amount
    }
}
"#,
        ),
        (
            "ext.ttrpg",
            r#"
use "Core"
system "Ext" {
    derive hp(c: Character) -> int { c.HP }
}
"#,
        ),
    ];
    let sources_ba: &[(&str, &str)] = &[sources_ab[1], sources_ab[0]];
    expect_multi_no_errors(sources_ab);
    expect_multi_no_errors(sources_ba);
}

#[test]
fn test_load_order_visibility_with_import_both_orderings() {
    // Hazard: visibility computation uses set union over imports.
    // If it becomes order-dependent, one ordering would miss names.
    let sources_ab: &[(&str, &str)] = &[
        (
            "lib.ttrpg",
            r#"
system "Lib" {
    enum Ability { STR, DEX, CON }
    entity Character { HP: int = 10 }
    derive modifier(score: int) -> int { floor((score - 10) / 2) }
}
"#,
        ),
        (
            "main.ttrpg",
            r#"
use "Lib"
system "Main" {
    derive str_mod(c: Character) -> int { modifier(c.HP) }
    derive get_str() -> Ability { STR }
}
"#,
        ),
    ];
    let sources_ba: &[(&str, &str)] = &[sources_ab[1], sources_ab[0]];
    expect_multi_no_errors(sources_ab);
    expect_multi_no_errors(sources_ba);
}

// ── Regression: tdsl-6fad — duplicate type across systems overwrites first body ──

#[test]
fn test_duplicate_type_across_systems_preserves_first_body() {
    // System A defines Color with {red, blue, green}. System B also defines Color
    // with {cyan, magenta, yellow}. pass_1a reports duplicate, but pass_1b
    // should NOT overwrite A's variants with B's. Using 'red' should still work.
    let source = r#"
system "A" {
    enum Color { red, blue, green }
    derive get_red() -> Color { red }
}
system "B" {
    enum Color { cyan, magenta, yellow }
}
"#;
    let result = check_source(source);
    let errors: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.severity == ttrpg_ast::diagnostic::Severity::Error)
        .collect();
    // We expect the "duplicate type" error but NOT a "red is undefined" error
    let has_duplicate = errors.iter().any(|e| e.message.contains("duplicate"));
    let has_undefined_red = errors.iter().any(|e| {
        e.message.contains("red")
            && (e.message.contains("undefined") || e.message.contains("unknown"))
    });
    assert!(
        has_duplicate,
        "should report duplicate type declaration; errors: {:?}",
        errors.iter().map(|e| &e.message).collect::<Vec<_>>()
    );
    assert!(
        !has_undefined_red,
        "variant 'red' from A's definition should still be valid after duplicate; errors: {:?}",
        errors.iter().map(|e| &e.message).collect::<Vec<_>>()
    );
}

// ── Regression: tdsl-24qg — variant visibility error can point to wrong owner system ──

#[test]
fn test_variant_visibility_reports_correct_owner_system() {
    // Two systems define a variant with the same name ("small").
    // System C uses "small" without importing either.
    // The error should point to the correct system (the one whose enum is first),
    // NOT an arbitrary last-write winner.
    let result = check_multi_source(&[
        (
            "a.ttrpg",
            r#"
system "A" {
    enum Size { small, medium, large }
}
"#,
        ),
        (
            "b.ttrpg",
            r#"
system "B" {
    enum Priority { small, normal, high }
}
"#,
        ),
        (
            "c.ttrpg",
            r#"
use "A"
system "C" {
    derive get_size() -> Size { small }
}
"#,
        ),
    ]);
    let errors: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.severity == ttrpg_ast::diagnostic::Severity::Error)
        .collect();
    // "small" is visible via import of A, so there should be no visibility error
    let has_visibility_err = errors
        .iter()
        .any(|e| e.message.contains("is defined in system"));
    assert!(
        !has_visibility_err,
        "variant 'small' should be visible via import of A; errors: {:?}",
        errors.iter().map(|e| &e.message).collect::<Vec<_>>()
    );
}

#[test]
fn test_variant_visibility_error_names_correct_system() {
    // System B defines enum with variant "fire". System C uses "fire" without import.
    // The error should mention system "B", not any other system.
    expect_multi_errors(
        &[
            (
                "b.ttrpg",
                r#"
system "B" {
    enum DamageType { fire, cold }
}
"#,
            ),
            (
                "c.ttrpg",
                r#"
system "C" {
    derive get_type() -> DamageType { fire }
}
"#,
            ),
        ],
        &[r#"`fire` is defined in system "B""#],
    );
}

// ── Regression: tdsl-rw0 — qualified types in modify let annotations ──

#[test]
fn test_qualified_type_in_condition_modify_let_annotation() {
    // A condition modify clause uses `let x: Alias.Type = ...` with a
    // qualified type annotation.  The resolver must desugar this to a
    // Named type; if it doesn't, the checker rejects the unresolved
    // qualified type.
    expect_multi_no_errors(&[
        (
            "core.ttrpg",
            r#"
system "Core" {
    enum DamageType { fire, cold, lightning }
    entity Character {
        HP: int
    }
    derive initial_budget(actor: Character) -> int {
        actor.HP
    }
}
"#,
        ),
        (
            "main.ttrpg",
            r#"
use "Core" as Core
system "Main" {
    condition Focused on bearer: Character {
        modify initial_budget(actor: bearer) {
            let dt: Core.DamageType = fire
            result = result + 1
        }
    }
}
"#,
        ),
    ]);
}

// ── aggregation builtins type checking ──────────────────────────

#[test]
fn test_sum_type_checks_int_list() {
    expect_no_errors(
        r#"
system "test" {
    derive f(xs: list<int>) -> int { sum(xs) }
}
"#,
    );
}

#[test]
fn test_sum_rejects_non_numeric_list() {
    expect_errors(
        r#"
system "test" {
    derive f(xs: list<bool>) -> int { sum(xs) }
}
"#,
        &["`sum` requires list<int> or list<float>"],
    );
}

#[test]
fn test_any_type_checks_bool_list() {
    expect_no_errors(
        r#"
system "test" {
    derive f(xs: list<bool>) -> bool { any(xs) }
}
"#,
    );
}

#[test]
fn test_any_rejects_non_bool_list() {
    expect_errors(
        r#"
system "test" {
    derive f(xs: list<int>) -> bool { any(xs) }
}
"#,
        &["`any` requires list<bool>"],
    );
}

#[test]
fn test_all_rejects_non_bool_list() {
    expect_errors(
        r#"
system "test" {
    derive f(xs: list<int>) -> bool { all(xs) }
}
"#,
        &["`all` requires list<bool>"],
    );
}

#[test]
fn test_sort_type_checks() {
    expect_no_errors(
        r#"
system "test" {
    derive f(xs: list<int>) -> list<int> { sort(xs) }
}
"#,
    );
}

// ── list comprehension type checking ────────────────────────────

#[test]
fn test_list_comprehension_type_checks() {
    expect_no_errors(
        r#"
system "test" {
    derive f(xs: list<int>) -> list<int> { [x + 1 for x in xs] }
}
"#,
    );
}

#[test]
fn test_list_comprehension_filter_type_checks() {
    expect_no_errors(
        r#"
system "test" {
    derive f(xs: list<int>) -> list<int> { [x for x in xs if x > 0] }
}
"#,
    );
}

#[test]
fn test_list_comprehension_filter_non_bool_error() {
    expect_errors(
        r#"
system "test" {
    derive f(xs: list<int>) -> list<int> { [x for x in xs if x + 1] }
}
"#,
        &["list comprehension filter must be bool"],
    );
}

#[test]
fn test_list_comprehension_non_iterable_error() {
    expect_errors(
        r#"
system "test" {
    derive f(x: int) -> list<int> { [x for x in x] }
}
"#,
        &["expected list or set"],
    );
}

#[test]
fn test_list_comprehension_range() {
    expect_no_errors(
        r#"
system "test" {
    derive f() -> list<int> { [i * 2 for i in 0..5] }
}
"#,
    );
}

#[test]
fn test_sum_of_comprehension_type_checks() {
    expect_no_errors(
        r#"
system "test" {
    derive f(xs: list<int>) -> int { sum([x * x for x in xs]) }
}
"#,
    );
}

#[test]
fn test_list_comprehension_method_sum() {
    expect_no_errors(
        r#"
system "test" {
    derive f(xs: list<int>) -> int { [x * x for x in xs].sum() }
}
"#,
    );
}

#[test]
fn test_list_comprehension_with_option_pattern() {
    expect_no_errors(
        r#"
system "test" {
    derive f(xs: list<option<int>>) -> list<int> { [x for some(x) in xs] }
}
"#,
    );
}

// ── some() constructor builtin ────────────────────────────────────

#[test]
fn some_constructor_returns_option_type() {
    expect_no_errors(
        r#"
system "test" {
    derive f() -> option<int> { some(42) }
}
"#,
    );
}

#[test]
fn some_constructor_with_variable() {
    expect_no_errors(
        r#"
system "test" {
    derive f(x: int) -> option<int> { some(x) }
}
"#,
    );
}

#[test]
fn some_constructor_nested() {
    expect_no_errors(
        r#"
system "test" {
    derive f() -> option<option<int>> { some(some(1)) }
}
"#,
    );
}

#[test]
fn some_constructor_wrong_arg_count() {
    expect_errors(
        r#"
system "test" {
    derive f() -> option<int> { some(1, 2) }
}
"#,
        &["`some` expects 1 argument, found 2"],
    );
}

#[test]
fn some_constructor_no_args() {
    expect_errors(
        r#"
system "test" {
    derive f() -> option<int> { some() }
}
"#,
        &["`some` expects 1 argument, found 0"],
    );
}

#[test]
fn some_constructor_type_mismatch() {
    expect_errors(
        r#"
system "test" {
    derive f() -> option<int> { some("hello") }
}
"#,
        &["has type option<string>, expected return type option<int>"],
    );
}

// ── Flattened included group fields ──────────────────────────────

#[test]
fn test_flattened_field_access_type_checks() {
    let source = r#"
system "test" {
    group CombatStats {
        ac: int = 10
    }
    entity Monster {
        HP: int
        include CombatStats
    }
    derive get_ac(m: Monster) -> int {
        m.ac
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_flattened_field_qualified_still_works() {
    let source = r#"
system "test" {
    group CombatStats {
        ac: int = 10
    }
    entity Monster {
        HP: int
        include CombatStats
    }
    derive get_ac(m: Monster) -> int {
        m.CombatStats.ac
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_flattened_field_collision_with_entity_field() {
    let source = r#"
system "test" {
    group CombatStats {
        ac: int = 10
    }
    entity Monster {
        ac: int
        include CombatStats
    }
}
"#;
    expect_errors(source, &["included group `CombatStats` field `ac` conflicts with"]);
}

#[test]
fn test_flattened_field_collision_between_included_groups() {
    let source = r#"
system "test" {
    group Stats {
        ac: int = 10
    }
    group Defense {
        ac: int = 12
    }
    entity Monster {
        HP: int
        include Stats
        include Defense
    }
}
"#;
    expect_errors(source, &["field `ac` defined in both included groups"]);
}

#[test]
fn test_flattened_field_collision_with_group_name() {
    let source = r#"
system "test" {
    group CombatStats {
        Rage: int = 0
    }
    entity Monster {
        HP: int
        include CombatStats
        optional Rage {
            damage: int
        }
    }
}
"#;
    expect_errors(source, &["included group `CombatStats` field `Rage` conflicts with"]);
}

#[test]
fn test_optional_groups_not_flattened() {
    let source = r#"
system "test" {
    entity Monster {
        HP: int
        optional Spellcasting {
            dc: int
        }
    }
    derive get_dc(m: Monster) -> int {
        m.dc
    }
}
"#;
    expect_errors(source, &["type `Monster` has no field `dc`"]);
}

// ── Group alias (`as`) tests ─────────────────────────────────────

#[test]
fn test_with_group_alias_read() {
    let source = r#"system "test" {
    entity Character {
        name: string
        optional Spellcasting { dc: int }
    }
    derive spell_dc(caster: Character with Spellcasting as sc) -> int {
        caster.sc.dc
    }
}"#;
    expect_no_errors(source);
}

#[test]
fn test_with_group_alias_on_receiver() {
    let source = r#"system "test" {
    entity Character {
        name: string
        optional Spellcasting { dc: int }
    }
    action CastSpell on caster: Character with Spellcasting as sc () {
        resolve {
            let x = caster.sc.dc
        }
    }
}"#;
    expect_no_errors(source);
}

#[test]
fn test_has_group_alias_read() {
    let source = r#"system "test" {
    entity Character {
        name: string
        optional Spellcasting { dc: int }
    }
    derive spell_dc(caster: Character) -> int {
        if caster has Spellcasting as sc {
            caster.sc.dc
        } else {
            0
        }
    }
}"#;
    expect_no_errors(source);
}

#[test]
fn test_has_group_alias_write() {
    let source = r#"system "test" {
    entity Character {
        name: string
        optional Spellcasting { dc: int }
    }
    action Boost on target: Character () {
        resolve {
            if target has Spellcasting as sc {
                target.sc.dc = 20
            }
        }
    }
}"#;
    expect_no_errors(source);
}

#[test]
fn test_alias_not_visible_outside_scope() {
    let source = r#"system "test" {
    entity Character {
        name: string
        optional Spellcasting { dc: int }
    }
    derive spell_dc(caster: Character) -> int {
        if caster has Spellcasting as sc {
            0
        }
        caster.sc.dc
    }
}"#;
    // `sc` is only valid inside the if-block; outside it should fail
    expect_errors(source, &["has"]);
}

#[test]
fn test_alias_shadows_field_error() {
    let source = r#"system "test" {
    entity Character {
        name: string
        optional Spellcasting { dc: int }
    }
    derive test(c: Character) -> int {
        if c has Spellcasting as name {
            0
        } else {
            0
        }
    }
}"#;
    expect_errors(source, &["alias `name` shadows a field"]);
}

#[test]
fn test_alias_shadows_group_error() {
    let source = r#"system "test" {
    entity Character {
        name: string
        optional Spellcasting { dc: int }
        optional Magic { power: int }
    }
    derive test(c: Character) -> int {
        if c has Spellcasting as Magic {
            0
        } else {
            0
        }
    }
}"#;
    expect_errors(source, &["alias `Magic` shadows an optional group"]);
}

#[test]
fn test_multiple_aliases_in_body() {
    let source = r#"system "test" {
    entity Character {
        name: string
        optional Spellcasting { dc: int }
        optional Rage { bonus: int }
    }
    derive combined(c: Character with Spellcasting as sc, Rage as r) -> int {
        c.sc.dc + c.r.bonus
    }
}"#;
    expect_no_errors(source);
}

// ═══════════════════════════════════════════════════════════════
// Tags and selectors
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_tag_declaration_basic() {
    let source = r#"system "Test" {
    tag attack
    struct AttackResult { hit: bool }
    entity Character { hp: int }
    mechanic sword_strike(a: Character, t: Character) -> AttackResult #attack {
        AttackResult { hit: true }
    }
}"#;
    expect_no_errors(source);
}

#[test]
fn test_tag_undeclared() {
    let source = r#"system "Test" {
    struct AttackResult { hit: bool }
    entity Character { hp: int }
    mechanic sword_strike(a: Character, t: Character) -> AttackResult #attack {
        AttackResult { hit: true }
    }
}"#;
    expect_errors(source, &["undeclared tag `attack`"]);
}

#[test]
fn test_tag_multiple_on_function() {
    let source = r#"system "Test" {
    tag attack
    tag ranged
    struct AttackResult { hit: bool }
    entity Character { hp: int }
    mechanic arrow_shot(a: Character, t: Character) -> AttackResult #attack #ranged {
        AttackResult { hit: true }
    }
}"#;
    expect_no_errors(source);
}

#[test]
fn test_selector_modify_basic() {
    let source = r#"system "Test" {
    tag attack
    struct AttackResult { hit: bool }
    entity Character { hp: int }
    mechanic sword_strike(attacker: Character, target: Character) -> AttackResult #attack {
        AttackResult { hit: true }
    }
    condition Prone on bearer: Character {
        modify [#attack](attacker: bearer) {
            result.hit = false
        }
    }
}"#;
    expect_no_errors(source);
}

#[test]
fn test_selector_empty_match_set() {
    let source = r#"system "Test" {
    tag attack
    entity Character { hp: int }
    condition Prone on bearer: Character {
        modify [#attack](attacker: bearer) {
        }
    }
}"#;
    expect_warnings(source, &["selector matches no functions"]);
}

#[test]
fn test_selector_binding_mismatch() {
    let source = r#"system "Test" {
    tag attack
    struct AttackResult { hit: bool }
    entity Character { hp: int }
    mechanic strike_a(attacker: Character, target: Character) -> AttackResult #attack {
        AttackResult { hit: true }
    }
    mechanic strike_b(attacker: Character, power: int) -> AttackResult #attack {
        AttackResult { hit: true }
    }
    condition Prone on bearer: Character {
        modify [#attack](target: bearer) {
        }
    }
}"#;
    expect_errors(source, &["does not exist on all matched functions"]);
}

#[test]
fn test_selector_result_type_mismatch() {
    let source = r#"system "Test" {
    tag attack
    struct ResultA { hit: bool }
    struct ResultB { damage: int }
    entity Character { hp: int }
    mechanic strike_a(attacker: Character) -> ResultA #attack {
        ResultA { hit: true }
    }
    mechanic strike_b(attacker: Character) -> ResultB #attack {
        ResultB { damage: 5 }
    }
    condition Prone on bearer: Character {
        modify [#attack](attacker: bearer) {
            result = result
        }
    }
}"#;
    expect_errors(source, &["different return types"]);
}

#[test]
fn test_selector_returns_predicate() {
    let source = r#"system "Test" {
    struct AttackResult { hit: bool }
    entity Character { hp: int }
    mechanic sword_strike(attacker: Character) -> AttackResult {
        AttackResult { hit: true }
    }
    derive get_hp(c: Character) -> int {
        c.hp
    }
    condition Prone on bearer: Character {
        modify [returns AttackResult](attacker: bearer) {
            result.hit = false
        }
    }
}"#;
    expect_no_errors(source);
}

#[test]
fn test_selector_has_predicate() {
    let source = r#"system "Test" {
    struct AttackResult { hit: bool }
    entity Character { hp: int }
    mechanic sword_strike(attacker: Character, target: Character) -> AttackResult {
        AttackResult { hit: true }
    }
    mechanic magic_bolt(attacker: Character, target: Character) -> AttackResult {
        AttackResult { hit: true }
    }
    condition Prone on bearer: Character {
        modify [has target: Character](target: bearer) {
            result.hit = false
        }
    }
}"#;
    expect_no_errors(source);
}

#[test]
fn test_selector_combined_predicates() {
    let source = r#"system "Test" {
    tag attack
    struct AttackResult { hit: bool }
    entity Character { hp: int }
    mechanic sword_strike(attacker: Character, target: Character) -> AttackResult #attack {
        AttackResult { hit: true }
    }
    derive get_hp(c: Character) -> int {
        c.hp
    }
    condition Prone on bearer: Character {
        modify [#attack, returns AttackResult](attacker: bearer) {
            result.hit = false
        }
    }
}"#;
    expect_no_errors(source);
}

#[test]
fn test_selector_excludes_synthetic() {
    // Move declarations produce synthetic mechanic functions.
    // Selectors should not match them.
    let source = r#"
system "test" {
    tag movement
    entity Character { stat: int }
    move GoAggro on actor: Character () {
        trigger: "When you threaten with force"
        roll: 2d6 + actor.stat
        on strong_hit { actor.stat += 1 }
        on weak_hit { actor.stat += 0 }
        on miss { actor.stat -= 1 }
    }
    condition Prone on bearer: Character {
        modify [#movement]() {
        }
    }
}
"#;
    // GoAggro is lowered to a synthetic mechanic; with no non-synthetic #movement fns, match set is empty
    let (_program, result) = check_lowered(source);
    let warnings: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.severity == ttrpg_ast::diagnostic::Severity::Warning)
        .collect();
    assert!(
        warnings.iter().any(|w| w.message.contains("selector matches no functions")),
        "expected warning about empty selector match set, got: {:?}",
        warnings.iter().map(|w| &w.message).collect::<Vec<_>>()
    );
}

#[test]
fn test_duplicate_tag_declaration() {
    let source = r#"system "Test" {
    tag attack
    tag attack
}"#;
    expect_errors(source, &["duplicate tag declaration `attack`"]);
}

// ═══════════════════════════════════════════════════════════════
// Invocation tracking
// ═══════════════════════════════════════════════════════════════

#[test]
fn invocation_in_action_body() {
    let source = r#"system "Test" {
    entity Character { HP: int }
    action Cast on caster: Character () {
        resolve {
            let inv = invocation()
        }
    }
}"#;
    expect_no_errors(source);
}

#[test]
fn invocation_in_reaction_body() {
    let source = r#"system "Test" {
    entity Character { HP: int }
    event DamageTaken(target: Character) {}
    reaction OnHit on target: Character (trigger: DamageTaken(target: target)) {
        resolve {
            let inv = invocation()
        }
    }
}"#;
    expect_no_errors(source);
}

#[test]
fn invocation_in_hook_body() {
    let source = r#"system "Test" {
    entity Character { HP: int }
    event TurnStarted(actor: Character) {}
    hook on_turn on actor: Character (trigger: TurnStarted(actor: actor)) {
        let inv = invocation()
    }
}"#;
    expect_no_errors(source);
}

#[test]
fn invocation_in_derive_rejected() {
    let source = r#"system "Test" {
    entity Character { HP: int }
    derive get_inv(c: Character) -> Invocation { invocation() }
}"#;
    expect_errors(
        source,
        &["invocation() can only be called in action, reaction, or hook blocks"],
    );
}

#[test]
fn invocation_in_mechanic_rejected() {
    let source = r#"system "Test" {
    entity Character { HP: int }
    mechanic get_inv(c: Character) -> Invocation { invocation() }
}"#;
    expect_errors(
        source,
        &["invocation() can only be called in action, reaction, or hook blocks"],
    );
}

#[test]
fn revoke_with_invocation_type() {
    let source = r#"system "Test" {
    entity Character { HP: int }
    action Cast on caster: Character () {
        resolve {
            let inv = invocation()
            revoke(inv)
        }
    }
}"#;
    expect_no_errors(source);
}

#[test]
fn revoke_with_option_invocation_type() {
    let source = r#"system "Test" {
    entity Character { HP: int, concentrating_on: option<Invocation> }
    action Cast on caster: Character () {
        resolve {
            revoke(caster.concentrating_on)
        }
    }
}"#;
    expect_no_errors(source);
}

#[test]
fn revoke_with_wrong_type_rejected() {
    let source = r#"system "Test" {
    entity Character { HP: int }
    action Cast on caster: Character () {
        resolve {
            revoke(42)
        }
    }
}"#;
    expect_errors(
        source,
        &["`revoke` expects Invocation or option<Invocation>"],
    );
}

#[test]
fn revoke_in_derive_rejected() {
    let source = r#"system "Test" {
    entity Character { HP: int, inv: Invocation }
    derive bad(c: Character) -> int {
        revoke(c.inv)
        0
    }
}"#;
    expect_errors(source, &["revoke() can only be called in action, reaction, or hook blocks"]);
}

#[test]
fn invocation_type_on_entity_field() {
    let source = r#"system "Test" {
    entity Character {
        HP: int
        concentrating_on: option<Invocation>
        sustained_spells: list<Invocation>
    }
}"#;
    expect_no_errors(source);
}

#[test]
fn invocation_type_on_event_param() {
    let source = r#"system "Test" {
    entity Character { HP: int }
    event ConcentrationStarted(caster: Character, inv: Invocation) {}
}"#;
    expect_no_errors(source);
}

#[test]
fn action_tags_accepted() {
    let source = r#"system "Test" {
    tag concentration
    entity Character { HP: int }
    action CastBless on caster: Character () #concentration {
        resolve {
            let inv = invocation()
        }
    }
}"#;
    expect_no_errors(source);
}

#[test]
fn action_undeclared_tag_rejected() {
    let source = r#"system "Test" {
    entity Character { HP: int }
    action CastBless on caster: Character () #concentration {
        resolve {
            let inv = invocation()
        }
    }
}"#;
    expect_errors(source, &["undeclared tag `concentration`"]);
}

#[test]
fn revoke_with_none_literal() {
    let source = r#"system "Test" {
    entity Character { HP: int }
    action Cast on caster: Character () {
        resolve {
            revoke(none)
        }
    }
}"#;
    expect_no_errors(source);
}

// ── Disjunctive with constraint checker tests ───────────────────

#[test]
fn test_disjunctive_with_body_rejects_direct_field_access() {
    let source = r#"system "test" {
    entity Character {
        hp: int
        optional Spellcasting { spell_slots: int }
        optional Martial { attacks: int }
    }
    derive combat_value(actor: Character with Spellcasting | Martial) -> int {
        actor.Spellcasting.spell_slots
    }
}"#;
    let result = check_source(source);
    assert!(
        !result.diagnostics.is_empty(),
        "expected error for direct field access on disjunctive with"
    );
}

#[test]
fn test_disjunctive_with_has_guard_narrows() {
    let source = r#"system "test" {
    entity Character {
        hp: int
        optional Spellcasting { spell_slots: int }
        optional Martial { attacks: int }
    }
    derive combat_value(actor: Character with Spellcasting | Martial) -> int {
        if actor has Spellcasting {
            actor.Spellcasting.spell_slots
        } else {
            0
        }
    }
}"#;
    let result = check_source(source);
    assert!(
        result.diagnostics.is_empty(),
        "unexpected errors: {:?}",
        result.diagnostics
    );
}

#[test]
fn test_disjunctive_with_callsite_no_proof_required() {
    let source = r#"system "test" {
    entity Character {
        hp: int
        optional Spellcasting { spell_slots: int }
        optional Martial { attacks: int }
    }
    derive combat_value(actor: Character with Spellcasting | Martial) -> int {
        0
    }
    mechanic test_it(c: Character) -> int {
        combat_value(c)
    }
}"#;
    let result = check_source(source);
    assert!(
        result.diagnostics.is_empty(),
        "disjunctive with should not require call-site proof: {:?}",
        result.diagnostics
    );
}

#[test]
fn test_conjunctive_with_callsite_requires_proof() {
    // Conjunctive `with` DOES require call-site proof (existing behavior)
    let source = r#"system "test" {
    entity Character {
        hp: int
        optional Spellcasting { spell_slots: int }
    }
    derive spell_stuff(actor: Character with Spellcasting) -> int {
        actor.Spellcasting.spell_slots
    }
    mechanic test_it(c: Character) -> int {
        spell_stuff(c)
    }
}"#;
    let result = check_source(source);
    assert!(
        !result.diagnostics.is_empty(),
        "conjunctive with should require call-site proof"
    );
}

#[test]
fn test_disjunctive_with_validates_groups_exist() {
    let source = r#"system "test" {
    entity Character {
        hp: int
        optional Spellcasting { spell_slots: int }
    }
    derive bad(actor: Character with Spellcasting | NoSuchGroup) -> int {
        0
    }
}"#;
    let result = check_source(source);
    assert!(
        result.diagnostics.iter().any(|d| d.message.contains("NoSuchGroup")),
        "expected error for nonexistent group in disjunctive with: {:?}",
        result.diagnostics
    );
}

// --- mutation permission across block types ---

#[test]
fn test_mutation_in_derive_error() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    derive foo(target: Character) -> int {
        target.hp -= 5
        0
    }
}
"#;
    expect_errors(source, &["assignment to entity fields requires action, reaction, or hook"]);
}

#[test]
fn test_mutation_in_hook_ok() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    event TurnStart(actor: Character) {}
    hook Regen on c: Character (trigger: TurnStart(actor: c)) {
        c.hp += 10
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn test_mutation_in_reaction_ok() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    event Attack(reactor: Character) { attacker: Character, damage: int }
    reaction Shield on defender: Character (trigger: Attack(reactor: defender)) {
        resolve {
            defender.hp -= trigger.damage
        }
    }
}
"#;
    expect_no_errors(source);
}

// --- grant/revoke permission ---

#[test]
fn test_grant_in_derive_error() {
    let source = r#"
system "test" {
    entity Character {
        hp: int
        optional Flying { speed: int }
    }
    derive foo(target: Character) -> int {
        grant target.Flying { speed: 60 }
        0
    }
}
"#;
    expect_errors(source, &["grant is only allowed in action, reaction, or hook"]);
}

#[test]
fn test_grant_in_mechanic_error() {
    let source = r#"
system "test" {
    entity Character {
        hp: int
        optional Flying { speed: int }
    }
    mechanic foo(target: Character) -> int {
        grant target.Flying { speed: 60 }
        0
    }
}
"#;
    expect_errors(source, &["grant is only allowed in action, reaction, or hook"]);
}

#[test]
fn test_grant_in_action_audit_ok() {
    let source = r#"
system "test" {
    entity Character {
        hp: int
        optional Flying { speed: int }
    }
    action GrantFlight on actor: Character (target: Character) {
        resolve {
            grant target.Flying { speed: 60 }
        }
    }
}
"#;
    expect_no_errors(source);
}

// --- action call context ---

#[test]
fn test_action_call_from_derive_error() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    action Heal on actor: Character (target: Character) {
        resolve {
            target.hp += 5
        }
    }
    derive foo(a: Character, b: Character) -> int {
        Heal(a, b)
        0
    }
}
"#;
    expect_errors(source, &["is an action and can only be called from action, reaction, or hook"]);
}

#[test]
fn test_action_call_from_mechanic_error() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    action Heal on actor: Character (target: Character) {
        resolve {
            target.hp += 5
        }
    }
    mechanic foo(a: Character, b: Character) -> int {
        Heal(a, b)
        0
    }
}
"#;
    expect_errors(source, &["is an action and can only be called from action, reaction, or hook"]);
}

#[test]
fn test_action_call_from_action_ok() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    action Heal on actor: Character (target: Character) {
        resolve {
            target.hp += 5
        }
    }
    action DoubleHeal on actor: Character (target: Character) {
        resolve {
            Heal(actor, target)
        }
    }
}
"#;
    expect_no_errors(source);
}

// --- reaction/hook cannot be called directly ---

#[test]
fn test_reaction_call_error() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    event Attack(reactor: Character) { attacker: Character }
    reaction Parry on defender: Character (trigger: Attack(reactor: defender)) {
        resolve { }
    }
    action Foo on actor: Character () {
        resolve {
            Parry(actor)
        }
    }
}
"#;
    expect_errors(source, &["reactions cannot be called directly"]);
}

#[test]
fn test_hook_call_error() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    event TurnStart(actor: Character) {}
    hook Regen on c: Character (trigger: TurnStart(actor: c)) {
        c.hp += 10
    }
    action Foo on actor: Character () {
        resolve {
            Regen(actor)
        }
    }
}
"#;
    expect_errors(source, &["hooks cannot be called directly"]);
}

// --- invocation/revoke permission ---

#[test]
fn test_invocation_in_derive_error() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    derive foo(target: Character) -> Invocation {
        invocation()
    }
}
"#;
    expect_errors(source, &["invocation() can only be called in action, reaction, or hook"]);
}

#[test]
fn test_invocation_in_action_ok() {
    let source = r#"
system "test" {
    entity Character {
        hp: int
        concentrating_on: option<Invocation>
    }
    action Foo on actor: Character () {
        resolve {
            actor.concentrating_on = some(invocation())
        }
    }
}
"#;
    expect_no_errors(source);
}

// ── Regression: tdsl-z7sj — reversed types_compatible in list/set methods ──

#[test]
fn list_append_accepts_compatible_subtype() {
    // append() should accept an element whose type is compatible with the list element type
    let source = r#"
system "test" {
    entity Character { hp: int }
    condition Prone on bearer: Character {}
    derive foo(conds: list<Condition>) -> list<Condition> {
        let c = conds
        append(c, Prone)
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn set_add_accepts_compatible_subtype() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    derive foo(items: set<int>) -> set<int> {
        items.add(42)
        items
    }
}
"#;
    expect_no_errors(source);
}

// ── Regression: tdsl-7bdk — condition/event defaults referencing earlier params ──

#[test]
fn condition_default_references_earlier_param() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    condition Buffed(amount: int, doubled: int = amount * 2) on bearer: Character {
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn event_default_references_earlier_param() {
    let source = r#"
system "test" {
    entity Character { hp: int }
    event Damaged(target: Character, amount: int, doubled: int = amount * 2) {}
}
"#;
    expect_no_errors(source);
}

// ── Regression: tdsl-5zuy — if/if-let branches ignore expected type hints ──

#[test]
fn if_branches_thread_type_hint() {
    let source = r#"
system "test" {
    enum Color { red, blue }
    enum Alert { red, yellow }
    derive pick(flag: bool) -> Color {
        if flag { red } else { blue }
    }
}
"#;
    expect_no_errors(source);
}

#[test]
fn if_let_branches_thread_type_hint() {
    let source = r#"
system "test" {
    enum Color { red, blue }
    enum Alert { red, yellow }
    derive pick(val: option<int>) -> Color {
        if let some(_) = val { red } else { blue }
    }
}
"#;
    expect_no_errors(source);
}

// ── Regression: tdsl-j5c2 — qualified types in modify selectors ──

#[test]
fn qualified_type_in_modify_selector_resolved() {
    expect_multi_no_errors(&[
        ("core.ttrpg", r#"
system "Core" {
    entity Character { hp: int }
    enum DamageType { fire, cold }
    derive deal(amount: int, dtype: DamageType) -> int { amount }
}
"#),
        ("ext.ttrpg", r#"
use "Core" as C
system "Ext" {
    entity Monster { hp: int }
    condition Resistant on bearer: Monster {
        modify [returns C.DamageType]() {
            result = 0
        }
    }
}
"#),
    ]);
}

/// Bug tdsl-8qat: validate_option_extends cycle error builder assumes the
/// cycle closes back to start_name, but for A->B->C->B the cycle is B->C->B
/// and the builder loops forever trying to reach A. Must stop on the detected
/// cycle node instead.
#[test]
fn option_extends_cycle_not_through_start_terminates() {
    // A extends B, B extends C, C extends B → cycle is B→C→B.
    // Starting from A, detection finds revisit at B. The error builder
    // must terminate without looping.
    expect_errors(
        r#"
system "test" {
    option a extends "b" {
        description: "A"
        default: off
    }
    option b extends "c" {
        description: "B"
        default: off
    }
    option c extends "b" {
        description: "C"
        default: off
    }
}
"#,
        &["circular option extends"],
    );
}

#[test]
fn option_extends_direct_self_cycle_detected() {
    expect_errors(
        r#"
system "test" {
    option x extends "x" {
        description: "Self"
        default: off
    }
}
"#,
        &["circular option extends"],
    );
}

// ═══════════════════════════════════════════════════════════════
// Fix: cost token exact match before alias fallback
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_cost_token_exact_match_before_alias() {
    // When both `action` and `actions` exist as fields, `action` should
    // resolve to itself (exact match), not to `actions` (alias).
    let source = r#"
system "test" {
    entity Character { HP: int }
    struct TurnBudget {
        action: int
        actions: int
    }
    action Step on actor: Character () {
        cost { action }
        resolve {}
    }
}
"#;
    expect_no_errors(source);
}

// ═══════════════════════════════════════════════════════════════
// Fix: has-alias shadow check catches flattened included fields
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_has_alias_shadows_flattened_field() {
    let source = r#"system "test" {
    group CombatStats {
        ac: int
    }
    entity Character {
        name: string
        include CombatStats
        optional Spellcasting {
            spell_dc: int
        }
    }
    derive check_spells(caster: Character) -> bool {
        if caster has Spellcasting as ac {
            true
        } else {
            false
        }
    }
}"#;
    expect_errors(source, &["alias `ac` shadows a field"]);
}
