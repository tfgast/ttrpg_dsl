use ttrpg_ast::diagnostic::SourceMap;
use ttrpg_checker::{check, CheckResult};

fn check_source(source: &str) -> CheckResult {
    let (program, parse_errors) = ttrpg_parser::parse(source);
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

// ═══════════════════════════════════════════════════════════════
// Pass 1: Declaration collection
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_collect_counts() {
    let source = include_str!("../../../spec/v0/04_full_example.ttrpg");
    let result = check_source(source);

    // Enums: Ability, RollMode, DamageType, WeaponProperty, ResolvedDamage + built-in Duration
    assert_eq!(result.env.types.values().filter(|d| matches!(d, ttrpg_checker::env::DeclInfo::Enum(_))).count(), 6);
    // Structs: DamageSpec, TurnBudget
    assert_eq!(result.env.types.values().filter(|d| matches!(d, ttrpg_checker::env::DeclInfo::Struct(_))).count(), 2);
    // Entities: Weapon, Character
    assert_eq!(result.env.types.values().filter(|d| matches!(d, ttrpg_checker::env::DeclInfo::Entity(_))).count(), 2);
    // Events: entity_leaves_reach
    assert_eq!(result.env.events.len(), 1);
    // Conditions: Prone, Dodging, Disengaging
    assert_eq!(result.env.conditions.len(), 3);
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
    expect_errors(source, &["function body has type int, expected return type bool"]);
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
fn test_int_division_yields_float() {
    let source = r#"
system "test" {
    derive foo(x: int) -> int {
        x / 2
    }
}
"#;
    // int / int -> float, so returning float as int should error
    expect_errors(source, &["function body has type float, expected return type int"]);
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

// ═══════════════════════════════════════════════════════════════
// Scope enforcement
// ═══════════════════════════════════════════════════════════════

#[test]
fn test_roll_in_derive_error() {
    let source = r#"
system "test" {
    derive foo() -> RollResult {
        roll(1d20)
    }
}
"#;
    expect_errors(source, &["roll() can only be called in mechanic, action, or reaction"]);
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
    expect_errors(source, &["assignment to entity fields requires action or reaction"]);
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
    expect_errors(source, &["apply_condition() can only be called in action or reaction"]);
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
    expect_errors(source, &["modify target `nonexistent_fn` is not a defined function"]);
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
    expect_errors(source, &["let `x`: value has type int, annotation says bool"]);
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
    expect_errors(source, &["missing required argument `a`", "missing required argument `b`"]);
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
    expect_errors(source, &["suppress binding `target` has type string, expected Character"]);
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
    expect_errors(source, &["modify target `Sprint` must be a derive or mechanic"]);
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
    expect_errors(source, &["positional trigger binding 0 has type Character, expected int"]);
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
    expect_errors(source, &["too many positional trigger bindings for event `flee`"]);
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
    expect_errors(source, &["parameter `x` default has type string, expected int"]);
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
    expect_warnings(source, &["unreachable match arm: wildcard `_` must be last"]);
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
    expect_errors(source, &["variant field `count` has type int, found string"]);
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
    expect_errors(source, &["variant `timed` has payload fields and must be called as a constructor"]);
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
    expect_errors(source, &["is an action and can only be called from action or reaction context"]);
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
    expect_errors(source, &["positional trigger binding 1 has type Character, expected int"]);
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
    expect_errors(source, &["receiver `turn` shadows the implicit turn budget binding"]);
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
    expect_errors(source, &["parameter `turn` shadows the implicit turn budget binding"]);
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
    expect_errors(source, &["receiver `trigger` shadows the implicit trigger binding"]);
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
    expect_errors(source, &["receiver `turn` shadows the implicit turn budget binding"]);
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
    expect_errors(source, &["cannot call a field access expression"]);
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
    expect_errors(source, &["cannot mutate field/index of immutable binding `s`"]);
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
    expect_errors(source, &["cannot mutate field/index of immutable binding `xs`"]);
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
    expect_warnings(source, &["function `bar` has the same name as an enum variant"]);
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
    expect_errors(source, &["suggest expression has type string, expected Character"]);
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
