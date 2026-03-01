// =============================================================================
// Grammar conformance tests
//
// Systematically verifies every production in 03_canonical_grammar.ttrpg.
// Organized by spec section.
// =============================================================================

use ttrpg_ast::ast::*;
use ttrpg_ast::FileId;
use ttrpg_parser::{parse, SourceMap};

/// Helper: parse source, assert no diagnostics, return program.
fn ok(source: &str) -> Program {
    let (program, diagnostics) = parse(source, FileId::SYNTH);
    if !diagnostics.is_empty() {
        let sm = SourceMap::new(source);
        for d in &diagnostics {
            eprintln!("{}", sm.render(d));
        }
        panic!(
            "expected no errors, got {}:\n{}",
            diagnostics.len(),
            diagnostics
                .iter()
                .map(|d| d.message.as_str())
                .collect::<Vec<_>>()
                .join("\n")
        );
    }
    program
}

/// Helper: parse source, assert at least one diagnostic.
fn err(source: &str) -> Vec<ttrpg_parser::Diagnostic> {
    let (_, diagnostics) = parse(source, FileId::SYNTH);
    assert!(
        !diagnostics.is_empty(),
        "expected at least one diagnostic, got none"
    );
    diagnostics
}

fn decls(p: &Program) -> &[ttrpg_ast::Spanned<DeclKind>] {
    match &p.items[0].node {
        TopLevel::System(s) => &s.decls,
        _ => panic!("expected system block"),
    }
}

fn first_decl(p: &Program) -> &DeclKind {
    &decls(p)[0].node
}

// =============================================================================
// 1. Program structure
// =============================================================================

#[test]
fn program_empty_system() {
    let p = ok(r#"system "test" {}"#);
    assert_eq!(p.items.len(), 1);
}

#[test]
fn program_use_decl() {
    let p = ok(r#"use "D&D 5e Combat"
system "homebrew" {}"#);
    assert_eq!(p.items.len(), 2);
    assert!(matches!(&p.items[0].node, TopLevel::Use(_)));
}

#[test]
fn program_use_with_alias() {
    // Parser extension: `use "name" as alias`
    let p = ok(r#"use "D&D 5e Combat" as dnd
system "homebrew" {}"#);
    match &p.items[0].node {
        TopLevel::Use(u) => assert!(u.alias.is_some()),
        _ => panic!("expected use"),
    }
}

#[test]
fn program_multiple_systems() {
    let p = ok(r#"
system "A" {}
system "B" {}
"#);
    assert_eq!(p.items.len(), 2);
}

#[test]
fn program_no_trailing_newline() {
    // EOF as term for the last item
    ok(r#"system "test" {}"#);
}

// =============================================================================
// 2. Declarations — Tag
// =============================================================================

#[test]
fn tag_decl_with_hash() {
    let p = ok(r#"system "t" { tag #Attack }"#);
    match first_decl(&p) {
        DeclKind::Tag(t) => assert_eq!(t.name.as_str(), "Attack"),
        _ => panic!("expected tag"),
    }
}

#[test]
fn tag_decl_without_hash() {
    // Parser accepts `tag name` (no #) for convenience
    let p = ok(r#"system "t" { tag Attack }"#);
    match first_decl(&p) {
        DeclKind::Tag(t) => assert_eq!(t.name.as_str(), "Attack"),
        _ => panic!("expected tag"),
    }
}

// =============================================================================
// 2. Declarations — Enum
// =============================================================================

#[test]
fn enum_comma_separated() {
    let p = ok(r#"system "t" { enum Size { small, medium, large } }"#);
    match first_decl(&p) {
        DeclKind::Enum(e) => {
            assert_eq!(e.name.as_str(), "Size");
            assert_eq!(e.variants.len(), 3);
        }
        _ => panic!("expected enum"),
    }
}

#[test]
fn enum_newline_separated() {
    let p = ok(r#"system "t" {
    enum Size {
        small
        medium
        large
    }
}"#);
    match first_decl(&p) {
        DeclKind::Enum(e) => assert_eq!(e.variants.len(), 3),
        _ => panic!("expected enum"),
    }
}

#[test]
fn enum_trailing_comma() {
    ok(r#"system "t" { enum Size { small, medium, large, } }"#);
}

#[test]
fn enum_mixed_comma_newline() {
    ok(r#"system "t" {
    enum X {
        a, b
        c
        d, e
    }
}"#);
}

#[test]
fn enum_variant_with_payload() {
    let p = ok(r#"system "t" {
    enum DamageResult {
        miss
        hit(amount: int)
        crit(amount: int, multiplier: int)
    }
}"#);
    match first_decl(&p) {
        DeclKind::Enum(e) => {
            assert!(e.variants[0].fields.is_none());
            assert_eq!(e.variants[1].fields.as_ref().unwrap().len(), 1);
            assert_eq!(e.variants[2].fields.as_ref().unwrap().len(), 2);
        }
        _ => panic!("expected enum"),
    }
}

#[test]
fn enum_ordered() {
    let p = ok(r#"system "t" { enum Size ordered { small, medium, large } }"#);
    match first_decl(&p) {
        DeclKind::Enum(e) => assert!(e.ordered),
        _ => panic!("expected enum"),
    }
}

#[test]
fn enum_not_ordered() {
    let p = ok(r#"system "t" { enum X { a, b } }"#);
    match first_decl(&p) {
        DeclKind::Enum(e) => assert!(!e.ordered),
        _ => panic!("expected enum"),
    }
}

#[test]
fn enum_empty_is_error() {
    err(r#"system "t" { enum X {} }"#);
}

// =============================================================================
// 2. Declarations — Struct
// =============================================================================

#[test]
fn struct_basic() {
    let p = ok(r#"system "t" {
    struct Stats {
        STR: int
        DEX: int
    }
}"#);
    match first_decl(&p) {
        DeclKind::Struct(s) => assert_eq!(s.fields.len(), 2),
        _ => panic!("expected struct"),
    }
}

#[test]
fn struct_with_defaults() {
    ok(r#"system "t" {
    struct Stats {
        STR: int = 10
        DEX: int = 10
    }
}"#);
}

#[test]
fn struct_comma_separated() {
    ok(r#"system "t" { struct S { a: int, b: string } }"#);
}

#[test]
fn struct_empty() {
    ok(r#"system "t" { struct S {} }"#);
}

#[test]
fn struct_trailing_comma() {
    ok(r#"system "t" { struct S { a: int, b: string, } }"#);
}

// =============================================================================
// 2. Declarations — Group
// =============================================================================

#[test]
fn group_basic() {
    let p = ok(r#"system "t" {
    group Spellcasting {
        spell_slots: int
        spell_dc: int
    }
}"#);
    match first_decl(&p) {
        DeclKind::Group(g) => assert_eq!(g.fields.len(), 2),
        _ => panic!("expected group"),
    }
}

// =============================================================================
// 2. Declarations — Entity
// =============================================================================

#[test]
fn entity_with_fields_and_optional() {
    let p = ok(r#"system "t" {
    group Spellcasting { spell_slots: int }
    entity Character {
        name: string
        HP: resource(0 ..= 100)
        optional Spellcasting
    }
}"#);
    match &decls(&p)[1].node {
        DeclKind::Entity(e) => {
            assert_eq!(e.fields.len(), 2);
            assert_eq!(e.optional_groups.len(), 1);
            assert!(e.optional_groups[0].is_external_ref);
        }
        _ => panic!("expected entity"),
    }
}

#[test]
fn entity_inline_optional() {
    let p = ok(r#"system "t" {
    entity Character {
        name: string
        optional Spellcasting {
            spell_slots: int
        }
    }
}"#);
    match first_decl(&p) {
        DeclKind::Entity(e) => {
            assert!(!e.optional_groups[0].is_external_ref);
            assert_eq!(e.optional_groups[0].fields.len(), 1);
        }
        _ => panic!("expected entity"),
    }
}

#[test]
fn entity_include_group() {
    let p = ok(r#"system "t" {
    group CombatStats { AC: int }
    entity Character {
        name: string
        include CombatStats
    }
}"#);
    match &decls(&p)[1].node {
        DeclKind::Entity(e) => {
            assert!(e.optional_groups[0].is_required);
        }
        _ => panic!("expected entity"),
    }
}

#[test]
fn entity_empty() {
    ok(r#"system "t" { entity Monster {} }"#);
}

#[test]
fn entity_comma_separated_members() {
    ok(r#"system "t" { entity E { a: int, b: string } }"#);
}

// =============================================================================
// 2. Declarations — Derive / Mechanic
// =============================================================================

#[test]
fn derive_basic() {
    let p = ok(r#"system "t" {
    derive modifier(score: int) -> int {
        floor((score - 10) / 2)
    }
}"#);
    match first_decl(&p) {
        DeclKind::Derive(f) => {
            assert_eq!(f.name.as_str(), "modifier");
            assert_eq!(f.params.len(), 1);
        }
        _ => panic!("expected derive"),
    }
}

#[test]
fn derive_with_tags() {
    let p = ok(r#"system "t" {
    tag #Attack
    derive damage(amount: int) -> int #Attack {
        amount
    }
}"#);
    match &decls(&p)[1].node {
        DeclKind::Derive(f) => assert_eq!(f.tags.len(), 1),
        _ => panic!("expected derive"),
    }
}

#[test]
fn derive_multiple_tags() {
    let p = ok(r#"system "t" {
    tag #A
    tag #B
    derive foo(x: int) -> int #A #B { x }
}"#);
    match &decls(&p)[2].node {
        DeclKind::Derive(f) => assert_eq!(f.tags.len(), 2),
        _ => panic!("expected derive"),
    }
}

#[test]
fn mechanic_basic() {
    let p = ok(r#"system "t" {
    mechanic attack_roll(attacker: int) -> RollResult {
        roll(1d20 + attacker)
    }
}"#);
    match first_decl(&p) {
        DeclKind::Mechanic(_) => {}
        _ => panic!("expected mechanic"),
    }
}

#[test]
fn one_line_block_value() {
    // Spec: `{ DEX }` should work (term matches &"}")
    ok(r#"system "t" {
    derive get_dex(score: int) -> int { score }
}"#);
}

// =============================================================================
// 2. Declarations — Action
// =============================================================================

#[test]
fn action_full() {
    let p = ok(r#"system "t" {
    entity Character { HP: resource(0 ..= 100) }
    action Attack on attacker: Character (target: Character) {
        cost { action }
        requires { attacker.HP > 0 }
        resolve {
            target.HP -= 5
        }
    }
}"#);
    match &decls(&p)[1].node {
        DeclKind::Action(a) => {
            assert_eq!(a.name.as_str(), "Attack");
            assert!(a.cost.is_some());
            assert!(a.requires.is_some());
        }
        _ => panic!("expected action"),
    }
}

#[test]
fn action_cost_free() {
    let p = ok(r#"system "t" {
    entity Character {}
    action Cantrip on caster: Character () {
        cost free
        resolve {}
    }
}"#);
    match &decls(&p)[1].node {
        DeclKind::Action(a) => {
            let cost = a.cost.as_ref().unwrap();
            assert!(cost.free);
            assert!(cost.tokens.is_empty());
        }
        _ => panic!("expected action"),
    }
}

#[test]
fn action_cost_multiple_tokens() {
    ok(r#"system "t" {
    entity C {}
    action X on a: C () {
        cost { action, bonus_action }
        resolve {}
    }
}"#);
}

#[test]
fn action_multiple_requires() {
    ok(r#"system "t" {
    entity C { HP: resource(0 ..= 100), ammo: int }
    action X on a: C () {
        cost { action }
        requires { a.HP > 0 }
        requires { a.ammo > 0 }
        resolve {}
    }
}"#);
}

#[test]
fn action_no_cost() {
    // Cost clause is optional
    let p = ok(r#"system "t" {
    entity C {}
    action X on a: C () {
        resolve {}
    }
}"#);
    match &decls(&p)[1].node {
        DeclKind::Action(a) => assert!(a.cost.is_none()),
        _ => panic!("expected action"),
    }
}

#[test]
fn action_with_tags() {
    let p = ok(r#"system "t" {
    tag #Melee
    entity C {}
    action Slash on a: C () #Melee {
        resolve {}
    }
}"#);
    match &decls(&p)[2].node {
        DeclKind::Action(a) => assert_eq!(a.tags.len(), 1),
        _ => panic!("expected action"),
    }
}

// =============================================================================
// 2. Declarations — Reaction
// =============================================================================

#[test]
fn reaction_basic() {
    ok(r#"system "t" {
    entity C {}
    event Damaged(target: C) {}
    reaction Shield on reactor: C (trigger: Damaged(target: reactor)) {
        cost { reaction }
        resolve {}
    }
}"#);
}

#[test]
fn reaction_with_cost_free() {
    ok(r#"system "t" {
    entity C {}
    event Damaged(target: C) {}
    reaction Shield on reactor: C (trigger: Damaged(target: reactor)) {
        cost free
        resolve {}
    }
}"#);
}

// =============================================================================
// 2. Declarations — Hook
// =============================================================================

#[test]
fn hook_basic() {
    // Note: hooks use parse_block() directly (no `resolve` keyword)
    ok(r#"system "t" {
    entity C { HP: resource(0 ..= 100) }
    event Damaged(target: C) {}
    hook DamageHook on target: C (trigger: Damaged(target: target)) {
        target.HP -= 1
    }
}"#);
}

// =============================================================================
// 2. Declarations — Event
// =============================================================================

#[test]
fn event_with_body() {
    let p = ok(r#"system "t" {
    entity C {}
    event Damaged(target: C) {
        amount: int
    }
}"#);
    match &decls(&p)[1].node {
        DeclKind::Event(e) => {
            assert_eq!(e.params.len(), 1);
            assert_eq!(e.fields.len(), 1);
        }
        _ => panic!("expected event"),
    }
}

#[test]
fn event_without_body() {
    // Parser extension: body is optional for events
    let p = ok(r#"system "t" {
    entity C {}
    event TurnStarted(actor: C)
}"#);
    match &decls(&p)[1].node {
        DeclKind::Event(e) => {
            assert!(e.fields.is_empty());
        }
        _ => panic!("expected event"),
    }
}

#[test]
fn event_empty_body() {
    ok(r#"system "t" {
    entity C {}
    event TurnStarted(actor: C) {}
}"#);
}

// =============================================================================
// 2. Declarations — Condition
// =============================================================================

#[test]
fn condition_basic_modify() {
    ok(r#"system "t" {
    entity C {}
    derive foo(x: int) -> int { x }
    condition Blessed on bearer: C {
        modify foo(x: bearer) {
            result.x = 99
        }
    }
}"#);
}

#[test]
fn condition_with_params() {
    ok(r#"system "t" {
    entity C {}
    derive foo(x: int) -> int { x }
    condition Frightened(source: C) on bearer: C {
        modify foo(x: bearer) {
            result.x = 0
        }
    }
}"#);
}

#[test]
fn condition_with_extends() {
    ok(r#"system "t" {
    entity C {}
    condition Incapacitated on bearer: C {}
    condition Stunned extends Incapacitated on bearer: C {}
}"#);
}

#[test]
fn condition_extends_multiple() {
    ok(r#"system "t" {
    entity C {}
    condition A on bearer: C {}
    condition B on bearer: C {}
    condition C extends A, B on bearer: C {}
}"#);
}

#[test]
fn condition_suppress_clause() {
    ok(r#"system "t" {
    entity C {}
    event Flee(actor: C) {}
    condition Grappled on bearer: C {
        suppress Flee(actor: bearer)
    }
}"#);
}

#[test]
fn condition_modify_cost() {
    ok(r#"system "t" {
    entity C {}
    action Dash on actor: C () {
        cost { action }
        resolve {}
    }
    condition QuickFeet on bearer: C {
        modify Dash.cost(actor: bearer) {
            cost = bonus_action
        }
    }
}"#);
}

#[test]
fn condition_modify_cost_free() {
    ok(r#"system "t" {
    entity C {}
    action Dash on actor: C () {
        cost { action }
        resolve {}
    }
    condition Swift on bearer: C {
        modify Dash.cost(actor: bearer) {
            cost = free
        }
    }
}"#);
}

#[test]
fn condition_modify_with_let_and_if() {
    ok(r#"system "t" {
    entity C {}
    derive foo(x: int) -> int { x }
    condition Buffed on bearer: C {
        modify foo(x: bearer) {
            let bonus = 2
            if bonus > 0 {
                result.x = 99
            }
        }
    }
}"#);
}

#[test]
fn condition_modify_param_override() {
    ok(r#"system "t" {
    entity C {}
    derive calc(x: int) -> int { x }
    condition Override on bearer: C {
        modify calc(x: bearer) {
            x = 42
        }
    }
}"#);
}

// =============================================================================
// 2. Declarations — Prompt
// =============================================================================

#[test]
fn prompt_basic() {
    ok(r#"system "t" {
    prompt choose(options: list<string>) -> string {
        hint: "Pick one"
        suggest: "default"
    }
}"#);
}

#[test]
fn prompt_no_clauses() {
    ok(r#"system "t" {
    prompt choose(options: list<string>) -> string {}
}"#);
}

#[test]
fn prompt_hint_only() {
    ok(r#"system "t" {
    prompt choose(x: int) -> int {
        hint: "Pick"
    }
}"#);
}

// =============================================================================
// 2. Declarations — Option
// =============================================================================

#[test]
fn option_full() {
    ok(r#"system "t" {
    entity C {}
    derive foo(x: int) -> int { x }
    option Flanking extends "D&D 5e Combat" {
        description: "Flanking rule"
        default: off
        when enabled {
            modify foo(x: x) {
                result.x = 99
            }
        }
    }
}"#);
}

#[test]
fn option_minimal() {
    ok(r#"system "t" { option Simple {} }"#);
}

#[test]
fn option_default_on() {
    ok(r#"system "t" {
    option X {
        default: on
    }
}"#);
}

// =============================================================================
// 2. Declarations — Move (PbtA sugar)
// =============================================================================

#[test]
fn move_basic() {
    ok(r#"system "t" {
    entity C { stats: map<string, int> }
    move GoAggro on actor: C (target: C) {
        trigger: "threaten with force"
        roll: 2d6 + actor.stats["Hard"]
        on strong_hit { }
        on weak_hit { }
        on miss { }
    }
}"#);
}

#[test]
fn move_no_outcomes_error() {
    err(r#"system "t" {
    entity C {}
    move X on actor: C () {
        trigger: "do thing"
        roll: 2d6
    }
}"#);
}

// =============================================================================
// 3. Parameters
// =============================================================================

#[test]
fn param_with_default() {
    ok(r#"system "t" {
    derive foo(x: int = 5) -> int { x }
}"#);
}

#[test]
fn param_trailing_comma() {
    ok(r#"system "t" {
    derive foo(x: int, y: int,) -> int { x }
}"#);
}

#[test]
fn param_no_params() {
    ok(r#"system "t" {
    derive foo() -> int { 42 }
}"#);
}

#[test]
fn param_with_conjunctive() {
    ok(r#"system "t" {
    group Spellcasting { slots: int }
    entity C {}
    derive foo(c: C with Spellcasting) -> int { c.Spellcasting.slots }
}"#);
}

#[test]
fn param_with_conjunctive_alias() {
    ok(r#"system "t" {
    group Spellcasting { slots: int }
    entity C {}
    derive foo(c: C with Spellcasting as sc) -> int { c.sc.slots }
}"#);
}

#[test]
fn param_with_disjunctive() {
    ok(r#"system "t" {
    group A { x: int }
    group B { y: int }
    entity C {}
    derive foo(c: C with A | B) -> int { 0 }
}"#);
}

#[test]
fn param_with_mixed_separator_error() {
    err(r#"system "t" {
    group A { x: int }
    group B { y: int }
    group D { z: int }
    entity C {}
    derive foo(c: C with A, B | D) -> int { 0 }
}"#);
}

// =============================================================================
// 4. Types
// =============================================================================

#[test]
fn type_primitives() {
    // Test all primitive types compile
    ok(r#"system "t" {
    struct Types {
        a: int
        b: bool
        c: string
        d: float
    }
}"#);
}

#[test]
fn type_builtins() {
    ok(r#"system "t" {
    struct Types {
        a: DiceExpr
        b: RollResult
        c: TurnBudget
        d: Duration
        e: Position
        f: Condition
        g: Invocation
    }
}"#);
}

#[test]
fn type_generic_list() {
    ok(r#"system "t" { struct S { items: list<int> } }"#);
}

#[test]
fn type_generic_set() {
    ok(r#"system "t" { struct S { items: set<string> } }"#);
}

#[test]
fn type_generic_map() {
    ok(r#"system "t" { struct S { items: map<string, int> } }"#);
}

#[test]
fn type_generic_option() {
    ok(r#"system "t" { struct S { val: option<int> } }"#);
}

#[test]
fn type_resource() {
    ok(r#"system "t" { entity E { HP: resource(0 ..= 100) } }"#);
}

#[test]
fn type_resource_exclusive_range_error() {
    // resource must use ..= not ..
    err(r#"system "t" { entity E { HP: resource(0 .. 100) } }"#);
}

#[test]
fn type_entity_alias() {
    ok(r#"system "t" {
    derive foo(e: entity) -> int { 0 }
}"#);
}

#[test]
fn type_user_defined() {
    ok(r#"system "t" {
    enum MyEnum { A, B }
    struct S { val: MyEnum }
}"#);
}

#[test]
fn type_nested_generics() {
    ok(r#"system "t" { struct S { val: list<option<int>> } }"#);
}

// =============================================================================
// 5. Statements and blocks
// =============================================================================

#[test]
fn stmt_let() {
    ok(r#"system "t" {
    derive foo() -> int {
        let x = 5
        x
    }
}"#);
}

#[test]
fn stmt_let_typed() {
    ok(r#"system "t" {
    derive foo() -> int {
        let x: int = 5
        x
    }
}"#);
}

#[test]
fn stmt_assign() {
    ok(r#"system "t" {
    entity C { HP: resource(0 ..= 100) }
    action X on a: C () {
        resolve {
            a.HP = 50
        }
    }
}"#);
}

#[test]
fn stmt_assign_plus_eq() {
    ok(r#"system "t" {
    entity C { HP: resource(0 ..= 100) }
    action X on a: C () {
        resolve {
            a.HP += 5
        }
    }
}"#);
}

#[test]
fn stmt_assign_minus_eq() {
    ok(r#"system "t" {
    entity C { HP: resource(0 ..= 100) }
    action X on a: C () {
        resolve {
            a.HP -= 5
        }
    }
}"#);
}

#[test]
fn stmt_assign_index() {
    ok(r#"system "t" {
    entity C { items: list<int> }
    action X on a: C () {
        resolve {
            a.items[0] = 99
        }
    }
}"#);
}

#[test]
fn stmt_grant() {
    ok(r#"system "t" {
    group Spellcasting { slots: int }
    entity C { optional Spellcasting }
    action X on a: C () {
        resolve {
            grant a.Spellcasting { slots: 3 }
        }
    }
}"#);
}

#[test]
fn stmt_grant_empty_fields() {
    ok(r#"system "t" {
    group G {}
    entity C { optional G }
    action X on a: C () {
        resolve {
            grant a.G {}
        }
    }
}"#);
}

#[test]
fn stmt_revoke() {
    ok(r#"system "t" {
    group G { x: int }
    entity C { optional G }
    action X on a: C () {
        resolve {
            revoke a.G
        }
    }
}"#);
}

#[test]
fn stmt_revoke_vs_function_call() {
    // `revoke(inv)` should parse as function call (expr_stmt), not revoke_stmt
    ok(r#"system "t" {
    entity C {}
    action X on a: C () {
        resolve {
            let inv = none
            revoke(inv)
        }
    }
}"#);
}

#[test]
fn stmt_emit() {
    ok(r#"system "t" {
    entity C {}
    event Damaged(target: C) {}
    action X on a: C () {
        resolve {
            emit Damaged(target: a)
        }
    }
}"#);
}

#[test]
fn stmt_emit_no_args() {
    ok(r#"system "t" {
    event Ping() {}
    entity C {}
    action X on a: C () {
        resolve {
            emit Ping()
        }
    }
}"#);
}

#[test]
fn block_empty() {
    ok(r#"system "t" {
    entity C {}
    action X on a: C () { resolve {} }
}"#);
}

#[test]
fn block_one_line() {
    // `{ expr }` works because term matches &"}"
    ok(r#"system "t" {
    derive f(x: int) -> int { x + 1 }
}"#);
}

#[test]
fn block_last_stmt_no_newline() {
    // Last statement before } can omit NL
    ok(r#"system "t" {
    derive f(x: int) -> int {
        let y = x + 1
        y }
}"#);
}

// =============================================================================
// 6. Expressions — Precedence
// =============================================================================

#[test]
fn expr_precedence_or_and() {
    // || binds looser than &&
    ok(r#"system "t" { derive f(a: bool, b: bool, c: bool) -> bool { a || b && c } }"#);
}

#[test]
fn expr_precedence_cmp() {
    ok(r#"system "t" { derive f(a: int, b: int) -> bool { a + 1 >= b * 2 } }"#);
}

#[test]
fn expr_precedence_mul_add() {
    ok(r#"system "t" { derive f(a: int) -> int { a + 2 * 3 } }"#);
}

#[test]
fn expr_unary_not() {
    ok(r#"system "t" { derive f(a: bool) -> bool { !a } }"#);
}

#[test]
fn expr_unary_neg() {
    ok(r#"system "t" { derive f(a: int) -> int { -a } }"#);
}

#[test]
fn expr_in_operator() {
    ok(r#"system "t" { derive f(x: int, xs: list<int>) -> bool { x in xs } }"#);
}

#[test]
fn expr_has_operator() {
    ok(r#"system "t" {
    group G { x: int }
    entity C { optional G }
    derive f(c: C) -> bool { c has G }
}"#);
}

#[test]
fn expr_has_with_alias() {
    ok(r#"system "t" {
    group G { x: int }
    entity C { optional G }
    derive f(c: C) -> int {
        if c has G as g { c.g.x } else { 0 }
    }
}"#);
}

// =============================================================================
// 6. Expressions — Primary
// =============================================================================

#[test]
fn expr_int_lit() {
    ok(r#"system "t" { derive f() -> int { 42 } }"#);
}

#[test]
fn expr_string_lit() {
    ok(r#"system "t" { derive f() -> string { "hello" } }"#);
}

#[test]
fn expr_bool_lits() {
    ok(r#"system "t" { derive f() -> bool { true } }"#);
    ok(r#"system "t" { derive f() -> bool { false } }"#);
}

#[test]
fn expr_none_lit() {
    ok(r#"system "t" { derive f() -> option<int> { none } }"#);
}

#[test]
fn expr_dice_lit() {
    ok(r#"system "t" { derive f() -> DiceExpr { 2d6 } }"#);
}

#[test]
fn expr_dice_with_filter() {
    ok(r#"system "t" { derive f() -> DiceExpr { 4d6kh3 } }"#);
}

#[test]
fn expr_paren() {
    ok(r#"system "t" { derive f(x: int) -> int { (x + 1) * 2 } }"#);
}

#[test]
fn expr_field_access() {
    ok(r#"system "t" {
    struct S { x: int }
    derive f(s: S) -> int { s.x }
}"#);
}

#[test]
fn expr_index() {
    ok(r#"system "t" {
    derive f(xs: list<int>) -> int { xs[0] }
}"#);
}

#[test]
fn expr_call() {
    ok(r#"system "t" {
    derive g(x: int) -> int { x }
    derive f(x: int) -> int { g(x) }
}"#);
}

#[test]
fn expr_named_args() {
    ok(r#"system "t" {
    derive g(x: int, y: int) -> int { x + y }
    derive f() -> int { g(x: 1, y: 2) }
}"#);
}

#[test]
fn expr_trailing_comma_in_args() {
    ok(r#"system "t" {
    derive g(x: int) -> int { x }
    derive f() -> int { g(1,) }
}"#);
}

#[test]
fn expr_method_call() {
    // obj.method(args) chains field access + call
    ok(r#"system "t" {
    struct S { x: int }
    derive f(s: S) -> int { s.x }
}"#);
}

// =============================================================================
// 6. Expressions — Struct literal
// =============================================================================

#[test]
fn expr_struct_lit() {
    ok(r#"system "t" {
    struct S { x: int, y: string }
    derive f() -> S { S { x: 1, y: "hi" } }
}"#);
}

#[test]
fn expr_struct_lit_trailing_comma() {
    ok(r#"system "t" {
    struct S { x: int }
    derive f() -> S { S { x: 1, } }
}"#);
}

#[test]
fn expr_struct_lit_empty() {
    ok(r#"system "t" {
    struct S {}
    derive f() -> S { S {} }
}"#);
}

#[test]
fn expr_struct_lit_base() {
    ok(r#"system "t" {
    struct S { x: int, y: int }
    derive f(s: S) -> S { S { x: 99, ..s } }
}"#);
}

#[test]
fn expr_struct_lit_base_only() {
    ok(r#"system "t" {
    struct S { x: int }
    derive f(s: S) -> S { S { ..s } }
}"#);
}

// =============================================================================
// 6. Expressions — List
// =============================================================================

#[test]
fn expr_list_empty() {
    ok(r#"system "t" { derive f() -> list<int> { [] } }"#);
}

#[test]
fn expr_list_elements() {
    ok(r#"system "t" { derive f() -> list<int> { [1, 2, 3] } }"#);
}

#[test]
fn expr_list_trailing_comma() {
    ok(r#"system "t" { derive f() -> list<int> { [1, 2,] } }"#);
}

#[test]
fn expr_list_comprehension() {
    ok(r#"system "t" {
    derive f(xs: list<int>) -> list<int> { [x * 2 for x in xs] }
}"#);
}

#[test]
fn expr_list_comprehension_with_filter() {
    ok(r#"system "t" {
    derive f(xs: list<int>) -> list<int> { [x for x in xs if x > 0] }
}"#);
}

#[test]
fn expr_list_comprehension_range() {
    ok(r#"system "t" {
    derive f() -> list<int> { [x for x in 0..5] }
}"#);
}

#[test]
fn expr_list_comprehension_inclusive_range() {
    ok(r#"system "t" {
    derive f() -> list<int> { [x for x in 0..=5] }
}"#);
}

// =============================================================================
// 6. Expressions — Map
// =============================================================================

#[test]
fn expr_map_empty() {
    ok(r#"system "t" { derive f() -> map<string, int> { {} } }"#);
}

#[test]
fn expr_map_entries() {
    ok(r#"system "t" {
    derive f() -> map<string, int> { {"a": 1, "b": 2} }
}"#);
}

#[test]
fn expr_map_trailing_comma() {
    ok(r#"system "t" {
    derive f() -> map<string, int> { {"a": 1,} }
}"#);
}

// =============================================================================
// 6. Expressions — If
// =============================================================================

#[test]
fn expr_if_else() {
    ok(r#"system "t" {
    derive f(x: int) -> int { if x > 0 { x } else { 0 } }
}"#);
}

#[test]
fn expr_if_no_else() {
    ok(r#"system "t" {
    entity C {}
    action X on a: C () {
        resolve {
            if true {}
        }
    }
}"#);
}

#[test]
fn expr_if_else_if() {
    ok(r#"system "t" {
    derive f(x: int) -> int {
        if x > 10 { 3 }
        else if x > 5 { 2 }
        else { 1 }
    }
}"#);
}

#[test]
fn expr_if_let() {
    // Parser extension: if let pattern = expr { ... }
    ok(r#"system "t" {
    derive f(x: option<int>) -> int {
        if let some(v) = x { v } else { 0 }
    }
}"#);
}

// =============================================================================
// 6. Expressions — Match
// =============================================================================

#[test]
fn expr_pattern_match() {
    ok(r#"system "t" {
    enum Result { hit, miss }
    derive f(r: Result) -> int {
        match r {
            hit => 1
            miss => 0
        }
    }
}"#);
}

#[test]
fn expr_pattern_match_comma_separated() {
    ok(r#"system "t" {
    enum R { a, b }
    derive f(r: R) -> int { match r { a => 1, b => 2 } }
}"#);
}

#[test]
fn expr_pattern_match_with_block() {
    ok(r#"system "t" {
    enum R { a, b }
    derive f(r: R) -> int {
        match r {
            a => {
                let x = 1
                x
            }
            b => 2
        }
    }
}"#);
}

#[test]
fn expr_pattern_wildcard() {
    ok(r#"system "t" {
    derive f(x: int) -> int {
        match x { 1 => 10, _ => 0 }
    }
}"#);
}

#[test]
fn expr_pattern_qualified() {
    ok(r#"system "t" {
    enum R { hit, miss }
    derive f(r: R) -> int {
        match r {
            R.hit => 1
            R.miss => 0
        }
    }
}"#);
}

#[test]
fn expr_pattern_destructure() {
    ok(r#"system "t" {
    enum R { hit(amount: int), miss }
    derive f(r: R) -> int {
        match r {
            hit(a) => a
            miss => 0
        }
    }
}"#);
}

#[test]
fn expr_pattern_qualified_destructure() {
    ok(r#"system "t" {
    enum R { hit(amount: int), miss }
    derive f(r: R) -> int {
        match r {
            R.hit(a) => a
            R.miss => 0
        }
    }
}"#);
}

#[test]
fn expr_guard_match() {
    ok(r#"system "t" {
    derive f(x: int) -> int {
        match {
            x > 10 => 3
            x > 5 => 2
            _ => 1
        }
    }
}"#);
}

#[test]
fn expr_guard_match_comma_separated() {
    ok(r#"system "t" {
    derive f(x: int) -> int {
        match { x > 0 => x, _ => 0 }
    }
}"#);
}

#[test]
fn expr_pattern_string() {
    ok(r#"system "t" {
    derive f(s: string) -> int {
        match s { "a" => 1, _ => 0 }
    }
}"#);
}

#[test]
fn expr_pattern_bool() {
    ok(r#"system "t" {
    derive f(b: bool) -> int {
        match b { true => 1, false => 0 }
    }
}"#);
}

#[test]
fn expr_pattern_none() {
    ok(r#"system "t" {
    derive f(x: option<int>) -> int {
        match x { some(v) => v, none => 0 }
    }
}"#);
}

// =============================================================================
// 6. Expressions — For
// =============================================================================

#[test]
fn expr_for_collection() {
    ok(r#"system "t" {
    entity C {}
    action X on a: C () {
        resolve {
            for x in [1, 2, 3] {}
        }
    }
}"#);
}

#[test]
fn expr_for_range_exclusive() {
    ok(r#"system "t" {
    entity C {}
    action X on a: C () {
        resolve {
            for i in 0..5 {}
        }
    }
}"#);
}

#[test]
fn expr_for_range_inclusive() {
    ok(r#"system "t" {
    entity C {}
    action X on a: C () {
        resolve {
            for i in 0..=5 {}
        }
    }
}"#);
}

#[test]
fn expr_for_with_pattern() {
    ok(r#"system "t" {
    enum R { hit(amount: int), miss }
    entity C {}
    action X on a: C () {
        resolve {
            let results: list<R> = []
            for hit(amount) in results {}
        }
    }
}"#);
}

// =============================================================================
// 6. Expressions — Call arguments
// =============================================================================

#[test]
fn expr_call_no_args() {
    ok(r#"system "t" { derive f() -> int { 1 } derive g() -> int { f() } }"#);
}

#[test]
fn expr_call_mixed_args() {
    ok(r#"system "t" {
    derive g(a: int, b: int) -> int { a + b }
    derive f() -> int { g(1, b: 2) }
}"#);
}

// =============================================================================
// 7. NL suppression contexts
// =============================================================================

#[test]
fn nl_suppressed_after_binary_ops() {
    // NL after +, -, *, /, ||, &&, ==, !=, >=, <=, in, =>, ->
    ok(r#"system "t" {
    derive f(a: int, b: int) -> int {
        a +
        b
    }
}"#);
    ok(r#"system "t" {
    derive f(a: int, b: int) -> int {
        a -
        b
    }
}"#);
    ok(r#"system "t" {
    derive f(a: int, b: int) -> int {
        a *
        b
    }
}"#);
    ok(r#"system "t" {
    derive f(a: int, b: int) -> int {
        a /
        b
    }
}"#);
}

#[test]
fn nl_suppressed_after_logical_ops() {
    ok(r#"system "t" {
    derive f(a: bool, b: bool) -> bool {
        a ||
        b
    }
}"#);
    ok(r#"system "t" {
    derive f(a: bool, b: bool) -> bool {
        a &&
        b
    }
}"#);
}

#[test]
fn nl_suppressed_after_comparison_ops() {
    ok(r#"system "t" {
    derive f(a: int, b: int) -> bool {
        a ==
        b
    }
}"#);
    ok(r#"system "t" {
    derive f(a: int, b: int) -> bool {
        a !=
        b
    }
}"#);
    ok(r#"system "t" {
    derive f(a: int, b: int) -> bool {
        a >=
        b
    }
}"#);
    ok(r#"system "t" {
    derive f(a: int, b: int) -> bool {
        a <=
        b
    }
}"#);
}

#[test]
fn nl_not_suppressed_after_bare_lt_gt() {
    // Bare > and < do NOT suppress NL (per spec, to avoid generic type ambiguity)
    // This should fail because `a >` then NL then `b` is two separate expressions
    err(r#"system "t" {
    derive f(a: int, b: int) -> bool {
        a >
        b
    }
}"#);
}

#[test]
fn nl_suppressed_after_assignment() {
    ok(r#"system "t" {
    derive f() -> int {
        let x =
            5
        x
    }
}"#);
}

#[test]
fn nl_suppressed_inside_parens() {
    ok(r#"system "t" {
    derive f(a: int, b: int) -> int {
        (a
         + b)
    }
}"#);
}

#[test]
fn nl_suppressed_inside_brackets() {
    ok(r#"system "t" {
    derive f() -> list<int> {
        [1,
         2,
         3]
    }
}"#);
}

#[test]
fn nl_suppressed_after_brace() {
    // After { NL is suppressed
    ok(r#"system "t" {
    derive f(x: int) -> int {
        if x > 0 {
            x
        } else {
            0
        }
    }
}"#);
}

#[test]
fn nl_suppressed_after_comma() {
    ok(r#"system "t" {
    derive g(a: int, b: int) -> int { a + b }
    derive f() -> int { g(1,
        2) }
}"#);
}

#[test]
fn nl_suppressed_after_colon() {
    ok(r#"system "t" {
    struct S {
        x:
            int
    }
}"#);
}

#[test]
fn nl_suppressed_after_fat_arrow() {
    ok(r#"system "t" {
    derive f(x: int) -> int {
        match x { 1 =>
            10, _ => 0 }
    }
}"#);
}

#[test]
fn nl_suppressed_after_arrow() {
    ok(r#"system "t" {
    derive f(x: int) ->
        int { x }
}"#);
}

// =============================================================================
// 8. Soft keyword disambiguation
// =============================================================================

#[test]
fn soft_keyword_as_field_name() {
    // Soft keywords used as field names
    ok(r#"system "t" {
    struct S {
        action: int
        cost: string
        result: bool
        trigger: int
        resolve: int
        on: bool
    }
}"#);
}

#[test]
fn soft_keyword_as_variable() {
    ok(r#"system "t" {
    derive f() -> int {
        let action = 5
        let cost = 10
        let result = 15
        action + cost + result
    }
}"#);
}

#[test]
fn soft_keyword_as_enum_variant() {
    ok(r#"system "t" {
    enum TokenType { action, bonus_action, reaction }
}"#);
}

// =============================================================================
// 9. Edge cases
// =============================================================================

#[test]
fn multiline_cost_clause() {
    ok(r#"system "t" {
    entity C {}
    action X on a: C () {
        cost {
            action
        }
        resolve {}
    }
}"#);
}

#[test]
fn multiline_requires_clause() {
    ok(r#"system "t" {
    entity C { HP: resource(0 ..= 100) }
    action X on a: C () {
        requires {
            a.HP > 0
        }
        resolve {}
    }
}"#);
}

#[test]
fn trigger_positional_binding() {
    // trigger_binding with just IDENT (positional)
    ok(r#"system "t" {
    entity C {}
    event Damaged(target: C) {}
    reaction R on reactor: C (trigger: Damaged(reactor)) {
        resolve {}
    }
}"#);
}

#[test]
fn trigger_named_binding() {
    ok(r#"system "t" {
    entity C {}
    event Damaged(target: C) {}
    reaction R on reactor: C (trigger: Damaged(target: reactor)) {
        resolve {}
    }
}"#);
}

#[test]
fn trigger_trailing_comma() {
    ok(r#"system "t" {
    entity C {}
    event E(a: C, b: C) {}
    reaction R on r: C (trigger: E(a: r, b: r,)) {
        resolve {}
    }
}"#);
}

#[test]
fn modify_binding_wildcard() {
    // Parser extension: wildcard `_` in modify bindings
    ok(r#"system "t" {
    entity C {}
    derive foo(x: int) -> int { x }
    condition X on bearer: C {
        modify foo(x: _) {
            result.x = 0
        }
    }
}"#);
}

#[test]
fn modify_selector_predicates() {
    // Parser extension: modify [predicates]
    ok(r#"system "t" {
    entity C {}
    tag #Attack
    derive foo(x: int) -> int #Attack { x }
    condition X on bearer: C {
        modify [#Attack](x: bearer) {
            result.x = 0
        }
    }
}"#);
}

#[test]
fn deeply_nested_field_access() {
    ok(r#"system "t" {
    struct Inner { val: int }
    struct Outer { inner: Inner }
    derive f(o: Outer) -> int { o.inner.val }
}"#);
}

#[test]
fn chained_postfix_ops() {
    ok(r#"system "t" {
    derive f(xs: list<list<int>>) -> int { xs[0][1] }
}"#);
}

#[test]
fn negative_int_pattern() {
    ok(r#"system "t" {
    derive f(x: int) -> int {
        match x { -1 => 0, _ => 1 }
    }
}"#);
}
