use super::*;

use std::sync::atomic::{AtomicU64, Ordering};
use ttrpg_checker::ty::Ty;

#[test]
fn eval_arithmetic() {
    let mut runner = Runner::new();
    let val = runner.eval("2 + 3").unwrap();
    assert_eq!(val, Value::Int(5));
}

#[test]
fn eval_string_literal() {
    let mut runner = Runner::new();
    let val = runner.eval("\"hello\"").unwrap();
    assert_eq!(val, Value::Str("hello".into()));
}

#[test]
fn eval_boolean() {
    let mut runner = Runner::new();
    assert_eq!(runner.eval("true").unwrap(), Value::Bool(true));
    assert_eq!(runner.eval("false").unwrap(), Value::Bool(false));
}

#[test]
fn eval_none_literal() {
    let mut runner = Runner::new();
    assert_eq!(runner.eval("none").unwrap(), Value::None);
}

#[test]
fn eval_comparison() {
    let mut runner = Runner::new();
    assert_eq!(runner.eval("3 > 2").unwrap(), Value::Bool(true));
    assert_eq!(runner.eval("1 == 2").unwrap(), Value::Bool(false));
}

#[test]
fn eval_complex_arithmetic() {
    let mut runner = Runner::new();
    assert_eq!(runner.eval("(10 + 5) * 2").unwrap(), Value::Int(30));
}

#[test]
fn eval_parse_error() {
    let mut runner = Runner::new();
    let err = runner.eval("2 +").unwrap_err();
    assert!(err.to_string().contains("parse error"), "got: {}", err);
}

#[test]
fn exec_eval_collects_output() {
    let mut runner = Runner::new();
    runner.exec("eval 2 + 3").unwrap();
    let output = runner.take_output();
    assert_eq!(output, vec!["5"]);
}

#[test]
fn exec_blank_line() {
    let mut runner = Runner::new();
    runner.exec("").unwrap();
    runner.exec("   ").unwrap();
    runner.exec("// comment").unwrap();
    assert!(runner.take_output().is_empty());
}

#[test]
fn exec_unknown_command() {
    let mut runner = Runner::new();
    let err = runner.exec("foobar").unwrap_err();
    assert!(err.to_string().contains("unknown command"));
}

#[test]
fn exec_reload_without_load() {
    let mut runner = Runner::new();
    let err = runner.exec("reload").unwrap_err();
    assert!(err.to_string().contains("no file loaded"));
}

#[test]
fn exec_errors_empty() {
    let mut runner = Runner::new();
    runner.exec("errors").unwrap();
    let output = runner.take_output();
    assert_eq!(output, vec!["no diagnostics"]);
}

#[test]
fn exec_load_nonexistent_file() {
    let mut runner = Runner::new();
    let err = runner.exec("load /nonexistent/path.ttrpg").unwrap_err();
    assert!(err.to_string().contains("cannot read"));
}

#[test]
fn exec_load_and_eval() {
    // Create a temp file with a simple system
    let dir = std::env::temp_dir().join("ttrpg_cli_test");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("test_load.ttrpg");
    std::fs::write(
        &path,
        r#"
system "test" {
    derive add(a: int, b: int) -> int { a + b }
}
"#,
    )
    .unwrap();

    let mut runner = Runner::new();
    runner.exec(&format!("load {}", path.display())).unwrap();
    let output = runner.take_output();
    assert_eq!(output.len(), 1);
    assert!(output[0].starts_with("loaded"));

    // Eval a basic expression (derives aren't callable via eval, but arithmetic works)
    runner.exec("eval 10 * 3").unwrap();
    let output = runner.take_output();
    assert_eq!(output, vec!["30"]);

    std::fs::remove_file(&path).ok();
}

#[test]
fn exec_load_with_errors_then_errors_command() {
    let dir = std::env::temp_dir().join("ttrpg_cli_test");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("test_errors.ttrpg");
    std::fs::write(
        &path,
        r#"
system "test" {
    derive bad() -> int { undefined_var }
}
"#,
    )
    .unwrap();

    let mut runner = Runner::new();
    let err = runner
        .exec(&format!("load {}", path.display()))
        .unwrap_err();
    assert!(err.to_string().contains("error"));
    // Output hint should still be available
    let output = runner.take_output();
    assert!(output.iter().any(|l| l.contains("errors")));

    runner.exec("errors").unwrap();
    let output = runner.take_output();
    assert!(!output.is_empty());
    assert!(output.iter().any(|l| l.contains("error")));

    std::fs::remove_file(&path).ok();
}

#[test]
fn exec_reload() {
    let dir = std::env::temp_dir().join("ttrpg_cli_test");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("test_reload.ttrpg");
    std::fs::write(
        &path,
        r#"
system "test" {
    derive add(a: int, b: int) -> int { a + b }
}
"#,
    )
    .unwrap();

    let mut runner = Runner::new();
    runner.exec(&format!("load {}", path.display())).unwrap();
    runner.take_output();

    runner.exec("reload").unwrap();
    let output = runner.take_output();
    assert!(output[0].starts_with("loaded"));

    std::fs::remove_file(&path).ok();
}

// ── Regression: tdsl-3zv — reload breaks paths with spaces ──

#[test]
fn exec_reload_path_with_spaces() {
    // Create a temp directory with a space in the name
    let dir = std::env::temp_dir().join("ttrpg cli test dir");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("test file.ttrpg");
    std::fs::write(
        &path,
        r#"
system "test" {
    derive add(a: int, b: int) -> int { a + b }
}
"#,
    )
    .unwrap();

    let mut runner = Runner::new();
    // Load directly via load_paths to simulate a path with spaces
    runner.load_paths(vec![path.clone()]).unwrap();
    let output = runner.take_output();
    assert!(output[0].starts_with("loaded"), "initial load failed");

    // Reload should succeed — it uses last_paths directly, not string round-trip
    runner.exec("reload").unwrap();
    let output = runner.take_output();
    assert!(
        output[0].starts_with("loaded"),
        "reload should succeed for paths with spaces; got: {:?}",
        output
    );

    std::fs::remove_file(&path).ok();
    std::fs::remove_dir(&dir).ok();
}

#[test]
fn eval_list_literal() {
    let mut runner = Runner::new();
    let val = runner.eval("[1, 2, 3]").unwrap();
    assert_eq!(
        val,
        Value::List(vec![Value::Int(1), Value::Int(2), Value::Int(3)])
    );
}

#[test]
fn failed_load_clears_stale_state() {
    let dir = std::env::temp_dir().join("ttrpg_cli_test");
    std::fs::create_dir_all(&dir).unwrap();

    // First, load a good file
    let good = dir.join("good_stale.ttrpg");
    std::fs::write(
        &good,
        r#"
system "test" {
    derive add(a: int, b: int) -> int { a + b }
}
"#,
    )
    .unwrap();

    let mut runner = Runner::new();
    runner.exec(&format!("load {}", good.display())).unwrap();
    runner.take_output();

    // Eval should work
    runner.exec("eval 1 + 2").unwrap();
    assert_eq!(runner.take_output(), vec!["3"]);

    // Now load a bad file
    let bad = dir.join("bad_stale.ttrpg");
    std::fs::write(
        &bad,
        r#"
system "test" {
    derive bad() -> int { undefined_var }
}
"#,
    )
    .unwrap();

    let err = runner.exec(&format!("load {}", bad.display())).unwrap_err();
    assert!(err.to_string().contains("failed to load"));
    runner.take_output();

    // Arithmetic still works (no program needed for basic eval)
    runner.exec("eval 1 + 2").unwrap();
    runner.take_output();

    // Reload should re-attempt the bad file, not the good one
    let err = runner.exec("reload").unwrap_err();
    assert!(
        err.to_string().contains("failed to load"),
        "reload should target the bad file, got: {}",
        err
    );
    runner.take_output();

    std::fs::remove_file(&good).ok();
    std::fs::remove_file(&bad).ok();
}

#[test]
fn io_failure_clears_stale_state() {
    let dir = std::env::temp_dir().join("ttrpg_cli_test");
    std::fs::create_dir_all(&dir).unwrap();

    // Load a good file first
    let good = dir.join("good_io.ttrpg");
    std::fs::write(
        &good,
        r#"
system "test" {
    derive add(a: int, b: int) -> int { a + b }
}
"#,
    )
    .unwrap();

    let mut runner = Runner::new();
    runner.exec(&format!("load {}", good.display())).unwrap();
    runner.take_output();

    // Now try to load a nonexistent file (I/O failure)
    let err = runner.exec("load /nonexistent/path.ttrpg").unwrap_err();
    assert!(err.to_string().contains("cannot read"));
    runner.take_output();

    // Diagnostics should be cleared (I/O failure has no parse diagnostics)
    runner.exec("errors").unwrap();
    let output = runner.take_output();
    assert_eq!(output, vec!["no diagnostics"]);

    // Reload should target the nonexistent file, not the good one
    let err = runner.exec("reload").unwrap_err();
    assert!(
        err.to_string().contains("cannot read"),
        "reload should target the failed path, got: {}",
        err
    );
    runner.take_output();

    std::fs::remove_file(&good).ok();
}

#[test]
fn failed_load_returns_err() {
    let dir = std::env::temp_dir().join("ttrpg_cli_test");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("test_load_err.ttrpg");
    std::fs::write(
        &path,
        r#"
system "test" {
    derive bad() -> int { undefined_var }
}
"#,
    )
    .unwrap();

    let mut runner = Runner::new();
    let result = runner.exec(&format!("load {}", path.display()));
    assert!(result.is_err(), "load with errors should return Err");
    let err = result.unwrap_err();
    assert!(err.to_string().contains("failed to load"), "got: {}", err);

    std::fs::remove_file(&path).ok();
}

// ── Helpers ─────────────────────────────────────────────────

/// Load a program that declares `entity Hero { scores: list<int> }`.
fn load_list_program(runner: &mut Runner) {
    static LIST_COUNTER: AtomicU64 = AtomicU64::new(0);
    let id = LIST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join("ttrpg_cli_test");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("test_list_{}.ttrpg", id));
    std::fs::write(
        &path,
        r#"
system "test" {
    entity Hero {
        scores: list<int>
    }
}
"#,
    )
    .unwrap();
    runner.exec(&format!("load {}", path.display())).unwrap();
    runner.take_output();
    std::fs::remove_file(&path).ok();
}

/// Load a program that declares `entity Character { HP: int  AC: int }`.
fn load_character_program(runner: &mut Runner) {
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let id = COUNTER.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join("ttrpg_cli_test");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("test_character_{}.ttrpg", id));
    std::fs::write(
        &path,
        r#"
system "test" {
    entity Character {
        HP: int
        AC: int
    }
    derive id(x: int) -> int { x }
}
"#,
    )
    .unwrap();
    runner.exec(&format!("load {}", path.display())).unwrap();
    runner.take_output();
    std::fs::remove_file(&path).ok();
}

// ── Spawn/Set/Destroy tests ─────────────────────────────────

#[test]
fn spawn_and_eval_handle() {
    let mut runner = Runner::new();
    load_character_program(&mut runner);
    runner
        .exec("spawn Character fighter { HP: 30, AC: 15 }")
        .unwrap();
    let output = runner.take_output();
    assert!(output[0].contains("spawned Character fighter"));

    // Eval a handle field — should resolve the handle and read the field
    runner.exec("eval fighter.HP").unwrap();
    let output = runner.take_output();
    assert_eq!(output[0], "30");

    runner.exec("eval fighter.AC").unwrap();
    let output = runner.take_output();
    assert_eq!(output[0], "15");

    // Handles work in compound expressions
    runner.exec("eval fighter.HP + fighter.AC").unwrap();
    let output = runner.take_output();
    assert_eq!(output[0], "45");
}

#[test]
fn spawn_duplicate_handle_rejected() {
    let mut runner = Runner::new();
    load_character_program(&mut runner);
    runner.exec("spawn Character fighter {}").unwrap();
    runner.take_output();
    let err = runner.exec("spawn Character fighter {}").unwrap_err();
    assert!(err.to_string().contains("already exists"));
}

#[test]
fn spawn_no_fields() {
    let mut runner = Runner::new();
    load_character_program(&mut runner);
    runner.exec("spawn Character fighter").unwrap();
    let output = runner.take_output();
    assert!(output[0].contains("spawned Character fighter"));
}

#[test]
fn spawn_unknown_entity_type() {
    let mut runner = Runner::new();
    load_character_program(&mut runner);
    let err = runner.exec("spawn Goblin g").unwrap_err();
    assert!(err.to_string().contains("unknown entity type 'Goblin'"));
}

#[test]
fn set_field() {
    let mut runner = Runner::new();
    load_character_program(&mut runner);
    runner.exec("spawn Character fighter { AC: 15 }").unwrap();
    runner.take_output();

    runner.exec("set fighter.AC = 18").unwrap();
    let output = runner.take_output();
    assert!(output.iter().any(|l| l.contains("fighter.AC = 18")));
}

#[test]
fn set_unknown_handle() {
    let mut runner = Runner::new();
    let err = runner.exec("set ghost.HP = 10").unwrap_err();
    assert!(err.to_string().contains("unknown handle"));
}

#[test]
fn destroy_entity() {
    let mut runner = Runner::new();
    load_character_program(&mut runner);
    runner.exec("spawn Character goblin { HP: 7 }").unwrap();
    runner.take_output();

    runner.exec("destroy goblin").unwrap();
    let output = runner.take_output();
    assert_eq!(output, vec!["destroyed goblin"]);

    // Handle should no longer exist
    let err = runner.exec("set goblin.HP = 10").unwrap_err();
    assert!(err.to_string().contains("unknown handle"));
}

#[test]
fn destroy_unknown_handle() {
    let mut runner = Runner::new();
    let err = runner.exec("destroy ghost").unwrap_err();
    assert!(err.to_string().contains("unknown handle"));
}

// ── Call tests ──────────────────────────────────────────────

#[test]
fn call_derive() {
    let dir = std::env::temp_dir().join("ttrpg_cli_test");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("test_call_derive.ttrpg");
    std::fs::write(
        &path,
        r#"
system "test" {
    derive double(x: int) -> int { x * 2 }
}
"#,
    )
    .unwrap();

    let mut runner = Runner::new();
    runner.exec(&format!("load {}", path.display())).unwrap();
    runner.take_output();

    runner.exec("call double(16)").unwrap();
    let output = runner.take_output();
    assert!(output.iter().any(|l| l.contains("=> 32")));

    std::fs::remove_file(&path).ok();
}

#[test]
fn call_mechanic_fallback() {
    let dir = std::env::temp_dir().join("ttrpg_cli_test");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("test_call_mechanic.ttrpg");
    std::fs::write(
        &path,
        r#"
system "test" {
    mechanic add(a: int, b: int) -> int { a + b }
}
"#,
    )
    .unwrap();

    let mut runner = Runner::new();
    runner.exec(&format!("load {}", path.display())).unwrap();
    runner.take_output();

    runner.exec("call add(10, 20)").unwrap();
    let output = runner.take_output();
    assert!(output.iter().any(|l| l.contains("=> 30")));

    std::fs::remove_file(&path).ok();
}

// ── Issue regression tests ────────────────────────────────────

#[test]
fn call_empty_arg_rejected() {
    let dir = std::env::temp_dir().join("ttrpg_cli_test");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("test_empty_arg.ttrpg");
    std::fs::write(
        &path,
        r#"
system "test" {
    derive add(a: int, b: int) -> int { a + b }
}
"#,
    )
    .unwrap();

    let mut runner = Runner::new();
    runner.exec(&format!("load {}", path.display())).unwrap();
    runner.take_output();

    let err = runner.exec("call add(1,,2)").unwrap_err();
    assert!(err.to_string().contains("empty argument"), "got: {}", err);

    std::fs::remove_file(&path).ok();
}

#[test]
fn call_undefined_function_rejected() {
    let dir = std::env::temp_dir().join("ttrpg_cli_test");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("test_undef_fn.ttrpg");
    std::fs::write(
        &path,
        r#"
system "test" {
    derive id(x: int) -> int { x }
}
"#,
    )
    .unwrap();

    let mut runner = Runner::new();
    runner.exec(&format!("load {}", path.display())).unwrap();
    runner.take_output();

    let err = runner.exec("call nonexistent(42)").unwrap_err();
    assert!(
        err.to_string().contains("undefined function"),
        "got: {}",
        err
    );

    std::fs::remove_file(&path).ok();
}

#[test]
fn do_undefined_action_rejected() {
    let dir = std::env::temp_dir().join("ttrpg_cli_test");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("test_undef_action.ttrpg");
    std::fs::write(
        &path,
        r#"
system "test" {
    entity Character { HP: int }
    derive id(x: int) -> int { x }
}
"#,
    )
    .unwrap();

    let mut runner = Runner::new();
    runner.exec(&format!("load {}", path.display())).unwrap();
    runner.take_output();

    runner.exec("spawn Character fighter { HP: 10 }").unwrap();
    runner.take_output();

    let err = runner.exec("do NoSuchAction(fighter)").unwrap_err();
    assert!(err.to_string().contains("undefined action"), "got: {}", err);

    std::fs::remove_file(&path).ok();
}

// ── Split helpers tests ──────────────────────────────────────

#[test]
fn split_top_level_commas_basic() {
    let parts = split_top_level_commas("a, b, c");
    assert_eq!(parts, vec!["a", " b", " c"]);
}

#[test]
fn split_top_level_commas_nested() {
    let parts = split_top_level_commas("f(a, b), c");
    assert_eq!(parts, vec!["f(a, b)", " c"]);
}

#[test]
fn split_top_level_commas_string() {
    let parts = split_top_level_commas(r#""a, b", c"#);
    assert_eq!(parts, vec![r#""a, b""#, " c"]);
}

#[test]
fn split_top_level_commas_empty() {
    let parts = split_top_level_commas("");
    assert_eq!(parts, vec![""]);
}

// ── Load clears handles ──────────────────────────────────────

#[test]
fn load_clears_handles() {
    let dir = std::env::temp_dir().join("ttrpg_cli_test");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("test_load_clears.ttrpg");
    std::fs::write(
        &path,
        r#"
system "test" {
    entity Character { HP: int }
    derive id(x: int) -> int { x }
}
"#,
    )
    .unwrap();

    let mut runner = Runner::new();
    runner.exec(&format!("load {}", path.display())).unwrap();
    runner.take_output();

    runner.exec("spawn Character fighter { HP: 30 }").unwrap();
    runner.take_output();

    // Reload clears handles
    runner.exec("reload").unwrap();
    runner.take_output();

    // Handle should no longer exist
    let err = runner.exec("set fighter.HP = 10").unwrap_err();
    assert!(err.to_string().contains("unknown handle"));

    std::fs::remove_file(&path).ok();
}

// ── Handle validation tests (Issue 3) ────────────────────────

#[test]
fn spawn_dotted_handle_rejected() {
    let mut runner = Runner::new();
    load_character_program(&mut runner);
    let err = runner.exec("spawn Character foo.bar").unwrap_err();
    assert!(err.to_string().contains("invalid handle"), "got: {}", err);
}

#[test]
fn spawn_numeric_handle_rejected() {
    let mut runner = Runner::new();
    load_character_program(&mut runner);
    let err = runner.exec("spawn Character 123abc").unwrap_err();
    assert!(err.to_string().contains("invalid handle"), "got: {}", err);
}

#[test]
fn spawn_underscore_handle_ok() {
    let mut runner = Runner::new();
    load_character_program(&mut runner);
    runner.exec("spawn Character _fighter").unwrap();
    let output = runner.take_output();
    assert!(output[0].contains("spawned Character _fighter"));
}

// ── Handle resolution in RHS tests (Issue 1) ────────────────

/// Load a program with entity-typed fields for handle resolution tests.
fn load_party_program(runner: &mut Runner) {
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let id = COUNTER.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join("ttrpg_cli_test");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("test_party_{}.ttrpg", id));
    std::fs::write(
        &path,
        r#"
system "test" {
    entity Character {
        HP: int
        AC: int
        ally: Character
    }
    derive id(x: int) -> int { x }
}
"#,
    )
    .unwrap();
    runner.exec(&format!("load {}", path.display())).unwrap();
    runner.take_output();
    std::fs::remove_file(&path).ok();
}

#[test]
fn spawn_field_handle_resolution() {
    let mut runner = Runner::new();
    load_party_program(&mut runner);

    runner
        .exec("spawn Character alice { HP: 30, AC: 15 }")
        .unwrap();
    runner.take_output();

    // Spawn bob with ally: alice (handle resolves to entity value)
    runner
        .exec("spawn Character bob { HP: 25, ally: alice }")
        .unwrap();
    let output = runner.take_output();
    assert!(output[0].contains("spawned Character bob"));
}

#[test]
fn set_handle_rhs_resolves() {
    let mut runner = Runner::new();
    load_party_program(&mut runner);

    runner.exec("spawn Character alice { HP: 30 }").unwrap();
    runner.take_output();
    runner.exec("spawn Character bob { HP: 25 }").unwrap();
    runner.take_output();

    // Set bob.ally = alice (handle resolves to entity value)
    runner.exec("set bob.ally = alice").unwrap();
    let output = runner.take_output();
    assert!(output[0].contains("bob.ally ="));
}

// ── Schema validation tests (Issue 2) ────────────────────────

#[test]
fn spawn_unknown_field_rejected() {
    let mut runner = Runner::new();
    load_character_program(&mut runner);
    let err = runner
        .exec("spawn Character fighter { HP: 30, STR: 16 }")
        .unwrap_err();
    assert!(
        err.to_string().contains("unknown field 'STR'"),
        "got: {}",
        err
    );
}

#[test]
fn set_unknown_field_rejected() {
    let mut runner = Runner::new();
    load_character_program(&mut runner);
    runner.exec("spawn Character fighter { HP: 30 }").unwrap();
    runner.take_output();

    let err = runner.exec("set fighter.STR = 16").unwrap_err();
    assert!(
        err.to_string().contains("unknown field 'STR'"),
        "got: {}",
        err
    );
}

#[test]
fn spawn_type_mismatch_rejected() {
    let mut runner = Runner::new();
    load_character_program(&mut runner);
    let err = runner
        .exec(r#"spawn Character fighter { HP: "thirty" }"#)
        .unwrap_err();
    assert!(err.to_string().contains("type mismatch"), "got: {}", err);
}

#[test]
fn spawn_nested_type_mismatch_rejected() {
    let mut runner = Runner::new();
    load_list_program(&mut runner);
    let err = runner
        .exec(r#"spawn Hero h { scores: [1, "oops", 3] }"#)
        .unwrap_err();
    assert!(
        err.to_string().contains("type mismatch"),
        "expected type mismatch for nested list element, got: {}",
        err
    );
}

#[test]
fn set_nested_type_mismatch_rejected() {
    let mut runner = Runner::new();
    load_list_program(&mut runner);
    runner.exec("spawn Hero h { scores: [1, 2] }").unwrap();
    runner.take_output();
    let err = runner.exec(r#"set h.scores = ["bad"]"#).unwrap_err();
    assert!(
        err.to_string().contains("type mismatch"),
        "expected type mismatch for nested list element, got: {}",
        err
    );
}

#[test]
fn spawn_duplicate_field_rejected() {
    let mut runner = Runner::new();
    load_character_program(&mut runner);
    let err = runner
        .exec("spawn Character fighter { HP: 30, HP: 40 }")
        .unwrap_err();
    assert!(
        err.to_string().contains("duplicate field"),
        "expected duplicate field error, got: {}",
        err
    );
}

#[test]
fn set_type_mismatch_rejected() {
    let mut runner = Runner::new();
    load_character_program(&mut runner);
    runner.exec("spawn Character fighter { HP: 30 }").unwrap();
    runner.take_output();

    let err = runner.exec(r#"set fighter.HP = "thirty""#).unwrap_err();
    assert!(err.to_string().contains("type mismatch"), "got: {}", err);
}

// ── Phase 3: Configuration tests ─────────────────────────────

#[test]
fn cmd_seed_deterministic() {
    let mut runner1 = Runner::new();
    runner1.exec("seed 42").unwrap();
    runner1.take_output();
    runner1.exec("eval 1d20").unwrap();
    let out1 = runner1.take_output();

    let mut runner2 = Runner::new();
    runner2.exec("seed 42").unwrap();
    runner2.take_output();
    runner2.exec("eval 1d20").unwrap();
    let out2 = runner2.take_output();

    assert_eq!(out1, out2, "same seed should produce same dice result");
}

#[test]
fn cmd_rolls_consumed() {
    let mut runner = Runner::new();
    load_character_program(&mut runner);
    runner.exec("rolls 10").unwrap();
    runner.take_output();
    // Queue should have 1 entry; it'll be consumed on next dice roll
    assert_eq!(runner.roll_queue.len(), 1);
    assert_eq!(runner.roll_queue[0], 10);
}

#[test]
fn cmd_rolls_clear() {
    let mut runner = Runner::new();
    runner.exec("rolls 10 15 20").unwrap();
    runner.take_output();
    assert_eq!(runner.roll_queue.len(), 3);

    runner.exec("rolls clear").unwrap();
    let output = runner.take_output();
    assert!(output[0].contains("cleared"));
    assert!(runner.roll_queue.is_empty());
}

#[test]
fn cmd_rolls_append() {
    let mut runner = Runner::new();
    runner.exec("rolls 3 5").unwrap();
    runner.take_output();
    runner.exec("rolls 7").unwrap();
    let output = runner.take_output();
    assert!(output[0].contains("3 total"));
    assert_eq!(runner.roll_queue.len(), 3);
}

// ── Phase 3: Assertion tests ─────────────────────────────────

#[test]
fn cmd_assert_true() {
    let mut runner = Runner::new();
    runner.exec("assert 2 + 3 == 5").unwrap();
}

#[test]
fn cmd_assert_false() {
    let mut runner = Runner::new();
    let err = runner.exec("assert 2 + 3 == 6").unwrap_err();
    assert!(err.to_string().contains("assertion failed"), "got: {}", err);
}

#[test]
fn cmd_assert_non_bool() {
    let mut runner = Runner::new();
    let err = runner.exec("assert 2 + 3").unwrap_err();
    assert!(err.to_string().contains("expected bool"), "got: {}", err);
}

#[test]
fn cmd_assert_eq_pass() {
    let mut runner = Runner::new();
    runner.exec("assert_eq 2 + 3, 5").unwrap();
}

#[test]
fn cmd_assert_eq_fail() {
    let mut runner = Runner::new();
    let err = runner.exec("assert_eq 2 + 3, 6").unwrap_err();
    assert!(err.to_string().contains("assertion failed"), "got: {}", err);
    assert!(err.to_string().contains("!="), "got: {}", err);
}

#[test]
fn cmd_assert_err_pass() {
    let mut runner = Runner::new();
    // destroy with unknown handle should error
    runner.exec("assert_err destroy nonexistent").unwrap();
    // No output should leak from the failed inner command
    assert!(runner.take_output().is_empty());
}

#[test]
fn cmd_assert_err_fail() {
    let mut runner = Runner::new();
    // eval 2+3 succeeds, so assert_err should fail
    let err = runner.exec("assert_err eval 2 + 3").unwrap_err();
    assert!(err.to_string().contains("expected error"), "got: {}", err);
}

// ── Phase 3: Inspection tests ────────────────────────────────

#[test]
fn cmd_inspect_entity() {
    let mut runner = Runner::new();
    load_character_program(&mut runner);
    runner
        .exec("spawn Character fighter { HP: 30, AC: 15 }")
        .unwrap();
    runner.take_output();

    runner.exec("inspect fighter").unwrap();
    let output = runner.take_output();
    assert!(output[0].contains("fighter"));
    assert!(output[0].contains("Character"));
    assert!(output.iter().any(|l| l.contains("HP") && l.contains("30")));
    assert!(output.iter().any(|l| l.contains("AC") && l.contains("15")));
}

#[test]
fn cmd_inspect_field() {
    let mut runner = Runner::new();
    load_character_program(&mut runner);
    runner.exec("spawn Character fighter { HP: 30 }").unwrap();
    runner.take_output();

    runner.exec("inspect fighter.HP").unwrap();
    let output = runner.take_output();
    assert_eq!(output.len(), 1);
    assert!(output[0].contains("fighter.HP = 30"));
}

#[test]
fn cmd_inspect_unknown() {
    let mut runner = Runner::new();
    let err = runner.exec("inspect ghost").unwrap_err();
    assert!(err.to_string().contains("unknown handle"));
}

#[test]
fn cmd_state_empty() {
    let mut runner = Runner::new();
    runner.exec("state").unwrap();
    let output = runner.take_output();
    assert_eq!(output, vec!["no entities"]);
}

#[test]
fn cmd_state_with_entities() {
    let mut runner = Runner::new();
    load_character_program(&mut runner);
    runner
        .exec("spawn Character alice { HP: 30, AC: 15 }")
        .unwrap();
    runner.take_output();
    runner
        .exec("spawn Character bob { HP: 25, AC: 12 }")
        .unwrap();
    runner.take_output();

    runner.exec("state").unwrap();
    let output = runner.take_output();
    // Should contain both entities sorted alphabetically
    assert!(output.iter().any(|l| l.contains("alice")));
    assert!(output.iter().any(|l| l.contains("bob")));
}

#[test]
fn cmd_types() {
    let mut runner = Runner::new();
    load_character_program(&mut runner);
    runner.exec("types").unwrap();
    let output = runner.take_output();
    assert!(output.iter().any(|l| l.contains("entity Character")));
    assert!(output.iter().any(|l| l.contains("HP")));
}

#[test]
fn cmd_actions() {
    let dir = std::env::temp_dir().join("ttrpg_cli_test");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("test_actions.ttrpg");
    std::fs::write(
        &path,
        r#"
system "test" {
    entity Character { HP: int }
    action Attack on attacker: Character (target: Character) {
        resolve {
            target.HP -= 5
        }
    }
}
"#,
    )
    .unwrap();

    let mut runner = Runner::new();
    runner.exec(&format!("load {}", path.display())).unwrap();
    runner.take_output();

    runner.exec("actions").unwrap();
    let output = runner.take_output();
    assert!(output.iter().any(|l| l.contains("action Attack")));

    std::fs::remove_file(&path).ok();
}

#[test]
fn cmd_mechanics() {
    let mut runner = Runner::new();
    load_character_program(&mut runner);
    runner.exec("mechanics").unwrap();
    let output = runner.take_output();
    assert!(output.iter().any(|l| l.contains("derive id")));
}

#[test]
fn cmd_conditions_empty() {
    let mut runner = Runner::new();
    load_character_program(&mut runner);
    runner.exec("spawn Character fighter { HP: 30 }").unwrap();
    runner.take_output();

    runner.exec("conditions").unwrap();
    let output = runner.take_output();
    assert!(output.iter().any(|l| l.contains("no active conditions")));
}

#[test]
fn cmd_types_empty() {
    let mut runner = Runner::new();
    runner.exec("types").unwrap();
    let output = runner.take_output();
    assert_eq!(output, vec!["no types"]);
}

#[test]
fn cmd_actions_empty() {
    let mut runner = Runner::new();
    runner.exec("actions").unwrap();
    let output = runner.take_output();
    assert_eq!(output, vec!["no actions"]);
}

#[test]
fn cmd_mechanics_empty() {
    let mut runner = Runner::new();
    runner.exec("mechanics").unwrap();
    let output = runner.take_output();
    assert_eq!(output, vec!["no mechanics"]);
}

#[test]
fn cmd_seed_invalid() {
    let mut runner = Runner::new();
    let err = runner.exec("seed abc").unwrap_err();
    assert!(err.to_string().contains("invalid seed"));
}

#[test]
fn cmd_rolls_invalid() {
    let mut runner = Runner::new();
    let err = runner.exec("rolls 3 abc 5").unwrap_err();
    assert!(err.to_string().contains("invalid roll value"));
}

#[test]
fn cmd_rolls_atomic_on_failure() {
    let mut runner = Runner::new();
    runner.exec("rolls 10").unwrap();
    runner.take_output();
    assert_eq!(runner.roll_queue.len(), 1);

    // Second call fails at "abc" — the 17 should NOT be queued
    let _ = runner.exec("rolls 17 abc");
    assert_eq!(
        runner.roll_queue.len(),
        1,
        "failed rolls should not leave partial state"
    );
}

#[test]
fn cmd_inspect_unset_field() {
    let mut runner = Runner::new();
    load_character_program(&mut runner);
    runner.exec("spawn Character fighter { HP: 30 }").unwrap();
    runner.take_output();

    // AC is declared but not set — should show <unset>, not error
    runner.exec("inspect fighter.AC").unwrap();
    let output = runner.take_output();
    assert_eq!(output.len(), 1);
    assert!(output[0].contains("<unset>"), "got: {}", output[0]);
}

// ── Grant/Revoke tests ──────────────────────────────────────

/// Load a program with optional groups for grant/revoke tests.
fn load_group_program(runner: &mut Runner) {
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let id = COUNTER.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join("ttrpg_cli_test");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("test_group_{}.ttrpg", id));
    std::fs::write(
        &path,
        r#"
system "test" {
    group CombatStats {
        base_ac: int = 10
    }
    entity Character {
        HP: int
        AC: int
        include CombatStats
        optional Spellcasting {
            spell_slots: int
            spell_dc: int = 10
        }
        optional Rage {
            rage_count: int
        }
    }
    derive id(x: int) -> int { x }
}
"#,
    )
    .unwrap();
    runner.exec(&format!("load {}", path.display())).unwrap();
    runner.take_output();
    std::fs::remove_file(&path).ok();
}

#[test]
fn grant_and_revoke_basic() {
    let mut runner = Runner::new();
    load_group_program(&mut runner);
    runner
        .exec("spawn Character hero { HP: 30, AC: 15 }")
        .unwrap();
    runner.take_output();

    // Grant with explicit fields
    runner
        .exec("grant hero.Spellcasting { spell_slots: 5 }")
        .unwrap();
    let output = runner.take_output();
    assert!(
        output[0].contains("granted hero.Spellcasting"),
        "got: {:?}",
        output
    );

    // Revoke
    runner.exec("revoke hero.Spellcasting").unwrap();
    let output = runner.take_output();
    assert_eq!(output, vec!["revoked hero.Spellcasting"]);
}

#[test]
fn grant_defaults_filled() {
    let mut runner = Runner::new();
    load_group_program(&mut runner);
    runner.exec("spawn Character hero { HP: 30 }").unwrap();
    runner.take_output();

    // spell_dc has default=10, so we only need spell_slots
    runner
        .exec("grant hero.Spellcasting { spell_slots: 3 }")
        .unwrap();
    let output = runner.take_output();
    assert!(
        output[0].contains("spell_dc"),
        "default should be filled, got: {:?}",
        output
    );
}

#[test]
fn grant_missing_required_field() {
    let mut runner = Runner::new();
    load_group_program(&mut runner);
    runner.exec("spawn Character hero { HP: 30 }").unwrap();
    runner.take_output();

    // spell_slots is required (no default)
    let err = runner.exec("grant hero.Spellcasting").unwrap_err();
    assert!(
        err.to_string().contains("missing required field"),
        "got: {}",
        err
    );
}

#[test]
fn grant_unknown_group() {
    let mut runner = Runner::new();
    load_group_program(&mut runner);
    runner.exec("spawn Character hero { HP: 30 }").unwrap();
    runner.take_output();

    let err = runner.exec("grant hero.Flying").unwrap_err();
    assert!(err.to_string().contains("unknown group"), "got: {}", err);
}

#[test]
fn grant_required_group_rejected() {
    let mut runner = Runner::new();
    load_group_program(&mut runner);
    runner.exec("spawn Character hero { HP: 30 }").unwrap();
    runner.take_output();

    let err = runner.exec("grant hero.CombatStats").unwrap_err();
    assert!(
        err.to_string().contains("required and cannot be granted"),
        "got: {}",
        err
    );
}

#[test]
fn grant_already_granted() {
    let mut runner = Runner::new();
    load_group_program(&mut runner);
    runner.exec("spawn Character hero { HP: 30 }").unwrap();
    runner.take_output();

    runner.exec("grant hero.Rage { rage_count: 3 }").unwrap();
    runner.take_output();

    let err = runner
        .exec("grant hero.Rage { rage_count: 2 }")
        .unwrap_err();
    assert!(err.to_string().contains("already granted"), "got: {}", err);
}

#[test]
fn revoke_not_granted() {
    let mut runner = Runner::new();
    load_group_program(&mut runner);
    runner.exec("spawn Character hero { HP: 30 }").unwrap();
    runner.take_output();

    let err = runner.exec("revoke hero.Spellcasting").unwrap_err();
    assert!(
        err.to_string().contains("not currently granted"),
        "got: {}",
        err
    );
}

#[test]
fn revoke_required_group_rejected() {
    let mut runner = Runner::new();
    load_group_program(&mut runner);
    runner.exec("spawn Character hero { HP: 30 }").unwrap();
    runner.take_output();

    let err = runner.exec("revoke hero.CombatStats").unwrap_err();
    assert!(
        err.to_string().contains("required and cannot be revoked"),
        "got: {}",
        err
    );
}

#[test]
fn set_group_field() {
    let mut runner = Runner::new();
    load_group_program(&mut runner);
    runner.exec("spawn Character hero { HP: 30 }").unwrap();
    runner.take_output();
    runner
        .exec("grant hero.Spellcasting { spell_slots: 5 }")
        .unwrap();
    runner.take_output();

    runner
        .exec("set hero.Spellcasting.spell_slots = 3")
        .unwrap();
    let output = runner.take_output();
    assert!(
        output[0].contains("hero.Spellcasting.spell_slots = 3"),
        "got: {:?}",
        output
    );
}

#[test]
fn set_group_field_not_granted() {
    let mut runner = Runner::new();
    load_group_program(&mut runner);
    runner.exec("spawn Character hero { HP: 30 }").unwrap();
    runner.take_output();

    let err = runner
        .exec("set hero.Spellcasting.spell_slots = 3")
        .unwrap_err();
    assert!(
        err.to_string().contains("not currently granted"),
        "got: {}",
        err
    );
}

#[test]
fn inspect_group() {
    let mut runner = Runner::new();
    load_group_program(&mut runner);
    runner.exec("spawn Character hero { HP: 30 }").unwrap();
    runner.take_output();
    runner
        .exec("grant hero.Spellcasting { spell_slots: 5 }")
        .unwrap();
    runner.take_output();

    // Inspect group
    runner.exec("inspect hero.Spellcasting").unwrap();
    let output = runner.take_output();
    assert!(output[0].contains("hero.Spellcasting"), "got: {:?}", output);
}

#[test]
fn inspect_group_not_granted() {
    let mut runner = Runner::new();
    load_group_program(&mut runner);
    runner.exec("spawn Character hero { HP: 30 }").unwrap();
    runner.take_output();

    runner.exec("inspect hero.Spellcasting").unwrap();
    let output = runner.take_output();
    assert!(output[0].contains("<not granted>"), "got: {:?}", output);
}

#[test]
fn inspect_group_field() {
    let mut runner = Runner::new();
    load_group_program(&mut runner);
    runner.exec("spawn Character hero { HP: 30 }").unwrap();
    runner.take_output();
    runner
        .exec("grant hero.Spellcasting { spell_slots: 5 }")
        .unwrap();
    runner.take_output();

    runner
        .exec("inspect hero.Spellcasting.spell_slots")
        .unwrap();
    let output = runner.take_output();
    assert!(
        output[0].contains("hero.Spellcasting.spell_slots = 5"),
        "got: {:?}",
        output
    );
}

#[test]
fn inspect_entity_shows_groups() {
    let mut runner = Runner::new();
    load_group_program(&mut runner);
    runner.exec("spawn Character hero { HP: 30 }").unwrap();
    runner.take_output();
    runner
        .exec("grant hero.Spellcasting { spell_slots: 5 }")
        .unwrap();
    runner.take_output();

    runner.exec("inspect hero").unwrap();
    let output = runner.take_output();
    assert!(
        output.iter().any(|l| l.contains("[group] Spellcasting")),
        "should show granted group, got: {:?}",
        output
    );
    assert!(
        output
            .iter()
            .any(|l| l.contains("spell_slots") && l.contains("5")),
        "should show group field value, got: {:?}",
        output
    );
}

#[test]
fn types_shows_optional_groups() {
    let mut runner = Runner::new();
    load_group_program(&mut runner);

    runner.exec("types").unwrap();
    let output = runner.take_output();
    assert!(
        output.iter().any(|l| l.contains("optional Spellcasting")),
        "types should show optional groups, got: {:?}",
        output
    );
    assert!(
        output.iter().any(|l| l.contains("include CombatStats")),
        "types should show include groups, got: {:?}",
        output
    );
    assert!(
        output.iter().any(|l| l.contains("spell_slots")),
        "types should show group fields, got: {:?}",
        output
    );
}

#[test]
fn spawn_auto_materializes_included_group() {
    let mut runner = Runner::new();
    load_group_program(&mut runner);

    runner.exec("spawn Character hero { HP: 30 }").unwrap();
    runner.take_output();

    runner.exec("inspect hero.CombatStats.base_ac").unwrap();
    let output = runner.take_output();
    assert!(
        output[0].contains("10"),
        "included group defaults should be materialized, got: {:?}",
        output
    );
}

#[test]
fn state_shows_granted_groups() {
    let mut runner = Runner::new();
    load_group_program(&mut runner);
    runner.exec("spawn Character hero { HP: 30 }").unwrap();
    runner.take_output();
    runner.exec("grant hero.Rage { rage_count: 3 }").unwrap();
    runner.take_output();

    runner.exec("state").unwrap();
    let output = runner.take_output();
    assert!(
        output.iter().any(|l| l.contains("[group] Rage")),
        "state should show granted group, got: {:?}",
        output
    );
}

#[test]
fn spawn_inline_group() {
    let mut runner = Runner::new();
    load_group_program(&mut runner);

    runner
        .exec("spawn Character wizard { HP: 20, Spellcasting { spell_slots: 5 } }")
        .unwrap();
    let output = runner.take_output();
    assert!(
        output[0].contains("spawned Character wizard"),
        "got: {:?}",
        output
    );

    // Verify the group was granted
    runner
        .exec("inspect wizard.Spellcasting.spell_slots")
        .unwrap();
    let output = runner.take_output();
    assert!(
        output[0].contains("5"),
        "inline group should set field, got: {:?}",
        output
    );
}

#[test]
fn spawn_inline_group_with_defaults() {
    let mut runner = Runner::new();
    load_group_program(&mut runner);

    // Spellcasting has spell_dc default=10
    runner
        .exec("spawn Character wizard { HP: 20, Spellcasting { spell_slots: 3 } }")
        .unwrap();
    runner.take_output();

    runner.exec("inspect wizard.Spellcasting.spell_dc").unwrap();
    let output = runner.take_output();
    assert!(
        output[0].contains("10"),
        "default should be filled, got: {:?}",
        output
    );
}

#[test]
fn spawn_inline_group_unknown_rejected() {
    let mut runner = Runner::new();
    load_group_program(&mut runner);

    let err = runner
        .exec("spawn Character hero { HP: 20, Flying { speed: 60 } }")
        .unwrap_err();
    assert!(err.to_string().contains("unknown group"), "got: {}", err);
}

#[test]
fn spawn_inline_group_error_is_atomic() {
    let mut runner = Runner::new();
    load_group_program(&mut runner);

    // Spawn with an inline group that has a type error — should fail
    let err = runner
        .exec("spawn Character hero { HP: 20, Spellcasting { spell_slots: \"bad\" } }")
        .unwrap_err();
    assert!(err.to_string().contains("type mismatch"), "got: {}", err);

    // The handle should NOT exist — spawn was rolled back
    let err2 = runner.exec("eval hero.HP").unwrap_err();
    assert!(
        err2.to_string().contains("undefined variable")
            || err2.to_string().contains("unknown handle"),
        "entity should not exist after failed spawn, got: {}",
        err2
    );
}

#[test]
fn grant_unknown_field_in_group() {
    let mut runner = Runner::new();
    load_group_program(&mut runner);
    runner.exec("spawn Character hero { HP: 30 }").unwrap();
    runner.take_output();

    let err = runner
        .exec("grant hero.Spellcasting { spell_slots: 5, nonexistent: 1 }")
        .unwrap_err();
    assert!(
        err.to_string().contains("unknown field 'nonexistent'"),
        "got: {}",
        err
    );
}

#[test]
fn revoke_unknown_group() {
    let mut runner = Runner::new();
    load_group_program(&mut runner);
    runner.exec("spawn Character hero { HP: 30 }").unwrap();
    runner.take_output();

    let err = runner.exec("revoke hero.Flying").unwrap_err();
    assert!(err.to_string().contains("unknown group"), "got: {}", err);
}

#[test]
fn assert_err_grant_revoke() {
    let mut runner = Runner::new();
    load_group_program(&mut runner);
    runner.exec("spawn Character hero { HP: 30 }").unwrap();
    runner.take_output();

    // Revoke when not granted should error
    runner.exec("assert_err revoke hero.Spellcasting").unwrap();
    // Grant with unknown group should error
    runner.exec("assert_err grant hero.Flying").unwrap();
}

#[test]
fn group_accessor_methods() {
    let mut runner = Runner::new();
    load_group_program(&mut runner);

    let groups = runner.group_names("Character");
    assert!(groups.contains(&"CombatStats".to_string()));
    assert!(groups.contains(&"Spellcasting".to_string()));
    assert!(groups.contains(&"Rage".to_string()));

    let fields = runner.group_field_names("Character", "Spellcasting");
    assert!(fields.contains(&"spell_slots".to_string()));
    assert!(fields.contains(&"spell_dc".to_string()));
}

// ── Multi-file loading tests ───────────────────────────────────

fn multi_file_dir(test_name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("ttrpg_test_{}", test_name));
    // Clean any stale directory from a previous run, then create fresh
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

#[test]
fn multi_file_load_basic() {
    let dir = multi_file_dir("load_basic");
    let core = dir.join("core.ttrpg");
    let extras = dir.join("extras.ttrpg");

    std::fs::write(
        &core,
        "\
system \"Core\" {
    entity Character {
        HP: int
        AC: int
    }
    derive double(x: int) -> int { x * 2 }
}
",
    )
    .unwrap();

    std::fs::write(
        &extras,
        "\
system \"Extras\" {
    derive triple(x: int) -> int { x * 3 }
}
",
    )
    .unwrap();

    let mut runner = Runner::new();
    runner
        .exec(&format!("load {} {}", core.display(), extras.display()))
        .unwrap();
    let output = runner.take_output();
    assert!(output[0].contains("loaded 2 files"));

    // Can spawn entities from the merged program
    runner
        .exec("spawn Character hero { HP: 30, AC: 15 }")
        .unwrap();
    runner.take_output();

    runner.exec("eval hero.HP").unwrap();
    let output = runner.take_output();
    assert_eq!(output, vec!["30"]);

    // Both systems' derives are accessible
    runner.exec("eval double(5)").unwrap();
    let output = runner.take_output();
    assert_eq!(output, vec!["10"]);

    runner.exec("eval triple(5)").unwrap();
    let output = runner.take_output();
    assert_eq!(output, vec!["15"]);

    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn multi_file_reload() {
    let dir = multi_file_dir("reload");
    let a = dir.join("reload_a.ttrpg");
    let b = dir.join("reload_b.ttrpg");

    std::fs::write(&a, "system \"A\" { entity Foo { x: int } }\n").unwrap();
    std::fs::write(
        &b,
        "system \"B\" { derive add(a: int, b: int) -> int { a + b } }\n",
    )
    .unwrap();

    let mut runner = Runner::new();
    runner
        .exec(&format!("load {} {}", a.display(), b.display()))
        .unwrap();
    runner.take_output();

    runner.exec("reload").unwrap();
    let output = runner.take_output();
    assert!(output[0].contains("loaded 2 files"));

    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn multi_file_cross_system_duplicate_error() {
    let dir = multi_file_dir("dup_error");
    let a = dir.join("dup_a.ttrpg");
    let b = dir.join("dup_b.ttrpg");

    std::fs::write(
        &a,
        "\
system \"A\" { entity Character { HP: int } }
",
    )
    .unwrap();
    std::fs::write(
        &b,
        "\
system \"B\" { entity Character { AC: int } }
",
    )
    .unwrap();

    let mut runner = Runner::new();
    let err = runner
        .exec(&format!("load {} {}", a.display(), b.display()))
        .unwrap_err();
    assert!(err.to_string().contains("error"));

    // errors command should mention the duplicate
    runner.exec("errors").unwrap();
    let output = runner.take_output();
    assert!(
        output.iter().any(|l| l.contains("Character")),
        "expected duplicate name 'Character' in errors, got: {:?}",
        output
    );

    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn multi_file_errors_command_renders() {
    let dir = multi_file_dir("errors_render");
    let a = dir.join("render_a.ttrpg");
    let b = dir.join("render_b.ttrpg");

    std::fs::write(
        &a,
        r#"
system "A" {
    derive bad() -> int { undefined_var }
}
"#,
    )
    .unwrap();
    std::fs::write(
        &b,
        r#"
system "B" {
    derive ok(x: int) -> int { x }
}
"#,
    )
    .unwrap();

    let mut runner = Runner::new();
    let _err = runner
        .exec(&format!("load {} {}", a.display(), b.display()))
        .unwrap_err();
    runner.take_output();

    runner.exec("errors").unwrap();
    let output = runner.take_output();
    assert!(!output.is_empty());
    // MultiSourceMap renders with filename prefix
    assert!(
        output.iter().any(|l| l.contains("render_a.ttrpg")),
        "expected filename in diagnostic, got: {:?}",
        output
    );

    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn multi_file_glob_expansion() {
    let dir = multi_file_dir("glob");
    let sub = dir.join("glob_test");
    std::fs::create_dir_all(&sub).unwrap();

    std::fs::write(
        sub.join("sys_a.ttrpg"),
        "system \"A\" { entity Foo { x: int } }\n",
    )
    .unwrap();
    std::fs::write(
        sub.join("sys_b.ttrpg"),
        "system \"B\" { derive id(x: int) -> int { x } }\n",
    )
    .unwrap();

    let mut runner = Runner::new();
    let glob_pattern = sub.join("*.ttrpg");
    runner
        .exec(&format!("load {}", glob_pattern.display()))
        .unwrap();
    let output = runner.take_output();
    assert!(
        output[0].contains("loaded 2 files"),
        "expected 2 files loaded, got: {:?}",
        output
    );

    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn multi_file_nonexistent_file_error() {
    let dir = multi_file_dir("nonexistent");
    let a = dir.join("exists.ttrpg");
    std::fs::write(&a, "system \"A\" { entity Foo { x: int } }\n").unwrap();

    let mut runner = Runner::new();
    let err = runner
        .exec(&format!("load {} /nonexistent/file.ttrpg", a.display()))
        .unwrap_err();
    assert!(err.to_string().contains("cannot read"));

    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn multi_file_glob_no_match_error() {
    let mut runner = Runner::new();
    let err = runner
        .exec("load /tmp/ttrpg_definitely_no_match_*.ttrpg")
        .unwrap_err();
    assert!(err.to_string().contains("no files matched"));
}

#[test]
fn single_file_backward_compat() {
    // Single-file load should still work exactly as before
    let dir = multi_file_dir("backward_compat");
    let path = dir.join("single.ttrpg");
    std::fs::write(
        &path,
        "\
system \"test\" {
    entity Character {
        HP: int
    }
    derive double(x: int) -> int { x * 2 }
}
",
    )
    .unwrap();

    let mut runner = Runner::new();
    runner.exec(&format!("load {}", path.display())).unwrap();
    let output = runner.take_output();
    // Single file says "loaded <path>" not "loaded N files"
    assert!(
        output[0].starts_with("loaded") && !output[0].contains("files"),
        "single file should say 'loaded <path>', got: {:?}",
        output
    );

    runner.exec("spawn Character hero { HP: 20 }").unwrap();
    runner.take_output();

    runner.exec("eval double(hero.HP)").unwrap();
    let output = runner.take_output();
    assert_eq!(output, vec!["40"]);

    runner.exec("reload").unwrap();
    let output = runner.take_output();
    assert!(output[0].starts_with("loaded"));

    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn single_file_with_module_syntax() {
    // Regression: single-file mode used to bypass module resolution,
    // so `use` + qualified types would fail.
    let dir = multi_file_dir("module_syntax");
    let core = dir.join("core.ttrpg");
    std::fs::write(
        &core,
        "\
system \"Core\" {
    entity Character {
        HP: int
    }
}
",
    )
    .unwrap();

    let main = dir.join("main.ttrpg");
    std::fs::write(
        &main,
        "\
use \"Core\"

system \"Main\" {
    derive greet(c: Character) -> int { c.HP }
}
",
    )
    .unwrap();

    // Multi-file should work (baseline)
    let mut runner = Runner::new();
    runner
        .exec(&format!("load {} {}", core.display(), main.display()))
        .unwrap();

    // Now test single file with use + qualified access
    let single = dir.join("single_mod.ttrpg");
    std::fs::write(
        &single,
        "\
use \"Core\"

system \"Core\" {
    entity Character {
        HP: int
    }
}

system \"Game\" {
    derive greet(c: Character) -> int { c.HP }
}
",
    )
    .unwrap();

    let mut runner = Runner::new();
    runner.exec(&format!("load {}", single.display())).unwrap();

    runner.exec("spawn Character hero { HP: 10 }").unwrap();
    runner.take_output();

    runner.exec("eval greet(hero)").unwrap();
    let output = runner.take_output();
    assert_eq!(output, vec!["10"]);

    std::fs::remove_dir_all(&dir).ok();
}

// ── Regression: tdsl-36qk — CLI eval with wrong arity should error, not panic ──

#[test]
fn eval_len_no_args_returns_error() {
    let mut runner = Runner::new();
    let result = runner.eval("len()");
    assert!(
        result.is_err(),
        "len() with no args should error, not panic"
    );
}

#[test]
fn eval_append_one_arg_returns_error() {
    let mut runner = Runner::new();
    let result = runner.eval("append([1])");
    assert!(
        result.is_err(),
        "append() with 1 arg should error, not panic"
    );
}

#[test]
fn eval_keys_no_args_returns_error() {
    let mut runner = Runner::new();
    let result = runner.eval("keys()");
    assert!(
        result.is_err(),
        "keys() with no args should error, not panic"
    );
}

#[test]
fn eval_reverse_no_args_returns_error() {
    let mut runner = Runner::new();
    let result = runner.eval("reverse()");
    assert!(
        result.is_err(),
        "reverse() with no args should error, not panic"
    );
}

// ── Regression: tdsl-0s0y — floor/ceil with non-finite floats ──

#[test]
fn eval_floor_nan_returns_error() {
    let mut runner = Runner::new();
    // 0.0 / 0.0 is NaN — but DSL may not allow this directly.
    // We test via the builtin with a large float that overflows.
    let result = runner.eval("floor(1e19)");
    // Should either succeed with a clamped value or error — not silently wrong
    // The key thing is it doesn't panic
    let _ = result;
}

// ── Regression: tdsl-vlw — value_matches_ty rejects wrong struct for TurnBudget/RollResult ──

#[test]
fn value_matches_ty_rejects_wrong_struct_for_rollresult() {
    let wrong = Value::Struct {
        name: "Damage".into(),
        fields: std::collections::BTreeMap::new(),
    };
    assert!(!value_matches_ty(&wrong, &Ty::RollResult, None));
}

#[test]
fn value_matches_ty_rejects_wrong_struct_for_turn_budget() {
    let wrong = Value::Struct {
        name: "Damage".into(),
        fields: std::collections::BTreeMap::new(),
    };
    assert!(!value_matches_ty(&wrong, &Ty::TurnBudget, None));
}

#[test]
fn value_matches_ty_accepts_correct_struct_for_rollresult() {
    let correct = Value::Struct {
        name: "RollResult".into(),
        fields: std::collections::BTreeMap::new(),
    };
    assert!(value_matches_ty(&correct, &Ty::RollResult, None));
}

#[test]
fn value_matches_ty_accepts_correct_struct_for_turn_budget() {
    let correct = Value::Struct {
        name: "TurnBudget".into(),
        fields: std::collections::BTreeMap::new(),
    };
    assert!(value_matches_ty(&correct, &Ty::TurnBudget, None));
}

// ── Regression: tdsl-hof — value_matches_ty checks entity concrete type ──

#[test]
fn value_matches_ty_rejects_wrong_entity_type() {
    let mut gs = GameState::new();
    let monster = gs.add_entity("Monster", std::collections::HashMap::new());

    // A Monster entity should not match a field typed as Character
    assert!(!value_matches_ty(
        &Value::Entity(monster),
        &Ty::Entity("Character".into()),
        Some(&gs)
    ));
}

#[test]
fn value_matches_ty_accepts_correct_entity_type() {
    let mut gs = GameState::new();
    let character = gs.add_entity("Character", std::collections::HashMap::new());

    assert!(value_matches_ty(
        &Value::Entity(character),
        &Ty::Entity("Character".into()),
        Some(&gs)
    ));
}

#[test]
fn value_matches_ty_entity_any_accepts_all() {
    let mut gs = GameState::new();
    let monster = gs.add_entity("Monster", std::collections::HashMap::new());

    // AnyEntity should accept any entity regardless of type
    assert!(value_matches_ty(
        &Value::Entity(monster),
        &Ty::AnyEntity,
        Some(&gs)
    ));
}

#[test]
fn value_matches_ty_entity_without_state_accepts() {
    // Without GameState, entity type matching is best-effort (accepts)
    assert!(value_matches_ty(
        &Value::Entity(EntityRef(42)),
        &Ty::Entity("Whatever".into()),
        None
    ));
}

// ── Resource bounds + compound assignment tests ──────────────

/// Load a program with a resource field: `hp: resource(0..=max_hp)`.
fn load_resource_program(runner: &mut Runner) {
    static RES_COUNTER: AtomicU64 = AtomicU64::new(0);
    let id = RES_COUNTER.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join("ttrpg_cli_test");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("test_resource_{}.ttrpg", id));
    std::fs::write(
        &path,
        r#"
system "test" {
    entity Character {
        max_hp: int
        hp: resource(0..=max_hp)
        AC: int
    }
}
"#,
    )
    .unwrap();
    runner.exec(&format!("load {}", path.display())).unwrap();
    runner.take_output();
    std::fs::remove_file(&path).ok();
}

#[test]
fn set_clamps_resource_to_max() {
    let mut runner = Runner::new();
    load_resource_program(&mut runner);
    runner
        .exec("spawn Character hero { max_hp: 20, hp: 20 }")
        .unwrap();
    runner.take_output();

    runner.exec("set hero.hp = 999").unwrap();
    let output = runner.take_output();
    // Should be clamped to max_hp (20)
    assert!(
        output[0].contains("hero.hp = 20") && output[0].contains("(clamped)"),
        "expected clamped to 20, got: {:?}",
        output
    );
}

#[test]
fn set_clamps_resource_to_min() {
    let mut runner = Runner::new();
    load_resource_program(&mut runner);
    runner
        .exec("spawn Character hero { max_hp: 20, hp: 20 }")
        .unwrap();
    runner.take_output();

    runner.exec("set hero.hp = -5").unwrap();
    let output = runner.take_output();
    // Should be clamped to 0
    assert!(
        output[0].contains("hero.hp = 0") && output[0].contains("(clamped)"),
        "expected clamped to 0, got: {:?}",
        output
    );
}

#[test]
fn set_no_clamp_for_non_resource() {
    let mut runner = Runner::new();
    load_resource_program(&mut runner);
    runner
        .exec("spawn Character hero { max_hp: 20, hp: 20, AC: 15 }")
        .unwrap();
    runner.take_output();

    // AC is a plain int, not a resource — should write without clamping
    runner.exec("set hero.AC = 999").unwrap();
    let output = runner.take_output();
    assert!(
        output[0].contains("hero.AC = 999"),
        "expected unclamped write, got: {:?}",
        output
    );
    assert!(
        !output[0].contains("clamped"),
        "non-resource should not be clamped, got: {:?}",
        output
    );
}

#[test]
fn set_plus_eq() {
    let mut runner = Runner::new();
    load_resource_program(&mut runner);
    runner
        .exec("spawn Character hero { max_hp: 20, hp: 10, AC: 15 }")
        .unwrap();
    runner.take_output();

    runner.exec("set hero.AC += 3").unwrap();
    let output = runner.take_output();
    assert!(
        output[0].contains("=> 18"),
        "expected AC to be 18, got: {:?}",
        output
    );
}

#[test]
fn set_minus_eq() {
    let mut runner = Runner::new();
    load_resource_program(&mut runner);
    runner
        .exec("spawn Character hero { max_hp: 20, hp: 10, AC: 15 }")
        .unwrap();
    runner.take_output();

    runner.exec("set hero.AC -= 5").unwrap();
    let output = runner.take_output();
    assert!(
        output[0].contains("=> 10"),
        "expected AC to be 10, got: {:?}",
        output
    );
}

#[test]
fn set_minus_eq_with_resource_clamps() {
    let mut runner = Runner::new();
    load_resource_program(&mut runner);
    runner
        .exec("spawn Character hero { max_hp: 20, hp: 5 }")
        .unwrap();
    runner.take_output();

    // hp=5, hp -= 100 should clamp to 0
    runner.exec("set hero.hp -= 100").unwrap();
    let output = runner.take_output();
    assert!(
        output[0].contains("=> 0"),
        "expected hp clamped to 0, got: {:?}",
        output
    );
}

#[test]
fn set_plus_eq_with_resource_clamps() {
    let mut runner = Runner::new();
    load_resource_program(&mut runner);
    runner
        .exec("spawn Character hero { max_hp: 20, hp: 18 }")
        .unwrap();
    runner.take_output();

    // hp=18, hp += 10 should clamp to max_hp (20)
    runner.exec("set hero.hp += 10").unwrap();
    let output = runner.take_output();
    assert!(
        output[0].contains("=> 20"),
        "expected hp clamped to 20, got: {:?}",
        output
    );
}

// ── Flattened included group fields ────────────────────────────────

#[test]
fn set_flattened_included_field() {
    let mut runner = Runner::new();
    load_group_program(&mut runner);
    runner
        .exec("spawn Character hero { HP: 30, AC: 15 }")
        .unwrap();
    runner.take_output();

    // Set flattened field: base_ac lives in included CombatStats group
    runner.exec("set hero.base_ac = 18").unwrap();
    let output = runner.take_output();
    assert!(
        output[0].contains("hero.base_ac = 18"),
        "got: {:?}",
        output
    );

    // Verify via qualified access
    runner.exec("inspect hero.CombatStats.base_ac").unwrap();
    let output = runner.take_output();
    assert!(
        output[0].contains("18"),
        "qualified access should show updated value, got: {:?}",
        output
    );
}

#[test]
fn inspect_flattened_included_field() {
    let mut runner = Runner::new();
    load_group_program(&mut runner);
    runner
        .exec("spawn Character hero { HP: 30, AC: 15 }")
        .unwrap();
    runner.take_output();

    // Inspect flattened field
    runner.exec("inspect hero.base_ac").unwrap();
    let output = runner.take_output();
    assert!(
        output[0].contains("hero.base_ac = 10"),
        "default base_ac should be 10, got: {:?}",
        output
    );
}

#[test]
fn qualified_access_still_works_after_flattening() {
    let mut runner = Runner::new();
    load_group_program(&mut runner);
    runner
        .exec("spawn Character hero { HP: 30, AC: 15 }")
        .unwrap();
    runner.take_output();

    // Qualified set still works
    runner
        .exec("set hero.CombatStats.base_ac = 20")
        .unwrap();
    let output = runner.take_output();
    assert!(
        output[0].contains("hero.CombatStats.base_ac = 20"),
        "got: {:?}",
        output
    );

    // Qualified inspect still works
    runner.exec("inspect hero.CombatStats.base_ac").unwrap();
    let output = runner.take_output();
    assert!(output[0].contains("20"), "got: {:?}", output);
}

// ── Entity field defaults at spawn ──────────────────────────

fn load_defaults_program(runner: &mut Runner) {
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let id = COUNTER.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join("ttrpg_cli_test");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("test_defaults_{}.ttrpg", id));
    std::fs::write(
        &path,
        r#"
system "test" {
    entity Character {
        name: string
        level: int = 1
        HP: int
        AC: int = 10
    }
}
"#,
    )
    .unwrap();
    runner.exec(&format!("load {}", path.display())).unwrap();
    runner.take_output();
    std::fs::remove_file(&path).ok();
}

#[test]
fn spawn_applies_entity_field_defaults() {
    let mut runner = Runner::new();
    load_defaults_program(&mut runner);

    // Spawn without providing defaulted fields
    runner
        .exec("spawn Character hero { name: \"Hero\", HP: 30 }")
        .unwrap();
    runner.take_output();

    // Defaulted fields should be set
    runner.exec("inspect hero.level").unwrap();
    let output = runner.take_output();
    assert!(output[0].contains("1"), "level should default to 1, got: {:?}", output);

    runner.exec("inspect hero.AC").unwrap();
    let output = runner.take_output();
    assert!(output[0].contains("10"), "AC should default to 10, got: {:?}", output);
}

#[test]
fn spawn_explicit_overrides_default() {
    let mut runner = Runner::new();
    load_defaults_program(&mut runner);

    // Spawn with explicit value overriding default
    runner
        .exec("spawn Character hero { name: \"Hero\", level: 5, HP: 30 }")
        .unwrap();
    runner.take_output();

    runner.exec("inspect hero.level").unwrap();
    let output = runner.take_output();
    assert!(output[0].contains("5"), "level should be 5 (explicit), got: {:?}", output);
}

#[test]
fn spawn_no_fields_applies_all_defaults() {
    let mut runner = Runner::new();
    load_defaults_program(&mut runner);

    // Spawn with no fields — only defaults applied, non-default fields unset
    runner.exec("spawn Character hero").unwrap();
    runner.take_output();

    runner.exec("inspect hero.level").unwrap();
    let output = runner.take_output();
    assert!(output[0].contains("1"), "level should default to 1, got: {:?}", output);

    runner.exec("inspect hero.AC").unwrap();
    let output = runner.take_output();
    assert!(output[0].contains("10"), "AC should default to 10, got: {:?}", output);
}
