//! OSE core types integration test.
//!
//! Verifies that ose/ose_core.ttrpg parses, lowers, and type-checks
//! through the full pipeline without errors.

use ttrpg_ast::FileId;
use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_ast::diagnostic::Severity;

fn compile_ose_core() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    let source = include_str!("../../../ose/ose_core.ttrpg");
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

/// Extract all DeclKind items from the first system block.
fn get_decls(program: &ttrpg_ast::ast::Program) -> &[ttrpg_ast::Spanned<DeclKind>] {
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            return &sys.decls;
        }
    }
    panic!("no system block found");
}

#[test]
fn ose_core_parses_and_typechecks() {
    let (program, _result) = compile_ose_core();
    // Should have one system block named "OSE"
    let has_ose = program.items.iter().any(|item| {
        matches!(&item.node, TopLevel::System(sys) if sys.name == "OSE")
    });
    assert!(has_ose, "expected system named 'OSE'");
}

#[test]
fn ose_core_has_all_enums() {
    let (program, _) = compile_ose_core();
    let decls = get_decls(&program);
    let enums: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Enum(e) => Some((&*e.name, e.variants.len())),
            _ => None,
        })
        .collect();
    assert!(enums.contains(&("Ability", 6)));
    assert!(enums.contains(&("Alignment", 3)));
    assert!(enums.contains(&("Class", 22)));
    assert!(enums.contains(&("SaveCategory", 13)));
    assert!(enums.contains(&("CombatAptitude", 3)));
    assert!(enums.contains(&("ArmourPermission", 5)));
    assert!(enums.contains(&("SpellProgression", 9)));
    assert!(enums.contains(&("SpellListType", 6)));
    assert!(enums.contains(&("EncumbranceLevel", 5)));
    assert!(enums.contains(&("ThiefSkill", 8)));
    assert!(enums.contains(&("TurnResult", 4)));
    assert_eq!(enums.len(), 11, "expected 11 enums total");
}

#[test]
fn ose_core_has_structs() {
    let (program, _) = compile_ose_core();
    let decls = get_decls(&program);
    let structs: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Struct(s) => Some((&*s.name, s.fields.len())),
            _ => None,
        })
        .collect();
    assert!(structs.contains(&("SavingThrows", 5)));
    assert!(structs.contains(&("ClassDef", 11)));
    assert_eq!(structs.len(), 2, "expected 2 structs total");
}

#[test]
fn ose_core_has_entities() {
    let (program, _) = compile_ose_core();
    let decls = get_decls(&program);
    let entities: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Entity(e) => Some(&*e.name),
            _ => None,
        })
        .collect();
    assert!(entities.contains(&"Character"));
    assert!(entities.contains(&"Monster"));
    assert_eq!(entities.len(), 2, "expected 2 entities total");
}
