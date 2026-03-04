//! OSRIC core types integration test.
//!
//! Verifies that osric/osric_core.ttrpg parses, lowers, and type-checks
//! through the full pipeline without errors. Tests all enums, structs,
//! entities (with optional groups), the Feet unit type, and the ds() derive.

use ttrpg_ast::ast::{DeclKind, TopLevel};
use ttrpg_ast::diagnostic::Severity;
use ttrpg_ast::FileId;
mod osric_common;
#[allow(unused_imports)]
use osric_common::*;

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_core() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    let source = include_str!("../../../osric/osric_core.ttrpg");
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

/// Extract all DeclKind items from the "OSRIC" system block.
fn get_decls(program: &ttrpg_ast::ast::Program) -> &[ttrpg_ast::Spanned<DeclKind>] {
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node {
            if sys.name == "OSRIC" {
                return &sys.decls;
            }
        }
    }
    panic!("no system block named 'OSRIC' found");
}

// ── Parse + typecheck ──────────────────────────────────────────

#[test]
fn osric_core_parses_and_typechecks() {
    let (program, _) = compile_osric_core();
    let has_osric = program
        .items
        .iter()
        .any(|item| matches!(&item.node, TopLevel::System(sys) if sys.name == "OSRIC"));
    assert!(has_osric, "expected system named 'OSRIC'");
}

// ── Enums ──────────────────────────────────────────────────────

#[test]
fn osric_core_has_all_enums() {
    let (program, _) = compile_osric_core();
    let decls = get_decls(&program);
    let enums: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Enum(e) => Some((&*e.name, e.variants.len())),
            _ => None,
        })
        .collect();

    // Ability: STR, DEX, CON, INT, WIS, CHA
    assert!(enums.contains(&("Ability", 6)), "missing Ability enum");
    // Alignment: 9-fold
    assert!(enums.contains(&("Alignment", 9)), "missing Alignment enum");
    // Class: 10 classes
    assert!(enums.contains(&("Class", 10)), "missing Class enum");
    // Ancestry: 7 ancestries
    assert!(enums.contains(&("Ancestry", 7)), "missing Ancestry enum");
    // Size: ordered, 3 variants
    assert!(enums.contains(&("Size", 3)), "missing Size enum");
    // SaveCategory: 5 categories
    assert!(
        enums.contains(&("SaveCategory", 5)),
        "missing SaveCategory enum"
    );
    // CombatGroup: 4 groups
    assert!(
        enums.contains(&("CombatGroup", 4)),
        "missing CombatGroup enum"
    );
    // SpellProgression: 7 variants
    assert!(
        enums.contains(&("SpellProgression", 7)),
        "missing SpellProgression enum"
    );
    // ArmourPermission: 5 levels
    assert!(
        enums.contains(&("ArmourPermission", 5)),
        "missing ArmourPermission enum"
    );
    // ThiefSkill: 8 skills
    assert!(
        enums.contains(&("ThiefSkill", 8)),
        "missing ThiefSkill enum"
    );

    assert_eq!(enums.len(), 11, "expected 11 enums, got {enums:?}");
}

#[test]
fn osric_core_size_is_ordered() {
    let (program, _) = compile_osric_core();
    let decls = get_decls(&program);
    let size_enum = decls
        .iter()
        .find_map(|d| match &d.node {
            DeclKind::Enum(e) if &*e.name == "Size" => Some(e),
            _ => None,
        })
        .expect("Size enum not found");
    assert!(size_enum.ordered, "Size enum should be ordered");
}

#[test]
fn osric_core_enum_variants() {
    let (program, _) = compile_osric_core();
    let decls = get_decls(&program);

    // Spot-check specific variant names
    let class_enum = decls
        .iter()
        .find_map(|d| match &d.node {
            DeclKind::Enum(e) if &*e.name == "Class" => Some(e),
            _ => None,
        })
        .expect("Class enum not found");

    let variant_names: Vec<_> = class_enum
        .variants
        .iter()
        .map(|v| v.name.as_str())
        .collect();

    let expected_classes = [
        "Assassin",
        "Cleric",
        "Druid",
        "Fighter",
        "Illusionist",
        "MagicUser",
        "Monk",
        "Paladin",
        "Ranger",
        "Thief",
    ];
    for name in &expected_classes {
        assert!(
            variant_names.contains(name),
            "Class enum missing variant: {name}"
        );
    }
}

// ── Structs ────────────────────────────────────────────────────

#[test]
fn osric_core_has_all_structs() {
    let (program, _) = compile_osric_core();
    let decls = get_decls(&program);
    let structs: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Struct(s) => Some((&*s.name, s.fields.len())),
            _ => None,
        })
        .collect();

    // SavingThrows: 5 fields
    assert!(
        structs.contains(&("SavingThrows", 5)),
        "missing SavingThrows struct"
    );
    // ClassDef: 14 fields
    assert!(
        structs.iter().any(|(name, _)| *name == "ClassDef"),
        "missing ClassDef struct"
    );
    // AncestryDef: ancestry + size + base_movement + infravision + 6 adj fields
    assert!(
        structs.iter().any(|(name, _)| *name == "AncestryDef"),
        "missing AncestryDef struct"
    );
    // AbilityRange: min, max
    assert!(
        structs.contains(&("AbilityRange", 2)),
        "missing AbilityRange struct"
    );
    // MonsterAttack: name, damage
    assert!(
        structs.contains(&("MonsterAttack", 2)),
        "missing MonsterAttack struct"
    );

    assert_eq!(structs.len(), 5, "expected 5 structs, got {structs:?}");
}

// ── Unit type ──────────────────────────────────────────────────

#[test]
fn osric_core_has_feet_unit() {
    let (program, _) = compile_osric_core();
    let decls = get_decls(&program);
    let units: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Unit(u) => Some((&*u.name, u.suffix.as_deref())),
            _ => None,
        })
        .collect();

    assert!(
        units.contains(&("Feet", Some("ft"))),
        "missing Feet unit with 'ft' suffix, got: {units:?}"
    );
    assert_eq!(units.len(), 1, "expected exactly 1 unit type");
}

// ── Entities ───────────────────────────────────────────────────

#[test]
fn osric_core_has_entities() {
    let (program, _) = compile_osric_core();
    let decls = get_decls(&program);
    let entities: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Entity(e) => Some(&*e.name),
            _ => None,
        })
        .collect();

    assert!(entities.contains(&"Character"), "missing Character entity");
    assert!(entities.contains(&"Monster"), "missing Monster entity");
    assert_eq!(entities.len(), 2, "expected 2 entities");
}

#[test]
fn character_entity_fields() {
    let (program, _) = compile_osric_core();
    let decls = get_decls(&program);
    let character = decls
        .iter()
        .find_map(|d| match &d.node {
            DeclKind::Entity(e) if &*e.name == "Character" => Some(e),
            _ => None,
        })
        .expect("Character entity not found");

    let field_names: Vec<_> = character.fields.iter().map(|f| f.name.as_str()).collect();

    let expected_fields = [
        "name",
        "class",
        "ancestry",
        "level",
        "alignment",
        "abilities",
        "max_hp",
        "hp",
        "armor_ac",
        "shield_ac_bonus",
        "xp",
        "base_movement",
        "current_weight",
        "armour_movement_cap",
        "gold",
        "saving_throws",
    ];
    for name in &expected_fields {
        assert!(
            field_names.contains(name),
            "Character missing field: {name}"
        );
    }
    assert_eq!(
        field_names.len(),
        expected_fields.len(),
        "Character field count mismatch: got {field_names:?}"
    );
}

#[test]
fn character_entity_optional_groups() {
    let (program, _) = compile_osric_core();
    let decls = get_decls(&program);
    let character = decls
        .iter()
        .find_map(|d| match &d.node {
            DeclKind::Entity(e) if &*e.name == "Character" => Some(e),
            _ => None,
        })
        .expect("Character entity not found");

    let group_names: Vec<_> = character
        .optional_groups
        .iter()
        .map(|g| g.name.as_str())
        .collect();

    let expected_groups = [
        "ExceptionalStrength",
        "Spellcasting",
        "ThiefSkills",
        "TurnUndead",
    ];
    for name in &expected_groups {
        assert!(
            group_names.contains(name),
            "Character missing optional group: {name}"
        );
    }
    assert_eq!(
        group_names.len(),
        expected_groups.len(),
        "optional group count mismatch: got {group_names:?}"
    );

    // All groups are inline (not external refs) and optional (not required)
    for group in &character.optional_groups {
        assert!(
            !group.is_external_ref,
            "{} should be inline, not external",
            group.name
        );
        assert!(
            !group.is_required,
            "{} should be optional, not required",
            group.name
        );
    }
}

#[test]
fn exceptional_strength_group_has_percentile() {
    let (program, _) = compile_osric_core();
    let decls = get_decls(&program);
    let character = decls
        .iter()
        .find_map(|d| match &d.node {
            DeclKind::Entity(e) if &*e.name == "Character" => Some(e),
            _ => None,
        })
        .expect("Character entity not found");

    let exc_str = character
        .optional_groups
        .iter()
        .find(|g| g.name.as_str() == "ExceptionalStrength")
        .expect("ExceptionalStrength group not found");

    let field_names: Vec<_> = exc_str.fields.iter().map(|f| f.name.as_str()).collect();
    assert_eq!(field_names, vec!["percentile"]);
}

#[test]
fn monster_entity_fields() {
    let (program, _) = compile_osric_core();
    let decls = get_decls(&program);
    let monster = decls
        .iter()
        .find_map(|d| match &d.node {
            DeclKind::Entity(e) if &*e.name == "Monster" => Some(e),
            _ => None,
        })
        .expect("Monster entity not found");

    let field_names: Vec<_> = monster.fields.iter().map(|f| f.name.as_str()).collect();

    let expected_fields = [
        "name", "hit_dice", "max_hp", "hp", "ac", "morale", "xp_value", "attacks", "size",
        "special",
    ];
    for name in &expected_fields {
        assert!(field_names.contains(name), "Monster missing field: {name}");
    }
    assert_eq!(
        field_names.len(),
        expected_fields.len(),
        "Monster field count mismatch: got {field_names:?}"
    );

    // Monster should have no optional groups
    assert!(
        monster.optional_groups.is_empty(),
        "Monster should have no optional groups"
    );
}

// ── Derives ────────────────────────────────────────────────────

#[test]
fn osric_core_monster_attack_uses_dice_expr() {
    // MonsterAttack.damage should be DiceExpr (not the old DiceSpec struct)
    let (program, _) = compile_osric_core();
    let decls = get_decls(&program);
    let structs: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Struct(s) => Some(&*s.name),
            _ => None,
        })
        .collect();

    assert!(
        structs.contains(&"MonsterAttack"),
        "missing MonsterAttack struct"
    );
    // DiceSpec should no longer exist
    assert!(
        !structs.contains(&"DiceSpec"),
        "DiceSpec should have been removed"
    );
}
