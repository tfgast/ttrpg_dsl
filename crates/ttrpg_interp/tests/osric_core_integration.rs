//! OSRIC core types integration test.
//!
//! Verifies that osric/osric_core.ttrpg parses, lowers, and type-checks
//! through the full pipeline without errors. Tests all enums, structs,
//! entities (with optional groups), the Feet unit type, and the ds() derive.

use ttrpg_ast::ast::{DeclKind, TopLevel};
mod osric_common;
use osric_common::{all_osric_sources, compile_osric_sources};

// ── Compile helpers ────────────────────────────────────────────

fn compile_osric_core() -> (ttrpg_ast::ast::Program, ttrpg_checker::CheckResult) {
    compile_osric_sources(all_osric_sources())
}

/// Extract all DeclKind items from the "OSRIC" system block.
fn get_decls(program: &ttrpg_ast::ast::Program) -> &[ttrpg_ast::Spanned<DeclKind>] {
    for item in &program.items {
        if let TopLevel::System(sys) = &item.node
            && sys.name == "OSRIC"
        {
            return &sys.decls;
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
    // Size: ordered, 6 variants
    assert!(enums.contains(&("Size", 6)), "missing Size enum");
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
    // DamageType: 11 variants (Slashing, Piercing, Blunt, Fire, Cold, Lightning, Acid, Poison, Corrosion, Disintegrate, Fall)
    assert!(
        enums.contains(&("DamageType", 11)),
        "missing DamageType enum"
    );
    // MeleeWeapon: 27 variants
    assert!(
        enums.contains(&("MeleeWeapon", 27)),
        "missing MeleeWeapon enum"
    );
    // MissileWeapon: 15 variants
    assert!(
        enums.contains(&("MissileWeapon", 15)),
        "missing MissileWeapon enum"
    );
    // ArmourType: 10 variants
    assert!(
        enums.contains(&("ArmourType", 10)),
        "missing ArmourType enum"
    );
    // ShieldType: 3 variants
    assert!(
        enums.contains(&("ShieldType", 3)),
        "missing ShieldType enum"
    );
    // WieldedItem: 2 data-carrying variants
    assert!(
        enums.contains(&("WieldedItem", 2)),
        "missing WieldedItem enum"
    );
    // ClassingMode: 3 variants
    assert!(
        enums.contains(&("ClassingMode", 3)),
        "missing ClassingMode enum"
    );
    // EncumbranceTier: 5 variants
    assert!(
        enums.contains(&("EncumbranceTier", 5)),
        "missing EncumbranceTier enum"
    );

    // SpellClassType: 4 variants
    assert!(
        enums.contains(&("SpellClassType", 4)),
        "missing SpellClassType enum"
    );
    // SpellSchool: 8 variants
    assert!(
        enums.contains(&("SpellSchool", 8)),
        "missing SpellSchool enum"
    );
    // SpellRange: 5 variants
    assert!(
        enums.contains(&("SpellRange", 5)),
        "missing SpellRange enum"
    );
    // SpellDuration: 8 variants
    assert!(
        enums.contains(&("SpellDuration", 8)),
        "missing SpellDuration enum"
    );
    // ZoneShape: 5 variants
    assert!(enums.contains(&("ZoneShape", 5)), "missing ZoneShape enum");
    // CastingTime: 5 variants
    assert!(
        enums.contains(&("CastingTime", 5)),
        "missing CastingTime enum"
    );
    // SpellSave: 4 variants
    assert!(enums.contains(&("SpellSave", 4)), "missing SpellSave enum");

    // SpecLevel: 2 variants (Single, Double)
    assert!(enums.contains(&("SpecLevel", 2)), "missing SpecLevel enum");
    // SpecWeapon: 2 variants (SpecMelee, SpecMissile)
    assert!(
        enums.contains(&("SpecWeapon", 2)),
        "missing SpecWeapon enum"
    );

    // SpellId: 18 variants (13 original + Silence15Radius, ProtectionFromEvil10Radius, WallOfFire, BladeBarrier, GlyphOfWarding)
    assert!(enums.contains(&("SpellId", 18)), "missing SpellId enum");

    // AreaShape: 7 variants (Radius, Sphere, Cube, Wall, Cone, Line, Special)
    assert!(enums.contains(&("AreaShape", 7)), "missing AreaShape enum");
    // AnchorMode: 3 variants (PositionOnly, EntityOnly, Either)
    assert!(
        enums.contains(&("AnchorMode", 3)),
        "missing AnchorMode enum"
    );
    // AnchorPoint: 2 variants (AtPosition, AtEntity)
    assert!(
        enums.contains(&("AnchorPoint", 2)),
        "missing AnchorPoint enum"
    );

    // EffectSource: 5 variants (Unknown, Spell, Item, Poison, MonsterAbility)
    assert!(
        enums.contains(&("EffectSource", 5)),
        "missing EffectSource enum"
    );

    // ContactMode: 2 variants (None, Crossed)
    assert!(
        enums.contains(&("ContactMode", 2)),
        "missing ContactMode enum"
    );

    // SpellUseLimit: 2 variants (AtWill, PerDay)
    assert!(
        enums.contains(&("SpellUseLimit", 2)),
        "missing SpellUseLimit enum"
    );

    assert_eq!(enums.len(), 37, "expected 37 enums, got {enums:?}");
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
    // Armor: armour_type, magic_bonus
    assert!(structs.contains(&("Armor", 2)), "missing Armor struct");
    // Shield: shield_type, magic_bonus
    assert!(structs.contains(&("Shield", 2)), "missing Shield struct");
    // ClassLevel: class, level, xp
    assert!(
        structs.contains(&("ClassLevel", 3)),
        "missing ClassLevel struct"
    );

    // SpellComponents: verbal, somatic, material
    assert!(
        structs.contains(&("SpellComponents", 3)),
        "missing SpellComponents struct"
    );
    // SpellDef: 12 fields
    assert!(
        structs.contains(&("SpellDef", 12)),
        "missing SpellDef struct"
    );

    // DrainEvent: class, original_level, timestamp
    assert!(
        structs.contains(&("DrainEvent", 3)),
        "missing DrainEvent struct"
    );
    // HpRoll: class, level, amount
    assert!(structs.contains(&("HpRoll", 3)), "missing HpRoll struct");
    // SpellSlotTrack: class_type, spell_slots, slots_used
    assert!(
        structs.contains(&("SpellSlotTrack", 3)),
        "missing SpellSlotTrack struct"
    );
    // MemorizedSpell: id, level, class_type
    assert!(
        structs.contains(&("MemorizedSpell", 3)),
        "missing MemorizedSpell struct"
    );

    // SpellArea: shape, anchor_mode
    assert!(
        structs.contains(&("SpellArea", 2)),
        "missing SpellArea struct"
    );
    // Placement: anchor, position, orientation
    assert!(
        structs.contains(&("Placement", 3)),
        "missing Placement struct"
    );

    // SpellLikeEntry: spell, uses, uses_remaining, override_caster_level
    assert!(
        structs.contains(&("SpellLikeEntry", 4)),
        "missing SpellLikeEntry struct"
    );

    assert_eq!(structs.len(), 19, "expected 19 structs, got {structs:?}");
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
    assert!(entities.contains(&"Zone"), "missing Zone entity");
    assert_eq!(entities.len(), 3, "expected 3 entities");
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

    // Only directly declared fields; include-group fields (HitPoints,
    // EquipmentSlots) are in optional_groups with is_required=true.
    let expected_fields = [
        "name",
        "classes",
        "classing_mode",
        "ancestry",
        "alignment",
        "abilities",
        "age",
        "base_movement",
        "drain_history",
        "hp_rolls",
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

    // Include groups (required, external ref)
    let expected_includes = ["HitPoints", "EquipmentSlots"];
    // Optional groups (not required)
    let expected_optionals = [
        "ExceptionalStrength",
        "Spellcasting",
        "ThiefSkills",
        "TurnUndead",
        "WeaponSpecialization",
        "Inventory",
        "HenchmanMorale",
    ];

    for name in expected_includes.iter().chain(expected_optionals.iter()) {
        assert!(
            group_names.contains(name),
            "Character missing group: {name}"
        );
    }
    assert_eq!(
        group_names.len(),
        expected_includes.len() + expected_optionals.len(),
        "group count mismatch: got {group_names:?}"
    );

    // Verify include groups are required + external
    for name in &expected_includes {
        let g = character
            .optional_groups
            .iter()
            .find(|g| g.name.as_str() == *name)
            .unwrap();
        assert!(g.is_required, "{name} should be required (include)");
        assert!(g.is_external_ref, "{name} should be external ref");
    }

    // Verify optional groups are not required
    for name in &expected_optionals {
        let g = character
            .optional_groups
            .iter()
            .find(|g| g.name.as_str() == *name)
            .unwrap();
        assert!(!g.is_required, "{name} should be optional, not required");
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
        "name",
        "hit_dice",
        "max_hp",
        "hp",
        "ac",
        "morale",
        "morale_checks_made",
        "xp_value",
        "intelligence",
        "alignment",
        "base_movement",
        "attacks",
        "size",
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

    // Monster should have EquipmentSlots and BreathWeapon as optional groups
    let opt_names: Vec<_> = monster
        .optional_groups
        .iter()
        .map(|g| g.name.as_str())
        .collect();
    assert!(
        opt_names.contains(&"EquipmentSlots"),
        "Monster should have optional EquipmentSlots, got {opt_names:?}"
    );
    assert!(
        opt_names.contains(&"BreathWeapon"),
        "Monster should have optional BreathWeapon, got {opt_names:?}"
    );
}

#[test]
fn zone_entity_fields() {
    let (program, _) = compile_osric_core();
    let decls = get_decls(&program);
    let zone = decls
        .iter()
        .find_map(|d| match &d.node {
            DeclKind::Entity(e) if &*e.name == "Zone" => Some(e),
            _ => None,
        })
        .expect("Zone entity not found");

    let field_names: Vec<_> = zone.fields.iter().map(|f| f.name.as_str()).collect();
    let expected_fields = [
        "name",
        "source",
        "creator",
        "anchor",
        "moves_with_anchor",
        "center",
        "shape",
        "active",
        "created_at",
        "contact_mode",
        "tracks_occupancy",
        "trigger",
    ];
    for name in &expected_fields {
        assert!(field_names.contains(name), "Zone missing field: {name}");
    }
    assert_eq!(
        field_names.len(),
        expected_fields.len(),
        "Zone field count mismatch: got {field_names:?}"
    );
}

#[test]
fn osric_core_has_zone_events() {
    let (program, _) = compile_osric_core();
    let decls = get_decls(&program);
    let events: Vec<_> = decls
        .iter()
        .filter_map(|d| match &d.node {
            DeclKind::Event(e) => Some(&*e.name),
            _ => None,
        })
        .collect();

    let expected_events = ["ZoneEntered", "ZoneExited", "ZoneCrossed", "ZoneExpired"];
    for name in &expected_events {
        assert!(events.contains(name), "missing zone event: {name}");
    }
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
