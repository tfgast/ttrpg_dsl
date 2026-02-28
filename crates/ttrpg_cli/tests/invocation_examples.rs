//! Integration tests for the invocation tracking example files.
//!
//! These tests load the D&D 5e concentration and PF2e sustained spell
//! examples and verify end-to-end runtime behavior through the CLI Runner.

use std::sync::atomic::{AtomicU64, Ordering};
use ttrpg_cli::runner::Runner;

// ── Helpers ──────────────────────────────────────────────────

/// Write source to a unique temp file and return the path.
fn write_temp(name: &str, source: &str) -> std::path::PathBuf {
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let id = COUNTER.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join("ttrpg_cli_inv_test");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{}_{}.ttrpg", name, id));
    std::fs::write(&path, source).unwrap();
    path
}

/// Load the 5e concentration example into a Runner, returning the Runner.
fn load_5e_concentration() -> Runner {
    let source = include_str!("../../../examples/dnd5e_concentration.ttrpg");
    let path = write_temp("dnd5e_conc", source);
    let mut runner = Runner::new();
    runner.exec(&format!("load {}", path.display())).unwrap();
    runner.take_output();
    std::fs::remove_file(&path).ok();
    runner
}

/// Load the PF2e sustained example into a Runner, returning the Runner.
fn load_pf2e_sustained() -> Runner {
    let source = include_str!("../../../examples/pf2e_sustained.ttrpg");
    let path = write_temp("pf2e_sust", source);
    let mut runner = Runner::new();
    runner.exec(&format!("load {}", path.display())).unwrap();
    runner.take_output();
    std::fs::remove_file(&path).ok();
    runner
}

/// Execute a command, consume output, return it.
fn exec(runner: &mut Runner, cmd: &str) -> Vec<String> {
    runner.exec(cmd).unwrap();
    runner.take_output()
}

/// Spawn a 5e Character with standard fields (no Position — not needed
/// for invocation tracking tests).
fn spawn_5e(runner: &mut Runner, handle: &str, fields: &str) {
    runner
        .exec(&format!("spawn Character {} {{ {} }}", handle, fields))
        .unwrap();
    runner.take_output();
}

/// Standard 5e caster fields.
const CASTER_FIELDS: &str = "name: \"Caster\", level: 5, abilities: { STR: 10, DEX: 12, CON: 14, INT: 18, WIS: 16, CHA: 10 }, AC: 12, HP: 30, max_HP: 30, speed: 30, concentrating_on: none";

/// Standard 5e target fields.
const TARGET_FIELDS: &str = "name: \"Target\", level: 1, abilities: { STR: 8, DEX: 14, CON: 10, INT: 6, WIS: 8, CHA: 6 }, AC: 13, HP: 20, max_HP: 20, speed: 30";

/// Standard PF2e caster fields.
const PF2E_CASTER: &str = "name: \"Druid\", level: 5, abilities: { STR: 10, DEX: 12, CON: 14, INT: 10, WIS: 18, CHA: 10 }, AC: 16, HP: 50, max_HP: 50, speed: 25, sustained_1: none, sustained_2: none";

/// Standard PF2e target fields.
const PF2E_TARGET: &str = "name: \"Goblin\", level: 1, abilities: { STR: 8, DEX: 14, CON: 10, INT: 6, WIS: 8, CHA: 6 }, AC: 13, HP: 20, max_HP: 20, speed: 25";

/// Standard PF2e ally fields.
const PF2E_ALLY: &str = "name: \"Ally\", level: 3, abilities: { STR: 16, DEX: 12, CON: 14, INT: 8, WIS: 10, CHA: 10 }, AC: 18, HP: 40, max_HP: 40, speed: 25";

// ═══════════════════════════════════════════════════════════════
//  D&D 5e Concentration Tests
// ═══════════════════════════════════════════════════════════════

#[test]
fn concentration_cast_bless_applies_condition_and_tracks_invocation() {
    let mut r = load_5e_concentration();
    spawn_5e(&mut r, "caster", CASTER_FIELDS);
    spawn_5e(&mut r, "ally", TARGET_FIELDS);

    let output = exec(&mut r, "do CastBless(caster, [ally])");
    // Action should succeed
    assert!(
        output.iter().any(|l| l.contains("succeeded")),
        "CastBless should succeed: {:?}",
        output
    );
    // Condition should be applied
    assert!(
        output.iter().any(|l| l.contains("Blessed")),
        "should apply Blessed condition: {:?}",
        output
    );
    // Hook should fire and set concentrating_on
    assert!(
        output.iter().any(|l| l.contains("on_conc")),
        "on_conc hook should fire: {:?}",
        output
    );

    // Verify condition is on the ally
    let conds = exec(&mut r, "conditions");
    assert!(
        conds.iter().any(|l| l.contains("ally") && l.contains("Blessed")),
        "ally should have Blessed condition: {:?}",
        conds
    );

    // Verify concentrating_on is set
    let field = exec(&mut r, "inspect caster.concentrating_on");
    assert!(
        field[0].contains("some(Invocation("),
        "concentrating_on should be set: {:?}",
        field
    );
}

#[test]
fn concentration_recast_revokes_previous_spell() {
    let mut r = load_5e_concentration();
    spawn_5e(&mut r, "caster", CASTER_FIELDS);
    spawn_5e(&mut r, "ally", TARGET_FIELDS);
    spawn_5e(&mut r, "enemy", TARGET_FIELDS);

    // Cast Bless on ally
    exec(&mut r, "do CastBless(caster, [ally])");

    // Ally should have Blessed
    let conds = exec(&mut r, "conditions");
    assert!(
        conds.iter().any(|l| l.contains("ally") && l.contains("Blessed")),
        "ally should have Blessed: {:?}",
        conds
    );

    // Now cast Hex on enemy (different concentration spell)
    let output = exec(&mut r, "do CastHex(caster, enemy)");

    // Hook should revoke the old invocation
    assert!(
        output.iter().any(|l| l.contains("RevokeInvocation")),
        "on_conc hook should revoke old invocation: {:?}",
        output
    );

    // After recasting: only Hexed should remain, Blessed should be gone
    let conds = exec(&mut r, "conditions");
    assert!(
        conds.iter().any(|l| l.contains("enemy") && l.contains("Hexed")),
        "enemy should have Hexed: {:?}",
        conds
    );
    assert!(
        !conds.iter().any(|l| l.contains("Blessed")),
        "Blessed should be revoked: {:?}",
        conds
    );

    // concentrating_on should point to the new invocation
    let field = exec(&mut r, "inspect caster.concentrating_on");
    assert!(
        field[0].contains("some(Invocation("),
        "concentrating_on should still be set: {:?}",
        field
    );
}

#[test]
fn concentration_multi_target_bless_all_revoked_together() {
    let mut r = load_5e_concentration();
    spawn_5e(&mut r, "caster", CASTER_FIELDS);
    spawn_5e(&mut r, "alice", TARGET_FIELDS);
    spawn_5e(&mut r, "bob", TARGET_FIELDS);
    spawn_5e(&mut r, "enemy", TARGET_FIELDS);

    // Bless two targets
    exec(&mut r, "do CastBless(caster, [alice, bob])");

    let conds = exec(&mut r, "conditions");
    assert!(
        conds.iter().any(|l| l.contains("alice") && l.contains("Blessed")),
        "alice should have Blessed: {:?}",
        conds
    );
    assert!(
        conds.iter().any(|l| l.contains("bob") && l.contains("Blessed")),
        "bob should have Blessed: {:?}",
        conds
    );

    // Cast Hex — should revoke ALL Blessed conditions (both targets)
    exec(&mut r, "do CastHex(caster, enemy)");

    let conds = exec(&mut r, "conditions");
    assert!(
        !conds.iter().any(|l| l.contains("Blessed")),
        "all Blessed conditions should be revoked: {:?}",
        conds
    );
    assert!(
        conds.iter().any(|l| l.contains("Hexed")),
        "Hexed should remain: {:?}",
        conds
    );
}

#[test]
fn concentration_save_succeeds_keeps_spell() {
    let mut r = load_5e_concentration();
    spawn_5e(&mut r, "caster", CASTER_FIELDS);
    spawn_5e(&mut r, "ally", TARGET_FIELDS);
    spawn_5e(&mut r, "attacker", &format!("{}, AC: 15, HP: 40, max_HP: 40",
        "name: \"Attacker\", level: 5, abilities: { STR: 16, DEX: 12, CON: 14, INT: 8, WIS: 10, CHA: 10 }, speed: 30"));

    // Cast Bless
    exec(&mut r, "do CastBless(caster, [ally])");

    // Attack the caster — use queued rolls to control the result
    // Attack roll: needs to beat AC 12, let's ensure a hit
    // d20 (attack roll) = 18, d8 (damage) = 4 → damage = 4 + modifier(16) = 4 + 3 = 7
    // Concentration save DC = max(10, floor(7/2)) = 10
    // d20 (con save) = 15 + modifier(14) = 15 + 2 = 17 >= 10 → saves
    exec(&mut r, "rolls 18 4 15");
    exec(&mut r, "do Attack(attacker, caster)");

    // Caster should still be concentrating
    let field = exec(&mut r, "inspect caster.concentrating_on");
    assert!(
        field[0].contains("some(Invocation("),
        "concentration should be maintained on successful save: {:?}",
        field
    );

    // Blessed should still be on the ally
    let conds = exec(&mut r, "conditions");
    assert!(
        conds.iter().any(|l| l.contains("Blessed")),
        "Blessed should persist after successful save: {:?}",
        conds
    );
}

#[test]
fn concentration_save_fails_revokes_spell() {
    let mut r = load_5e_concentration();
    spawn_5e(&mut r, "caster", CASTER_FIELDS);
    spawn_5e(&mut r, "ally", TARGET_FIELDS);
    spawn_5e(&mut r, "attacker", &format!("{}, AC: 15, HP: 40, max_HP: 40",
        "name: \"Attacker\", level: 5, abilities: { STR: 16, DEX: 12, CON: 14, INT: 8, WIS: 10, CHA: 10 }, speed: 30"));

    // Cast Bless
    exec(&mut r, "do CastBless(caster, [ally])");

    // Attack the caster — use queued rolls to ensure save fails
    // d20 (attack roll) = 18, d8 (damage) = 6 → damage = 6 + 3 = 9
    // Concentration save DC = max(10, floor(9/2)) = 10
    // d20 (con save) = 3 + modifier(14) = 3 + 2 = 5 < 10 → fails
    exec(&mut r, "rolls 18 6 3");
    let output = exec(&mut r, "do Attack(attacker, caster)");

    // ConcentrationSave hook should fire and revoke
    assert!(
        output.iter().any(|l| l.contains("ConcentrationSave")),
        "ConcentrationSave hook should fire: {:?}",
        output
    );
    assert!(
        output.iter().any(|l| l.contains("RevokeInvocation")),
        "failed save should revoke: {:?}",
        output
    );

    // Concentration should be lost
    let field = exec(&mut r, "inspect caster.concentrating_on");
    assert!(
        field[0].contains("none"),
        "concentrating_on should be none after failed save: {:?}",
        field
    );

    // Blessed should be gone
    let conds = exec(&mut r, "conditions");
    assert!(
        !conds.iter().any(|l| l.contains("Blessed")),
        "Blessed should be revoked after failed save: {:?}",
        conds
    );
}

#[test]
fn concentration_none_initial_revoke_is_noop() {
    // First concentration spell should work even though
    // concentrating_on starts as none (revoke(none) is a no-op).
    let mut r = load_5e_concentration();
    spawn_5e(&mut r, "caster", CASTER_FIELDS);
    spawn_5e(&mut r, "target", TARGET_FIELDS);

    let output = exec(&mut r, "do CastHex(caster, target)");

    // Should succeed without errors
    assert!(
        output.iter().any(|l| l.contains("succeeded")),
        "first concentration spell should succeed: {:?}",
        output
    );
    // No RevokeInvocation should appear (revoke(none) is silent)
    assert!(
        !output.iter().any(|l| l.contains("RevokeInvocation")),
        "revoke(none) should not emit RevokeInvocation: {:?}",
        output
    );
}

#[test]
fn concentration_hold_person_with_save() {
    let mut r = load_5e_concentration();
    spawn_5e(&mut r, "caster", CASTER_FIELDS);
    // Target with low WIS to fail the save
    spawn_5e(&mut r, "target", TARGET_FIELDS);

    // Queue a low save roll so the target fails
    // Save DC = 8 + proficiency_bonus(5) + modifier(16) = 8 + 3 + 3 = 14
    // Actually, caster WIS is 16: modifier = 3, proficiency_bonus(5) = 3, DC = 8 + 3 + 3 = 14
    // Target rolls d20 + modifier(WIS=8) = d20 + (-1)
    // Queue d20 = 5 → total = 4 < 14 → fails → held
    exec(&mut r, "rolls 5");
    let output = exec(&mut r, "do CastHoldPerson(caster, target)");

    assert!(
        output.iter().any(|l| l.contains("HeldByPerson")),
        "target should get HeldByPerson on failed save: {:?}",
        output
    );

    let conds = exec(&mut r, "conditions");
    assert!(
        conds.iter().any(|l| l.contains("HeldByPerson")),
        "HeldByPerson should be active: {:?}",
        conds
    );

    // Concentration should be tracked
    let field = exec(&mut r, "inspect caster.concentrating_on");
    assert!(
        field[0].contains("some(Invocation("),
        "concentrating_on should be set for Hold Person: {:?}",
        field
    );
}

#[test]
fn concentration_hold_person_save_succeeds_no_effect() {
    let mut r = load_5e_concentration();
    spawn_5e(&mut r, "caster", CASTER_FIELDS);
    spawn_5e(&mut r, "target", TARGET_FIELDS);

    // Queue a high save roll so the target succeeds
    // DC = 14, target d20 + modifier(WIS=8) = d20 - 1
    // Queue d20 = 20 → total = 19 >= 14 → saves
    exec(&mut r, "rolls 20");
    exec(&mut r, "do CastHoldPerson(caster, target)");

    // No condition should be applied
    let conds = exec(&mut r, "conditions");
    assert!(
        !conds.iter().any(|l| l.contains("HeldByPerson")),
        "target should not be held on successful save: {:?}",
        conds
    );

    // No concentration — the spell didn't take effect
    // (ConcentrationStarted is only emitted inside the if-block)
    let field = exec(&mut r, "inspect caster.concentrating_on");
    assert!(
        field[0].contains("none"),
        "concentrating_on should remain none when spell fails: {:?}",
        field
    );
}

// ═══════════════════════════════════════════════════════════════
//  PF2e Sustained Spell Tests
// ═══════════════════════════════════════════════════════════════

/// Spawn a PF2e Character.
fn spawn_pf2e(runner: &mut Runner, handle: &str, fields: &str) {
    runner
        .exec(&format!("spawn Character {} {{ {} }}", handle, fields))
        .unwrap();
    runner.take_output();
}

#[test]
fn sustained_cast_fills_first_slot() {
    let mut r = load_pf2e_sustained();
    spawn_pf2e(&mut r, "druid", PF2E_CASTER);
    spawn_pf2e(&mut r, "goblin", PF2E_TARGET);

    // Queue rolls: save (d20=1, low so damage hits), damage (3d6: 3,4,5 = 12)
    exec(&mut r, "rolls 1 3 4 5");
    let output = exec(&mut r, "do CastFlamingSphere(druid, goblin)");

    // Action should succeed
    assert!(
        output.iter().any(|l| l.contains("succeeded") && l.contains("CastFlamingSphere")),
        "CastFlamingSphere should succeed: {:?}",
        output
    );

    // Caster should have the sustaining condition
    let conds = exec(&mut r, "conditions");
    assert!(
        conds.iter().any(|l| l.contains("Sustaining_Flaming_Sphere")),
        "druid should have Sustaining_Flaming_Sphere: {:?}",
        conds
    );

    // First sustained slot should be filled
    let slot = exec(&mut r, "inspect druid.sustained_1");
    assert!(
        slot[0].contains("some(Invocation("),
        "sustained_1 should hold the invocation: {:?}",
        slot
    );

    // Second slot should still be empty
    let slot2 = exec(&mut r, "inspect druid.sustained_2");
    assert!(
        slot2[0].contains("none"),
        "sustained_2 should still be none: {:?}",
        slot2
    );
}

#[test]
fn sustained_two_spells_fill_both_slots() {
    let mut r = load_pf2e_sustained();
    spawn_pf2e(&mut r, "druid", PF2E_CASTER);
    spawn_pf2e(&mut r, "goblin", PF2E_TARGET);
    spawn_pf2e(&mut r, "ally", PF2E_ALLY);

    // Cast Flaming Sphere (2 actions) — queue rolls for save+damage
    exec(&mut r, "rolls 1 3 4 5");
    exec(&mut r, "do CastFlamingSphere(druid, goblin)");

    // Cast Inspire Courage (1 action)
    exec(&mut r, "do CastInspireCourage(druid, ally)");

    // Both slots should be filled
    let slot1 = exec(&mut r, "inspect druid.sustained_1");
    assert!(
        slot1[0].contains("some(Invocation("),
        "sustained_1 should be set: {:?}",
        slot1
    );

    let slot2 = exec(&mut r, "inspect druid.sustained_2");
    assert!(
        slot2[0].contains("some(Invocation("),
        "sustained_2 should be set: {:?}",
        slot2
    );

    // Both conditions should be active
    let conds = exec(&mut r, "conditions");
    assert!(
        conds.iter().any(|l| l.contains("Sustaining_Flaming_Sphere")),
        "Sustaining_Flaming_Sphere should be active: {:?}",
        conds
    );
    assert!(
        conds.iter().any(|l| l.contains("InspiredCourage")),
        "InspiredCourage should be active: {:?}",
        conds
    );
}

#[test]
fn sustained_dismiss_revokes_conditions_and_clears_slot() {
    let mut r = load_pf2e_sustained();
    spawn_pf2e(&mut r, "druid", PF2E_CASTER);
    spawn_pf2e(&mut r, "goblin", PF2E_TARGET);
    spawn_pf2e(&mut r, "ally", PF2E_ALLY);

    // Cast both spells
    exec(&mut r, "rolls 1 3 4 5");
    exec(&mut r, "do CastFlamingSphere(druid, goblin)");
    exec(&mut r, "do CastInspireCourage(druid, ally)");

    // Read the first slot's invocation value for dismiss
    let slot1 = exec(&mut r, "inspect druid.sustained_1");
    assert!(slot1[0].contains("some(Invocation("));

    // Dismiss the first spell by passing its invocation
    // We need to get the raw Invocation value. Use eval to extract it.
    let output = exec(&mut r, "do DismissSpell(druid, druid.sustained_1)");
    assert!(
        output.iter().any(|l| l.contains("RevokeInvocation")),
        "DismissSpell should revoke the invocation: {:?}",
        output
    );

    // First slot should be cleared
    let slot1 = exec(&mut r, "inspect druid.sustained_1");
    assert!(
        slot1[0].contains("none"),
        "sustained_1 should be none after dismiss: {:?}",
        slot1
    );

    // Sustaining_Flaming_Sphere should be gone
    let conds = exec(&mut r, "conditions");
    assert!(
        !conds.iter().any(|l| l.contains("Sustaining_Flaming_Sphere")),
        "Sustaining_Flaming_Sphere should be revoked: {:?}",
        conds
    );

    // InspiredCourage should still be active (different invocation)
    assert!(
        conds.iter().any(|l| l.contains("InspiredCourage")),
        "InspiredCourage should survive dismiss of other spell: {:?}",
        conds
    );

    // Second slot should still hold its invocation
    let slot2 = exec(&mut r, "inspect druid.sustained_2");
    assert!(
        slot2[0].contains("some(Invocation("),
        "sustained_2 should still be set: {:?}",
        slot2
    );
}

#[test]
fn sustained_inspire_courage_modifies_attack() {
    let mut r = load_pf2e_sustained();
    spawn_pf2e(&mut r, "bard", PF2E_CASTER);
    spawn_pf2e(&mut r, "ally", PF2E_ALLY);
    spawn_pf2e(&mut r, "enemy", PF2E_TARGET);

    // Cast Inspire Courage on ally
    exec(&mut r, "do CastInspireCourage(bard, ally)");

    // Verify the condition is active
    let conds = exec(&mut r, "conditions");
    assert!(
        conds.iter().any(|l| l.contains("InspiredCourage")),
        "InspiredCourage should be active: {:?}",
        conds
    );

    // Ally attacks with the buff — the modify clause adds +1 to attack_roll.
    // Queue a known roll so we can verify the bonus applies.
    // d20 = 10, modifier(STR=16) = 3, bonus from InspiredCourage = 1
    // Total = 10 + 3 + 1 = 14 >= AC 13 → hit
    exec(&mut r, "rolls 10 5");
    let output = exec(&mut r, "do Strike(ally, enemy)");

    // Strike should succeed
    assert!(
        output.iter().any(|l| l.contains("succeeded") && l.contains("Strike")),
        "Strike should succeed: {:?}",
        output
    );

    // Damage should have been dealt (enemy HP reduced)
    assert!(
        output.iter().any(|l| l.contains("HP") && l.contains("->")),
        "enemy should take damage: {:?}",
        output
    );
}

#[test]
fn sustained_flaming_sphere_deals_damage_on_cast() {
    let mut r = load_pf2e_sustained();
    spawn_pf2e(&mut r, "druid", PF2E_CASTER);
    spawn_pf2e(&mut r, "goblin", PF2E_TARGET);

    // Queue rolls: save (d20=1 + modifier(DEX=14)=2 → 3 < DC), damage (3d6: 6,6,6 = 18)
    // DC = 10 + modifier(WIS=18) = 10 + 4 = 14
    // Save total = 1 + 2 = 3 < 14 → fails → damage applied
    exec(&mut r, "rolls 1 6 6 6");
    exec(&mut r, "do CastFlamingSphere(druid, goblin)");

    // Goblin should have taken 18 damage (20 - 18 = 2 HP)
    let hp = exec(&mut r, "inspect goblin.HP");
    assert!(
        hp[0].contains("2"),
        "goblin should have 2 HP after 18 fire damage: {:?}",
        hp
    );
}

#[test]
fn sustained_flaming_sphere_save_prevents_damage() {
    let mut r = load_pf2e_sustained();
    spawn_pf2e(&mut r, "druid", PF2E_CASTER);
    spawn_pf2e(&mut r, "goblin", PF2E_TARGET);

    // Queue rolls: save succeeds (d20=20 + 2 = 22 >= 14)
    // No damage rolls needed since save succeeds
    exec(&mut r, "rolls 20");
    exec(&mut r, "do CastFlamingSphere(druid, goblin)");

    // Goblin should be at full HP
    let hp = exec(&mut r, "inspect goblin.HP");
    assert!(
        hp[0].contains("20"),
        "goblin should be at full HP after successful save: {:?}",
        hp
    );

    // But the sustaining condition should still be on the druid
    let conds = exec(&mut r, "conditions");
    assert!(
        conds.iter().any(|l| l.contains("Sustaining_Flaming_Sphere")),
        "druid should still have Sustaining_Flaming_Sphere: {:?}",
        conds
    );
}

#[test]
fn sustained_dismiss_both_spells_clears_all() {
    let mut r = load_pf2e_sustained();
    spawn_pf2e(&mut r, "druid", PF2E_CASTER);
    spawn_pf2e(&mut r, "goblin", PF2E_TARGET);
    spawn_pf2e(&mut r, "ally", PF2E_ALLY);

    // Cast both
    exec(&mut r, "rolls 20"); // save succeeds → no damage rolls
    exec(&mut r, "do CastFlamingSphere(druid, goblin)");
    exec(&mut r, "do CastInspireCourage(druid, ally)");

    // Dismiss first spell
    exec(&mut r, "do DismissSpell(druid, druid.sustained_1)");

    // Dismiss second spell
    exec(&mut r, "do DismissSpell(druid, druid.sustained_2)");

    // Both slots should be cleared
    let slot1 = exec(&mut r, "inspect druid.sustained_1");
    let slot2 = exec(&mut r, "inspect druid.sustained_2");
    assert!(slot1[0].contains("none"), "sustained_1 should be none: {:?}", slot1);
    assert!(slot2[0].contains("none"), "sustained_2 should be none: {:?}", slot2);

    // No conditions should remain
    let conds = exec(&mut r, "conditions");
    assert!(
        !conds.iter().any(|l| l.contains("Sustaining_Flaming_Sphere")),
        "no sustained conditions should remain: {:?}",
        conds
    );
    assert!(
        !conds.iter().any(|l| l.contains("InspiredCourage")),
        "no inspired conditions should remain: {:?}",
        conds
    );
}
