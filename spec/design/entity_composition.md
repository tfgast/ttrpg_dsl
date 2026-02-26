# Entity Composition Design Analysis

How should the TTRPG DSL handle entity composition, inheritance, and conditional
field groups? This document surveys the entity modeling needs of six major TTRPG
systems and evaluates four candidate approaches against each.

## Table of Contents

1. [Systems Survey](#systems-survey)
2. [Candidate Approaches](#candidate-approaches)
3. [Approach × System Matrix](#approach--system-matrix)
4. [Cross-Cutting Concerns](#cross-cutting-concerns)
5. [Conclusions](#conclusions)

---

## Systems Survey

### D&D 5e — Deep Compositional Hierarchy

A 5e Character is assembled from multiple independent sources, each contributing
fields, proficiencies, and features:

```
Character = Species + Background + Class(level) + Subclass(level) + Feats[]
```

**Structural challenges:**

- **Multiclassing** creates per-class field groups: a Fighter 5 / Wizard 3 has
  separate hit dice (5d10 + 3d6), separate class features, separate spells
  known/prepared, but *shared* ability scores, HP pool, and spell slots
  (computed from weighted caster levels).

- **Conditional subsystems**: Ki points exist only on Monks. Sorcery Points only
  on Sorcerers. Rage only on Barbarians. Channel Divinity only on
  Clerics/Paladins. Wild Shape only on Druids. These are entire field groups
  gated on class membership.

- **Spellcasting variance**: 12+ classes/subclasses get spellcasting, but with
  different abilities (INT/WIS/CHA), preparation styles (known vs. prepared vs.
  spellbook), slot progression (full/half/third/pact), and spell lists. Warlock
  Pact Magic is a completely separate slot system that recharges on short rest.

- **Creature vs. Character**: Monsters and PCs share a core stat block (ability
  scores, AC, HP, speed, saves, skills, resistances, senses) but diverge
  significantly. Monsters have CR, legendary actions, lair actions, and
  pre-computed stats. NPCs use the monster format, not the character format.

**Entity type inventory:**
Character, Monster/NPC (shared creature base), Weapon, Armor, Spell, Item.

**Key pattern:** Layered composition with conditional field groups. ~40% of a
Character's fields are class-conditional.

---

### Pathfinder 2e — Granular Feat-Based Extension

PF2e uses a similar layered model but with more granularity:

```
Character = Ancestry + Heritage + Background + Class + Archetypes[] + Feats[]
```

**Structural challenges:**

- **Proficiency system (TEML)**: Every combat stat, save, skill, weapon group,
  and armor category has a 5-rank proficiency track
  (Untrained/Trained/Expert/Master/Legendary). This is a *map* from ~40+
  categories to proficiency ranks — a large, uniform field group shared by all
  characters.

- **Archetype dedications** replace traditional multiclassing. You spend class
  feat slots to buy into an archetype, which progressively grants features from
  another class or a custom archetype. This is "cherry-pick capabilities" rather
  than "add an entire class template."

- **Spellcasting has three orthogonal axes**: tradition (Arcane/Divine/Occult/
  Primal), preparation type (prepared/spontaneous), and source (full list/
  spellbook/repertoire). Each class fixes these differently.

- **Creature vs. Character**: Characters are built bottom-up (compose parts,
  derive stats). Creatures are built top-down (pick final numbers from
  benchmark tables). They share ~70% of fields but are constructed completely
  differently.

**Entity type inventory:**
Character, Creature, Hazard, Weapon, Armor, Shield, Item (with subtypes:
consumable, rune, wand, staff, worn, held), Spell, Feat.

**Key pattern:** Fine-grained feat-based extension. Feats can grant actions,
modify proficiencies, add conditional bonuses, unlock spell access. They are the
primary extensibility mechanism.

---

### Call of Cthulhu 7e — Flat and Simple

CoC has the simplest entity model of the systems surveyed.

```
Investigator = 8 Characteristics + ~60 Skills + Occupation(skill allocation template)
```

**Structural challenges:**

- **Almost none.** The entity model is flat: 8 fixed characteristics, ~60
  percentile skills (all on the same scale), a handful of derived values
  (HP, MP, Sanity, Damage Bonus). No classes, no feats, no conditional
  subsystems.

- **Sanity as inverse resource**: Gaining Cthulhu Mythos skill permanently
  lowers maximum Sanity. This is a bidirectional constraint between two fields
  — rare but important.

- **Monsters are nearly the same template**: Monsters share characteristics and
  skills with Investigators, adding only intrinsic armor and SAN loss values.

**Entity type inventory:**
Investigator, NPC (abbreviated Investigator), Monster (Investigator + armor +
SAN loss + special attacks).

**Key pattern:** Near-flat entity model. Minimal composition needed. Occupation
constrains skill point allocation at creation time but doesn't add fields.

---

### Savage Worlds — Die-Type Stats with Conditional Subsystems

Savage Worlds uses a fundamentally different value system: attributes and skills
are die types (d4, d6, d8, d10, d12), not integers.

```
Character = 5 Attributes(die) + Skills(die) + Edges[] + Hindrances[] + [Powers]
```

**Structural challenges:**

- **Wild Card vs. Extra**: The same entity template has a boolean flag that
  changes wound capacity (3 vs. 1) and grants/removes the Wild Die. This is a
  behavioral modifier on a shared type, not a separate type.

- **Edges can activate subsystems**: Taking the "Arcane Background" edge adds
  an entire Powers subsystem (Power Points pool, power list, arcane skill).
  Before that edge, those fields don't exist on the character. This is
  *runtime* conditional composition.

- **Vehicles are genuinely different**: Vehicles share almost nothing with
  characters (Toughness is computed differently, plus Top Speed, Handling, Crew,
  Mods). This is a separate entity type, not a variant.

- **Die-type as value**: Attribute and skill values are not integers — they are
  die types with step-up/step-down arithmetic. d4 → d6 → d8 → d10 → d12 →
  d12+1.

**Entity type inventory:**
Character (Wild Card/Extra flag), Vehicle, Weapon, Armor, Power, Edge.

**Key pattern:** Conditional subsystem activation via edges. The character's
schema grows at runtime when certain edges are taken.

---

### World of Darkness (Chronicles of Darkness) — Template Layering

CofD has the most structurally interesting entity model: a mortal base template
with supernatural overlays.

```
Character = Mortal Template + [Supernatural Template(Clan/Auspice/Path, Covenant/Tribe/Order)]
```

**Structural challenges:**

- **Template overlay**: Every supernatural character IS a mortal (9 attributes,
  24 skills, merits, health, willpower) PLUS a supernatural template that
  *adds* fields (power stat, supernatural resource, powers) and *replaces*
  one field (morality track: Integrity → Humanity/Harmony/Wisdom). The mortal
  template is never removed, only extended.

- **Each splat adds different fields**: Vampires get Disciplines + Blood Potency
  + Vitae + Humanity. Werewolves get Gifts + Primal Urge + Essence + Harmony +
  5 shapeshifting forms. Mages get Arcana + Gnosis + Mana + Wisdom + Paradox.
  These are completely different subsystems layered onto the same mortal base.

- **Form-shifting (Werewolf)**: Five named forms, each applying a different set
  of stat modifiers (attribute bonuses, size changes, speed changes, available
  abilities). The character's effective stat block changes shape during play.

- **Power stat as meta-modifier**: Blood Potency/Primal Urge/Gnosis doesn't
  just sit there — it modifies the *caps* of other fields (max attribute
  rating, max vitae per turn, discipline effectiveness).

- **Becoming supernatural**: A mortal can become a vampire mid-campaign,
  *adding* an entire template at runtime.

**Entity type inventory:**
Mortal (base), 10+ supernatural types (each extending Mortal differently),
Ephemeral Entity (spirits/ghosts — different base template).

**Key pattern:** Additive template composition with field replacement. The
strongest argument for trait-based composition.

---

### Powered by the Apocalypse (PbtA) — Playbook as Type

PbtA radically ties character structure to the playbook (class). Different
playbooks have *structurally different* characters.

```
Character = Playbook(stats, moves, special subsystem)
```

**Structural challenges:**

- **Per-playbook subsystems**: The Hardholder has a settlement (want, surplus,
  size, gang). The Chopper has a gang (size, harm, armor, tags). The Savvyhead
  has a workspace. The Hocus has followers. These are unique data structures
  that exist on *one* playbook only. There is no fixed character schema.

- **Asymmetric PCs vs. NPCs**: NPCs have no stats, no HP, no mechanical
  structure. They are narrative constructs with a threat type and impulse.
  PCs and NPCs are fundamentally different entity types.

- **Moves as first-class objects**: A character IS its moves plus a few stats.
  Moves are trigger-condition → roll+stat → branching outcomes. The move list
  is the primary structural differentiator between characters.

- **Cross-playbook acquisition**: Advancement lets you take moves from other
  playbooks, but not their subsystems. Taking a Hardholder move doesn't give
  you a holding.

**Entity type inventory:**
PC (per-playbook schema), NPC/Threat (narrative construct, no shared fields
with PCs).

**Key pattern:** Playbook-as-type with unique per-type subsystems. The most
extreme case of structural variance between instances of "character."

---

### FATE Core — Minimally Typed, Maximally Generic

FATE has the simplest fixed schema but the most flexible semantics.

```
Character = Aspects[] + Skills(pyramid) + Stunts[] + StressTracks + Consequences
```

**Structural challenges:**

- **Aspects are free-text with mechanical weight**: The core "fields" are
  strings that gain mechanical significance through invocation/compel. There
  is no fixed semantic for what an aspect means.

- **The Bronze Rule (Fractal)**: Anything can be a character — a disease, a
  city, an organization. The entity template is universally reusable. A sword
  can have aspects, stress tracks, and stunts just like a person.

- **Stunts are user-defined rules**: Each stunt is a bespoke mechanical
  modification. There is no fixed stunt list.

- **Scaling by omission**: NPCs are the same template with fewer fields filled
  in. A nameless NPC is just an aspect. A major NPC has aspects, skills,
  stress, and consequences. The difference is degree, not kind.

- **Custom stress tracks**: Settings add/remove stress tracks (Wealth,
  Reputation, etc.) that function identically to physical/mental stress.

**Entity type inventory:**
One universal template, scaled by complexity. Everything is a character.

**Key pattern:** Single generic template. Composition is unnecessary because
the template is already maximally flexible. The challenge is that FATE resists
typed fields entirely.

---

## Candidate Approaches

### Approach 1: Trait-Based Composition (Rust-like)

Traits define named field groups. Entities compose them with `with`. Actions can
accept trait bounds for polymorphic dispatch.

```ttrpg
trait Combatant {
    AC: int
    HP: resource(0..=max_HP)
    max_HP: int
}

trait Spellcaster {
    spellcasting_ability: Ability
    spell_save_DC: int
    spell_slots: map<int, resource(0..=max)>
}

entity Character with Combatant {
    name: string
    level: int = 1
    abilities: map<Ability, int>
}

entity Wizard with Combatant, Spellcaster {
    name: string
    level: int = 1
    arcane_tradition: string
}

// Polymorphic action — works on anything with Combatant
action Attack on attacker: impl Combatant
    (target: impl Combatant, weapon: Weapon) { ... }
```

**Strengths:** Polymorphism, code reuse, type-safe field groups.
**Weaknesses:** Verbose for simple cases, traits are fixed at declaration time
(no runtime gain/loss), multiple-trait diamond problems.

---

### Approach 2: Entity Inheritance (OOP-like)

Entities can extend other entities, inheriting all fields.

```ttrpg
entity Creature {
    name: string
    AC: int
    HP: resource(0..=max_HP)
    max_HP: int
    abilities: map<Ability, int>
}

entity Character extends Creature {
    level: int = 1
    class: CharacterClass
    proficiency_bonus: int
}

entity Monster extends Creature {
    CR: float
    legendary_actions: int = 0
}
```

**Strengths:** Simple mental model, familiar to most users.
**Weaknesses:** Single inheritance is too rigid for cross-cutting concerns
(Spellcaster × Combatant × HasKi). Multiple inheritance opens a can of worms.
No conditional fields.

---

### Approach 3: Mixin / Field Group Inlining

Named field groups that get inlined (copy-pasted) into entities. No
polymorphism — purely a convenience for avoiding repetition.

```ttrpg
mixin Combatant {
    AC: int
    HP: resource(0..=max_HP)
    max_HP: int
}

mixin Spellcaster {
    spellcasting_ability: Ability
    spell_save_DC: int
}

entity Character {
    include Combatant
    include Spellcaster  // optional, depends on class
    name: string
    level: int = 1
}
```

**Strengths:** Simple, no type system complexity, easy to understand.
**Weaknesses:** No polymorphism — can't write `action Attack on x: Combatant`.
No way to conditionally include at runtime. Field conflicts resolved by...
what?

---

### Approach 4: Optional Field Groups (Conditional Composition)

Entities declare optional field groups that may or may not be present on a given
instance.

```ttrpg
entity Character {
    name: string
    level: int = 1
    abilities: map<Ability, int>
    AC: int
    HP: resource(0..=max_HP)
    max_HP: int

    optional Spellcasting {
        spellcasting_ability: Ability
        spell_save_DC: int
        spell_slots: map<int, resource(0..=max)>
    }

    optional KiPowers {
        ki_points: resource(0..=max_ki)
        max_ki: int
        martial_arts_die: DiceExpr
    }
}
```

**Strengths:** Directly models conditional subsystems, runtime flexibility.
**Weaknesses:** No cross-entity sharing (every entity re-declares the optional
group), no polymorphism, field access requires null checks or guard clauses.

---

## Approach × System Matrix

### D&D 5e

| Concern | Traits (1) | Inheritance (2) | Mixins (3) | Optional (4) |
|---------|:----------:|:---------------:|:----------:|:------------:|
| Creature base (shared by Character + Monster) | Define `trait Combatant` — both entity types compose it. Actions accept `impl Combatant`. | `entity Creature` as base, `Character extends Creature`, `Monster extends Creature`. Clean for this case. | `mixin CombatStats` inlined into both. Works but no polymorphic actions. | Not applicable — this is shared, not conditional. |
| Class-conditional fields (Ki, Rage, etc.) | Multiple traits per class: `trait HasKi`, `trait HasRage`. Entity types compose the relevant ones. But: must declare `entity Monk with Combatant, HasKi` — fixed at type declaration time, not at spawn time. | Subclass per class variant: `entity Monk extends Character`. Explosion of entity types. | `mixin Ki`, `mixin Rage` inlined selectively. Same explosion. | `optional Ki { ... }` inside Character. Runtime flexible. Must guard access. |
| Multiclassing (Fighter/Wizard) | Awkward. `entity FighterWizard with Combatant, HasActionSurge, Spellcaster`? Combinatorial explosion unless traits are very fine-grained. | Impossible with single inheritance. `FighterWizard extends ???`. | Same combinatorial problem. | `optional FighterFeatures { ... }`, `optional WizardFeatures { ... }` inside Character. Works naturally. |
| Polymorphic actions | `action Attack on x: impl Combatant` — works directly. | `action Attack on x: Creature` — works via inheritance. | Not supported without a separate mechanism. | Not supported. Must use the concrete type. |
| Spellcasting variance | `trait Spellcaster` with associated constants. Different entity types implement it differently. | `entity Caster extends Character { ... }`, then per-class subtypes. Deep hierarchy. | `mixin PreparedCasting`, `mixin KnownCasting` — different mixins per style. | `optional Spellcasting { ... }` — but how to express prepared vs. known variance? |

**Verdict for 5e:** No single approach handles everything. Traits (1) handle the
Creature/Character/Monster shared base and polymorphic actions well. Optional
groups (4) handle class-conditional subsystems and multiclassing well. Inheritance
(2) works for the simple Creature → Character/Monster split but fails for
anything cross-cutting.

---

### Pathfinder 2e

| Concern | Traits (1) | Inheritance (2) | Mixins (3) | Optional (4) |
|---------|:----------:|:---------------:|:----------:|:------------:|
| Character vs. Creature shared base | Same as 5e — trait or inheritance both work. | Same as 5e. | Same as 5e. | Same as 5e. |
| Proficiency system (uniform across all characters) | Part of a shared `trait Proficient` or just entity fields. Not really a composition issue. | Base class field. Fine. | Not really a composition issue. | Not really a composition issue. |
| Archetype dedications (cherry-pick features) | Traits per archetype's capabilities. But archetypes grant individual feats, not field groups. | Doesn't fit — archetypes aren't subtypes. | Doesn't fit — archetypes don't add field blocks. | Closest fit: optional groups that get "enabled" as dedication feats are taken. |
| Spellcasting (3 orthogonal axes) | Can model each axis as a trait parameter or associated type. Complex but expressive. | Would need a hierarchy per combination. Unworkable. | Separate mixins per combination. Proliferation. | Optional spellcasting group with internal configuration. |
| Hazards (different entity type) | Define `trait HasDefenses` shared between Creature and Hazard. | `entity Hazard extends ???` — no natural parent with Creature. | `mixin Defenses` shared. | Not applicable. |

**Verdict for PF2e:** Similar to 5e. Traits handle the shared-base + polymorphism
well. PF2e's archetype system doesn't map cleanly to any approach because it
operates at the individual-feat level, not the field-group level. The DSL might
not need to model feat-level granularity — that's a content/data concern, not a
type system concern.

---

### Call of Cthulhu 7e

| Concern | Traits (1) | Inheritance (2) | Mixins (3) | Optional (4) |
|---------|:----------:|:---------------:|:----------:|:------------:|
| Nearly-flat entity model | Overkill. One entity type with all fields covers it. | One base `entity Character` with `entity Monster extends Character` adding armor + SAN loss. Clean. | One mixin for the 2 extra monster fields. Works but unnecessary. | Not needed. |
| Sanity inverse constraint | Orthogonal to composition. Handled by derives/mechanics. | Same. | Same. | Same. |
| Monster vs. Investigator | Minimal divergence. | `entity Monster extends Investigator` with 2 extra fields. Fine. | `mixin MonsterExtras`. Fine. | Not needed. |

**Verdict for CoC:** The entity model is so flat that composition barely matters.
Any approach works. Inheritance is the natural fit for the tiny Investigator →
Monster extension, but even that's optional — you could just have one entity type
with optional `armor` and `san_loss` fields.

---

### Savage Worlds

| Concern | Traits (1) | Inheritance (2) | Mixins (3) | Optional (4) |
|---------|:----------:|:---------------:|:----------:|:------------:|
| Wild Card vs. Extra (boolean flag) | Not a trait concern — same entity type, different flag. | Not an inheritance concern. | Not a mixin concern. | Could model as `optional WildCardAbilities { ... }`, but a boolean flag is simpler. |
| Edges activating Powers subsystem | `trait HasPowers { power_points: resource(...), powers: list<Power> }`. Applied at type declaration time. But edge acquisition is at runtime. | `entity Arcanist extends Character`. Fixed at type declaration. | `mixin Powers` inlined. Fixed at type declaration. | `optional Powers { power_points: resource(...), ... }` enabled when Arcane Background edge is taken. Best fit. |
| Vehicles (separate entity type) | Define `trait HasToughness` shared. Vehicles have it but with different derivation. Forced. | `entity Vehicle` — completely separate type. Clean. | Separate entity. Clean. | Separate entity. Clean. |

**Verdict for Savage Worlds:** Optional groups (4) are the clear winner for the
Arcane Background → Powers pattern. Traits are overly rigid because edges are
gained at runtime. Vehicles are a separate entity type regardless of approach.

---

### World of Darkness / Chronicles of Darkness

| Concern | Traits (1) | Inheritance (2) | Mixins (3) | Optional (4) |
|---------|:----------:|:---------------:|:----------:|:------------:|
| Mortal base + supernatural overlay | `trait Supernatural { power_stat: int, resource: resource(...) }` with splat-specific sub-traits. The mortal fields live on the entity. Supernatural traits are composed on. | `entity Mortal` → `entity Vampire extends Mortal` → etc. Clean single-inheritance tree. Each subtype adds its unique fields. | `mixin VampireTemplate { ... }` inlined. Works for declaration. | `optional VampireTemplate { ... }` on a single Character entity. Enables mid-campaign transformation. |
| Field replacement (Integrity → Humanity) | Traits can't *replace* fields — they can only add. Would need a base `trait HasMorality { morality: int }` that gets overridden. Awkward. | Subtype overrides the field type. Natural if supported. | Inline replaces. Must handle conflicts. | Optional group replaces the morality field. Awkward — two fields, one active? |
| Form-shifting (Werewolf 5 forms) | Orthogonal to composition — this is runtime state, not type structure. Modeled as modifier sets applied/removed during play. | Same. | Same. | Same. |
| Per-splat unique subsystems (Disciplines vs. Arcana vs. Gifts) | Each splat's powers are a separate trait. `trait HasDisciplines`, `trait HasArcana`. Vampire composes `HasDisciplines`, Mage composes `HasArcana`. Clean. | Each splat subtype declares its own power fields. Clean. | Each splat's mixin declares its own power fields. Clean. | Each splat's optional group. But they'd all live on one entity type — cluttered. |
| Becoming supernatural at runtime | Traits are fixed at type declaration. Can't add a trait at runtime. **Fails.** | Subtype is fixed at spawn. Can't change type at runtime. **Fails.** | Same as inheritance. **Fails.** | Enable the optional supernatural group at runtime. **Works.** |

**Verdict for CofD:** This system most directly motivates trait-based composition
for the static case (mortal base + supernatural overlay). Inheritance also works
well for the hierarchy. But the "becoming supernatural at runtime" requirement
*only* works with optional groups (4). If we consider that requirement niche
(it's unusual even in CofD campaigns), then traits or inheritance work for the
common case.

---

### PbtA (Apocalypse World)

| Concern | Traits (1) | Inheritance (2) | Mixins (3) | Optional (4) |
|---------|:----------:|:---------------:|:----------:|:------------:|
| Per-playbook subsystems (holding, gang, workspace) | Each playbook's subsystem is a trait. `trait HasHolding { ... }`. Applied to the Hardholder entity type. Works but creates many single-use traits. | Each playbook is a separate entity type. `entity Hardholder extends Character { holding: Holding }`. Works. | `mixin Holding { ... }` inlined into Hardholder. Works. | `optional Holding { ... }` on a generic Character. Works but Character becomes cluttered with every playbook's subsystem. |
| Asymmetric PCs vs. NPCs | Separate entity types. Traits/inheritance/mixins don't help — they're genuinely different data models. | Separate entity types. | Separate entity types. | Separate entity types. |
| Cross-playbook move acquisition | Moves are a content/data concern, not a type system concern. The DSL already handles this via the action system. | Same. | Same. | Same. |

**Verdict for PbtA:** Any approach works for the static playbook-as-type pattern.
Inheritance is the most natural — each playbook is a subtype of Character with
its own fields. The per-playbook subsystems aren't shared across playbooks, so
traits don't add much. PbtA's asymmetric PC/NPC model requires separate entity
types regardless.

---

### FATE Core

| Concern | Traits (1) | Inheritance (2) | Mixins (3) | Optional (4) |
|---------|:----------:|:---------------:|:----------:|:------------:|
| Single generic template | No composition needed — one entity type handles everything. | No composition needed. | No composition needed. | No composition needed. |
| Bronze Rule (anything is a character) | One entity type. Traits unnecessary. | One entity type. | One entity type. | One entity type. |
| Custom stress tracks | Could model as `trait HasReputationStress { ... }`, but this is more of a settings/config concern. | Not an inheritance concern. | Not a mixin concern. | `optional ReputationStress { ... }` — closest fit for settings that add/remove stress tracks. |

**Verdict for FATE:** Composition is largely irrelevant. FATE's challenge is
elsewhere — in the free-text-with-mechanical-weight aspect system, which is
orthogonal to entity composition.

---

## Cross-Cutting Concerns

### 1. Static vs. Runtime Composition

The sharpest divide in the matrix above:

| | Static (type declaration time) | Runtime (spawn/play time) |
|---|---|---|
| **Needs** | Shared field groups, polymorphic actions | Multiclassing, gaining powers, becoming supernatural |
| **Works** | Traits (1), Inheritance (2), Mixins (3) | Optional Groups (4) |
| **Fails** | Optional Groups (adds clutter to type declaration) | Traits, Inheritance, Mixins (all fixed at type declaration) |

Most systems need both: a static mechanism for shared structure (Creature base,
Combatant fields) and a runtime mechanism for conditional subsystems (Ki points,
Powers, supernatural templates).

### 2. Polymorphism

Only traits (1) and inheritance (2) support writing actions that work on "anything
with these fields." Mixins (3) and optional groups (4) require concrete entity
types.

Systems that benefit most from polymorphism: D&D 5e (action on any Combatant),
PF2e (action on any Creature), CofD (action on any supernatural being).

Systems that don't need it: CoC, FATE, most PbtA games.

### 3. Field Conflict Resolution

When two composed groups define the same field:

- **Traits**: Compiler error (require explicit resolution).
- **Inheritance**: Child overrides parent (well-defined).
- **Mixins**: Ambiguous — which one wins? Needs a rule.
- **Optional**: Each group is namespaced — `self.Spellcasting.spell_save_DC`,
  not `self.spell_save_DC`. Avoids conflicts but adds verbosity.

### 4. Complexity Budget

This is a DSL for game designers, not systems programmers. Ranked by conceptual
complexity:

1. **Mixins (3)** — simplest. "Copy-paste these fields." No new concepts.
2. **Inheritance (2)** — familiar. "This entity is like that one but with more."
3. **Optional Groups (4)** — moderate. "These fields might not exist." Requires
   null-checking discipline.
4. **Traits (1)** — most complex. Requires understanding: trait definition, trait
   composition, trait bounds on action parameters, potential diamond problems.

### 5. The Combinatorial Explosion Problem

D&D 5e multiclassing is the acid test. With 13 classes, there are 78 possible
dual-class combinations, 286 triple-class, etc. Approaches that require a
separate entity type per combination (separate trait compositions, separate
inheritance subtypes) are unworkable for this case.

Only optional groups (4) handle this naturally — one `Character` entity type
with optional `FighterFeatures`, `WizardFeatures`, etc. that get enabled at
spawn time based on class selection.

### 6. How Other Systems Handle This

For reference, how existing digital TTRPG tools approach composition:

- **Foundry VTT (PF2e system)**: Uses a flat entity model with runtime rule
  elements. Items/feats are "rules" that modify the character. Effectively
  approach 4 implemented as a rule engine.

- **D&D Beyond**: Backend uses a modifier stacking system. Each class, feat,
  race, etc. contributes modifiers to a flat character object. Not type-system
  level composition.

- **Roll20**: Flat character sheet with all fields always present. Unused fields
  are zeroed. No composition at all.

---

## Conclusions

### What the Survey Shows

No single approach handles all systems well. The needs cluster into two distinct
categories:

**Category A — Shared Structure + Polymorphism (static)**
- Creature base shared by Character and Monster
- Actions that work on "anything with HP and AC"
- Spellcaster field group shared across casting classes

Best served by: **Traits (1)** or **Inheritance (2)**.

**Category B — Conditional Subsystems (runtime-flexible)**
- Class-specific resource pools (Ki, Rage, Sorcery Points)
- Multiclassing (arbitrary combinations of class features)
- Gaining supernatural templates mid-campaign
- Edge-activated power systems

Best served by: **Optional Groups (4)**.

### Systems Alignment

| System | Primary Need | Secondary Need |
|--------|-------------|---------------|
| D&D 5e | Category B (class-conditional, multiclass) | Category A (Creature base, polymorphic actions) |
| PF2e | Category A (shared base, polymorphic actions) | Category B (archetype dedications) |
| CoC 7e | Neither (flat model) | — |
| Savage Worlds | Category B (edge-activated subsystems) | — |
| CofD | Category A (mortal + supernatural template) | Category B (becoming supernatural) |
| PbtA | Category A (playbook-as-subtype) | — |
| FATE | Neither (single generic template) | — |

### Decision: Optional Groups

Based on the analysis above, **optional groups** provide the most value for the
complexity they introduce. They directly address Category B (the primary need
for D&D 5e, Savage Worlds, and CofD) while keeping the type system simple
enough for game designers.

Category A (shared structure + polymorphism) is deferred. It can be addressed
later with traits or inheritance if the need proves strong enough in practice.
For now, reusable optional-group schemas are handled by top-level `group`
declarations (attached with `optional GroupName`), while polymorphic actions
still use concrete entity types.

---

## Optional Groups: Detailed Design

### Design Decisions (All Settled)

1. **Namespaced access**: Fields inside optional groups are accessed through
   the group name: `actor.Spellcasting.spell_save_DC`, not `actor.spell_save_DC`.
   This avoids name collisions between groups and makes it visually clear which
   fields are conditional.

2. **Checker-enforced guards via `has`**: The type checker rejects access to
   optional group fields without a guard proving the group is active. The `has`
   keyword is a composable boolean expression (`if actor has Spellcasting`)
   that narrows the type through control flow. Composes with `and`/`or`/`not`.

3. **Runtime activation via `grant`/`revoke`**: Optional groups can be granted
   and revoked at runtime (not just at spawn time). `grant` fits TTRPG domain
   language. `revoke` discards field values — optional groups model structural
   identity, not momentary toggles.

4. **Action/derive constraints via `with`**: Actions, derives, mechanics,
   conditions, and reactions can require that a parameter has a specific
   optional group active using `with`: `on caster: Character with Spellcasting`.
   This provides a lightweight form of polymorphism without full trait bounds.

### Declaration

Optional groups can be declared in two ways:
- Inline inside an entity: `optional GroupName { ... }`
- As reusable top-level schemas: `group GroupName { ... }`, then attached with
  `optional GroupName`

```ttrpg
group Spellcasting {
    spellcasting_ability: Ability
    spell_save_DC: int
    spell_slots: map<int, resource(0..=max)>
}

entity Character {
    name: string
    level: int = 1
    abilities: map<Ability, int>
    AC: int
    HP: resource(0..=max_HP)
    max_HP: int

    optional Spellcasting     // attaches top-level group schema

    optional KiPowers {
        ki_points: resource(0..=max_ki)
        max_ki: int
        martial_arts_die: DiceExpr
    }

    optional Rage {
        rage_uses: resource(0..=max_rage)
        max_rage: int
        rage_damage: int
    }
}
```

**Rules:**
- Group names must be unique within an entity.
- Group names occupy a separate namespace from field names (no conflict between
  a field named `rage` and a group named `Rage`).
- Top-level `group` names are unique per system (and follow import visibility
  rules like other declarations).
- `optional GroupName` must resolve to a visible top-level `group`.
- Fields inside optional groups can have defaults, same as regular fields.
- Fields inside optional groups can reference fields from the entity's base
  (e.g., a resource bounded by a base field).
- Optional groups cannot nest (no optional-within-optional).

### Activation and Deactivation

Optional groups are activated and deactivated at runtime. The host (CLI, VTT,
etc.) is responsible for managing this.

**At spawn time** — the host provides initial field values for active groups:

```
spawn Character hero {
    name: "Gandalf", level: 5, ...,
    Spellcasting { spellcasting_ability: INT, spell_save_DC: 15, ... }
}
```

Groups not mentioned at spawn are inactive. Groups mentioned must have all
required fields provided (fields without defaults).

**At runtime** — activation/deactivation happens through effects:

```ttrpg
action GainSpellcasting on actor: Character (...) {
    resolve {
        grant actor.Spellcasting {
            spellcasting_ability: WIS,
            spell_save_DC: 8 + proficiency_bonus(actor.level) + modifier(actor.abilities[WIS]),
            ...
        }
    }
}

action LoseSpellcasting on actor: Character (...) {
    resolve {
        revoke actor.Spellcasting
    }
}
```

The keywords `grant` and `revoke` are used for activation and deactivation.
`grant` fits the TTRPG domain — "the character is granted spellcasting" is how
game designers talk. `revoke` accurately describes removing a capability.
Alternatives considered and rejected: `enable`/`disable` (too generic, could
conflict with option toggles), `activate`/`deactivate` (implies momentary
toggling, not structural change), `attach`/`detach` (too ECS-flavored).

### Guard Syntax and Type Narrowing

Accessing optional group fields requires a guard. Inside the guard's body, the
checker knows the group is active and permits field access. Outside the guard,
access is a compile-time error.

The `has` keyword is used as a boolean expression that also narrows the type.
It composes with `and`/`or`/`not`, works in `if`/`else`, and doesn't require
new block syntax. The checker tracks narrowing through control flow, same as
null checks in languages with flow-sensitive typing.

Alternatives considered and rejected: `with` blocks (introduce implicit name
resolution and a new scoping mechanism), `match`-style (heavier syntax for a
simple boolean check).

```ttrpg
// Basic guard
if actor has Spellcasting {
    let dc = actor.Spellcasting.spell_save_DC
}

// Composable — multiple groups
if actor has Spellcasting and actor has KiPowers {
    // both narrowed
}

// Negative guard with early return
if not actor has Spellcasting {
    // actor.Spellcasting access is still an error here
    return
}
// after early return, actor.Spellcasting is narrowed as active
let dc = actor.Spellcasting.spell_save_DC
```

### Action Receiver Constraints

Actions can require optional groups on their receiver using `with`:

```ttrpg
action CastSpell on caster: Character with Spellcasting (
    target: Character,
    spell_level: int
) {
    cost { action }
    requires { caster.Spellcasting.spell_slots[spell_level] > 0 }

    resolve {
        caster.Spellcasting.spell_slots[spell_level] -= 1
        // ... spell effect ...
    }
}
```

Inside the action body, `caster.Spellcasting.*` is accessible without a guard
because the `with Spellcasting` constraint guarantees the group is active.

**Multiple constraints** compose with commas:

```ttrpg
action StunningStrike on monk: Character with KiPowers (
    target: Character
) {
    requires { monk.KiPowers.ki_points >= 1 }

    resolve {
        monk.KiPowers.ki_points -= 1
        // ... stunning strike logic ...
    }
}
```

**Parameter constraints**: The `with` constraint can also appear on non-receiver
parameters:

```ttrpg
action Counterspell on caster: Character with Spellcasting (
    target: Character with Spellcasting
) {
    // both caster and target have Spellcasting narrowed
}
```

The same constraint syntax works with the polymorphic entity alias:

```ttrpg
derive spell_dc_if_any(x: entity with Spellcasting) -> int {
    x.Spellcasting.spell_save_DC
}
```

Here `entity` means "any entity type". The `with Spellcasting` clause narrows
the parameter so group access is type-safe.

**Constraint checking**: The runtime checks that the optional group is active
when an action is invoked. If not, it produces a runtime error (analogous to
calling an action on an entity that doesn't exist). The checker ensures that
code inside the action body can safely access the constrained groups.

### Derives and Mechanics with Optional Groups

Derives and mechanics can also use `with` constraints on parameters:

```ttrpg
derive spell_attack_bonus(caster: Character with Spellcasting) -> int {
    let ability = caster.Spellcasting.spellcasting_ability
    modifier(caster.abilities[ability]) + proficiency_bonus(caster.level)
}
```

Or use guards for more flexibility:

```ttrpg
derive effective_save_DC(actor: Character, base_DC: int) -> int {
    if actor has Spellcasting {
        max(base_DC, actor.Spellcasting.spell_save_DC)
    } else {
        base_DC
    }
}
```

### Conditions on Optional Groups

Conditions that only apply to entities with a specific group use `with`:

```ttrpg
condition Silenced on bearer: Character with Spellcasting {
    // Only attachable to characters with Spellcasting active
    modify spell_attack_bonus(caster: bearer) {
        // Prevent verbal-component spells — details TBD
    }
}
```

### Cross-Entity Group Reuse

Optional-group schemas can be shared across entity types using top-level
`group` declarations:

```ttrpg
group Spellcasting {
    spellcasting_ability: Ability
    spell_save_DC: int
}

entity Character {
    // ... base fields ...
    optional Spellcasting
}

entity Monster {
    // ... base fields ...
    optional Spellcasting
}
```

Sharing schema does not imply receiver polymorphism: an action
`on caster: Character with Spellcasting` still does not accept a `Monster`.
Traits/mixins remain a possible future addition for broader behavioral
composition.

### Interaction with Existing Features

**Resources inside optional groups**: Resource fields work normally. The
resource bounds are checked when the group is active and ignored when inactive.

```ttrpg
optional KiPowers {
    ki_points: resource(0..=max_ki)
    max_ki: int
}
// ki_points is clamped to [0, max_ki] when KiPowers is active
```

**Conditions referencing optional fields**: A condition can modify a derive
that uses optional groups. The condition's `with` constraint ensures it is only
applied to entities where the group is active.

**Turn budgets**: Optional groups do not interact with the turn budget system.
Turn budget fields remain on the entity base.

**Events and reactions**: Reactions can use `with` constraints on their reactor,
same as actions.

### State Representation

At the interpreter/runtime level, optional groups are stored alongside regular
fields with an active/inactive flag:

- Each optional group on an entity instance has a boolean `active` state.
- When active, its fields are readable and writable through the normal
  `StateProvider`/`WritableState` interface, namespaced by group name.
- When inactive, read/write attempts produce a runtime error.
- Granting a group requires providing values for all fields without defaults.
- Revoking a group **discards** its field values (they are not preserved).

Discard-on-revoke is the right semantic because optional groups model structural
identity ("this character IS a spellcaster"), not momentary toggles (that's what
conditions are for). If a character regains a capability, the context is likely
different (different ability, different DC). Preserved stale state would be wrong
more often than right, and hidden state that can't be inspected is a maintenance
hazard.

### CLI Interaction

The CLI `spawn` command gains group-activation syntax:

```
> spawn Character hero { name: "Gandalf", level: 5, AC: 15, ... }
> grant hero.Spellcasting { spellcasting_ability: INT, spell_save_DC: 15 }
> eval hero.Spellcasting.spell_save_DC
15
> revoke hero.Spellcasting
> eval hero.Spellcasting.spell_save_DC
error: optional group 'Spellcasting' is not active on 'hero'
```

Or inline at spawn time:

```
> spawn Character hero { name: "Gandalf", level: 5, ..., Spellcasting { spellcasting_ability: INT, spell_save_DC: 15 } }
```

### Type Checking Summary

| Context | Behavior |
|---------|----------|
| Access `entity.Group.field` without guard | Compile error |
| Access inside `if entity has Group { ... }` | Allowed |
| Access inside action `on x: Entity with Group` | Allowed |
| Access inside derive with `param: Entity with Group` | Allowed |
| Access inside derive/action with `x: entity with Group` | Allowed if `Group` is known |
| `grant`/`revoke` in derive or mechanic | Compile error (no mutation) |
| `grant`/`revoke` in action resolve block | Allowed |
| `grant`/`revoke` on `x: entity` when group schema is ambiguous | Compile error (use concrete entity type) |
| Duplicate group names in one entity | Compile error |
| Optional group on a struct (not entity) | Compile error |

### All Decisions Summary

| Decision | Choice | Rationale |
|----------|--------|-----------|
| Access syntax | Namespaced: `actor.Group.field` | Avoids name collisions, visually clear |
| Guard enforcement | Checker-enforced, compile error without guard | Prevents runtime surprises |
| Guard syntax | `has` as composable boolean expression | Composes with `and`/`or`/`not`, flow-sensitive narrowing, no new block types |
| Activation keywords | `grant` / `revoke` | TTRPG-natural ("granted spellcasting"), implies structural change not momentary toggle |
| Runtime activation | Supported via `grant`/`revoke` in actions | Enables multiclassing, edge-activated subsystems, mid-campaign transformation |
| Deactivation semantics | Discard field values on `revoke` | Optional groups model structural identity, not toggles. Stale preserved state would be wrong more often than right |
| Action/derive constraints | `with GroupName` on parameters | Lightweight polymorphism, checker narrows within body |
| Nesting | Disallowed (no optional-within-optional) | Simplicity |
| Cross-entity sharing | Supported via top-level `group` declarations + `optional GroupName` attachment | Reuse schema without introducing traits/mixins |
| Structs | Cannot have optional groups (entities only) | Optional groups require identity and mutable state |
