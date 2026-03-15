# Roguelike Host: Plan & Design Goals

**Status:** Active exploration
**Started:** 2026-03-13

## Purpose

The roguelike crate (`ttrpg_roguelike`) serves as a laboratory for discovering the host-DSL interface. Today, hosts are theorized about but never built — rules modules defer to "the host will handle it" without testing that claim. Building a real, interactive host forces both sides of the boundary into concrete existence.

### Goals

1. **Discover the interface.** Run real TTRPG systems through a real host. Find where the current API is insufficient, where conventions are needed, and where the DSL needs new capabilities.

2. **Minimize system-specific host code.** The host should be able to load any `.ttrpg` system and run it with mostly shared code. System-specific code should be limited to things that genuinely can't be generalized (and those cases inform DSL improvements).

3. **Inform DSL development.** Findings feed back into the language: prompt expansion, step-based execution, host interface conventions, display metadata, and turn structure abstractions.

4. **Build something playable.** The roguelike should be a functional game — not a test harness. Real gameplay reveals real friction.

## Current State (POC)

The existing roguelike POC demonstrates basic integration:
- Hardcoded `roguelike.ttrpg` with a minimal `Creature` entity and `MeleeAttack` action
- Fixed 40×20 dungeon with 3 rooms, spawns hero + goblins + rat
- Simple chase/attack AI, 8-directional movement
- Synchronous effect handler for dice rolls
- No character creation, no spellcasting, no conditions in use, no save/load

Everything is hardcoded — entity stats, which actions to call, turn order, display glyphs.

## Architecture

```
┌──────────────────────────────────────────────┐
│              Roguelike Host                   │
│  Map generation, rendering, input, pathfind  │
│  Save/load, message log, UI chrome           │
├──────────────────────────────────────────────┤
│            Game Session Layer                 │
│  Turn management, action menus, AI,          │
│  prompt answering, event dispatch,           │
│  zone tracking, character creation flow      │
├──────────────────────────────────────────────┤
│             DSL Bridge Layer                  │
│  Interpreter lifecycle, state adapter,       │
│  effect handler, introspection queries,      │
│  entity spawning from DSL definitions        │
├──────────────────────────────────────────────┤
│           TTRPG Interpreter                   │
│  (existing — rules engine)                   │
└──────────────────────────────────────────────┘
```

### Layer responsibilities

**Roguelike Host** — Fully generic. Map generation, terminal rendering (ratatui), input handling, pathfinding. No TTRPG knowledge. Draws entities as glyphs on a grid, shows messages, accepts commands.

**Game Session Layer** — The interesting new piece. Mediates between the generic host and the DSL. Drives turn flow, presents action choices, answers prompts, runs AI. Should be *mostly* generic but this is where system-specific friction will appear. The goal is to push as much as possible into the DSL or into convention-based discovery.

**DSL Bridge Layer** — Wraps the interpreter API. Handles interpreter lifecycle (parse → check → create interpreter), state management (GameState + StateAdapter), effect handling (dice, mutations, gates). Provides introspection (what entities exist, what actions are available, what fields an entity has).

**TTRPG Interpreter** — Already exists. Rules engine that yields effects. No changes needed initially; changes come later as the host reveals API gaps.

## Resolved Design Decisions

### Entity spawning: DSL spawn functions + host config

**Decision:** The DSL declares spawn functions (e.g., `spawn_goblin(pos: Position) -> Creature`) that own all entity data — stats, defaults, dice expressions. The host calls these via `interp.evaluate_function()`, passing position from the grid. A host-specific RON config file maps spawn functions to display properties (glyph, color) and AI behavior.

**Rationale:** The DSL owns the rules data, the host config owns presentation. The host code is generic — it reads any config, calls whatever spawn functions it names. No system-specific Rust code needed for entity creation.

### Entity display and UI: Host config file

**Decision:** A RON configuration file per system provides all host-specific data:
- Which `.ttrpg` files to load
- Creature catalog: spawn function name, glyph, color, AI hints
- Stats panel: which entity fields to display and how (bar, number, modifier, dice expression)
- Player configuration

**Rationale:** The host needs to understand entity fields for UI (display HP bar, show AC) but doesn't need to understand what they mean mechanically. The config tells the host *which* fields to show and *how* to render them. The DSL handles all mechanical meaning.

Example config shape:
```ron
HostConfig(
    system: SystemConfig(
        files: ["roguelike.ttrpg"],
    ),
    player: PlayerConfig(
        spawn_fn: "spawn_hero",
        glyph: '@',
        color: White,
    ),
    creatures: [
        CreatureConfig(
            id: "goblin",
            spawn_fn: "spawn_goblin",
            glyph: 'g',
            color: Green,
            ai: Aggressive(chase_range: 6),
        ),
    ],
    ui: UiConfig(
        stats_panel: [
            StatField(field: "HP", label: "HP", display: Bar(max_field: "max_HP")),
            StatField(field: "AC", label: "AC", display: Number),
            StatField(field: "attack_bonus", label: "ATK", display: Modifier),
            StatField(field: "damage", label: "DMG", display: DiceExpr),
        ],
    ),
)
```

## Open Design Questions (To Be Discovered)

These are explicitly **not answered yet**. The roguelike is how we answer them.

### How does the host discover available actions?

The interpreter has `has_action(name)` but no "list all actions entity X can take." The host needs to present action menus. Options to explore:
- Introspect action definitions from TypeEnv (read actor type, cost, target requirements)
- DSL declares action menus or action categories
- Host config lists available actions per creature type (like the creature catalog)

### How does turn structure work generically?

OSRIC's `resolve_round()` owns the full 10-segment loop in DSL code. Most other systems use individual turns ("your turn, what do you do?"). The host needs to drive either model. Options:
- The DSL declares a resolution function the host calls
- The host drives individual turns, calling actions one at a time
- Both patterns coexist — the host detects which model the system uses

### How does the host answer spatial prompts?

OSRIC expects `is_rear_attack()`, `creatures_engaged_with()`, `area_occupants()`. These require the host to compute spatial relationships. Options:
- Host implements prompt handlers that compute from grid state
- DSL provides default implementations using a standard spatial API
- Prompts declare their spatial requirements, host provides raw data

### How smart is monster AI?

Start simple (chase/attack/flee), discover what's needed. AI behavior type is configured per creature in the host config. Options for expansion:
- Host-side heuristics only (current approach)
- DSL declares AI behavior hints or priority lists
- AI uses action introspection to evaluate options

### What role do prompts play?

Prompts are currently underused in the DSL modules. For host integration, they become the primary mechanism for the host (acting as GM) to inject decisions. Areas to explore:
- Expanding prompt capabilities (richer return types, context passing)
- More prompts in rule modules for GM decisions
- Host-side prompt answering strategies (auto-answer with spatial data, defer to player, use defaults)

## Phased Approach

### Phase 1: Foundation — Data-Driven Entity Spawning

**Goal:** Load any `.ttrpg` system and spawn entities from DSL definitions instead of hardcoding stats. Host config drives all system-specific presentation.

- Define RON config format (`HostConfig`) with serde deserialization
- Load `.ttrpg` files specified in config (replace `include_str!`)
- Add DSL spawn functions to `roguelike.ttrpg` (e.g., `spawn_goblin(pos: Position)`)
- Replace `spawn_creature()` Rust function with `interp.evaluate_function()` calls
- Render entities using glyph/color from config instead of hardcoded values
- Build stats panel from config field list, reading values via `StateProvider`
- Keep existing combat and AI working — only change entity creation and display

### Phase 2: Action Discovery & Execution

**Goal:** Present action menus derived from the DSL, execute actions through the interpreter.

- Discover available actions via TypeEnv introspection
- Build action menus showing valid actions for the current entity
- Execute actions through the interpreter with proper budget management
- Handle action results (damage, conditions, death) generically

### Phase 3: Turn Management

**Goal:** Support both individual turns and batch-declaration turn models.

- Implement simple "your turn" individual turn model first
- Add initiative mechanics (call DSL's initiative derives/mechanics)
- Support the OSRIC `resolve_round()` pattern for batch resolution
- Discover what abstraction, if any, unifies the two models

### Phase 4: Prompt & Spatial Integration

**Goal:** Answer DSL prompts from game state, especially spatial queries.

- Implement prompt handler that computes spatial answers from grid state
- Handle character creation prompts (either auto-generate or player-driven)
- Discover which prompts need host computation vs. can use DSL defaults
- Feed findings back into prompt design

### Phase 5: OSE Integration

**Goal:** Run OSE rules through the roguelike host.

- Load OSE modules, spawn Characters and Monsters from OSE definitions
- Run OSE combat through the host
- Character creation flow (ability scores, class selection, equipment)
- Identify system-specific code that had to be written — this is the friction report

### Phase 6: OSRIC Integration

**Goal:** Run OSRIC rules — the stress test.

- Segment-based initiative via `resolve_round()`
- Spatial queries (rear attacks, engagement, fend-off)
- Zone tracking and event dispatch (ZoneEntered/Exited)
- Spellcasting pipeline (memorization, casting time, interruption)
- This phase will generate the most feedback for both DSL and host design

### Phase 7: Interface Refinement

**Goal:** Codify discoveries into stable conventions and DSL features.

- Formalize host interface conventions based on Phase 5-6 findings
- Propose DSL features for gaps discovered (display metadata, action categories, turn structure declarations)
- Update the step-based execution design with real requirements from host integration
- Document the host development guide

## Relationship to Step-Based Execution

The step-based execution design (`spec/design/step_based_execution.md`, tdsl-qi09) replaces the synchronous `EffectHandler` callback with a pull-based `Execution` API. This is complementary:

- **Early phases work with the current synchronous API.** The roguelike runs on a single thread with blocking input — the callback model is fine initially.
- **Later phases benefit from step-based execution.** Async prompt resolution, animation between effects, and non-blocking UI all want the pull-based model.
- **Host experience informs step-based priorities.** Which effects the host most wants to intercept, pause at, or animate determines which frame types matter most.

## Success Criteria

The roguelike host is successful when:
1. It can load and run at least two different TTRPG systems (OSE + OSRIC) with minimal system-specific code
2. The system-specific code that *does* exist is clearly motivated and documented
3. Findings have produced concrete DSL improvement proposals
4. Someone can write a new `.ttrpg` system and run it in the roguelike without modifying host code (for basic combat at minimum)
