# Game System Templates

Skeleton `.ttrpg` files for bootstrapping new game systems.
Each template is self-contained and passes `ttrpg check`.

## Quick Start

1. Copy the template closest to your starting point
2. Rename to `<your_game>.ttrpg`
3. Replace the system name: `system "Your Game" { ... }`
4. Fill in `// TEMPLATE:` sections with your game's rules
5. Validate: `ttrpg check your_game.ttrpg`

## Template Index

| Template | Use when you need... | Key patterns |
|----------|---------------------|--------------|
| `game_skeleton.ttrpg` | Blank slate, minimal starting point | system, entity, action |
| `combat_module.ttrpg` | Attack/damage/conditions loop | mechanic, action, event, hook, condition |
| `magic_module.ttrpg` | Spellcasting with concentration | group, tag, invocation, revoke |
| `skill_module.ttrpg` | Ability scores + skill checks | derive, mechanic, map, set |
| `class_module.ttrpg` | Character classes + XP progression | enum, struct, derive, match, dice() |

## Composing Modules

Templates are standalone, but a real game system combines patterns from
multiple templates. Use `system "Same Name" { }` blocks across files
(they merge additively) or `use "System Name"` for imports between systems.

## Validation

Run each file individually since they define separate systems:

```sh
for f in templates/*.ttrpg; do ttrpg check "$f"; done
```
