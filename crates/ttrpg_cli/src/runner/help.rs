use super::{CliError, Runner};

struct CommandInfo {
    name: &'static str,
    syntax: &'static str,
    description: &'static str,
    detail: &'static str,
    examples: &'static [&'static str],
    category: &'static str,
}

const COMMANDS: &[CommandInfo] = &[
    // Pipeline
    CommandInfo {
        name: "load",
        syntax: "load <path...>",
        description: "Load source files",
        detail: "Parse, lower, check, and build interpreter from one or more source files.\n  Glob patterns are supported. Clears previous program state.",
        examples: &[
            "load game.ttrpg",
            "load spec/v0/*.ttrpg",
        ],
        category: "Pipeline",
    },
    CommandInfo {
        name: "source",
        syntax: "source [-s] <<DELIM ... DELIM",
        description: "Define inline DSL source",
        detail: "Define DSL source inline using heredoc syntax. Lines between the opening\n  <<DELIM and the closing DELIM line are parsed, checked, and loaded as if\n  they were a .ttrpg file. Use -s for snippet mode (auto-wraps in a system block).",
        examples: &[
            "source <<END\nsystem \"test\" {\n    entity Character { HP: int }\n}\nEND",
            "source -s <<END\n    entity Character { HP: int }\nEND",
        ],
        category: "Pipeline",
    },
    CommandInfo {
        name: "eval",
        syntax: "eval <expr>",
        description: "Evaluate a DSL expression",
        detail: "Evaluate an expression in the current program context.\n  Spawned entity handles are available as variables.",
        examples: &[
            "eval 2 + 3",
            "eval floor((16 - 10) / 2)",
            "eval fighter.HP",
        ],
        category: "Pipeline",
    },
    CommandInfo {
        name: "let",
        syntax: "let <name> = <expr>",
        description: "Bind expression result to a variable",
        detail: "Evaluate an expression and store the result in a named variable.\n  The variable can then be used in subsequent eval, assert, and assert_eq expressions.\n  Works with any expression including action calls (both function-call and method syntax).\n  Useful for capturing action return values or testing multiple fields without re-evaluating.",
        examples: &[
            "let result = resolve_attack(fighter, goblin)",
            "assert result.hit == true",
            "assert_eq result.damage, 5",
            "let hp = Heal(cleric)",
            "let x = 2 + 3",
        ],
        category: "Pipeline",
    },
    CommandInfo {
        name: "reload",
        syntax: "reload",
        description: "Reload last loaded files",
        detail: "Re-run the pipeline on the most recently loaded files.\n  Useful after editing source files externally.",
        examples: &["reload"],
        category: "Pipeline",
    },
    CommandInfo {
        name: "errors",
        syntax: "errors",
        description: "Show diagnostics from last load",
        detail: "Display all errors and warnings from the most recent load or reload.",
        examples: &["errors"],
        category: "Pipeline",
    },
    // Entities
    CommandInfo {
        name: "spawn",
        syntax: "spawn <Type> <handle> [{ field: value, ... }]",
        description: "Create an entity instance",
        detail: "Create a new entity in game state with optional field initialization.\n  Fields with defaults can be omitted. Optional groups use inline syntax.",
        examples: &[
            "spawn Character fighter { name: \"Ava\", HP: 30, AC: 18 }",
            "spawn Character caster { Spellcasting { spell_dc: 15 } }",
        ],
        category: "Entities",
    },
    CommandInfo {
        name: "set",
        syntax: "set <handle>.<field> [= | += | -=] <value>",
        description: "Modify an entity field",
        detail: "Set, increment, or decrement a field on a spawned entity.\n  Resource fields are automatically clamped to their declared bounds.",
        examples: &[
            "set fighter.HP -= 10",
            "set fighter.AC = 20",
            "set caster.Spellcasting.spell_slots -= 1",
        ],
        category: "Entities",
    },
    CommandInfo {
        name: "destroy",
        syntax: "destroy <handle>",
        description: "Remove an entity",
        detail: "Remove a spawned entity from game state.",
        examples: &["destroy goblin"],
        category: "Entities",
    },
    CommandInfo {
        name: "inspect",
        syntax: "inspect <handle>[.field]",
        description: "View entity or field state",
        detail: "Display an entity's type, fields, optional groups, and conditions.\n  Can also inspect a single field or group field.",
        examples: &[
            "inspect fighter",
            "inspect fighter.HP",
            "inspect caster.Spellcasting.spell_dc",
        ],
        category: "Entities",
    },
    // Execution
    CommandInfo {
        name: "do",
        syntax: "do <expr>",
        description: "Evaluate an expression for its side effects",
        detail: "Evaluate any expression and print the result. Typically used to\n  execute actions, but works with any expression.\n  Supports both function-call and method-call syntax for actions.",
        examples: &[
            "do Attack(fighter, goblin)",
            "do fighter.Attack(goblin)",
            "do CastBless(caster, [fighter, rogue])",
        ],
        category: "Execution",
    },
    CommandInfo {
        name: "call",
        syntax: "call <func>(args...)",
        description: "Call a derive, mechanic, or function",
        detail: "Call a derive, mechanic, or function block.\n  Derives are pure computations, mechanics can roll dice,\n  and functions can roll dice and mutate state.\n  Arguments are evaluated as expressions or handle names.",
        examples: &[
            "call modifier(16)",
            "call attack_roll(5)",
            "call heal_target(hero, 10)",
        ],
        category: "Execution",
    },
    CommandInfo {
        name: "breakdown",
        syntax: "breakdown <expr>",
        description: "Show modify provenance for a derive/mechanic call",
        detail: "Evaluate an expression and display all modifiers that were applied,\n  including their source (condition/option), tags, phase, and changes.\n  Useful for debugging why a value was modified.",
        examples: &[
            "breakdown attack_roll(fighter, goblin)",
            "breakdown resolve_save(target, 14)",
        ],
        category: "Execution",
    },
    // Groups
    CommandInfo {
        name: "grant",
        syntax: "grant <handle>.<Group> [{ field: value, ... }]",
        description: "Grant an optional group",
        detail: "Activate an optional group on an entity with optional field initialization.\n  Cannot grant required (include) groups.",
        examples: &[
            "grant hero.Spellcasting { spell_slots: 5, spell_dc: 14 }",
            "grant hero.Rage",
        ],
        category: "Groups",
    },
    CommandInfo {
        name: "revoke",
        syntax: "revoke <handle>.<Group>",
        description: "Revoke an optional group",
        detail: "Remove an optional group from an entity.\n  Cannot revoke required (include) groups.",
        examples: &["revoke hero.Spellcasting"],
        category: "Groups",
    },
    // Inspection
    CommandInfo {
        name: "state",
        syntax: "state",
        description: "Show all entities and their values",
        detail: "Display all spawned entities with their fields, groups, and conditions.",
        examples: &["state"],
        category: "Inspection",
    },
    CommandInfo {
        name: "types",
        syntax: "types",
        description: "List all defined types",
        detail: "List all declared types: entities, structs, enums, and unit types.",
        examples: &["types"],
        category: "Inspection",
    },
    CommandInfo {
        name: "entity",
        syntax: "entity <name>",
        description: "Show entity type declaration",
        detail: "Display an entity type's fields, optional groups, and defaults.\n  Shows the type declaration, not a runtime instance (use 'inspect' for that).",
        examples: &[
            "entity Character",
            "entity Monster",
        ],
        category: "Inspection",
    },
    CommandInfo {
        name: "actions",
        syntax: "actions",
        description: "List all actions with signatures",
        detail: "List all declared actions showing receiver, parameters, and return type.",
        examples: &["actions"],
        category: "Inspection",
    },
    CommandInfo {
        name: "mechanics",
        syntax: "mechanics",
        description: "List all derives and mechanics (alias: derives)",
        detail: "List all declared derives and mechanics with their signatures.",
        examples: &["mechanics", "derives"],
        category: "Inspection",
    },
    CommandInfo {
        name: "functions",
        syntax: "functions",
        description: "List all function blocks",
        detail: "List all declared function blocks with their signatures.\n  Functions can roll dice and mutate state but have no receiver.",
        examples: &["functions"],
        category: "Inspection",
    },
    CommandInfo {
        name: "conditions",
        syntax: "conditions",
        description: "List active conditions",
        detail: "List all active conditions across all spawned entities.",
        examples: &["conditions"],
        category: "Inspection",
    },
    CommandInfo {
        name: "condition_decls",
        syntax: "condition_decls",
        description: "List all condition declarations",
        detail: "List all declared conditions showing parameters, receiver, and extends list. Unlike 'conditions' which shows active instances on live entities, this shows the type declarations.",
        examples: &["condition_decls"],
        category: "Inspection",
    },
    CommandInfo {
        name: "events",
        syntax: "events",
        description: "List all event declarations",
        detail: "List all declared events showing parameters and body fields.",
        examples: &["events"],
        category: "Inspection",
    },
    CommandInfo {
        name: "reactions",
        syntax: "reactions",
        description: "List all reaction declarations",
        detail: "List all declared reactions showing receiver, trigger, parameters, and return type.",
        examples: &["reactions"],
        category: "Inspection",
    },
    CommandInfo {
        name: "hooks",
        syntax: "hooks",
        description: "List all hook declarations",
        detail: "List all declared hooks showing receiver, trigger, parameters, and return type.",
        examples: &["hooks"],
        category: "Inspection",
    },
    // Options
    CommandInfo {
        name: "enable",
        syntax: "enable <name>",
        description: "Enable an option",
        detail: "Enable a declared option (variant rule / feature flag).",
        examples: &["enable flanking"],
        category: "Options",
    },
    CommandInfo {
        name: "disable",
        syntax: "disable <name>",
        description: "Disable an option",
        detail: "Disable a declared option.",
        examples: &["disable flanking"],
        category: "Options",
    },
    CommandInfo {
        name: "options",
        syntax: "options",
        description: "List all options with current state",
        detail: "List all declared options showing on/off state and description.",
        examples: &["options"],
        category: "Options",
    },
    // Testing
    CommandInfo {
        name: "assert",
        syntax: "assert <expr>",
        description: "Verify expression is true",
        detail: "Evaluate an expression and fail if it is not true.",
        examples: &[
            "assert fighter.HP > 0",
            "assert 2 + 3 == 5",
        ],
        category: "Testing",
    },
    CommandInfo {
        name: "assert_eq",
        syntax: "assert_eq <expr>, <expr>",
        description: "Verify two expressions are equal",
        detail: "Evaluate two comma-separated expressions and fail if they differ.",
        examples: &[
            "assert_eq fighter.HP, 30",
            "assert_eq modifier(16), 3",
        ],
        category: "Testing",
    },
    CommandInfo {
        name: "assert_ne",
        syntax: "assert_ne <expr>, <expr>",
        description: "Verify two expressions are not equal",
        detail: "Evaluate two comma-separated expressions and fail if they are equal.",
        examples: &[
            "assert_ne result, TurnOutcome.Impossible",
            "assert_ne fighter.HP, 0",
        ],
        category: "Testing",
    },
    CommandInfo {
        name: "assert_match",
        syntax: "assert_match <expr>, <EnumName>.<Variant>",
        description: "Verify expression matches an enum variant",
        detail: "Evaluate an expression and check that it is a specific enum variant.\n  Only checks the variant name — fields are ignored.",
        examples: &[
            "assert_match result, TurnOutcome.Turned",
            "assert_match school, SpellSchool.Evocation",
        ],
        category: "Testing",
    },
    CommandInfo {
        name: "assert_err",
        syntax: "assert_err <command>",
        description: "Verify a command errors",
        detail: "Run a command and fail if it does not produce an error.\n  The command's error is suppressed on success.",
        examples: &[
            "assert_err destroy nonexistent",
            "assert_err eval 1 + true",
        ],
        category: "Testing",
    },
    CommandInfo {
        name: "assert_condition",
        syntax: "assert_condition <handle>, <ConditionName>",
        description: "Verify entity has a condition",
        detail: "Check that a spawned entity currently has the named condition active.",
        examples: &[
            "assert_condition fighter, Prone",
            "assert_condition target, CastingSpell",
        ],
        category: "Testing",
    },
    CommandInfo {
        name: "assert_no_condition",
        syntax: "assert_no_condition <handle>, <ConditionName>",
        description: "Verify entity does not have a condition",
        detail: "Check that a spawned entity does not currently have the named condition active.",
        examples: &[
            "assert_no_condition fighter, Prone",
            "assert_no_condition target, Stunned",
        ],
        category: "Testing",
    },
    // Dice Control
    CommandInfo {
        name: "seed",
        syntax: "seed <value>",
        description: "Set RNG seed",
        detail: "Set the random number generator seed for deterministic dice rolls.",
        examples: &["seed 42"],
        category: "Dice Control",
    },
    CommandInfo {
        name: "rolls",
        syntax: "rolls <v1 v2 ...> | clear",
        description: "Queue predetermined roll results",
        detail: "Queue specific values for upcoming dice rolls, consumed in order.\n  Use 'rolls clear' to empty the queue. RNG resumes after queue empties.",
        examples: &[
            "rolls 18 5 12",
            "rolls clear",
        ],
        category: "Dice Control",
    },
    CommandInfo {
        name: "prompts",
        syntax: "prompts <expr> | clear",
        description: "Queue predetermined prompt responses",
        detail: "Queue a value for the next ResolvePrompt effect, consumed in order.\n  Values are parsed and evaluated at queue time — syntax errors are caught immediately.\n  Use 'prompts clear' to empty the queue. When the queue is empty, prompts\n  fall back to auto-resolve (default body, then suggest value).",
        examples: &[
            "prompts 42",
            "prompts \"longsword\"",
            "prompts true",
            "prompts clear",
        ],
        category: "Dice Control",
    },
    // Host Simulation
    CommandInfo {
        name: "emit",
        syntax: "emit <Event>(param: expr, ...)",
        description: "Fire a DSL event from the host side",
        detail: "Emit an event, executing all matching hooks and reactions.\n  Arguments are evaluated as DSL expressions with handle resolution.\n  Useful for testing zone events and host-driven interactions.",
        examples: &[
            "emit ZoneEntered(target: orc, zone: silence_zone)",
            "emit ZoneExited(target: fighter, zone: wall)",
            "emit ZoneCrossed(target: goblin, zone: fire_wall)",
        ],
        category: "Host Simulation",
    },
    CommandInfo {
        name: "place",
        syntax: "place <handle> <x> <y>",
        description: "Set entity position on a grid",
        detail: "Set an entity's position field to a GridPosition(x, y) value.\n  Uses 'center' for Zone entities, 'position' for others.\n  Supports 'x y', 'x,y', or 'at x,y' syntax.",
        examples: &[
            "place fighter 5 3",
            "place silence_zone at 10,10",
            "place goblin 0, 0",
        ],
        category: "Host Simulation",
    },
    // Help
    CommandInfo {
        name: "help",
        syntax: "help [<command>]",
        description: "Show this help",
        detail: "Show a summary of all commands, or detailed help for a specific command.",
        examples: &[
            "help",
            "help spawn",
        ],
        category: "Help",
    },
];

/// Category display order.
const CATEGORIES: &[&str] = &[
    "Pipeline",
    "Entities",
    "Execution",
    "Groups",
    "Inspection",
    "Options",
    "Testing",
    "Dice Control",
    "Host Simulation",
    "Help",
];

/// Returns `true` if `name` matches a known command in the help system.
pub(super) fn is_known_command(name: &str) -> bool {
    COMMANDS.iter().any(|c| c.name == name)
}

impl Runner {
    pub(super) fn cmd_help(&mut self, topic: Option<&str>) -> Result<(), CliError> {
        match topic {
            None => self.help_overview(),
            Some(name) => self.help_command(name),
        }
    }

    fn help_overview(&mut self) -> Result<(), CliError> {
        // Find the longest syntax string for alignment
        let max_syntax = COMMANDS.iter().map(|c| c.syntax.len()).max().unwrap_or(0);

        for (i, &cat) in CATEGORIES.iter().enumerate() {
            if i > 0 {
                self.output.push(String::new());
            }
            self.output.push(format!("{cat}:"));
            for cmd in COMMANDS.iter().filter(|c| c.category == cat) {
                self.output.push(format!(
                    "  {:<width$}  {}",
                    cmd.syntax,
                    cmd.description,
                    width = max_syntax,
                ));
            }
        }
        Ok(())
    }

    pub(super) fn help_command(&mut self, name: &str) -> Result<(), CliError> {
        let cmd = COMMANDS.iter().find(|c| c.name == name);
        match cmd {
            Some(info) => {
                self.output.push(info.syntax.to_string());
                self.output.push(String::new());
                for line in info.detail.split('\n') {
                    self.output.push(format!("  {}", line.trim_start()));
                }
                if !info.examples.is_empty() {
                    self.output.push(String::new());
                    self.output.push("  Examples:".to_string());
                    for ex in info.examples {
                        self.output.push(format!("    {ex}"));
                    }
                }
                Ok(())
            }
            None => Err(CliError::Message(format!(
                "unknown command: {name}. Type 'help' for a list."
            ))),
        }
    }
}
