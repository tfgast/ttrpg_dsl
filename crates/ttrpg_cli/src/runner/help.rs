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
        syntax: "do <Action>(<actor>, args...)",
        description: "Execute an action",
        detail: "Execute a declared action. The first argument is the actor (receiver).\n  Remaining arguments are evaluated as expressions or handle names.",
        examples: &[
            "do Attack(fighter, goblin)",
            "do CastBless(caster, [fighter, rogue])",
        ],
        category: "Execution",
    },
    CommandInfo {
        name: "call",
        syntax: "call <func>(args...)",
        description: "Call a derive or mechanic",
        detail: "Call a pure computation (derive) or dice-rolling function (mechanic).\n  Arguments are evaluated as expressions or handle names.",
        examples: &[
            "call modifier(16)",
            "call attack_roll(5)",
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
        description: "List all derives and mechanics",
        detail: "List all declared derives and mechanics with their signatures.",
        examples: &["mechanics"],
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
            "assert_eq call modifier(16), 3",
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
    "Help",
];

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
            self.output.push(format!("{}:", cat));
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

    fn help_command(&mut self, name: &str) -> Result<(), CliError> {
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
                        self.output.push(format!("    {}", ex));
                    }
                }
                Ok(())
            }
            None => Err(CliError::Message(format!(
                "unknown command: {}. Type 'help' for a list.",
                name
            ))),
        }
    }
}
