pub mod config;
mod map;
mod state;
mod ui;

use std::collections::BTreeMap;
use std::io;
use std::path::Path;

use crossterm::event::{self, Event, KeyCode, KeyEventKind};
use rand::SeedableRng;
use rand::rngs::StdRng;
use ttrpg_ast::Name;
use ttrpg_interp::Interpreter;
use ttrpg_interp::adapter::StateAdapter;
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::EntityRef;
use ttrpg_interp::value::Value;

use rustc_hash::FxHashMap;

use crate::config::{DisplayHint, HostConfig, StatField};
use crate::map::{EntityDisplay, Map};
use crate::state::{RoguelikeHandler, read_hp, read_name, read_position};
use crate::ui::StatLine;

// ── Game state ──────────────────────────────────────────────────

struct Game {
    map: Map,
    player: EntityRef,
    monsters: Vec<EntityRef>,
    messages: Vec<String>,
    over: bool,
    /// Glyph + color per entity, populated at spawn time from config.
    display: FxHashMap<EntityRef, (char, ratatui::style::Color)>,
}

impl Game {
    fn alive_monsters(&self, state: &dyn ttrpg_interp::state::StateProvider) -> Vec<EntityRef> {
        self.monsters
            .iter()
            .copied()
            .filter(|e| read_hp(state, e) > 0)
            .collect()
    }

    fn entity_displays(
        &self,
        state: &dyn ttrpg_interp::state::StateProvider,
    ) -> Vec<EntityDisplay> {
        let mut displays = Vec::new();

        // All tracked entities: player + monsters
        let all_entities = std::iter::once(self.player).chain(self.monsters.iter().copied());

        for entity in all_entities {
            if read_hp(state, &entity) <= 0 {
                continue;
            }
            if let Some((x, y)) = read_position(state, &entity) {
                let &(glyph, color) = self.display.get(&entity).unwrap_or(&('?', ratatui::style::Color::White));
                displays.push(EntityDisplay { x, y, glyph, color });
            }
        }

        displays
    }

    /// Build stat lines for the player from config field list.
    fn player_stats(
        &self,
        state: &dyn ttrpg_interp::state::StateProvider,
        stats_panel: &[StatField],
    ) -> Vec<StatLine> {
        stats_panel
            .iter()
            .map(|sf| format_stat(state, &self.player, sf))
            .collect()
    }

    /// Find a monster at a given position.
    fn monster_at(
        &self,
        state: &dyn ttrpg_interp::state::StateProvider,
        x: i64,
        y: i64,
    ) -> Option<EntityRef> {
        for &monster in &self.monsters {
            if read_hp(state, &monster) <= 0 {
                continue;
            }
            if let Some((mx, my)) = read_position(state, &monster)
                && mx == x
                && my == y
            {
                return Some(monster);
            }
        }
        None
    }
}

// ── DSL loading ─────────────────────────────────────────────────

fn load_rules(
    config: &HostConfig,
    config_dir: &Path,
) -> (ttrpg_ast::ast::Program, ttrpg_checker::env::TypeEnv) {
    let manifest_path = config_dir.join(&config.system.manifest);
    let manifest = ttrpg_parser::manifest::load_manifest(&manifest_path).unwrap_or_else(|e| {
        eprintln!("error: {e}");
        std::process::exit(1);
    });

    let pkg_root = manifest_path.parent().unwrap_or(config_dir);
    let resolved = manifest
        .resolve_target(config.system.bundle.as_deref())
        .unwrap_or_else(|e| {
            eprintln!("error: {e}");
            std::process::exit(1);
        });

    let entry_paths: Vec<_> = resolved
        .entry_paths
        .iter()
        .map(|p| pkg_root.join(p))
        .collect();

    let sources = ttrpg_parser::source_resolve::resolve_sources(&entry_paths).unwrap_or_else(|e| {
        eprintln!("error: {e}");
        std::process::exit(1);
    });

    for diag in &sources.diagnostics {
        eprintln!("{}", diag.message);
    }

    let result = ttrpg_parser::parse_multi(&sources.sources);
    if result.has_errors {
        for diag in &result.diagnostics {
            eprintln!("{}", diag.message);
        }
        std::process::exit(1);
    }

    let check_result = ttrpg_checker::check_with_modules(&result.program, &result.module_map);
    let errors: Vec<_> = check_result
        .diagnostics
        .iter()
        .filter(|d| d.severity == ttrpg_ast::diagnostic::Severity::Error)
        .collect();
    if !errors.is_empty() {
        for diag in &errors {
            eprintln!("{}", diag.message);
        }
        std::process::exit(1);
    }

    (result.program, check_result.env)
}

// ── Stat formatting ─────────────────────────────────────────────

fn format_stat(
    state: &dyn ttrpg_interp::state::StateProvider,
    entity: &EntityRef,
    field: &StatField,
) -> StatLine {
    let value = state.read_field(entity, &field.field);
    match &field.display {
        DisplayHint::Bar { max_field } => {
            let cur = match &value {
                Some(Value::Int(n)) => *n,
                _ => 0,
            };
            let max = match state.read_field(entity, max_field) {
                Some(Value::Int(n)) => n,
                _ => 0,
            };
            StatLine {
                label: field.label.clone(),
                text: format!("{cur}/{max}"),
                bar: Some((cur, max)),
            }
        }
        DisplayHint::Number => {
            let text = match &value {
                Some(Value::Int(n)) => n.to_string(),
                _ => "?".into(),
            };
            StatLine { label: field.label.clone(), text, bar: None }
        }
        DisplayHint::Modifier => {
            let text = match &value {
                Some(Value::Int(n)) if *n >= 0 => format!("+{n}"),
                Some(Value::Int(n)) => n.to_string(),
                _ => "?".into(),
            };
            StatLine { label: field.label.clone(), text, bar: None }
        }
        DisplayHint::DiceExpr => {
            let text = match &value {
                Some(Value::DiceExpr(expr)) => format_dice_expr(expr),
                _ => "?".into(),
            };
            StatLine { label: field.label.clone(), text, bar: None }
        }
    }
}

fn format_dice_expr(expr: &ttrpg_interp::value::DiceExpr) -> String {
    let parts: Vec<String> = expr
        .groups
        .iter()
        .map(|g| {
            let base = format!("{}d{}", g.count, g.sides);
            match &g.filter {
                Some(ttrpg_ast::DiceFilter::KeepHighest(n)) => format!("{base}kh{n}"),
                Some(ttrpg_ast::DiceFilter::KeepLowest(n)) => format!("{base}kl{n}"),
                Some(ttrpg_ast::DiceFilter::DropHighest(n)) => format!("{base}dh{n}"),
                Some(ttrpg_ast::DiceFilter::DropLowest(n)) => format!("{base}dl{n}"),
                None => base,
            }
        })
        .collect();
    let joined = parts.join("+");
    match expr.modifier.cmp(&0) {
        std::cmp::Ordering::Greater => format!("{joined}+{}", expr.modifier),
        std::cmp::Ordering::Less => format!("{joined}{}", expr.modifier),
        std::cmp::Ordering::Equal => joined,
    }
}

// ── Entity spawning ─────────────────────────────────────────────

/// Spawn an entity by calling a DSL function with a grid position.
fn spawn_entity(
    interp: &Interpreter,
    adapter: &StateAdapter<GameState>,
    handler: &mut RoguelikeHandler,
    fn_name: &str,
    pos: (i64, i64),
) -> EntityRef {
    use ttrpg_interp::reference_state::GridPosition;

    let pos_val = adapter.with_state_mut(|state| state.register_position(GridPosition(pos.0, pos.1)));
    let result = adapter.run(handler, |state, eff| {
        interp.evaluate_function(state, eff, fn_name, vec![pos_val.clone()])
    });
    match result {
        Ok(Value::Entity(entity)) => entity,
        Ok(other) => {
            eprintln!("error: {fn_name} returned {other:?}, expected entity");
            std::process::exit(1);
        }
        Err(e) => {
            eprintln!("error: {fn_name} failed: {}", e.message);
            std::process::exit(1);
        }
    }
}

// ── Main ────────────────────────────────────────────────────────

fn main() -> io::Result<()> {
    // Load config
    let config_path = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "roguelike.ron".to_string());
    let config_path = Path::new(&config_path);
    let config = HostConfig::load(config_path).unwrap_or_else(|e| {
        eprintln!("error: {e}");
        std::process::exit(1);
    });
    let config_dir = config_path
        .parent()
        .unwrap_or(Path::new("."))
        .to_path_buf();

    // Load DSL rules
    let (program, type_env) = load_rules(&config, &config_dir);
    let interp = Interpreter::new(&program, &type_env).expect("interpreter init failed");

    // Set up game state
    let gs = GameState::new();
    let adapter = StateAdapter::new(gs);
    let mut handler = RoguelikeHandler::new(StdRng::from_os_rng());

    // Build display info map
    let mut display: FxHashMap<EntityRef, (char, ratatui::style::Color)> = FxHashMap::default();

    // Spawn player via DSL
    let player = spawn_entity(&interp, &adapter, &mut handler, &config.player.spawn_fn, (5, 5));
    display.insert(player, (config.player.glyph, config.player.color.into()));

    // Spawn monsters (positions are still hardcoded — map generation will own this later)
    let monster_spawns: &[(&str, (i64, i64))] = &[
        ("spawn_goblin", (25, 4)),
        ("spawn_goblin", (28, 5)),
        ("spawn_rat", (15, 14)),
    ];

    // Build a lookup from spawn_fn name → config display info
    let creature_configs: FxHashMap<&str, _> = config
        .creatures
        .iter()
        .map(|c| (c.spawn_fn.as_str(), (c.glyph, ratatui::style::Color::from(c.color))))
        .collect();

    let monsters: Vec<EntityRef> = monster_spawns
        .iter()
        .map(|(fn_name, pos)| {
            let entity = spawn_entity(&interp, &adapter, &mut handler, fn_name, *pos);
            if let Some(&info) = creature_configs.get(fn_name) {
                display.insert(entity, info);
            }
            entity
        })
        .collect();

    let mut game = Game {
        map: Map::demo_dungeon(),
        player,
        monsters,
        messages: vec!["Welcome to the dungeon! Arrow keys to move, q to quit.".into()],
        over: false,
        display,
    };

    // Terminal setup
    let mut terminal = ratatui::init();

    let result = run_game_loop(
        &mut terminal,
        &interp,
        &adapter,
        &mut handler,
        &mut game,
        &config.ui.stats_panel,
    );

    ratatui::restore();
    result
}

fn run_game_loop(
    terminal: &mut ratatui::DefaultTerminal,
    interp: &Interpreter,
    adapter: &StateAdapter<GameState>,
    handler: &mut RoguelikeHandler,
    game: &mut Game,
    stats_panel: &[StatField],
) -> io::Result<()> {
    loop {
        // Render
        let displays = game.entity_displays(adapter);
        let stats = game.player_stats(adapter, stats_panel);
        terminal.draw(|frame| {
            ui::draw(frame, &game.map, &displays, &game.messages, &stats);
        })?;

        if game.over {
            // Wait for q to quit
            if let Event::Key(key) = event::read()?
                && key.code == KeyCode::Char('q')
            {
                return Ok(());
            }
            continue;
        }

        // Input
        let Event::Key(key) = event::read()? else {
            continue;
        };
        if key.kind != KeyEventKind::Press {
            continue;
        }

        let (dx, dy) = match key.code {
            KeyCode::Char('q') | KeyCode::Esc => return Ok(()),
            KeyCode::Up | KeyCode::Char('k') => (0, -1),
            KeyCode::Down | KeyCode::Char('j') => (0, 1),
            KeyCode::Left | KeyCode::Char('h') => (-1, 0),
            KeyCode::Right | KeyCode::Char('l') => (1, 0),
            KeyCode::Char('y') => (-1, -1),
            KeyCode::Char('u') => (1, -1),
            KeyCode::Char('b') => (-1, 1),
            KeyCode::Char('n') => (1, 1),
            KeyCode::Char('.') => (0, 0), // wait
            _ => continue,
        };

        // Player turn
        player_turn(interp, adapter, handler, game, dx, dy);

        // Check player death
        let player_hp = read_hp(adapter, &game.player);
        if player_hp <= 0 {
            game.messages.push("You died! Press q to quit.".into());
            game.over = true;
            continue;
        }

        // Monster turns
        monster_turns(interp, adapter, handler, game);

        // Check player death again after monster turns
        let player_hp = read_hp(adapter, &game.player);
        if player_hp <= 0 {
            game.messages.push("You died! Press q to quit.".into());
            game.over = true;
        }
    }
}

fn player_turn(
    interp: &Interpreter,
    adapter: &StateAdapter<GameState>,
    handler: &mut RoguelikeHandler,
    game: &mut Game,
    dx: i64,
    dy: i64,
) {
    let Some((px, py)) = read_position(adapter, &game.player) else {
        return;
    };

    let nx = px + dx;
    let ny = py + dy;

    // Wait action
    if dx == 0 && dy == 0 {
        game.messages.push("You wait...".into());
        return;
    }

    // Check for monster at target — attack instead of move
    if let Some(target) = game.monster_at(adapter, nx, ny) {
        let target_name = read_name(adapter, &target);
        let target_hp_before = read_hp(adapter, &target);

        // Provision a turn budget so the action cost can be deducted
        let result = adapter.run(handler, |state, eff| {
            let mut budget = BTreeMap::new();
            budget.insert(Name::from("actions"), Value::Int(1));
            budget.insert(Name::from("bonus_actions"), Value::Int(1));
            budget.insert(Name::from("reactions"), Value::Int(1));
            budget.insert(Name::from("movement"), Value::Int(0));
            budget.insert(Name::from("free_interactions"), Value::Int(1));
            // Set budget via effect
            eff.handle(ttrpg_interp::effect::Effect::ProvisionBudget {
                actor: game.player,
                budget,
            });

            interp.execute_action(
                state,
                eff,
                "MeleeAttack",
                game.player,
                vec![Value::Entity(target)],
            )
        });

        match result {
            Ok(_) => {
                let target_hp_after = read_hp(adapter, &target);
                let damage_dealt = target_hp_before - target_hp_after;
                if damage_dealt > 0 {
                    game.messages.push(format!(
                        "You hit the {target_name} for {damage_dealt} damage! (HP: {target_hp_after})"
                    ));
                    if target_hp_after <= 0 {
                        game.messages.push(format!("The {target_name} is slain!"));
                    }
                } else {
                    game.messages.push(format!("You miss the {target_name}!"));
                }
            }
            Err(e) => {
                game.messages.push(format!("Attack failed: {}", e.message));
            }
        }

        // Clear budget
        adapter.run(handler, |_state, eff| {
            eff.handle(ttrpg_interp::effect::Effect::ClearBudget { actor: game.player });
        });
        return;
    }

    // Movement — check wall collision
    if !game.map.walkable(nx, ny) {
        game.messages.push("You bump into a wall.".into());
        return;
    }

    // Move player
    adapter.run(handler, |_state, _eff| {
        // Direct state mutation for movement (not a DSL action)
    });
    // We need mutable access to GameState for set_position.
    // StateAdapter doesn't expose mutable access directly, so we
    // use a ProvisionBudget/ClearBudget hack... Actually, let me
    // use write_field through the adapter's StateProvider path.
    // The adapter auto-applies MutateField effects.
    let pos_val = adapter.with_state_mut(|state| {
        use ttrpg_interp::reference_state::GridPosition;
        state.register_position(GridPosition(nx, ny))
    });
    adapter.run(handler, |_state, eff| {
        use ttrpg_ast::ast::AssignOp;
        use ttrpg_interp::effect::FieldPathSegment;

        eff.handle(ttrpg_interp::effect::Effect::MutateField {
            entity: game.player,
            path: vec![FieldPathSegment::Field(Name::from("position"))],
            op: AssignOp::Eq,
            value: pos_val,
            bounds: None,
        });
    });
}

fn monster_turns(
    interp: &Interpreter,
    adapter: &StateAdapter<GameState>,
    handler: &mut RoguelikeHandler,
    game: &mut Game,
) {
    let alive = game.alive_monsters(adapter);
    let Some((px, py)) = read_position(adapter, &game.player) else {
        return;
    };

    for &monster in &alive {
        let Some((mx, my)) = read_position(adapter, &monster) else {
            continue;
        };
        let monster_name = read_name(adapter, &monster);

        // Chebyshev distance
        let dist = (px - mx).abs().max((py - my).abs());

        if dist <= 1 {
            // Adjacent — attack!
            let player_hp_before = read_hp(adapter, &game.player);

            let result = adapter.run(handler, |state, eff| {
                let mut budget = BTreeMap::new();
                budget.insert(Name::from("actions"), Value::Int(1));
                budget.insert(Name::from("bonus_actions"), Value::Int(1));
                budget.insert(Name::from("reactions"), Value::Int(1));
                budget.insert(Name::from("movement"), Value::Int(0));
                budget.insert(Name::from("free_interactions"), Value::Int(1));
                eff.handle(ttrpg_interp::effect::Effect::ProvisionBudget {
                    actor: monster,
                    budget,
                });

                interp.execute_action(
                    state,
                    eff,
                    "MeleeAttack",
                    monster,
                    vec![Value::Entity(game.player)],
                )
            });

            match result {
                Ok(_) => {
                    let player_hp_after = read_hp(adapter, &game.player);
                    let damage_dealt = player_hp_before - player_hp_after;
                    if damage_dealt > 0 {
                        game.messages.push(format!(
                            "The {monster_name} hits you for {damage_dealt} damage! (HP: {player_hp_after})"
                        ));
                    } else {
                        game.messages
                            .push(format!("The {monster_name} misses you!"));
                    }
                }
                Err(_) => {
                    game.messages
                        .push(format!("The {monster_name} flails wildly!"));
                }
            }

            adapter.run(handler, |_state, eff| {
                eff.handle(ttrpg_interp::effect::Effect::ClearBudget { actor: monster });
            });
        } else if dist <= 6 {
            // Close enough to chase — A* pathfind toward player
            let blocked: Vec<(i64, i64)> = alive
                .iter()
                .filter(|m| **m != monster)
                .filter_map(|m| read_position(adapter, m))
                .collect();

            if let Some((nx, ny)) = game.map.astar_next_step((mx, my), (px, py), &blocked) {
                // Don't move onto the player (attack range handled above)
                if (nx, ny) != (px, py) {
                    let pos_val = adapter.with_state_mut(|state| {
                        use ttrpg_interp::reference_state::GridPosition;
                        state.register_position(GridPosition(nx, ny))
                    });
                    adapter.run(handler, |_state, eff| {
                        use ttrpg_ast::ast::AssignOp;
                        use ttrpg_interp::effect::FieldPathSegment;

                        eff.handle(ttrpg_interp::effect::Effect::MutateField {
                            entity: monster,
                            path: vec![FieldPathSegment::Field(Name::from("position"))],
                            op: AssignOp::Eq,
                            value: pos_val,
                            bounds: None,
                        });
                    });
                }
            }
        }
        // else: too far, monster idles
    }
}
