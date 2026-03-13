mod map;
mod state;
mod ui;

use std::collections::BTreeMap;
use std::io;

use crossterm::event::{self, Event, KeyCode, KeyEventKind};
use rand::SeedableRng;
use rand::rngs::StdRng;
use ttrpg_ast::Name;
use ttrpg_interp::Interpreter;
use ttrpg_interp::adapter::StateAdapter;
use ttrpg_interp::reference_state::GameState;
use ttrpg_interp::state::EntityRef;
use ttrpg_interp::value::{DiceExpr, Value};

use crate::map::{EntityDisplay, Map};
use crate::state::{RoguelikeHandler, read_hp, read_name, read_position, spawn_creature};

// ── Game state ──────────────────────────────────────────────────

struct Game {
    map: Map,
    player: EntityRef,
    monsters: Vec<EntityRef>,
    messages: Vec<String>,
    game_over: bool,
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

        if let Some((x, y)) = read_position(state, &self.player) {
            displays.push(EntityDisplay {
                x,
                y,
                glyph: '@',
                is_player: true,
            });
        }

        for &monster in &self.monsters {
            if read_hp(state, &monster) <= 0 {
                continue;
            }
            if let Some((x, y)) = read_position(state, &monster) {
                let name = read_name(state, &monster);
                let glyph = name.chars().next().unwrap_or('?');
                displays.push(EntityDisplay {
                    x,
                    y,
                    glyph,
                    is_player: false,
                });
            }
        }

        displays
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

fn load_rules() -> (ttrpg_ast::ast::Program, ttrpg_checker::env::TypeEnv) {
    let source = include_str!("../roguelike.ttrpg");
    let sources = vec![("roguelike.ttrpg".to_string(), source.to_string())];

    let result = ttrpg_parser::parse_multi(&sources);
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

// ── Main ────────────────────────────────────────────────────────

fn main() -> io::Result<()> {
    // Load DSL rules
    let (program, type_env) = load_rules();
    let interp = Interpreter::new(&program, &type_env).expect("interpreter init failed");

    // Set up game state
    let mut gs = GameState::new();

    // Player: 20 HP, AC 14, +3 to hit, 1d6 damage
    let player = spawn_creature(
        &mut gs,
        "Hero",
        "Player",
        (5, 5),
        20,
        14,
        3,
        DiceExpr::single(1, 6, None, 0),
    );

    // Monsters in room 2 and room 3
    let goblin1 = spawn_creature(
        &mut gs,
        "Goblin",
        "Goblin",
        (25, 4),
        6,
        12,
        2,
        DiceExpr::single(1, 4, None, 0),
    );
    let goblin2 = spawn_creature(
        &mut gs,
        "Goblin",
        "Goblin",
        (28, 5),
        6,
        12,
        2,
        DiceExpr::single(1, 4, None, 0),
    );
    let rat = spawn_creature(
        &mut gs,
        "Rat",
        "Rat",
        (15, 14),
        3,
        10,
        0,
        DiceExpr::single(1, 2, None, 0),
    );

    let adapter = StateAdapter::new(gs);
    let mut handler = RoguelikeHandler::new(StdRng::from_os_rng());

    let mut game = Game {
        map: Map::demo_dungeon(),
        player,
        monsters: vec![goblin1, goblin2, rat],
        messages: vec!["Welcome to the dungeon! Arrow keys to move, q to quit.".into()],
        game_over: false,
    };

    // Terminal setup
    let mut terminal = ratatui::init();

    let result = run_game_loop(&mut terminal, &interp, &adapter, &mut handler, &mut game);

    ratatui::restore();
    result
}

fn run_game_loop(
    terminal: &mut ratatui::DefaultTerminal,
    interp: &Interpreter,
    adapter: &StateAdapter<GameState>,
    handler: &mut RoguelikeHandler,
    game: &mut Game,
) -> io::Result<()> {
    loop {
        // Render
        let displays = game.entity_displays(adapter);
        terminal.draw(|frame| {
            ui::draw(frame, &game.map, &displays, &game.messages);
        })?;

        if game.game_over {
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
            game.game_over = true;
            continue;
        }

        // Monster turns
        monster_turns(interp, adapter, handler, game);

        // Check player death again after monster turns
        let player_hp = read_hp(adapter, &game.player);
        if player_hp <= 0 {
            game.messages.push("You died! Press q to quit.".into());
            game.game_over = true;
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
