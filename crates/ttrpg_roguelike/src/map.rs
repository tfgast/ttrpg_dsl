use pathfinding::prelude::astar;
use ttrpg_interp::state::EntityRef;

// ── Tile ────────────────────────────────────────────────────────

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Tile {
    Floor,
    Wall,
}

impl Tile {
    pub fn walkable(self) -> bool {
        self == Tile::Floor
    }

    pub fn glyph(self) -> char {
        match self {
            Tile::Floor => '.',
            Tile::Wall => '#',
        }
    }
}

// ── Map ─────────────────────────────────────────────────────────

pub struct Map {
    pub width: usize,
    pub height: usize,
    tiles: Vec<Tile>,
}

impl Map {
    pub fn new(width: usize, height: usize) -> Self {
        Map {
            width,
            height,
            tiles: vec![Tile::Floor; width * height],
        }
    }

    pub fn get(&self, x: usize, y: usize) -> Tile {
        if x < self.width && y < self.height {
            self.tiles[y * self.width + x]
        } else {
            Tile::Wall
        }
    }

    pub fn set(&mut self, x: usize, y: usize, tile: Tile) {
        if x < self.width && y < self.height {
            self.tiles[y * self.width + x] = tile;
        }
    }

    pub fn walkable(&self, x: i64, y: i64) -> bool {
        if x < 0 || y < 0 {
            return false;
        }
        self.get(x as usize, y as usize).walkable()
    }

    /// Create a simple dungeon with rooms and corridors.
    pub fn demo_dungeon() -> Self {
        let (w, h) = (40, 20);
        let mut map = Map::new(w, h);

        // Fill everything with walls
        for y in 0..h {
            for x in 0..w {
                map.set(x, y, Tile::Wall);
            }
        }

        // Room 1: top-left (2,2)-(12,8)
        carve_room(&mut map, 2, 2, 11, 7);

        // Room 2: top-right (20,2)-(35,8)
        carve_room(&mut map, 20, 2, 14, 7);

        // Room 3: bottom-center (10,12)-(28,18)
        carve_room(&mut map, 10, 12, 17, 7);

        // Corridor: room 1 → room 2 (horizontal at y=5)
        carve_h_corridor(&mut map, 13, 19, 5);

        // Corridor: room 2 → room 3 (vertical at x=25, then horizontal)
        carve_v_corridor(&mut map, 9, 11, 25);

        // Corridor: room 1 → room 3 (vertical at x=8)
        carve_v_corridor(&mut map, 9, 11, 8);
        carve_h_corridor(&mut map, 8, 10, 12);

        map
    }
}

fn carve_room(map: &mut Map, x: usize, y: usize, w: usize, h: usize) {
    for dy in 0..h {
        for dx in 0..w {
            map.set(x + dx, y + dy, Tile::Floor);
        }
    }
}

fn carve_h_corridor(map: &mut Map, x1: usize, x2: usize, y: usize) {
    let (start, end) = if x1 < x2 { (x1, x2) } else { (x2, x1) };
    for x in start..=end {
        map.set(x, y, Tile::Floor);
    }
}

fn carve_v_corridor(map: &mut Map, y1: usize, y2: usize, x: usize) {
    let (start, end) = if y1 < y2 { (y1, y2) } else { (y2, y1) };
    for y in start..=end {
        map.set(x, y, Tile::Floor);
    }
}

// ── Pathfinding ─────────────────────────────────────────────────

impl Map {
    /// Use A* to find the next step from `start` toward `goal`.
    ///
    /// `blocked` contains positions occupied by other monsters (not the goal).
    /// Returns `Some((nx, ny))` with the first step, or `None` if no path exists.
    pub fn astar_next_step(
        &self,
        start: (i64, i64),
        goal: (i64, i64),
        blocked: &[(i64, i64)],
    ) -> Option<(i64, i64)> {
        let successors = |&(x, y): &(i64, i64)| {
            // 8-directional neighbors
            let dirs: [(i64, i64); 8] = [
                (-1, -1),
                (0, -1),
                (1, -1),
                (-1, 0),
                (1, 0),
                (-1, 1),
                (0, 1),
                (1, 1),
            ];
            dirs.into_iter().filter_map(move |(dx, dy)| {
                let nx = x + dx;
                let ny = y + dy;
                if !self.walkable(nx, ny) {
                    return None;
                }
                // Allow moving onto the goal, but not through other monsters
                if (nx, ny) != goal && blocked.contains(&(nx, ny)) {
                    return None;
                }
                // Diagonal moves cost ~1.4, cardinal cost 1 (use integers: 14 vs 10)
                let cost = if dx != 0 && dy != 0 { 14u32 } else { 10 };
                Some(((nx, ny), cost))
            })
        };

        let heuristic = |&(x, y): &(i64, i64)| {
            // Chebyshev distance scaled to match cardinal cost of 10
            let dx = (goal.0 - x).unsigned_abs() as u32;
            let dy = (goal.1 - y).unsigned_abs() as u32;
            dx.max(dy) * 10
        };

        let success = |pos: &(i64, i64)| *pos == goal;

        let (path, _cost) = astar(&start, successors, heuristic, success)?;

        // path[0] is start, path[1] is first step
        if path.len() >= 2 { Some(path[1]) } else { None }
    }
}

// ── Entity display info ─────────────────────────────────────────

pub struct EntityDisplay {
    pub entity: EntityRef,
    pub x: i64,
    pub y: i64,
    pub glyph: char,
    pub is_player: bool,
}
