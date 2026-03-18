use std::path::PathBuf;

use serde::Deserialize;

/// Top-level host configuration loaded from a RON file.
#[derive(Debug, Deserialize)]
pub struct HostConfig {
    pub system: SystemConfig,
    pub player: PlayerConfig,
    pub creatures: Vec<CreatureConfig>,
    pub ui: UiConfig,
}

/// Which `.ttrpg` system to load.
#[derive(Debug, Deserialize)]
pub struct SystemConfig {
    /// Path to a `ttrpg.toml` manifest file (relative to config file location).
    pub manifest: PathBuf,
    /// Which bundle to load from the manifest. If `None`, uses the manifest's
    /// `default_target`.
    pub bundle: Option<String>,
}

/// Player entity configuration.
#[derive(Debug, Deserialize)]
pub struct PlayerConfig {
    /// Name of the DSL spawn function (e.g. `"spawn_hero"`).
    pub spawn_fn: String,
    pub glyph: char,
    pub color: Color,
}

/// A creature type the host knows how to spawn and display.
#[derive(Debug, Deserialize)]
pub struct CreatureConfig {
    /// Unique identifier for this creature type.
    pub id: String,
    /// Name of the DSL spawn function (e.g. `"spawn_goblin"`).
    pub spawn_fn: String,
    pub glyph: char,
    pub color: Color,
    pub ai: AiBehavior,
}

/// AI behavior hint for a creature type.
#[derive(Debug, Clone, Copy, Deserialize)]
pub enum AiBehavior {
    /// Chase and attack within `chase_range` tiles.
    Aggressive { chase_range: u32 },
    /// Never acts.
    Passive,
}

/// UI layout configuration.
#[derive(Debug, Deserialize)]
pub struct UiConfig {
    /// Fields to show in the player stats panel.
    pub stats_panel: Vec<StatField>,
}

/// A single field to display in the stats panel.
#[derive(Debug, Deserialize)]
pub struct StatField {
    /// DSL field name on the entity (e.g. `"HP"`).
    pub field: String,
    /// Label shown in the UI (e.g. `"HP"`).
    pub label: String,
    /// How to render this field's value.
    pub display: DisplayHint,
}

/// How a stat field should be rendered.
#[derive(Debug, Deserialize)]
pub enum DisplayHint {
    /// A bar (e.g. HP). `max_field` names the entity field holding the maximum.
    Bar { max_field: String },
    /// Plain integer.
    Number,
    /// Signed modifier (e.g. `+2`, `-1`).
    Modifier,
    /// Dice expression shown as text (e.g. `1d8+2`).
    DiceExpr,
}

/// Named colors matching ratatui's basic 16-color palette.
#[derive(Debug, Clone, Copy, Deserialize)]
pub enum Color {
    Black,
    Red,
    Green,
    Yellow,
    Blue,
    Magenta,
    Cyan,
    Gray,
    DarkGray,
    LightRed,
    LightGreen,
    LightYellow,
    LightBlue,
    LightMagenta,
    LightCyan,
    White,
}

impl From<Color> for ratatui::style::Color {
    fn from(c: Color) -> Self {
        match c {
            Color::Black => Self::Black,
            Color::Red => Self::Red,
            Color::Green => Self::Green,
            Color::Yellow => Self::Yellow,
            Color::Blue => Self::Blue,
            Color::Magenta => Self::Magenta,
            Color::Cyan => Self::Cyan,
            Color::Gray => Self::Gray,
            Color::DarkGray => Self::DarkGray,
            Color::LightRed => Self::LightRed,
            Color::LightGreen => Self::LightGreen,
            Color::LightYellow => Self::LightYellow,
            Color::LightBlue => Self::LightBlue,
            Color::LightMagenta => Self::LightMagenta,
            Color::LightCyan => Self::LightCyan,
            Color::White => Self::White,
        }
    }
}

impl HostConfig {
    /// Load a `HostConfig` from a RON file at the given path.
    pub fn load(path: &std::path::Path) -> Result<Self, ConfigError> {
        let contents =
            std::fs::read_to_string(path).map_err(|e| ConfigError::Io(path.to_path_buf(), e))?;
        ron::from_str(&contents).map_err(ConfigError::Parse)
    }
}

#[derive(Debug)]
pub enum ConfigError {
    Io(PathBuf, std::io::Error),
    Parse(ron::error::SpannedError),
}

impl std::fmt::Display for ConfigError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Io(path, e) => write!(f, "failed to read config {}: {e}", path.display()),
            Self::Parse(e) => write!(f, "failed to parse config: {e}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_roguelike_ron() {
        let config = HostConfig::load(std::path::Path::new("roguelike.ron"))
            .expect("failed to parse roguelike.ron");

        assert_eq!(config.player.spawn_fn, "spawn_hero");
        assert_eq!(config.player.glyph, '@');
        assert_eq!(config.creatures.len(), 2);
        assert_eq!(config.creatures[0].id, "goblin");
        assert_eq!(config.creatures[1].id, "rat");
        assert_eq!(config.ui.stats_panel.len(), 4);

        // Verify AI deserialization
        assert!(matches!(
            config.creatures[0].ai,
            AiBehavior::Aggressive { chase_range: 6 }
        ));

        // Verify display hint deserialization
        assert!(matches!(
            &config.ui.stats_panel[0].display,
            DisplayHint::Bar { max_field } if max_field == "max_HP"
        ));
    }
}
