//! Bundled OSE (Old-School Essentials) `.ttrpg` rule files.
//!
//! This crate embeds all 13 OSE rule-system files at compile time and exposes
//! them through a simple API for listing, reading, and extracting to disk.

use std::path::Path;

/// A bundled rule file: name and contents.
struct BundledFile {
    name: &'static str,
    contents: &'static str,
}

const FILES: &[BundledFile] = &[
    BundledFile {
        name: "ose_ability.ttrpg",
        contents: include_str!("../../../ose/ose_ability.ttrpg"),
    },
    BundledFile {
        name: "ose_chargen.ttrpg",
        contents: include_str!("../../../ose/ose_chargen.ttrpg"),
    },
    BundledFile {
        name: "ose_class.ttrpg",
        contents: include_str!("../../../ose/ose_class.ttrpg"),
    },
    BundledFile {
        name: "ose_combat.ttrpg",
        contents: include_str!("../../../ose/ose_combat.ttrpg"),
    },
    BundledFile {
        name: "ose_core.ttrpg",
        contents: include_str!("../../../ose/ose_core.ttrpg"),
    },
    BundledFile {
        name: "ose_equipment.ttrpg",
        contents: include_str!("../../../ose/ose_equipment.ttrpg"),
    },
    BundledFile {
        name: "ose_exploration.ttrpg",
        contents: include_str!("../../../ose/ose_exploration.ttrpg"),
    },
    BundledFile {
        name: "ose_magic.ttrpg",
        contents: include_str!("../../../ose/ose_magic.ttrpg"),
    },
    BundledFile {
        name: "ose_saves.ttrpg",
        contents: include_str!("../../../ose/ose_saves.ttrpg"),
    },
    BundledFile {
        name: "ose_spells.ttrpg",
        contents: include_str!("../../../ose/ose_spells.ttrpg"),
    },
    BundledFile {
        name: "ose_thief.ttrpg",
        contents: include_str!("../../../ose/ose_thief.ttrpg"),
    },
    BundledFile {
        name: "ose_time_economy.ttrpg",
        contents: include_str!("../../../ose/ose_time_economy.ttrpg"),
    },
    BundledFile {
        name: "ose_wilderness.ttrpg",
        contents: include_str!("../../../ose/ose_wilderness.ttrpg"),
    },
];

/// Return the names of all bundled rule files.
pub fn list_files() -> Vec<&'static str> {
    FILES.iter().map(|f| f.name).collect()
}

/// Read a bundled rule file by name. Returns `None` if not found.
pub fn read_file(name: &str) -> Option<&'static str> {
    FILES.iter().find(|f| f.name == name).map(|f| f.contents)
}

/// Write all bundled rule files to `target_dir`.
///
/// Creates `target_dir` if it doesn't exist. Returns the list of paths written.
pub fn write_defaults(target_dir: &Path) -> std::io::Result<Vec<std::path::PathBuf>> {
    std::fs::create_dir_all(target_dir)?;
    let mut written = Vec::new();
    for file in FILES {
        let path = target_dir.join(file.name);
        std::fs::write(&path, file.contents)?;
        written.push(path);
    }
    Ok(written)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn list_files_returns_all_thirteen() {
        let files = list_files();
        assert_eq!(files.len(), 13);
        assert!(files.contains(&"ose_ability.ttrpg"));
        assert!(files.contains(&"ose_chargen.ttrpg"));
        assert!(files.contains(&"ose_class.ttrpg"));
        assert!(files.contains(&"ose_combat.ttrpg"));
        assert!(files.contains(&"ose_core.ttrpg"));
        assert!(files.contains(&"ose_equipment.ttrpg"));
        assert!(files.contains(&"ose_exploration.ttrpg"));
        assert!(files.contains(&"ose_magic.ttrpg"));
        assert!(files.contains(&"ose_saves.ttrpg"));
        assert!(files.contains(&"ose_spells.ttrpg"));
        assert!(files.contains(&"ose_thief.ttrpg"));
        assert!(files.contains(&"ose_time_economy.ttrpg"));
        assert!(files.contains(&"ose_wilderness.ttrpg"));
    }

    #[test]
    fn read_file_returns_content() {
        let content = read_file("ose_core.ttrpg").unwrap();
        assert!(content.contains("system"));
        assert!(!content.is_empty());
    }

    #[test]
    fn read_file_missing_returns_none() {
        assert!(read_file("nonexistent.ttrpg").is_none());
    }

    #[test]
    fn write_defaults_creates_files() {
        let dir = std::env::temp_dir().join("ttrpg_ose_data_test");
        let _ = std::fs::remove_dir_all(&dir);

        let paths = write_defaults(&dir).unwrap();
        assert_eq!(paths.len(), 13);

        for path in &paths {
            assert!(path.exists(), "{} should exist", path.display());
            let on_disk = std::fs::read_to_string(path).unwrap();
            let name = path.file_name().unwrap().to_str().unwrap();
            let bundled = read_file(name).unwrap();
            assert_eq!(on_disk, bundled, "on-disk content should match bundled for {}", name);
        }

        let _ = std::fs::remove_dir_all(&dir);
    }
}
