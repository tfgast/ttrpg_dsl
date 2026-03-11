//! Package manifest (`ttrpg.toml`) parsing and target resolution.
//!
//! A manifest describes package identity, named entrypoints, and curated
//! bundles. The file graph itself lives in source files via `import`
//! directives — the manifest does not list every transitive file.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use serde::Deserialize;

/// Name of the manifest file searched for by [`find_manifest`].
pub const MANIFEST_FILENAME: &str = "ttrpg.toml";

// ── Raw TOML shape ──────────────────────────────────────────────────

/// Top-level manifest as deserialized from `ttrpg.toml`.
#[derive(Debug, Deserialize)]
pub struct PackageManifest {
    pub manifest_version: u32,
    pub package: PackageInfo,
    #[serde(default)]
    pub entries: BTreeMap<String, EntryDef>,
    #[serde(default)]
    pub bundles: BTreeMap<String, BundleDef>,
}

/// The `[package]` table.
#[derive(Debug, Deserialize)]
pub struct PackageInfo {
    pub name: String,
    #[serde(default)]
    pub version: Option<String>,
    #[serde(default)]
    pub default_target: Option<String>,
}

/// A single named entry — one root source file.
#[derive(Debug, Deserialize)]
pub struct EntryDef {
    pub path: String,
}

/// A named bundle — a curated list of entries to load together.
#[derive(Debug, Deserialize)]
pub struct BundleDef {
    pub entries: Vec<String>,
}

// ── Errors ──────────────────────────────────────────────────────────

#[derive(Debug)]
pub enum ManifestError {
    /// Could not read the manifest file.
    Io(PathBuf, std::io::Error),
    /// TOML parse/deserialize error.
    Parse(PathBuf, toml::de::Error),
    /// Unsupported manifest_version.
    UnsupportedVersion(u32),
    /// The requested target name is not an entry or bundle.
    UnknownTarget(String),
    /// A bundle references an entry name that doesn't exist.
    UnknownEntry { bundle: String, entry: String },
    /// No default_target specified and none requested.
    NoDefaultTarget,
}

impl std::fmt::Display for ManifestError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ManifestError::Io(path, e) => {
                write!(f, "cannot read '{}': {}", path.display(), e)
            }
            ManifestError::Parse(path, e) => {
                write!(f, "invalid manifest '{}': {}", path.display(), e)
            }
            ManifestError::UnsupportedVersion(v) => {
                write!(f, "unsupported manifest_version {v} (expected 1)")
            }
            ManifestError::UnknownTarget(name) => {
                write!(f, "unknown target '{name}' (not an entry or bundle)")
            }
            ManifestError::UnknownEntry { bundle, entry } => {
                write!(f, "bundle '{bundle}' references unknown entry '{entry}'")
            }
            ManifestError::NoDefaultTarget => {
                write!(f, "no default_target specified in manifest")
            }
        }
    }
}

// ── Loading ─────────────────────────────────────────────────────────

/// Search for `ttrpg.toml` starting from `start_dir` and walking up
/// to parent directories. Returns the path to the manifest and its
/// parent directory (the package root).
pub fn find_manifest(start_dir: &Path) -> Option<(PathBuf, PathBuf)> {
    let mut dir = start_dir.to_path_buf();
    loop {
        let candidate = dir.join(MANIFEST_FILENAME);
        if candidate.is_file() {
            return Some((candidate, dir));
        }
        if !dir.pop() {
            return None;
        }
    }
}

/// Read and parse a manifest from the given path.
pub fn load_manifest(path: &Path) -> Result<PackageManifest, ManifestError> {
    let content =
        std::fs::read_to_string(path).map_err(|e| ManifestError::Io(path.to_path_buf(), e))?;
    let manifest: PackageManifest =
        toml::from_str(&content).map_err(|e| ManifestError::Parse(path.to_path_buf(), e))?;
    if manifest.manifest_version != 1 {
        return Err(ManifestError::UnsupportedVersion(manifest.manifest_version));
    }
    Ok(manifest)
}

// ── Target resolution ───────────────────────────────────────────────

/// The result of resolving a target: a list of entry file paths
/// relative to the package root.
#[derive(Debug)]
pub struct ResolvedTarget {
    /// Entry file paths relative to the package root.
    pub entry_paths: Vec<PathBuf>,
    /// Name of the resolved target (entry or bundle name).
    pub target_name: String,
    /// Whether the target is a bundle (true) or single entry (false).
    pub is_bundle: bool,
}

impl PackageManifest {
    /// Resolve a target name to entry file paths.
    ///
    /// - If `target` is `None`, uses `default_target` from the manifest.
    /// - Looks up bundles first, then entries.
    /// - Returns paths relative to the package root.
    pub fn resolve_target(&self, target: Option<&str>) -> Result<ResolvedTarget, ManifestError> {
        let target_name = match target {
            Some(name) => name,
            None => self
                .package
                .default_target
                .as_deref()
                .ok_or(ManifestError::NoDefaultTarget)?,
        };

        // Check bundles first
        if let Some(bundle) = self.bundles.get(target_name) {
            let mut paths = Vec::with_capacity(bundle.entries.len());
            for entry_name in &bundle.entries {
                let entry =
                    self.entries
                        .get(entry_name)
                        .ok_or_else(|| ManifestError::UnknownEntry {
                            bundle: target_name.to_string(),
                            entry: entry_name.clone(),
                        })?;
                paths.push(PathBuf::from(&entry.path));
            }
            return Ok(ResolvedTarget {
                entry_paths: paths,
                target_name: target_name.to_string(),
                is_bundle: true,
            });
        }

        // Check entries
        if let Some(entry) = self.entries.get(target_name) {
            return Ok(ResolvedTarget {
                entry_paths: vec![PathBuf::from(&entry.path)],
                target_name: target_name.to_string(),
                is_bundle: false,
            });
        }

        Err(ManifestError::UnknownTarget(target_name.to_string()))
    }

    /// List all available target names (entries + bundles).
    pub fn available_targets(&self) -> Vec<&str> {
        let mut names: Vec<&str> = self.entries.keys().map(|s| s.as_str()).collect();
        names.extend(self.bundles.keys().map(|s| s.as_str()));
        names.sort_unstable();
        names
    }
}

/// Parse a package load specifier like `"ose"` or `"ose:combat"`.
///
/// Returns `(package_name, optional_target)`.
pub fn parse_load_specifier(spec: &str) -> (&str, Option<&str>) {
    match spec.split_once(':') {
        Some((pkg, target)) => (pkg, Some(target)),
        None => (spec, None),
    }
}

/// Attempt to find and load a package by name, searching from `search_dir`.
///
/// Looks for `<search_dir>/<package_name>/ttrpg.toml`.
/// Returns the manifest and the package root directory.
pub fn find_package(
    package_name: &str,
    search_dirs: &[&Path],
) -> Option<(PackageManifest, PathBuf)> {
    for dir in search_dirs {
        let pkg_dir = dir.join(package_name);
        let manifest_path = pkg_dir.join(MANIFEST_FILENAME);
        if manifest_path.is_file()
            && let Ok(manifest) = load_manifest(&manifest_path)
        {
            return Some((manifest, pkg_dir));
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    fn write_manifest(dir: &Path, content: &str) {
        fs::write(dir.join(MANIFEST_FILENAME), content).unwrap();
    }

    #[test]
    fn parse_minimal_manifest() {
        let toml = r#"
manifest_version = 1

[package]
name = "test"
"#;
        let manifest: PackageManifest = toml::from_str(toml).unwrap();
        assert_eq!(manifest.package.name, "test");
        assert_eq!(manifest.manifest_version, 1);
        assert!(manifest.entries.is_empty());
        assert!(manifest.bundles.is_empty());
    }

    #[test]
    fn parse_full_manifest() {
        let toml = r#"
manifest_version = 1

[package]
name = "ose"
default_target = "full"

[entries.core]
path = "ose_core.ttrpg"

[entries.combat]
path = "ose_combat.ttrpg"

[entries.class]
path = "ose_class.ttrpg"

[bundles.full]
entries = ["core", "class", "combat"]

[bundles.chargen]
entries = ["core", "class"]
"#;
        let manifest: PackageManifest = toml::from_str(toml).unwrap();
        assert_eq!(manifest.package.name, "ose");
        assert_eq!(manifest.package.default_target.as_deref(), Some("full"));
        assert_eq!(manifest.entries.len(), 3);
        assert_eq!(manifest.bundles.len(), 2);
        assert_eq!(manifest.bundles["full"].entries.len(), 3);
    }

    #[test]
    fn resolve_entry_target() {
        let toml = r#"
manifest_version = 1

[package]
name = "ose"

[entries.core]
path = "ose_core.ttrpg"
"#;
        let manifest: PackageManifest = toml::from_str(toml).unwrap();
        let resolved = manifest.resolve_target(Some("core")).unwrap();
        assert_eq!(resolved.entry_paths, vec![PathBuf::from("ose_core.ttrpg")]);
        assert!(!resolved.is_bundle);
    }

    #[test]
    fn resolve_bundle_target() {
        let toml = r#"
manifest_version = 1

[package]
name = "ose"

[entries.core]
path = "ose_core.ttrpg"

[entries.class]
path = "ose_class.ttrpg"

[bundles.full]
entries = ["core", "class"]
"#;
        let manifest: PackageManifest = toml::from_str(toml).unwrap();
        let resolved = manifest.resolve_target(Some("full")).unwrap();
        assert_eq!(resolved.entry_paths.len(), 2);
        assert!(resolved.is_bundle);
    }

    #[test]
    fn resolve_default_target() {
        let toml = r#"
manifest_version = 1

[package]
name = "ose"
default_target = "full"

[entries.core]
path = "ose_core.ttrpg"

[bundles.full]
entries = ["core"]
"#;
        let manifest: PackageManifest = toml::from_str(toml).unwrap();
        let resolved = manifest.resolve_target(None).unwrap();
        assert_eq!(resolved.target_name, "full");
    }

    #[test]
    fn resolve_no_default_target() {
        let toml = r#"
manifest_version = 1

[package]
name = "ose"

[entries.core]
path = "ose_core.ttrpg"
"#;
        let manifest: PackageManifest = toml::from_str(toml).unwrap();
        let result = manifest.resolve_target(None);
        assert!(matches!(result, Err(ManifestError::NoDefaultTarget)));
    }

    #[test]
    fn resolve_unknown_target() {
        let toml = r#"
manifest_version = 1

[package]
name = "ose"

[entries.core]
path = "ose_core.ttrpg"
"#;
        let manifest: PackageManifest = toml::from_str(toml).unwrap();
        let result = manifest.resolve_target(Some("nope"));
        assert!(matches!(result, Err(ManifestError::UnknownTarget(_))));
    }

    #[test]
    fn resolve_bundle_with_unknown_entry() {
        let toml = r#"
manifest_version = 1

[package]
name = "ose"

[entries.core]
path = "ose_core.ttrpg"

[bundles.full]
entries = ["core", "missing"]
"#;
        let manifest: PackageManifest = toml::from_str(toml).unwrap();
        let result = manifest.resolve_target(Some("full"));
        assert!(matches!(result, Err(ManifestError::UnknownEntry { .. })));
    }

    #[test]
    fn unsupported_version() {
        let dir = tempfile::tempdir().unwrap();
        write_manifest(
            dir.path(),
            r#"
manifest_version = 99

[package]
name = "test"
"#,
        );
        let result = load_manifest(&dir.path().join(MANIFEST_FILENAME));
        assert!(matches!(result, Err(ManifestError::UnsupportedVersion(99))));
    }

    #[test]
    fn find_manifest_in_current_dir() {
        let dir = tempfile::tempdir().unwrap();
        write_manifest(
            dir.path(),
            r#"
manifest_version = 1

[package]
name = "test"
"#,
        );
        let (path, root) = find_manifest(dir.path()).unwrap();
        assert_eq!(path, dir.path().join(MANIFEST_FILENAME));
        assert_eq!(root, dir.path());
    }

    #[test]
    fn find_manifest_in_parent() {
        let dir = tempfile::tempdir().unwrap();
        let sub = dir.path().join("sub");
        fs::create_dir(&sub).unwrap();
        write_manifest(
            dir.path(),
            r#"
manifest_version = 1

[package]
name = "test"
"#,
        );
        let (path, root) = find_manifest(&sub).unwrap();
        assert_eq!(path, dir.path().join(MANIFEST_FILENAME));
        assert_eq!(root, dir.path());
    }

    #[test]
    fn parse_load_specifier_with_target() {
        let (pkg, target) = parse_load_specifier("ose:combat");
        assert_eq!(pkg, "ose");
        assert_eq!(target, Some("combat"));
    }

    #[test]
    fn parse_load_specifier_without_target() {
        let (pkg, target) = parse_load_specifier("ose");
        assert_eq!(pkg, "ose");
        assert_eq!(target, None);
    }

    #[test]
    fn available_targets_sorted() {
        let toml = r#"
manifest_version = 1

[package]
name = "ose"

[entries.core]
path = "ose_core.ttrpg"

[entries.combat]
path = "ose_combat.ttrpg"

[bundles.full]
entries = ["core", "combat"]
"#;
        let manifest: PackageManifest = toml::from_str(toml).unwrap();
        let targets = manifest.available_targets();
        assert_eq!(targets, vec!["combat", "core", "full"]);
    }
}
