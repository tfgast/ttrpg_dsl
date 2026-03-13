use super::*;
use ttrpg_parser::manifest;

impl Runner {
    /// Reset all loaded state (program, types, game state, entities, etc.)
    fn clear_state(&mut self, paths: Vec<PathBuf>) {
        *self.program = Program::default();
        *self.type_env = TypeEnv::new();
        self.module_map = ModuleMap::default();
        self.game_state = RefCell::new(GameState::new());
        self.last_paths = paths;
        self.handles.clear();
        self.variables.retain(|_, v| !matches!(v, Value::Entity(_)));
        self.source_map = None;
        self.unit_suffixes = crate::format::UnitSuffixes::new();
    }

    pub(super) fn cmd_load(&mut self, paths_str: &str) -> Result<(), CliError> {
        // Split on whitespace and expand globs
        let tokens: Vec<&str> = paths_str.split_whitespace().collect();

        // Try manifest-based loading for single-token package specifiers.
        // A package specifier is a single token that either contains ':'
        // (explicit target) or looks like a bare name (no extension, no
        // path separators, no glob characters).
        if tokens.len() == 1 {
            let token = tokens[0];
            if let Some(paths) = self.try_resolve_package(token)? {
                return self.load_paths(paths);
            }
        }

        let mut resolved_paths: Vec<PathBuf> = Vec::new();
        for token in &tokens {
            if token.contains('*') || token.contains('?') || token.contains('[') {
                // Glob expansion
                let entries = match glob::glob(token) {
                    Ok(e) => e,
                    Err(e) => {
                        self.clear_state(Vec::new());
                        return Err(CliError::Message(format!(
                            "invalid glob pattern '{token}': {e}"
                        )));
                    }
                };
                let mut found = false;
                for entry in entries {
                    match entry {
                        Ok(path) => {
                            resolved_paths.push(path);
                            found = true;
                        }
                        Err(e) => {
                            self.clear_state(Vec::new());
                            return Err(CliError::Message(format!(
                                "glob error for '{token}': {e}"
                            )));
                        }
                    }
                }
                if !found {
                    self.clear_state(Vec::new());
                    return Err(CliError::Message(format!(
                        "no files matched pattern '{token}'"
                    )));
                }
            } else {
                resolved_paths.push(PathBuf::from(token));
            }
        }

        if resolved_paths.is_empty() {
            self.clear_state(Vec::new());
            return Err(CliError::Message("no files specified".into()));
        }

        self.load_paths(resolved_paths)
    }

    /// Try to resolve a token as a package specifier (`pkg` or `pkg:target`).
    ///
    /// Returns `Some(paths)` if a matching manifest was found, `None` if the
    /// token doesn't look like a package specifier, or `Err` on manifest errors.
    fn try_resolve_package(&self, token: &str) -> Result<Option<Vec<PathBuf>>, CliError> {
        let (pkg_name, target) = manifest::parse_load_specifier(token);

        // If there's an explicit `:target`, it's definitely a package specifier.
        // Otherwise only try if it looks like a bare name (no extension, no
        // path separators, no glob characters).
        let is_explicit = target.is_some();
        if !is_explicit
            && (pkg_name.contains('/')
                || pkg_name.contains('\\')
                || pkg_name.contains('.')
                || pkg_name.contains('*')
                || pkg_name.contains('?')
                || pkg_name.contains('['))
        {
            return Ok(None);
        }

        // Search for the package manifest in known locations:
        // 1. Current directory (the package dir itself may be cwd)
        // 2. Sibling directories of cwd (e.g., cwd is repo root, package is ./ose/)
        let cwd = std::env::current_dir().unwrap_or_default();
        let search_dirs: Vec<&std::path::Path> = vec![&cwd];

        // Try finding as a subdirectory of search dirs
        if let Some((pkg_manifest, pkg_root)) = manifest::find_package(pkg_name, &search_dirs) {
            let resolved = pkg_manifest
                .resolve_target(target)
                .map_err(|e| CliError::Message(e.to_string()))?;

            let paths: Vec<PathBuf> = resolved
                .entry_paths
                .iter()
                .map(|p| pkg_root.join(p))
                .collect();

            return Ok(Some(paths));
        }

        // Try finding manifest in cwd itself (cwd IS the package)
        let manifest_path = cwd.join(manifest::MANIFEST_FILENAME);
        if manifest_path.is_file()
            && let Ok(pkg_manifest) = manifest::load_manifest(&manifest_path)
            && pkg_manifest.package.name == pkg_name
        {
            let resolved = pkg_manifest
                .resolve_target(target)
                .map_err(|e| CliError::Message(e.to_string()))?;

            let paths: Vec<PathBuf> = resolved.entry_paths.iter().map(|p| cwd.join(p)).collect();

            return Ok(Some(paths));
        }

        // If `:target` was explicit, it must be a package — report error.
        if is_explicit {
            return Err(CliError::Message(format!(
                "package '{pkg_name}' not found (no ttrpg.toml found)"
            )));
        }

        // Not a package specifier — fall through to file path resolution
        Ok(None)
    }

    /// Load from already-resolved paths. Used by both `cmd_load` and `cmd_reload`
    /// so that reload doesn't need to round-trip paths through string tokenization.
    ///
    /// The source resolver follows `import` directives transitively, so callers
    /// only need to provide entrypoint paths.
    pub(super) fn load_paths(&mut self, resolved_paths: Vec<PathBuf>) -> Result<(), CliError> {
        // Resolve imports transitively: reads all files, follows `import` edges,
        // deduplicates, and returns a stable load order.
        let resolved =
            ttrpg_parser::source_resolve::resolve_sources(&resolved_paths).map_err(|e| {
                self.clear_state(resolved_paths.clone());
                self.diagnostics = Vec::new();
                CliError::Message(e.to_string())
            })?;

        let sources = resolved.sources;

        // Always use parse_multi + check_with_modules so module resolution
        // works even for single-file programs.
        let result = ttrpg_parser::parse_multi(&sources);

        let mut all_diags = resolved.diagnostics;
        all_diags.extend(result.diagnostics);

        // Run checker (module-aware)
        let check_result = ttrpg_checker::check_with_modules(&result.program, &result.module_map);
        all_diags.extend(check_result.diagnostics);

        let error_count = all_diags
            .iter()
            .filter(|d| d.severity == Severity::Error)
            .count();

        let loaded_label = if sources.len() == 1 {
            format!("loaded {}", sources[0].0)
        } else {
            let file_list: Vec<_> = sources.iter().map(|(name, _)| name.as_str()).collect();
            format!("loaded {} files: {}", file_list.len(), file_list.join(", "))
        };

        let error_label = if sources.len() == 1 {
            format!("'{}'", sources[0].0)
        } else {
            sources
                .iter()
                .map(|(name, _)| name.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        };

        if error_count == 0 && !result.has_errors {
            *self.program = result.program;
            *self.type_env = check_result.env;
            self.unit_suffixes = crate::format::build_unit_suffixes(&self.type_env);
            self.module_map = result.module_map;
            let mut gs = GameState::new();
            // Auto-enable options declared with `default: on`
            for (name, decl) in &self.program.options {
                if decl.default_on == Some(true) {
                    gs.enable_option(name.as_str());
                }
            }
            self.game_state = RefCell::new(gs);
            self.diagnostics = all_diags;
            self.source_map = Some(MultiSourceMap::new(sources));
            self.last_paths = resolved_paths;
            self.handles.clear();
            self.variables.retain(|_, v| !matches!(v, Value::Entity(_)));
            self.output.push(loaded_label);
            Ok(())
        } else {
            self.clear_state(resolved_paths);
            self.diagnostics = all_diags;
            self.source_map = Some(MultiSourceMap::new(sources));
            self.output.push("use 'errors' to see diagnostics".into());
            Err(CliError::Message(format!(
                "failed to load {}: {} error{}",
                error_label,
                error_count,
                if error_count == 1 { "" } else { "s" }
            )))
        }
    }

    /// Load DSL source from an inline string (from `source <<DELIM` blocks).
    /// When `snippet` is true, the source is auto-wrapped in `system "<source>" { ... }`.
    pub(super) fn cmd_source(&mut self, source: &str, snippet: bool) -> Result<(), CliError> {
        let actual_source = if snippet {
            format!("system \"<source>\" {{\n{source}\n}}\n")
        } else {
            source.to_string()
        };

        let sources = vec![("<source>".to_string(), actual_source)];
        let result = self.load_sources(sources);
        if snippet {
            for diag in &mut self.diagnostics {
                if diag.message == "system blocks cannot be nested" && diag.help.is_none() {
                    diag.help = Some(
                        "snippet mode (-s) already wraps your source in a system block; \
                         write declarations directly without a system wrapper"
                            .into(),
                    );
                }
            }
        }
        result
    }

    /// Shared implementation for loading from already-parsed source pairs.
    /// Used by both `load_paths` (after reading files) and `cmd_source` (inline text).
    fn load_sources(&mut self, sources: Vec<(String, String)>) -> Result<(), CliError> {
        let result = ttrpg_parser::parse_multi(&sources);
        let mut all_diags = result.diagnostics;
        let check_result = ttrpg_checker::check_with_modules(&result.program, &result.module_map);
        all_diags.extend(check_result.diagnostics);

        let error_count = all_diags
            .iter()
            .filter(|d| d.severity == Severity::Error)
            .count();

        if error_count == 0 && !result.has_errors {
            *self.program = result.program;
            *self.type_env = check_result.env;
            self.unit_suffixes = crate::format::build_unit_suffixes(&self.type_env);
            self.module_map = result.module_map;
            let mut gs = GameState::new();
            for (name, decl) in &self.program.options {
                if decl.default_on == Some(true) {
                    gs.enable_option(name.as_str());
                }
            }
            self.game_state = RefCell::new(gs);
            self.diagnostics = all_diags;
            self.last_paths = Vec::new();
            self.handles.clear();
            self.variables.retain(|_, v| !matches!(v, Value::Entity(_)));
            self.output.push("loaded <source>".into());
            self.source_map = Some(MultiSourceMap::new(sources));
            Ok(())
        } else {
            self.clear_state(Vec::new());
            self.diagnostics = all_diags;
            self.output.push("use 'errors' to see diagnostics".into());
            self.source_map = Some(MultiSourceMap::new(sources));
            Err(CliError::Message(format!(
                "source block failed: {} error{}",
                error_count,
                if error_count == 1 { "" } else { "s" }
            )))
        }
    }

    pub(super) fn cmd_eval(&mut self, expr_str: &str) -> Result<(), CliError> {
        let val = self.eval(expr_str)?;
        self.output.push(format_value(&val, &self.unit_suffixes));
        Ok(())
    }

    pub(super) fn cmd_let(&mut self, tail: &str) -> Result<(), CliError> {
        let eq_pos = tail
            .find('=')
            .ok_or_else(|| CliError::Message("usage: let <name> = <expr>".into()))?;
        let name = tail[..eq_pos].trim();
        let expr_str = tail[eq_pos + 1..].trim();
        if name.is_empty() || expr_str.is_empty() {
            return Err(CliError::Message("usage: let <name> = <expr>".into()));
        }
        // Validate name is a simple identifier
        if !name.chars().all(|c| c.is_alphanumeric() || c == '_')
            || name.starts_with(char::is_numeric)
        {
            return Err(CliError::Message(format!("invalid variable name: {name}")));
        }
        let val = self.eval(expr_str)?;
        self.output.push(format!(
            "{name} = {}",
            format_value(&val, &self.unit_suffixes)
        ));
        self.variables.insert(name.to_string(), val);
        Ok(())
    }

    pub(super) fn cmd_reload(&mut self) -> Result<(), CliError> {
        if self.last_paths.is_empty() {
            return Err(CliError::Message("no file loaded yet".into()));
        }
        let paths = self.last_paths.clone();
        self.load_paths(paths)
    }

    pub(super) fn cmd_errors(&mut self) -> Result<(), CliError> {
        if self.diagnostics.is_empty() {
            self.output.push("no diagnostics".into());
        } else {
            for diag in &self.diagnostics {
                if let Some(ref map) = self.source_map {
                    self.output.push(map.render(diag));
                } else {
                    let severity = match diag.severity {
                        Severity::Error => "error",
                        Severity::Warning => "warning",
                    };
                    self.output.push(format!("[{}] {}", severity, diag.message));
                }
            }
        }
        Ok(())
    }
}
