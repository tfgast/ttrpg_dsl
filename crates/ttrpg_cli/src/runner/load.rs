use super::*;

impl Runner {
    pub(super) fn cmd_load(&mut self, paths_str: &str) -> Result<(), CliError> {
        // Split on whitespace and expand globs
        let tokens: Vec<&str> = paths_str.split_whitespace().collect();
        let mut resolved_paths: Vec<PathBuf> = Vec::new();
        for token in &tokens {
            if token.contains('*') || token.contains('?') || token.contains('[') {
                // Glob expansion
                let entries = glob::glob(token).map_err(|e| {
                    CliError::Message(format!("invalid glob pattern '{}': {}", token, e))
                })?;
                let mut found = false;
                for entry in entries {
                    match entry {
                        Ok(path) => {
                            resolved_paths.push(path);
                            found = true;
                        }
                        Err(e) => {
                            return Err(CliError::Message(format!(
                                "glob error for '{}': {}",
                                token, e
                            )));
                        }
                    }
                }
                if !found {
                    return Err(CliError::Message(format!(
                        "no files matched pattern '{}'",
                        token
                    )));
                }
            } else {
                resolved_paths.push(PathBuf::from(token));
            }
        }

        if resolved_paths.is_empty() {
            return Err(CliError::Message("no files specified".into()));
        }

        self.load_paths(resolved_paths)
    }

    /// Load from already-resolved paths. Used by both `cmd_load` and `cmd_reload`
    /// so that reload doesn't need to round-trip paths through string tokenization.
    pub(super) fn load_paths(&mut self, resolved_paths: Vec<PathBuf>) -> Result<(), CliError> {
        // Helper to clear stale state
        fn clear_state(runner: &mut Runner, paths: Vec<PathBuf>) {
            *runner.program = Program::default();
            *runner.type_env = TypeEnv::new();
            runner.module_map = ModuleMap::default();
            runner.game_state = RefCell::new(GameState::new());
            runner.last_paths = paths;
            runner.handles.clear();
            runner.reverse_handles.clear();
            runner.source_map = None;
        }

        // Read all files
        let mut sources: Vec<(String, String)> = Vec::new();
        for path in &resolved_paths {
            let path_str = path.to_string_lossy();
            match std::fs::read_to_string(path) {
                Ok(s) => sources.push((path_str.into_owned(), s)),
                Err(e) => {
                    let msg = format!("cannot read '{}': {}", path_str, e);
                    clear_state(self, resolved_paths);
                    self.diagnostics = Vec::new();
                    return Err(CliError::Message(msg));
                }
            }
        }

        // Always use parse_multi + check_with_modules so module resolution
        // works even for single-file programs.
        let result = ttrpg_parser::parse_multi(&sources);

        let mut all_diags = result.diagnostics;

        // Run checker (module-aware)
        let check_result =
            ttrpg_checker::check_with_modules(&result.program, &result.module_map);
        all_diags.extend(check_result.diagnostics);

        let error_count = all_diags
            .iter()
            .filter(|d| d.severity == Severity::Error)
            .count();

        let loaded_label = if sources.len() == 1 {
            format!("loaded {}", sources[0].0)
        } else {
            let file_list: Vec<_> = resolved_paths
                .iter()
                .map(|p| p.to_string_lossy().into_owned())
                .collect();
            format!("loaded {} files: {}", file_list.len(), file_list.join(", "))
        };

        let error_label = if sources.len() == 1 {
            format!("'{}'", sources[0].0)
        } else {
            resolved_paths
                .iter()
                .map(|p| p.to_string_lossy().into_owned())
                .collect::<Vec<_>>()
                .join(", ")
        };

        if error_count == 0 && !result.has_errors {
            *self.program = result.program;
            *self.type_env = check_result.env;
            self.module_map = result.module_map;
            self.game_state = RefCell::new(GameState::new());
            self.diagnostics = all_diags;
            self.source_map = Some(MultiSourceMap::new(sources));
            self.last_paths = resolved_paths;
            self.handles.clear();
            self.reverse_handles.clear();
            self.output.push(loaded_label);
            Ok(())
        } else {
            clear_state(self, resolved_paths);
            self.diagnostics = all_diags;
            self.source_map = Some(MultiSourceMap::new(sources));
            self.output
                .push("use 'errors' to see diagnostics".into());
            Err(CliError::Message(format!(
                "failed to load {}: {} error{}",
                error_label,
                error_count,
                if error_count == 1 { "" } else { "s" }
            )))
        }
    }

    pub(super) fn cmd_eval(&mut self, expr_str: &str) -> Result<(), CliError> {
        let val = self.eval(expr_str)?;
        self.output.push(format_value(&val));
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
                    self.output
                        .push(format!("[{}] {}", severity, diag.message));
                }
            }
        }
        Ok(())
    }
}
