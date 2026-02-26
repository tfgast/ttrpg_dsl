use std::sync::{Arc, Mutex};

use nu_ansi_term::{Color, Style};
use reedline::{
    default_emacs_keybindings, default_vi_insert_keybindings, default_vi_normal_keybindings,
    ColumnarMenu, DefaultHinter, EditMode, Emacs, FileBackedHistory, KeyCode, KeyModifiers,
    Keybindings, MenuBuilder, Prompt, PromptEditMode, PromptHistorySearch,
    PromptHistorySearchStatus, Reedline, ReedlineEvent, ReedlineMenu, Signal, Vi,
};

use crate::completer::{CompletionContext, TtrpgCompleter};
use crate::highlighter::TtrpgHighlighter;
use crate::runner::Runner;
use crate::validator::TtrpgValidator;

/// Custom prompt for the TTRPG REPL.
struct TtrpgPrompt;

impl Prompt for TtrpgPrompt {
    fn render_prompt_left(&self) -> std::borrow::Cow<'_, str> {
        std::borrow::Cow::Owned(Color::Green.bold().paint("ttrpg").to_string())
    }

    fn render_prompt_right(&self) -> std::borrow::Cow<'_, str> {
        std::borrow::Cow::Borrowed("")
    }

    fn render_prompt_indicator(&self, edit_mode: PromptEditMode) -> std::borrow::Cow<'_, str> {
        match edit_mode {
            PromptEditMode::Default | PromptEditMode::Emacs => std::borrow::Cow::Borrowed("> "),
            PromptEditMode::Vi(vi_mode) => match vi_mode {
                reedline::PromptViMode::Normal => std::borrow::Cow::Borrowed(": "),
                reedline::PromptViMode::Insert => std::borrow::Cow::Borrowed("> "),
            },
            PromptEditMode::Custom(_) => std::borrow::Cow::Borrowed("> "),
        }
    }

    fn render_prompt_multiline_indicator(&self) -> std::borrow::Cow<'_, str> {
        std::borrow::Cow::Borrowed("... > ")
    }

    fn render_prompt_history_search_indicator(
        &self,
        history_search: PromptHistorySearch,
    ) -> std::borrow::Cow<'_, str> {
        let prefix = match history_search.status {
            PromptHistorySearchStatus::Passing => "",
            PromptHistorySearchStatus::Failing => "(failed) ",
        };
        std::borrow::Cow::Owned(format!("{}search: ", prefix))
    }
}

/// Refresh the completion context from the current runner state.
fn refresh_completions(runner: &Runner, ctx: &Arc<Mutex<CompletionContext>>) {
    let Ok(mut c) = ctx.lock() else {
        return;
    };
    c.handles = runner.handle_names();
    c.entity_types = runner.entity_type_names();
    c.action_names = runner.action_names();
    c.derive_names = runner.derive_names();
    c.mechanic_names = runner.mechanic_names();

    // Populate handle→type, type→groups, type→fields, and (type,group)→fields maps
    c.handle_types.clear();
    c.type_groups.clear();
    c.group_fields.clear();
    c.type_fields.clear();

    let handles: Vec<String> = c.handles.clone();
    for handle in &handles {
        if let Some(entity_type) = runner.handle_type(handle) {
            c.handle_types.insert(handle.clone(), entity_type);
        }
    }

    let entity_types: Vec<String> = c.entity_types.clone();
    for entity_type in &entity_types {
        c.type_fields
            .insert(entity_type.clone(), runner.field_names(entity_type));
        let groups = runner.group_names(entity_type);
        for group_name in &groups {
            let key = (entity_type.clone(), group_name.clone());
            c.group_fields
                .insert(key, runner.group_field_names(entity_type, group_name));
        }
        c.type_groups.insert(entity_type.clone(), groups);
    }
}

/// Build the history file path, creating parent directories if needed.
fn history_path() -> Option<std::path::PathBuf> {
    let data_dir = data_dir()?.join("ttrpg");
    std::fs::create_dir_all(&data_dir).ok()?;
    Some(data_dir.join("history.txt"))
}

/// Get the XDG data directory or fall back to ~/.local/share.
fn data_dir() -> Option<std::path::PathBuf> {
    std::env::var_os("XDG_DATA_HOME")
        .map(std::path::PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|h| std::path::PathBuf::from(h).join(".local/share"))
        })
}

/// Run the interactive REPL with reedline.
pub fn run_repl(vi_mode: bool) {
    let mut runner = Runner::new();
    let completion_ctx = Arc::new(Mutex::new(CompletionContext::default()));

    let completer = TtrpgCompleter::new(Arc::clone(&completion_ctx));
    let highlighter = TtrpgHighlighter;
    let validator = TtrpgValidator;
    let hinter = DefaultHinter::default().with_style(Style::new().fg(Color::DarkGray));

    // Build completion menu
    let completion_menu = ColumnarMenu::default().with_name("completion_menu");

    // Build keybindings with Tab → completion menu
    let edit_mode: Box<dyn EditMode> = if vi_mode {
        let mut normal_kb = default_vi_normal_keybindings();
        let mut insert_kb = default_vi_insert_keybindings();
        bind_tab_completion(&mut insert_kb);
        bind_tab_completion(&mut normal_kb);
        Box::new(Vi::new(insert_kb, normal_kb))
    } else {
        let mut kb = default_emacs_keybindings();
        bind_tab_completion(&mut kb);
        Box::new(Emacs::new(kb))
    };

    // Build reedline editor
    let mut editor = Reedline::create()
        .with_completer(Box::new(completer))
        .with_highlighter(Box::new(highlighter))
        .with_validator(Box::new(validator))
        .with_hinter(Box::new(hinter))
        .with_menu(ReedlineMenu::EngineCompleter(Box::new(completion_menu)))
        .with_edit_mode(edit_mode);

    // Add file-backed history if possible
    if let Some(path) = history_path() {
        if let Ok(history) = FileBackedHistory::with_file(1000, path) {
            editor = editor.with_history(Box::new(history));
        }
    }

    let prompt = TtrpgPrompt;

    // Initialize completions before first prompt
    refresh_completions(&runner, &completion_ctx);

    loop {
        match editor.read_line(&prompt) {
            Ok(Signal::Success(buffer)) => {
                let result = runner.exec(&buffer);

                for out in runner.take_output() {
                    println!("{}", out);
                }

                if let Err(e) = result {
                    eprintln!("error: {}", e);
                }

                // Refresh completion context after each command
                refresh_completions(&runner, &completion_ctx);
            }
            Ok(Signal::CtrlC) => {
                // Clear current line, continue
            }
            Ok(Signal::CtrlD) => {
                break;
            }
            Err(err) => {
                eprintln!("I/O error: {}", err);
                break;
            }
        }
    }
}

/// Bind Tab to open/cycle the completion menu.
fn bind_tab_completion(kb: &mut Keybindings) {
    kb.add_binding(
        KeyModifiers::NONE,
        KeyCode::Tab,
        ReedlineEvent::UntilFound(vec![
            ReedlineEvent::Menu("completion_menu".to_string()),
            ReedlineEvent::MenuNext,
        ]),
    );
    kb.add_binding(
        KeyModifiers::SHIFT,
        KeyCode::BackTab,
        ReedlineEvent::MenuPrevious,
    );
}
