use std::collections::HashSet;

use ttrpg_ast::Span;
use ttrpg_ast::ast::{
    ActionDecl, Block, DeclKind, HookDecl, Program, ReactionDecl, StmtKind, TopLevel,
};
use ttrpg_ast::span::FileId;

// ── Core data types ────────────────────────────────────────────

/// Accumulated coverage data from interpreter execution.
#[derive(Debug, Default)]
pub struct CoverageData {
    /// Set of (FileId index, byte offset) for each executed span.
    pub hit_spans: HashSet<(u32, u32)>,
    /// Set of branch points taken during execution.
    pub hit_branches: HashSet<BranchPoint>,
    /// Set of function/action/derive/mechanic/etc. names that were entered.
    pub hit_functions: HashSet<String>,
}

impl CoverageData {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn reset(&mut self) {
        self.hit_spans.clear();
        self.hit_branches.clear();
        self.hit_functions.clear();
    }

    /// Merge another `CoverageData` into this one (union of all sets).
    pub fn merge(&mut self, other: &CoverageData) {
        self.hit_spans.extend(&other.hit_spans);
        self.hit_branches.extend(other.hit_branches.iter().cloned());
        self.hit_functions
            .extend(other.hit_functions.iter().cloned());
    }
}

/// A specific branch point that was taken during execution.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BranchPoint {
    /// The span of the parent construct (if/match).
    pub parent_span: Span,
    /// What kind of branch this is.
    pub kind: BranchKind,
    /// The span of the arm/branch that was taken.
    pub arm_span: Span,
}

/// The kind of branch within a control flow construct.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BranchKind {
    IfThen,
    IfElse,
    MatchArm(usize),
    GuardArm(usize),
}

// ── Source info for report generation ──────────────────────────

/// Source information for a single file, used by the report generator.
pub struct CoverageSource {
    pub filename: String,
    pub source: String,
    pub file_id: u32,
    pub line_starts: Vec<usize>,
}

// ── Report generation ─────────────────────────────────────────

/// Render a plain-text coverage report for LLM consumption.
pub fn render_coverage_report(
    data: &CoverageData,
    sources: &[CoverageSource],
    program: &Program,
) -> String {
    let mut out = String::new();

    let mut total_coverable = 0usize;
    let mut total_hit = 0usize;
    let mut total_branches = 0usize;
    let mut total_branches_hit = 0usize;

    for src in sources {
        let coverable = compute_coverable_lines(program, src);
        let hit = compute_hit_lines(data, src);

        let hit_set: HashSet<usize> = hit.iter().copied().collect();
        let coverable_set: HashSet<usize> = coverable.iter().copied().collect();

        // Branch coverage for this file
        let file_branches = count_branches_in_file(program, src);
        let file_branches_hit = count_hit_branches_in_file(data, src);

        total_coverable += coverable_set.len();
        total_hit += coverable_set.intersection(&hit_set).count();
        total_branches += file_branches;
        total_branches_hit += file_branches_hit;

        out.push_str(&format!("=== Coverage: {} ===\n", src.filename));

        let lines: Vec<&str> = src.source.lines().collect();
        for (i, line_text) in lines.iter().enumerate() {
            let lineno = i + 1;
            let marker = if coverable_set.contains(&lineno) {
                if hit_set.contains(&lineno) {
                    "  HIT"
                } else {
                    " MISS"
                }
            } else {
                "     "
            };
            out.push_str(&format!("{marker} | {lineno:>4}: {line_text}\n"));
        }

        let file_hit = coverable_set.intersection(&hit_set).count();
        let file_total = coverable_set.len();
        let pct = if file_total > 0 {
            file_hit as f64 / file_total as f64 * 100.0
        } else {
            100.0
        };
        let branch_pct = if file_branches > 0 {
            file_branches_hit as f64 / file_branches as f64 * 100.0
        } else {
            100.0
        };
        out.push_str(&format!(
            "Summary: {file_hit}/{file_total} lines covered ({pct:.1}%), {file_branches_hit}/{file_branches} branches covered ({branch_pct:.1}%)\n",
        ));

        // Uncovered details
        let uncovered = find_uncovered_details(program, data, src, &coverable_set, &hit_set);
        if !uncovered.is_empty() {
            out.push_str("Uncovered:\n");
            for detail in &uncovered {
                out.push_str(&format!("  {detail}\n"));
            }
        }
        out.push('\n');
    }

    // Overall summary
    if sources.len() > 1 {
        let pct = if total_coverable > 0 {
            total_hit as f64 / total_coverable as f64 * 100.0
        } else {
            100.0
        };
        let branch_pct = if total_branches > 0 {
            total_branches_hit as f64 / total_branches as f64 * 100.0
        } else {
            100.0
        };
        out.push_str(&format!(
            "Overall: {total_hit}/{total_coverable} lines ({pct:.1}%), {total_branches_hit}/{total_branches} branches ({branch_pct:.1}%)\n",
        ));
    }

    out
}

// ── Coverable line computation (AST walk) ─────────────────────

/// Compute all line numbers in a file that contain executable code.
fn compute_coverable_lines(program: &Program, src: &CoverageSource) -> Vec<usize> {
    let file_id = FileId(src.file_id);
    let mut lines = HashSet::new();

    // Walk all declarations in the program and collect executable spans
    // that belong to this file.
    for item in &program.items {
        if let TopLevel::System(system) = &item.node {
            for decl in &system.decls {
                match &decl.node {
                    DeclKind::Derive(f) | DeclKind::Mechanic(f) => {
                        collect_block_lines(&f.body, file_id, &src.line_starts, &mut lines);
                    }
                    DeclKind::Function(f) => {
                        collect_block_lines(&f.body, file_id, &src.line_starts, &mut lines);
                    }
                    DeclKind::Action(a) => {
                        collect_action_lines(a, file_id, &src.line_starts, &mut lines);
                    }
                    DeclKind::Reaction(r) => {
                        collect_reaction_lines(r, file_id, &src.line_starts, &mut lines);
                    }
                    DeclKind::Hook(h) => {
                        collect_hook_lines(h, file_id, &src.line_starts, &mut lines);
                    }
                    _ => {}
                }
            }
        }
    }

    let mut sorted: Vec<usize> = lines.into_iter().collect();
    sorted.sort_unstable();
    sorted
}

fn collect_block_lines(
    block: &Block,
    file_id: FileId,
    line_starts: &[usize],
    lines: &mut HashSet<usize>,
) {
    for stmt in &block.node {
        if stmt.span.file == file_id && !stmt.span.is_dummy() {
            let lineno = byte_to_line(stmt.span.start as usize, line_starts);
            lines.insert(lineno);
        }
        collect_stmt_inner_lines(&stmt.node, file_id, line_starts, lines);
    }
}

fn collect_stmt_inner_lines(
    stmt: &StmtKind,
    file_id: FileId,
    line_starts: &[usize],
    lines: &mut HashSet<usize>,
) {
    match stmt {
        StmtKind::Expr(expr) => {
            collect_expr_lines(expr, file_id, line_starts, lines);
        }
        StmtKind::Let { value, .. } => {
            collect_expr_lines(value, file_id, line_starts, lines);
        }
        StmtKind::Assign { value, .. } => {
            collect_expr_lines(value, file_id, line_starts, lines);
        }
        StmtKind::WithBudget { body, .. }
        | StmtKind::WithBudgets { body, .. }
        | StmtKind::WithCostPayer { body, .. } => {
            collect_block_lines(body, file_id, line_starts, lines);
        }
        StmtKind::Emit { .. } | StmtKind::Grant { .. } | StmtKind::Revoke { .. } => {}
        StmtKind::Return(Some(expr)) => {
            collect_expr_lines(expr, file_id, line_starts, lines);
        }
        StmtKind::Return(None) => {}
    }
}

fn collect_expr_lines(
    expr: &ttrpg_ast::Spanned<ttrpg_ast::ast::ExprKind>,
    file_id: FileId,
    line_starts: &[usize],
    lines: &mut HashSet<usize>,
) {
    use ttrpg_ast::ast::ExprKind;
    match &expr.node {
        ExprKind::If {
            then_block,
            else_branch,
            ..
        } => {
            collect_block_lines(then_block, file_id, line_starts, lines);
            if let Some(eb) = else_branch {
                match eb {
                    ttrpg_ast::ast::ElseBranch::Block(b) => {
                        collect_block_lines(b, file_id, line_starts, lines);
                    }
                    ttrpg_ast::ast::ElseBranch::If(if_expr) => {
                        collect_expr_lines(if_expr, file_id, line_starts, lines);
                    }
                }
            }
        }
        ExprKind::IfLet {
            then_block,
            else_branch,
            ..
        } => {
            collect_block_lines(then_block, file_id, line_starts, lines);
            if let Some(eb) = else_branch {
                match eb {
                    ttrpg_ast::ast::ElseBranch::Block(b) => {
                        collect_block_lines(b, file_id, line_starts, lines);
                    }
                    ttrpg_ast::ast::ElseBranch::If(if_expr) => {
                        collect_expr_lines(if_expr, file_id, line_starts, lines);
                    }
                }
            }
        }
        ExprKind::PatternMatch { arms, .. } => {
            for arm in arms {
                match &arm.body {
                    ttrpg_ast::ast::ArmBody::Block(b) => {
                        collect_block_lines(b, file_id, line_starts, lines);
                    }
                    ttrpg_ast::ast::ArmBody::Expr(e) => {
                        if e.span.file == file_id && !e.span.is_dummy() {
                            lines.insert(byte_to_line(e.span.start as usize, line_starts));
                        }
                        collect_expr_lines(e, file_id, line_starts, lines);
                    }
                }
            }
        }
        ExprKind::GuardMatch { arms } => {
            for arm in arms {
                match &arm.body {
                    ttrpg_ast::ast::ArmBody::Block(b) => {
                        collect_block_lines(b, file_id, line_starts, lines);
                    }
                    ttrpg_ast::ast::ArmBody::Expr(e) => {
                        if e.span.file == file_id && !e.span.is_dummy() {
                            lines.insert(byte_to_line(e.span.start as usize, line_starts));
                        }
                        collect_expr_lines(e, file_id, line_starts, lines);
                    }
                }
            }
        }
        ExprKind::For { body, .. } => {
            collect_block_lines(body, file_id, line_starts, lines);
        }
        _ => {}
    }
}

fn collect_action_lines(
    action: &ActionDecl,
    file_id: FileId,
    line_starts: &[usize],
    lines: &mut HashSet<usize>,
) {
    collect_block_lines(&action.resolve, file_id, line_starts, lines);
    if let Some(ref req) = action.requires
        && req.span.file == file_id
        && !req.span.is_dummy()
    {
        lines.insert(byte_to_line(req.span.start as usize, line_starts));
    }
}

fn collect_reaction_lines(
    reaction: &ReactionDecl,
    file_id: FileId,
    line_starts: &[usize],
    lines: &mut HashSet<usize>,
) {
    collect_block_lines(&reaction.resolve, file_id, line_starts, lines);
}

fn collect_hook_lines(
    hook: &HookDecl,
    file_id: FileId,
    line_starts: &[usize],
    lines: &mut HashSet<usize>,
) {
    collect_block_lines(&hook.resolve, file_id, line_starts, lines);
}

// ── Hit line computation ──────────────────────────────────────

/// Convert recorded byte offsets to line numbers for a file.
fn compute_hit_lines(data: &CoverageData, src: &CoverageSource) -> Vec<usize> {
    let mut lines = HashSet::new();
    for &(file_idx, byte_offset) in &data.hit_spans {
        if file_idx == src.file_id {
            let lineno = byte_to_line(byte_offset as usize, &src.line_starts);
            lines.insert(lineno);
        }
    }
    let mut sorted: Vec<usize> = lines.into_iter().collect();
    sorted.sort_unstable();
    sorted
}

/// Convert a byte offset to a 1-indexed line number.
fn byte_to_line(byte_offset: usize, line_starts: &[usize]) -> usize {
    line_starts
        .partition_point(|&start| start <= byte_offset)
        .max(1)
}

// ── Branch counting ───────────────────────────────────────────

fn count_branches_in_file(program: &Program, src: &CoverageSource) -> usize {
    let file_id = FileId(src.file_id);
    let mut count = 0;
    for item in &program.items {
        if let TopLevel::System(system) = &item.node {
            for decl in &system.decls {
                match &decl.node {
                    DeclKind::Derive(f) | DeclKind::Mechanic(f) | DeclKind::Function(f) => {
                        count += count_branches_in_block(&f.body, file_id);
                    }
                    DeclKind::Action(a) => {
                        count += count_branches_in_block(&a.resolve, file_id);
                    }
                    DeclKind::Reaction(r) => {
                        count += count_branches_in_block(&r.resolve, file_id);
                    }
                    DeclKind::Hook(h) => {
                        count += count_branches_in_block(&h.resolve, file_id);
                    }
                    _ => {}
                }
            }
        }
    }
    count
}

fn count_branches_in_block(block: &Block, file_id: FileId) -> usize {
    let mut count = 0;
    for stmt in &block.node {
        count += count_branches_in_stmt(&stmt.node, file_id);
    }
    count
}

fn count_branches_in_stmt(stmt: &StmtKind, file_id: FileId) -> usize {
    match stmt {
        StmtKind::Expr(expr) => count_branches_in_expr(expr, file_id),
        StmtKind::Let { value, .. } => count_branches_in_expr(value, file_id),
        StmtKind::Assign { value, .. } => count_branches_in_expr(value, file_id),
        StmtKind::WithBudget { body, .. }
        | StmtKind::WithBudgets { body, .. }
        | StmtKind::WithCostPayer { body, .. } => count_branches_in_block(body, file_id),
        _ => 0,
    }
}

fn count_branches_in_expr(
    expr: &ttrpg_ast::Spanned<ttrpg_ast::ast::ExprKind>,
    file_id: FileId,
) -> usize {
    use ttrpg_ast::ast::ExprKind;
    match &expr.node {
        ExprKind::If {
            then_block,
            else_branch,
            ..
        } => {
            let mut count = 0;
            if expr.span.file == file_id {
                // 2 branches: then + else
                count += 2;
            }
            count += count_branches_in_block(then_block, file_id);
            if let Some(eb) = else_branch {
                match eb {
                    ttrpg_ast::ast::ElseBranch::Block(b) => {
                        count += count_branches_in_block(b, file_id);
                    }
                    ttrpg_ast::ast::ElseBranch::If(if_expr) => {
                        count += count_branches_in_expr(if_expr, file_id);
                    }
                }
            }
            count
        }
        ExprKind::IfLet {
            then_block,
            else_branch,
            ..
        } => {
            let mut count = 0;
            if expr.span.file == file_id {
                count += 2;
            }
            count += count_branches_in_block(then_block, file_id);
            if let Some(eb) = else_branch {
                match eb {
                    ttrpg_ast::ast::ElseBranch::Block(b) => {
                        count += count_branches_in_block(b, file_id);
                    }
                    ttrpg_ast::ast::ElseBranch::If(if_expr) => {
                        count += count_branches_in_expr(if_expr, file_id);
                    }
                }
            }
            count
        }
        ExprKind::PatternMatch { arms, .. } => {
            let mut count = 0;
            if expr.span.file == file_id {
                count += arms.len();
            }
            for arm in arms {
                match &arm.body {
                    ttrpg_ast::ast::ArmBody::Block(b) => {
                        count += count_branches_in_block(b, file_id);
                    }
                    ttrpg_ast::ast::ArmBody::Expr(e) => {
                        count += count_branches_in_expr(e, file_id);
                    }
                }
            }
            count
        }
        ExprKind::GuardMatch { arms } => {
            let mut count = 0;
            if expr.span.file == file_id {
                count += arms.len();
            }
            for arm in arms {
                match &arm.body {
                    ttrpg_ast::ast::ArmBody::Block(b) => {
                        count += count_branches_in_block(b, file_id);
                    }
                    ttrpg_ast::ast::ArmBody::Expr(e) => {
                        count += count_branches_in_expr(e, file_id);
                    }
                }
            }
            count
        }
        ExprKind::For { body, .. } => count_branches_in_block(body, file_id),
        _ => 0,
    }
}

fn count_hit_branches_in_file(data: &CoverageData, src: &CoverageSource) -> usize {
    let file_id = FileId(src.file_id);
    data.hit_branches
        .iter()
        .filter(|bp| bp.parent_span.file == file_id)
        .count()
}

// ── Uncovered details ─────────────────────────────────────────

fn find_uncovered_details(
    program: &Program,
    data: &CoverageData,
    src: &CoverageSource,
    coverable: &HashSet<usize>,
    hit: &HashSet<usize>,
) -> Vec<String> {
    let mut details = Vec::new();
    let file_id = FileId(src.file_id);

    // Report uncalled functions/derives/mechanics/actions
    for item in &program.items {
        if let TopLevel::System(system) = &item.node {
            for decl in &system.decls {
                let (name, kind, span) = match &decl.node {
                    DeclKind::Derive(f) => (&f.name, "derive", f.body.span),
                    DeclKind::Mechanic(f) => (&f.name, "mechanic", f.body.span),
                    DeclKind::Function(f) => (&f.name, "function", f.body.span),
                    DeclKind::Action(a) => (&a.name, "action", a.resolve.span),
                    DeclKind::Reaction(r) => (&r.name, "reaction", r.resolve.span),
                    DeclKind::Hook(h) => (&h.name, "hook", h.resolve.span),
                    _ => continue,
                };

                if span.file != file_id || span.is_dummy() {
                    continue;
                }

                if !data.hit_functions.contains(name.as_str()) {
                    let lineno = byte_to_line(span.start as usize, &src.line_starts);
                    details.push(format!("line {lineno}: {kind} {name} -- never called"));
                }
            }
        }
    }

    // Report uncovered line ranges (contiguous runs of MISS lines)
    let mut uncovered_lines: Vec<usize> = coverable
        .iter()
        .filter(|l| !hit.contains(l))
        .copied()
        .collect();
    uncovered_lines.sort_unstable();

    let mut i = 0;
    while i < uncovered_lines.len() {
        let start = uncovered_lines[i];
        let mut end = start;
        while i + 1 < uncovered_lines.len() && uncovered_lines[i + 1] == end + 1 {
            end = uncovered_lines[i + 1];
            i += 1;
        }
        if start == end {
            // Only report contiguous ranges if not already covered by function-level report
            // (skip single-line misses that are part of a function report)
        } else {
            details.push(format!("lines {start}-{end}: uncovered"));
        }
        i += 1;
    }

    details
}
