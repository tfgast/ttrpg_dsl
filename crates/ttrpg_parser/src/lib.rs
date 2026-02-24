pub mod diagnostic;
pub mod lower;
pub mod parser;
pub mod resolve;
mod decl;
mod expr;
mod pattern;
mod stmt;
mod types;

pub use diagnostic::{Diagnostic, Severity, SourceMap};
pub use lower::lower_moves;
pub use resolve::FileSystemInfo;
use ttrpg_ast::ast::*;
use ttrpg_ast::module::ModuleMap;
use ttrpg_ast::{Span, Spanned};
use ttrpg_lexer::TokenKind;
use parser::Parser;

pub fn parse(source: &str) -> (Program, Vec<Diagnostic>) {
    Parser::new(source).parse()
}

/// Parse a standalone expression from source text.
///
/// Returns the parsed expression (if successful) and any diagnostics.
/// Emits a diagnostic if there are trailing tokens after the expression.
pub fn parse_expr(source: &str) -> (Option<Spanned<ExprKind>>, Vec<Diagnostic>) {
    let mut parser = Parser::new(source);
    let result = parser.parse_expr();
    match result {
        Ok(expr) => {
            if !matches!(parser.peek(), TokenKind::Eof) {
                parser.error(format!("unexpected trailing token: {:?}", parser.peek()));
            }
            let diags = parser.into_diagnostics();
            (Some(expr), diags)
        }
        Err(()) => {
            let diags = parser.into_diagnostics();
            (None, diags)
        }
    }
}

/// Result of parsing multiple source files.
pub struct ParseMultiResult {
    pub program: Program,
    pub module_map: ModuleMap,
    pub diagnostics: Vec<Diagnostic>,
    pub has_errors: bool,
}

impl ParseMultiResult {
    /// Returns program + module_map only if no errors.
    /// CLI and other callers use this before calling check_with_modules.
    pub fn ok(&self) -> Option<(&Program, &ModuleMap)> {
        if self.has_errors {
            None
        } else {
            Some((&self.program, &self.module_map))
        }
    }
}

/// Parse multiple source files, lower moves, rebase spans, merge, and resolve modules.
///
/// Each source is a `(filename, source_text)` pair.
///
/// Steps:
/// 1. Parse each file independently
/// 2. Lower moves per file (so synthetic decls are visible to resolver)
/// 3. Compute base offsets and rebase all spans + diagnostics to global offsets
/// 4. Merge programs into single Program
/// 5. Resolve modules (registry, validation, collision detection, visibility, desugar)
/// 6. Return merged Program + ModuleMap + all diagnostics
pub fn parse_multi(sources: &[(String, String)]) -> ParseMultiResult {
    let mut all_diagnostics: Vec<Diagnostic> = Vec::new();
    let mut file_programs: Vec<Program> = Vec::new();
    let mut file_systems_info: Vec<FileSystemInfo> = Vec::new();
    let mut base_offsets: Vec<usize> = Vec::new();

    // Step 1-2: Parse and lower each file
    let mut current_offset: usize = 0;
    for (filename, source) in sources {
        base_offsets.push(current_offset);

        let (program, mut diags) = parse(source);
        let program = lower_moves(program, &mut diags);

        // Extract file-system info before rebasing
        let mut system_names = Vec::new();
        let mut use_decls = Vec::new();
        for item in &program.items {
            match &item.node {
                TopLevel::System(s) => system_names.push(s.name.clone()),
                TopLevel::Use(u) => use_decls.push(u.clone()),
            }
        }

        file_programs.push(program);
        // Diagnostics will be rebased below
        all_diagnostics.extend(diags.into_iter().map(|mut d| {
            // Will be rebased in step 3
            d.span = Span::new(d.span.start, d.span.end);
            d
        }));

        // Store pre-rebase file system info (use_decl spans will be rebased)
        file_systems_info.push(FileSystemInfo {
            system_names,
            use_decls,
        });

        // 1-byte sentinel gap between files
        current_offset += source.len() + 1;
        let _ = filename; // filename used for error reporting in future phases
    }

    // Step 3: Rebase all spans to global offsets
    let diag_start_index = {
        // We need to rebase diagnostics per-file. Let's redo: collect diags per-file first.
        // Actually, we already pushed them above — let's recount.
        // Re-approach: track diag counts per file.
        0 // We'll rebase in-place below
    };
    let _ = diag_start_index;

    // Re-do: parse again with proper per-file tracking
    // (the approach above mixed diagnostic collection and rebasing; let's clean it up)
    all_diagnostics.clear();
    let mut rebased_programs: Vec<Program> = Vec::new();
    file_systems_info.clear();

    let mut current_offset: usize = 0;
    for (_filename, source) in sources {
        let base = current_offset;

        let (program, mut diags) = parse(source);
        let program = lower_moves(program, &mut diags);

        // Extract file-system info
        let mut system_names = Vec::new();
        let mut use_decls = Vec::new();
        for item in &program.items {
            match &item.node {
                TopLevel::System(s) => system_names.push(s.name.clone()),
                TopLevel::Use(u) => use_decls.push(u.clone()),
            }
        }

        // Rebase diagnostics
        for d in &mut diags {
            d.span = rebase_span(d.span, base);
        }
        all_diagnostics.extend(diags);

        // Rebase program spans
        let program = rebase_program(program, base);

        // Rebase use_decls for file_systems_info
        let use_decls: Vec<UseDecl> = use_decls
            .into_iter()
            .map(|mut u| {
                u.span = rebase_span(u.span, base);
                u
            })
            .collect();

        rebased_programs.push(program);
        file_systems_info.push(FileSystemInfo {
            system_names,
            use_decls,
        });

        current_offset += source.len() + 1;
    }

    // Step 4: Merge programs into single Program
    let mut merged = Program::default();
    for p in rebased_programs {
        merged.items.extend(p.items);
    }
    merged.build_index();

    // Step 5: Resolve modules
    let (module_map, resolve_diags) = resolve::resolve_modules(&mut merged, &file_systems_info);
    all_diagnostics.extend(resolve_diags);

    let has_errors = all_diagnostics
        .iter()
        .any(|d| d.severity == Severity::Error);

    ParseMultiResult {
        program: merged,
        module_map,
        diagnostics: all_diagnostics,
        has_errors,
    }
}

/// Rebase a span by adding a base offset.
fn rebase_span(span: Span, base: usize) -> Span {
    if base == 0 {
        return span;
    }
    // Don't rebase dummy spans
    if span.start == 0 && span.end == 0 {
        return span;
    }
    Span::new(span.start + base, span.end + base)
}

/// Rebase all spans in a Program by adding a base offset.
fn rebase_program(mut program: Program, base: usize) -> Program {
    if base == 0 {
        return program;
    }
    for item in &mut program.items {
        item.span = rebase_span(item.span, base);
        match &mut item.node {
            TopLevel::System(system) => {
                for decl in &mut system.decls {
                    rebase_decl(decl, base);
                }
            }
            TopLevel::Use(u) => {
                u.span = rebase_span(u.span, base);
            }
        }
    }
    program
}

/// Rebase all spans in a declaration.
fn rebase_decl(decl: &mut Spanned<DeclKind>, base: usize) {
    decl.span = rebase_span(decl.span, base);
    match &mut decl.node {
        DeclKind::Enum(e) => {
            for v in &mut e.variants {
                v.span = rebase_span(v.span, base);
                if let Some(ref mut fields) = v.fields {
                    for f in fields {
                        f.span = rebase_span(f.span, base);
                        rebase_type_expr(&mut f.ty, base);
                    }
                }
            }
        }
        DeclKind::Struct(s) => {
            for f in &mut s.fields {
                rebase_field_def(f, base);
            }
        }
        DeclKind::Entity(e) => {
            for f in &mut e.fields {
                rebase_field_def(f, base);
            }
            for g in &mut e.optional_groups {
                g.span = rebase_span(g.span, base);
                for f in &mut g.fields {
                    rebase_field_def(f, base);
                }
            }
        }
        DeclKind::Derive(f) | DeclKind::Mechanic(f) => {
            rebase_fn_decl(f, base);
        }
        DeclKind::Action(a) => {
            rebase_type_expr(&mut a.receiver_type, base);
            for p in &mut a.params {
                rebase_param(p, base);
            }
            if let Some(ref mut cost) = a.cost {
                cost.span = rebase_span(cost.span, base);
                for t in &mut cost.tokens {
                    t.span = rebase_span(t.span, base);
                }
            }
            if let Some(ref mut req) = a.requires {
                rebase_expr(req, base);
            }
            rebase_block(&mut a.resolve, base);
        }
        DeclKind::Reaction(r) => {
            rebase_type_expr(&mut r.receiver_type, base);
            rebase_trigger(&mut r.trigger, base);
            if let Some(ref mut cost) = r.cost {
                cost.span = rebase_span(cost.span, base);
                for t in &mut cost.tokens {
                    t.span = rebase_span(t.span, base);
                }
            }
            rebase_block(&mut r.resolve, base);
        }
        DeclKind::Hook(h) => {
            rebase_type_expr(&mut h.receiver_type, base);
            rebase_trigger(&mut h.trigger, base);
            rebase_block(&mut h.resolve, base);
        }
        DeclKind::Condition(c) => {
            rebase_type_expr(&mut c.receiver_type, base);
            for p in &mut c.params {
                rebase_param(p, base);
            }
            for clause in &mut c.clauses {
                match clause {
                    ConditionClause::Modify(m) => {
                        m.span = rebase_span(m.span, base);
                        for b in &mut m.bindings {
                            b.span = rebase_span(b.span, base);
                            if let Some(ref mut v) = b.value {
                                rebase_expr(v, base);
                            }
                        }
                        for stmt in &mut m.body {
                            rebase_modify_stmt(stmt, base);
                        }
                    }
                    ConditionClause::Suppress(s) => {
                        s.span = rebase_span(s.span, base);
                        for b in &mut s.bindings {
                            b.span = rebase_span(b.span, base);
                            if let Some(ref mut v) = b.value {
                                rebase_expr(v, base);
                            }
                        }
                    }
                }
            }
        }
        DeclKind::Prompt(p) => {
            rebase_type_expr(&mut p.return_type, base);
            for param in &mut p.params {
                rebase_param(param, base);
            }
            if let Some(ref mut suggest) = p.suggest {
                rebase_expr(suggest, base);
            }
        }
        DeclKind::Option(o) => {
            if let Some(ref mut clauses) = o.when_enabled {
                for clause in clauses {
                    clause.span = rebase_span(clause.span, base);
                    for b in &mut clause.bindings {
                        b.span = rebase_span(b.span, base);
                        if let Some(ref mut v) = b.value {
                            rebase_expr(v, base);
                        }
                    }
                    for stmt in &mut clause.body {
                        rebase_modify_stmt(stmt, base);
                    }
                }
            }
        }
        DeclKind::Event(e) => {
            for p in &mut e.params {
                rebase_param(p, base);
            }
            for f in &mut e.fields {
                rebase_field_def(f, base);
            }
        }
        DeclKind::Move(m) => {
            rebase_type_expr(&mut m.receiver_type, base);
            for p in &mut m.params {
                rebase_param(p, base);
            }
            rebase_expr(&mut m.roll_expr, base);
            for o in &mut m.outcomes {
                o.span = rebase_span(o.span, base);
                rebase_block(&mut o.body, base);
            }
        }
    }
}

fn rebase_fn_decl(f: &mut FnDecl, base: usize) {
    rebase_type_expr(&mut f.return_type, base);
    for p in &mut f.params {
        rebase_param(p, base);
    }
    rebase_block(&mut f.body, base);
}

fn rebase_param(p: &mut Param, base: usize) {
    p.span = rebase_span(p.span, base);
    rebase_type_expr(&mut p.ty, base);
    if let Some(ref mut d) = p.default {
        rebase_expr(d, base);
    }
}

fn rebase_field_def(f: &mut FieldDef, base: usize) {
    f.span = rebase_span(f.span, base);
    rebase_type_expr(&mut f.ty, base);
    if let Some(ref mut d) = f.default {
        rebase_expr(d, base);
    }
}

fn rebase_trigger(t: &mut TriggerExpr, base: usize) {
    t.span = rebase_span(t.span, base);
    for b in &mut t.bindings {
        b.span = rebase_span(b.span, base);
        rebase_expr(&mut b.value, base);
    }
}

fn rebase_type_expr(texpr: &mut Spanned<TypeExpr>, base: usize) {
    texpr.span = rebase_span(texpr.span, base);
    match &mut texpr.node {
        TypeExpr::List(inner) | TypeExpr::Set(inner) | TypeExpr::OptionType(inner) => {
            rebase_type_expr(inner, base);
        }
        TypeExpr::Map(k, v) => {
            rebase_type_expr(k, base);
            rebase_type_expr(v, base);
        }
        TypeExpr::Resource(lo, hi) => {
            rebase_expr(lo, base);
            rebase_expr(hi, base);
        }
        _ => {}
    }
}

fn rebase_block(block: &mut Block, base: usize) {
    block.span = rebase_span(block.span, base);
    for stmt in &mut block.node {
        rebase_stmt(stmt, base);
    }
}

fn rebase_stmt(stmt: &mut Spanned<StmtKind>, base: usize) {
    stmt.span = rebase_span(stmt.span, base);
    match &mut stmt.node {
        StmtKind::Let { ty, value, .. } => {
            if let Some(ref mut t) = ty {
                rebase_type_expr(t, base);
            }
            rebase_expr(value, base);
        }
        StmtKind::Assign { target, value, .. } => {
            target.span = rebase_span(target.span, base);
            for seg in &mut target.segments {
                if let LValueSegment::Index(ref mut idx) = seg {
                    rebase_expr(idx, base);
                }
            }
            rebase_expr(value, base);
        }
        StmtKind::Expr(e) => {
            rebase_expr(e, base);
        }
        StmtKind::Grant { entity, fields, .. } => {
            rebase_expr(entity, base);
            for f in fields {
                f.span = rebase_span(f.span, base);
                rebase_expr(&mut f.value, base);
            }
        }
        StmtKind::Revoke { entity, .. } => {
            rebase_expr(entity, base);
        }
    }
}

fn rebase_expr(expr: &mut Spanned<ExprKind>, base: usize) {
    expr.span = rebase_span(expr.span, base);
    match &mut expr.node {
        ExprKind::IntLit(_)
        | ExprKind::StringLit(_)
        | ExprKind::BoolLit(_)
        | ExprKind::NoneLit
        | ExprKind::DiceLit { .. }
        | ExprKind::Ident(_) => {}
        ExprKind::BinOp { lhs, rhs, .. } => {
            rebase_expr(lhs, base);
            rebase_expr(rhs, base);
        }
        ExprKind::UnaryOp { operand, .. } => {
            rebase_expr(operand, base);
        }
        ExprKind::FieldAccess { object, .. } => {
            rebase_expr(object, base);
        }
        ExprKind::Index { object, index } => {
            rebase_expr(object, base);
            rebase_expr(index, base);
        }
        ExprKind::Call { callee, args } => {
            rebase_expr(callee, base);
            for a in args {
                a.span = rebase_span(a.span, base);
                rebase_expr(&mut a.value, base);
            }
        }
        ExprKind::StructLit { fields, base: base_expr, .. } => {
            if let Some(b) = base_expr {
                rebase_expr(b, base);
            }
            for f in fields {
                f.span = rebase_span(f.span, base);
                rebase_expr(&mut f.value, base);
            }
        }
        ExprKind::ListLit(items) => {
            for item in items {
                rebase_expr(item, base);
            }
        }
        ExprKind::Paren(inner) => {
            rebase_expr(inner, base);
        }
        ExprKind::If { condition, then_block, else_branch } => {
            rebase_expr(condition, base);
            rebase_block(then_block, base);
            if let Some(ref mut else_br) = else_branch {
                match else_br {
                    ElseBranch::Block(b) => rebase_block(b, base),
                    ElseBranch::If(e) => rebase_expr(e, base),
                }
            }
        }
        ExprKind::IfLet { pattern, scrutinee, then_block, else_branch } => {
            rebase_pattern(pattern, base);
            rebase_expr(scrutinee, base);
            rebase_block(then_block, base);
            if let Some(ref mut else_br) = else_branch {
                match else_br {
                    ElseBranch::Block(b) => rebase_block(b, base),
                    ElseBranch::If(e) => rebase_expr(e, base),
                }
            }
        }
        ExprKind::PatternMatch { scrutinee, arms } => {
            rebase_expr(scrutinee, base);
            for arm in arms {
                arm.span = rebase_span(arm.span, base);
                rebase_pattern(&mut arm.pattern, base);
                rebase_arm_body(&mut arm.body, base);
            }
        }
        ExprKind::GuardMatch { arms } => {
            for arm in arms {
                arm.span = rebase_span(arm.span, base);
                if let GuardKind::Expr(ref mut e) = arm.guard {
                    rebase_expr(e, base);
                }
                rebase_arm_body(&mut arm.body, base);
            }
        }
        ExprKind::For { pattern, iterable, body } => {
            rebase_pattern(pattern, base);
            match iterable {
                ForIterable::Collection(e) => rebase_expr(e, base),
                ForIterable::Range { start, end, .. } => {
                    rebase_expr(start, base);
                    rebase_expr(end, base);
                }
            }
            rebase_block(body, base);
        }
        ExprKind::Has { entity, .. } => {
            rebase_expr(entity, base);
        }
    }
}

fn rebase_pattern(pat: &mut Spanned<PatternKind>, base: usize) {
    pat.span = rebase_span(pat.span, base);
    match &mut pat.node {
        PatternKind::QualifiedDestructure { fields, .. }
        | PatternKind::BareDestructure { fields, .. } => {
            for f in fields {
                rebase_pattern(f, base);
            }
        }
        PatternKind::Some(inner) => {
            rebase_pattern(inner, base);
        }
        _ => {}
    }
}

fn rebase_arm_body(body: &mut ArmBody, base: usize) {
    match body {
        ArmBody::Expr(e) => rebase_expr(e, base),
        ArmBody::Block(b) => rebase_block(b, base),
    }
}

fn rebase_modify_stmt(stmt: &mut ModifyStmt, base: usize) {
    match stmt {
        ModifyStmt::Let { value, ty, span, .. } => {
            *span = rebase_span(*span, base);
            if let Some(ref mut t) = ty {
                rebase_type_expr(t, base);
            }
            rebase_expr(value, base);
        }
        ModifyStmt::ParamOverride { value, span, .. } => {
            *span = rebase_span(*span, base);
            rebase_expr(value, base);
        }
        ModifyStmt::ResultOverride { value, span, .. } => {
            *span = rebase_span(*span, base);
            rebase_expr(value, base);
        }
        ModifyStmt::If { condition, then_body, else_body, span } => {
            *span = rebase_span(*span, base);
            rebase_expr(condition, base);
            for s in then_body {
                rebase_modify_stmt(s, base);
            }
            if let Some(ref mut elses) = else_body {
                for s in elses {
                    rebase_modify_stmt(s, base);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_multi_single_file() {
        let sources = vec![(
            "test.ttrpg".to_string(),
            r#"system "Core" {
    enum Ability { STR, DEX }
    derive modifier(score: int) -> int {
        floor((score - 10) / 2)
    }
}"#.to_string(),
        )];

        let result = parse_multi(&sources);
        assert!(!result.has_errors, "unexpected errors: {:?}", result.diagnostics);
        assert!(result.ok().is_some());

        let (program, map) = result.ok().unwrap();
        assert!(!program.items.is_empty());
        let core = map.systems.get("Core").unwrap();
        assert!(core.types.contains("Ability"));
        assert!(core.functions.contains("modifier"));
    }

    #[test]
    fn parse_multi_two_files_different_systems() {
        let sources = vec![
            (
                "core.ttrpg".to_string(),
                r#"system "Core" {
    enum Ability { STR, DEX }
}"#.to_string(),
            ),
            (
                "extra.ttrpg".to_string(),
                r#"system "Extra" {
    enum Size { small, medium, large }
}"#.to_string(),
            ),
        ];

        let result = parse_multi(&sources);
        assert!(!result.has_errors, "unexpected errors: {:?}", result.diagnostics);

        let (_, map) = result.ok().unwrap();
        assert!(map.systems.contains_key("Core"));
        assert!(map.systems.contains_key("Extra"));
    }

    #[test]
    fn parse_multi_cross_system_collision() {
        let sources = vec![
            (
                "a.ttrpg".to_string(),
                r#"system "A" {
    enum Ability { STR }
}"#.to_string(),
            ),
            (
                "b.ttrpg".to_string(),
                r#"system "B" {
    enum Ability { DEX }
}"#.to_string(),
            ),
        ];

        let result = parse_multi(&sources);
        assert!(result.has_errors, "expected collision error");
        assert!(result.ok().is_none());
    }

    #[test]
    fn parse_multi_use_as_parsed() {
        let sources = vec![(
            "main.ttrpg".to_string(),
            r#"use "Core" as C
system "Main" {
    derive foo() -> int { 1 }
}
system "Core" {
    derive bar() -> int { 2 }
}"#.to_string(),
        )];

        let result = parse_multi(&sources);
        assert!(!result.has_errors, "unexpected errors: {:?}", result.diagnostics);

        let (_, map) = result.ok().unwrap();
        let main_info = map.systems.get("Main").unwrap();
        assert_eq!(main_info.imports.len(), 1);
        assert_eq!(main_info.imports[0].system_name, "Core");
        assert_eq!(main_info.imports[0].alias, Some("C".into()));
    }

    #[test]
    fn parse_multi_span_rebasing() {
        // Two files — errors in second file should have rebased spans
        let source1 = r#"system "A" {
    derive foo() -> int { 1 }
}"#;
        let source2 = r#"system "B" {
    derive bar() -> int { unknown_var }
}"#;
        let sources = vec![
            ("a.ttrpg".to_string(), source1.to_string()),
            ("b.ttrpg".to_string(), source2.to_string()),
        ];

        let result = parse_multi(&sources);
        // Parse itself won't error on unknown_var (that's a checker concern),
        // but spans in the second file should be rebased
        let expected_base = source1.len() + 1; // +1 for sentinel
        for item in &result.program.items {
            if let TopLevel::System(sys) = &item.node {
                if sys.name == "B" {
                    // Spans from file B should be >= expected_base
                    assert!(
                        item.span.start >= expected_base,
                        "expected span.start >= {}, got {}",
                        expected_base,
                        item.span.start,
                    );
                }
            }
        }
    }
}
