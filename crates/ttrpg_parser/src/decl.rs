use crate::parser::Parser;
use ttrpg_ast::ast::*;
use ttrpg_ast::Spanned;
use ttrpg_lexer::TokenKind;

impl Parser {
    pub(crate) fn parse_decl(&mut self) -> Result<DeclKind, ()> {
        match self.peek() {
            TokenKind::Ident(name) => match name.as_str() {
                "group" => self.parse_group_decl().map(DeclKind::Group),
                "enum" => self.parse_enum_decl().map(DeclKind::Enum),
                "struct" => self.parse_struct_decl().map(DeclKind::Struct),
                "entity" => self.parse_entity_decl().map(DeclKind::Entity),
                "derive" => self.parse_derive_decl().map(DeclKind::Derive),
                "mechanic" => self.parse_mechanic_decl().map(DeclKind::Mechanic),
                "action" => self.parse_action_decl().map(DeclKind::Action),
                "reaction" => self.parse_reaction_decl().map(DeclKind::Reaction),
                "hook" => self.parse_hook_decl().map(DeclKind::Hook),
                "condition" => self.parse_condition_decl().map(DeclKind::Condition),
                "prompt" => self.parse_prompt_decl().map(DeclKind::Prompt),
                "option" => self.parse_option_decl().map(DeclKind::Option),
                "event" => self.parse_event_decl().map(DeclKind::Event),
                "move" => self.parse_move_decl().map(DeclKind::Move),
                "table" => self.parse_table_decl().map(DeclKind::Table),
                "unit" => self.parse_unit_decl().map(DeclKind::Unit),
                "tag" => self.parse_tag_decl().map(DeclKind::Tag),
                _ => {
                    self.error(format!(
                        "unexpected identifier '{}' in declaration position",
                        name
                    ));
                    Err(())
                }
            },
            _ => {
                self.error(format!("expected declaration, found {:?}", self.peek()));
                Err(())
            }
        }
    }

    // ── Enum ─────────────────────────────────────────────────────

    fn parse_enum_decl(&mut self) -> Result<EnumDecl, ()> {
        self.expect_soft_keyword("enum")?;
        let (name, _) = self.expect_ident()?;
        let ordered = if self.at_ident("ordered") {
            self.advance();
            true
        } else {
            false
        };
        self.expect(&TokenKind::LBrace)?;
        self.skip_newlines();

        let mut variants = Vec::new();
        loop {
            self.skip_newlines();
            if matches!(self.peek(), TokenKind::RBrace | TokenKind::Eof) {
                break;
            }
            variants.push(self.parse_enum_variant()?);
            let saw_comma = matches!(self.peek(), TokenKind::Comma);
            if saw_comma {
                self.advance();
            }
            let saw_newline = self.skip_newlines();
            if !saw_comma
                && !saw_newline
                && !matches!(self.peek(), TokenKind::RBrace | TokenKind::Eof)
            {
                self.error("expected ',' or newline between enum variants");
                return Err(());
            }
        }

        if variants.is_empty() {
            self.error("enum declaration requires at least one variant");
            return Err(());
        }

        self.expect(&TokenKind::RBrace)?;
        Ok(EnumDecl {
            name,
            ordered,
            variants,
        })
    }

    fn parse_enum_variant(&mut self) -> Result<EnumVariant, ()> {
        let start = self.start_span();
        let (name, _) = self.expect_ident()?;

        let fields = if matches!(self.peek(), TokenKind::LParen) {
            self.advance();
            let list = self.parse_field_list()?;
            if list.is_empty() {
                self.error("enum variant payload requires at least one field");
                return Err(());
            }
            self.expect(&TokenKind::RParen)?;
            Some(list)
        } else {
            None
        };

        Ok(EnumVariant {
            name,
            fields,
            span: self.end_span(start),
        })
    }

    fn parse_field_list(&mut self) -> Result<Vec<FieldEntry>, ()> {
        let mut fields = Vec::new();
        if !matches!(self.peek(), TokenKind::RParen) {
            fields.push(self.parse_field_entry()?);
            while matches!(self.peek(), TokenKind::Comma) {
                self.advance();
                if matches!(self.peek(), TokenKind::RParen) {
                    break;
                }
                fields.push(self.parse_field_entry()?);
            }
        }
        Ok(fields)
    }

    fn parse_field_entry(&mut self) -> Result<FieldEntry, ()> {
        let start = self.start_span();
        let (name, _) = self.expect_ident()?;
        self.expect(&TokenKind::Colon)?;
        let ty = self.parse_type()?;
        Ok(FieldEntry {
            name,
            ty,
            span: self.end_span(start),
        })
    }

    // ── Struct / Entity ──────────────────────────────────────────

    fn parse_group_decl(&mut self) -> Result<GroupDecl, ()> {
        self.expect_soft_keyword("group")?;
        let (name, _) = self.expect_ident()?;
        self.expect(&TokenKind::LBrace)?;
        self.skip_newlines();
        let fields = self.parse_field_defs()?;
        self.expect(&TokenKind::RBrace)?;
        Ok(GroupDecl { name, fields })
    }

    fn parse_struct_decl(&mut self) -> Result<StructDecl, ()> {
        self.expect_soft_keyword("struct")?;
        let (name, _) = self.expect_ident()?;
        self.expect(&TokenKind::LBrace)?;
        self.skip_newlines();
        let fields = self.parse_field_defs()?;
        self.expect(&TokenKind::RBrace)?;
        Ok(StructDecl { name, fields })
    }

    fn parse_entity_decl(&mut self) -> Result<EntityDecl, ()> {
        self.expect_soft_keyword("entity")?;
        let (name, _) = self.expect_ident()?;
        self.expect(&TokenKind::LBrace)?;
        self.skip_newlines();

        let mut fields = Vec::new();
        let mut optional_groups = Vec::new();

        while !matches!(self.peek(), TokenKind::RBrace | TokenKind::Eof) {
            if self.at_ident("optional") {
                optional_groups.push(self.parse_optional_group()?);
            } else if self.at_ident("include") {
                optional_groups.push(self.parse_include_group()?);
            } else {
                fields.push(self.parse_field_def()?);
            }
            let saw_comma = matches!(self.peek(), TokenKind::Comma);
            if saw_comma {
                self.advance();
            }
            let saw_newline = self.skip_newlines();
            if !saw_comma
                && !saw_newline
                && !matches!(self.peek(), TokenKind::RBrace | TokenKind::Eof)
            {
                self.error("expected ',' or newline between fields");
                return Err(());
            }
        }

        self.expect(&TokenKind::RBrace)?;
        Ok(EntityDecl {
            name,
            fields,
            optional_groups,
        })
    }

    fn parse_optional_group(&mut self) -> Result<OptionalGroup, ()> {
        let start = self.start_span();
        self.expect_soft_keyword("optional")?;
        let (name, _) = self.expect_ident()?;
        let (fields, is_external_ref) = if matches!(self.peek(), TokenKind::LBrace) {
            self.advance();
            self.skip_newlines();
            let fields = self.parse_field_defs()?;
            self.expect(&TokenKind::RBrace)?;
            (fields, false)
        } else {
            (Vec::new(), true)
        };
        Ok(OptionalGroup {
            name,
            fields,
            is_external_ref,
            is_required: false,
            span: self.end_span(start),
        })
    }

    fn parse_include_group(&mut self) -> Result<OptionalGroup, ()> {
        let start = self.start_span();
        self.expect_soft_keyword("include")?;
        let (name, _) = self.expect_ident()?;
        Ok(OptionalGroup {
            name,
            fields: Vec::new(),
            is_external_ref: true,
            is_required: true,
            span: self.end_span(start),
        })
    }

    pub(crate) fn parse_field_defs(&mut self) -> Result<Vec<FieldDef>, ()> {
        let mut fields = Vec::new();
        while !matches!(self.peek(), TokenKind::RBrace | TokenKind::Eof) {
            fields.push(self.parse_field_def()?);
            let saw_comma = matches!(self.peek(), TokenKind::Comma);
            if saw_comma {
                self.advance();
            }
            let saw_newline = self.skip_newlines();
            if !saw_comma
                && !saw_newline
                && !matches!(self.peek(), TokenKind::RBrace | TokenKind::Eof)
            {
                self.error("expected ',' or newline between fields");
                return Err(());
            }
        }
        Ok(fields)
    }

    pub(crate) fn parse_field_def(&mut self) -> Result<FieldDef, ()> {
        let start = self.start_span();
        let (name, _) = self.expect_ident()?;
        self.expect(&TokenKind::Colon)?;
        let ty = self.parse_type()?;

        let default = if matches!(self.peek(), TokenKind::Eq) {
            self.advance();
            Some(self.parse_expr()?)
        } else {
            None
        };

        Ok(FieldDef {
            name,
            ty,
            default,
            span: self.end_span(start),
        })
    }

    // ── Derive / Mechanic ────────────────────────────────────────

    fn parse_derive_decl(&mut self) -> Result<FnDecl, ()> {
        self.expect_soft_keyword("derive")?;
        self.parse_fn_body()
    }

    fn parse_mechanic_decl(&mut self) -> Result<FnDecl, ()> {
        self.expect_soft_keyword("mechanic")?;
        self.parse_fn_body()
    }

    fn parse_fn_body(&mut self) -> Result<FnDecl, ()> {
        let (name, _) = self.expect_ident()?;
        self.expect(&TokenKind::LParen)?;
        let params = self.parse_params()?;
        self.expect(&TokenKind::RParen)?;
        self.expect(&TokenKind::Arrow)?;
        let return_type = self.parse_type()?;

        // Parse tag annotations: #tag1 #tag2 ... before the body block
        let mut tags = Vec::new();
        while matches!(self.peek(), TokenKind::Hash) {
            self.advance(); // consume #
            let (tag_name, _) = self.expect_ident()?;
            tags.push(tag_name);
        }

        let body = self.parse_block()?;
        Ok(FnDecl {
            name,
            params,
            return_type,
            body,
            synthetic: false,
            tags,
        })
    }

    fn parse_tag_decl(&mut self) -> Result<TagDecl, ()> {
        self.expect_soft_keyword("tag")?;
        let (name, _) = self.expect_ident()?;
        self.expect_term()?;
        Ok(TagDecl { name })
    }

    pub(crate) fn parse_params(&mut self) -> Result<Vec<Param>, ()> {
        let mut params = Vec::new();
        if !matches!(self.peek(), TokenKind::RParen) {
            params.push(self.parse_param()?);
            while matches!(self.peek(), TokenKind::Comma) {
                self.advance();
                if matches!(self.peek(), TokenKind::RParen) {
                    break;
                }
                params.push(self.parse_param()?);
            }
        }
        Ok(params)
    }

    fn parse_param(&mut self) -> Result<Param, ()> {
        let start = self.start_span();
        let (name, _) = self.expect_ident()?;
        self.expect(&TokenKind::Colon)?;
        let ty = self.parse_type()?;

        let with_groups = self.parse_with_groups()?;

        let default = if matches!(self.peek(), TokenKind::Eq) {
            self.advance();
            Some(self.parse_expr()?)
        } else {
            None
        };

        Ok(Param {
            name,
            ty,
            default,
            with_groups,
            span: self.end_span(start),
        })
    }

    /// Parse an optional `with Group1 as alias1, Group2` constraint list.
    /// Returns an empty vec if no `with` keyword is present.
    fn parse_with_groups(&mut self) -> Result<Vec<GroupConstraint>, ()> {
        if !self.at_ident("with") {
            return Ok(vec![]);
        }
        self.advance(); // consume 'with'
        let mut groups = Vec::new();
        let (name, _) = self.expect_ident()?;
        let alias = if self.at_ident("as") {
            self.advance();
            let (a, _) = self.expect_ident()?;
            Some(a)
        } else {
            None
        };
        groups.push(GroupConstraint { name, alias });
        while matches!(self.peek(), TokenKind::Comma) {
            // Peek ahead: if the next token after comma is IDENT followed by
            // colon or rparen, it's the next param, not another group name.
            if matches!(self.peek_at(1), TokenKind::Ident(_))
                && matches!(self.peek_at(2), TokenKind::Colon)
            {
                break;
            }
            // Trailing comma: comma followed by ')' ends the param list.
            if matches!(self.peek_at(1), TokenKind::RParen) {
                break;
            }
            self.advance(); // consume ','
            let (name, _) = self.expect_ident()?;
            let alias = if self.at_ident("as") {
                self.advance();
                let (a, _) = self.expect_ident()?;
                Some(a)
            } else {
                None
            };
            groups.push(GroupConstraint { name, alias });
        }
        Ok(groups)
    }

    // ── Action ───────────────────────────────────────────────────

    fn parse_action_decl(&mut self) -> Result<ActionDecl, ()> {
        self.expect_soft_keyword("action")?;
        let (name, _) = self.expect_ident()?;
        self.expect_soft_keyword("on")?;
        let (receiver_name, _) = self.expect_ident()?;
        self.expect(&TokenKind::Colon)?;
        let receiver_type = self.parse_type()?;
        let receiver_with_groups = self.parse_with_groups()?;
        self.expect(&TokenKind::LParen)?;
        let params = self.parse_params()?;
        self.expect(&TokenKind::RParen)?;
        self.expect(&TokenKind::LBrace)?;
        self.skip_newlines();

        let cost = if self.at_ident("cost") {
            Some(self.parse_cost_clause()?)
        } else {
            None
        };

        self.skip_newlines();

        let requires = self.parse_multiple_requires_clauses()?;

        self.skip_newlines();
        let resolve = self.parse_resolve_block()?;
        self.skip_newlines();
        self.expect(&TokenKind::RBrace)?;

        Ok(ActionDecl {
            name,
            receiver_name,
            receiver_type,
            receiver_with_groups,
            params,
            cost,
            requires,
            resolve,
            trigger_text: None,
            tags: vec![],
            synthetic: false,
        })
    }

    fn parse_cost_clause(&mut self) -> Result<CostClause, ()> {
        let start = self.start_span();
        self.expect_soft_keyword("cost")?;

        // `cost free` — intentionally no cost
        if self.at_ident("free") {
            self.advance();
            self.expect_term()?;
            return Ok(CostClause {
                tokens: vec![],
                free: true,
                span: self.end_span(start),
            });
        }

        self.expect(&TokenKind::LBrace)?;
        self.suppress_newlines_in_brace_block();

        let mut tokens = Vec::new();
        let tok_start = self.start_span();
        let (name, _) = self.expect_ident()?;
        tokens.push(Spanned::new(name, self.end_span(tok_start)));
        while matches!(self.peek(), TokenKind::Comma) {
            self.advance();
            if matches!(self.peek(), TokenKind::RBrace) {
                break;
            }
            let tok_start = self.start_span();
            let (name, _) = self.expect_ident()?;
            tokens.push(Spanned::new(name, self.end_span(tok_start)));
        }

        self.expect(&TokenKind::RBrace)?;
        self.expect_term()?;
        Ok(CostClause {
            tokens,
            free: false,
            span: self.end_span(start),
        })
    }

    fn parse_requires_clause(&mut self) -> Result<Spanned<ExprKind>, ()> {
        self.expect_soft_keyword("requires")?;
        self.expect(&TokenKind::LBrace)?;
        self.suppress_newlines_in_brace_block();
        let expr = self.parse_expr()?;
        self.expect(&TokenKind::RBrace)?;
        self.expect_term()?;
        Ok(expr)
    }

    fn parse_multiple_requires_clauses(&mut self) -> Result<Option<Spanned<ExprKind>>, ()> {
        if !self.at_ident("requires") {
            return Ok(None);
        }

        let mut combined = self.parse_requires_clause()?;
        self.skip_newlines();
        while self.at_ident("requires") {
            let next = self.parse_requires_clause()?;
            self.skip_newlines();
            let span = combined.span.merge(next.span);
            combined = Spanned::new(
                ExprKind::BinOp {
                    op: BinOp::And,
                    lhs: Box::new(combined),
                    rhs: Box::new(next),
                },
                span,
            );
        }
        Ok(Some(combined))
    }

    fn parse_resolve_block(&mut self) -> Result<Block, ()> {
        self.expect_soft_keyword("resolve")?;
        self.parse_block()
    }

    // ── Reaction ─────────────────────────────────────────────────

    fn parse_reaction_decl(&mut self) -> Result<ReactionDecl, ()> {
        self.expect_soft_keyword("reaction")?;
        let (name, _) = self.expect_ident()?;
        self.expect_soft_keyword("on")?;
        let (receiver_name, _) = self.expect_ident()?;
        self.expect(&TokenKind::Colon)?;
        let receiver_type = self.parse_type()?;
        let receiver_with_groups = self.parse_with_groups()?;
        self.expect(&TokenKind::LParen)?;
        self.skip_newlines();
        let trigger = self.parse_trigger_param()?;
        self.skip_newlines();
        self.expect(&TokenKind::RParen)?;
        self.expect(&TokenKind::LBrace)?;
        self.skip_newlines();

        let cost = if self.at_ident("cost") {
            Some(self.parse_cost_clause()?)
        } else {
            None
        };

        self.skip_newlines();
        let resolve = self.parse_resolve_block()?;
        self.skip_newlines();
        self.expect(&TokenKind::RBrace)?;

        Ok(ReactionDecl {
            name,
            receiver_name,
            receiver_type,
            receiver_with_groups,
            trigger,
            cost,
            resolve,
        })
    }

    // ── Hook ─────────────────────────────────────────────────────

    fn parse_hook_decl(&mut self) -> Result<HookDecl, ()> {
        self.expect_soft_keyword("hook")?;
        let (name, _) = self.expect_ident()?;
        self.expect_soft_keyword("on")?;
        let (receiver_name, _) = self.expect_ident()?;
        self.expect(&TokenKind::Colon)?;
        let receiver_type = self.parse_type()?;
        let receiver_with_groups = self.parse_with_groups()?;
        self.expect(&TokenKind::LParen)?;
        self.skip_newlines();
        let trigger = self.parse_trigger_param()?;
        self.skip_newlines();
        self.expect(&TokenKind::RParen)?;
        let resolve = self.parse_block()?;

        Ok(HookDecl {
            name,
            receiver_name,
            receiver_type,
            receiver_with_groups,
            trigger,
            resolve,
        })
    }

    fn parse_trigger_param(&mut self) -> Result<TriggerExpr, ()> {
        let start = self.start_span();
        self.expect_soft_keyword("trigger")?;
        self.expect(&TokenKind::Colon)?;
        let (event_name, _) = self.expect_ident()?;
        self.expect(&TokenKind::LParen)?;
        let bindings = self.parse_trigger_bindings()?;
        self.expect(&TokenKind::RParen)?;
        Ok(TriggerExpr {
            event_name,
            bindings,
            span: self.end_span(start),
        })
    }

    fn parse_trigger_bindings(&mut self) -> Result<Vec<TriggerBinding>, ()> {
        let mut bindings = Vec::new();
        bindings.push(self.parse_trigger_binding()?);
        while matches!(self.peek(), TokenKind::Comma) {
            self.advance();
            if matches!(self.peek(), TokenKind::RParen) {
                break;
            }
            bindings.push(self.parse_trigger_binding()?);
        }
        Ok(bindings)
    }

    fn parse_trigger_binding(&mut self) -> Result<TriggerBinding, ()> {
        let start = self.start_span();
        // Named binding: IDENT : expr, or positional: just IDENT
        if matches!(self.peek(), TokenKind::Ident(_)) && matches!(self.peek_at(1), TokenKind::Colon)
        {
            let (name, _) = self.expect_ident()?;
            self.advance(); // colon
            let value = self.parse_expr()?;
            Ok(TriggerBinding {
                name: Some(name),
                value,
                span: self.end_span(start),
            })
        } else {
            // Positional binding must be a bare IDENT per spec
            let (ident, ident_span) = self.expect_ident()?;
            let value = Spanned::new(ExprKind::Ident(ident), ident_span);
            Ok(TriggerBinding {
                name: None,
                value,
                span: self.end_span(start),
            })
        }
    }

    // ── Event ────────────────────────────────────────────────────

    fn parse_event_decl(&mut self) -> Result<EventDecl, ()> {
        self.expect_soft_keyword("event")?;
        let (name, _) = self.expect_ident()?;
        self.expect(&TokenKind::LParen)?;
        let params = self.parse_params()?;
        self.expect(&TokenKind::RParen)?;
        self.expect(&TokenKind::LBrace)?;
        self.skip_newlines();
        let fields = self.parse_field_defs()?;
        self.expect(&TokenKind::RBrace)?;
        Ok(EventDecl {
            name,
            params,
            fields,
        })
    }

    // ── Condition ────────────────────────────────────────────────

    fn parse_condition_decl(&mut self) -> Result<ConditionDecl, ()> {
        self.expect_soft_keyword("condition")?;
        let (name, _) = self.expect_ident()?;
        // Optional parameters: condition Frightened(source: Character) on ...
        let params = if matches!(self.peek(), TokenKind::LParen) {
            self.expect(&TokenKind::LParen)?;
            let params = self.parse_params()?;
            self.expect(&TokenKind::RParen)?;
            params
        } else {
            Vec::new()
        };
        let extends = if self.at_ident("extends") {
            self.advance();
            let mut parents = Vec::new();
            let start = self.start_span();
            let (name, _) = self.expect_ident()?;
            parents.push(Spanned::new(ttrpg_ast::Name::from(name), self.end_span(start)));
            while matches!(self.peek(), TokenKind::Comma) {
                self.advance();
                let start = self.start_span();
                let (name, _) = self.expect_ident()?;
                parents.push(Spanned::new(ttrpg_ast::Name::from(name), self.end_span(start)));
            }
            parents
        } else {
            Vec::new()
        };
        self.expect_soft_keyword("on")?;
        let (receiver_name, _) = self.expect_ident()?;
        self.expect(&TokenKind::Colon)?;
        let receiver_type = self.parse_type()?;
        let receiver_with_groups = self.parse_with_groups()?;
        self.expect(&TokenKind::LBrace)?;
        self.skip_newlines();

        let mut clauses = Vec::new();
        while !matches!(self.peek(), TokenKind::RBrace | TokenKind::Eof) {
            if self.at_ident("modify") {
                clauses.push(ConditionClause::Modify(self.parse_modify_clause()?));
            } else if self.at_ident("suppress") {
                clauses.push(ConditionClause::Suppress(self.parse_suppress_clause()?));
            } else {
                self.error(format!(
                    "expected 'modify' or 'suppress' in condition body, found {:?}",
                    self.peek()
                ));
                return Err(());
            }
            self.skip_newlines();
        }

        self.expect(&TokenKind::RBrace)?;
        Ok(ConditionDecl {
            name,
            params,
            extends,
            receiver_name,
            receiver_type,
            receiver_with_groups,
            clauses,
        })
    }

    pub(crate) fn parse_modify_clause(&mut self) -> Result<ModifyClause, ()> {
        let start = self.start_span();
        self.expect_soft_keyword("modify")?;

        // Parse target: either a selector [predicates] or a named function (possibly with .cost)
        let target = if matches!(self.peek(), TokenKind::LBracket) {
            self.advance(); // consume [
            let mut predicates = Vec::new();
            // At least one predicate required
            predicates.push(self.parse_selector_predicate()?);
            while matches!(self.peek(), TokenKind::Comma) {
                self.advance();
                if matches!(self.peek(), TokenKind::RBracket) {
                    break;
                }
                predicates.push(self.parse_selector_predicate()?);
            }
            if predicates.is_empty() {
                self.error("selector requires at least one predicate");
                return Err(());
            }
            self.expect(&TokenKind::RBracket)?;
            ModifyTarget::Selector(predicates)
        } else {
            let (name, _) = self.expect_ident()?;
            // Check for `.cost` suffix: `modify ActionName.cost(...)`
            if matches!(self.peek(), TokenKind::Dot)
                && matches!(self.peek_at(1), TokenKind::Ident(s) if s == "cost")
            {
                self.advance(); // consume .
                self.advance(); // consume cost
                ModifyTarget::Cost(name)
            } else {
                ModifyTarget::Named(name)
            }
        };

        self.expect(&TokenKind::LParen)?;
        let bindings = if matches!(self.peek(), TokenKind::RParen) {
            Vec::new()
        } else {
            self.parse_modify_bindings()?
        };
        self.expect(&TokenKind::RParen)?;
        self.expect(&TokenKind::LBrace)?;
        self.skip_newlines();

        // Use cost-specific body parser for Cost targets
        let body = match &target {
            ModifyTarget::Cost(_) => self.parse_cost_modify_stmts()?,
            _ => self.parse_modify_stmts()?,
        };
        self.expect(&TokenKind::RBrace)?;

        Ok(ModifyClause {
            target,
            bindings,
            body,
            span: self.end_span(start),
            id: ModifyClauseId(0), // placeholder; build_index() assigns real IDs
        })
    }

    fn parse_selector_predicate(&mut self) -> Result<SelectorPredicate, ()> {
        // #tag_name
        if matches!(self.peek(), TokenKind::Hash) {
            self.advance();
            let (name, _) = self.expect_ident()?;
            return Ok(SelectorPredicate::Tag(name));
        }
        // returns Type
        if self.at_ident("returns") {
            self.advance();
            let ty = self.parse_type()?;
            return Ok(SelectorPredicate::Returns(ty));
        }
        // has param_name (: Type)?
        if self.at_ident("has") {
            self.advance();
            let (name, _) = self.expect_ident()?;
            let ty = if matches!(self.peek(), TokenKind::Colon) {
                self.advance();
                Some(self.parse_type()?)
            } else {
                None
            };
            return Ok(SelectorPredicate::HasParam { name, ty });
        }
        self.error(format!(
            "expected selector predicate (#tag, 'returns', or 'has'), found {:?}",
            self.peek()
        ));
        Err(())
    }

    fn parse_modify_bindings(&mut self) -> Result<Vec<ModifyBinding>, ()> {
        let mut bindings = Vec::new();
        bindings.push(self.parse_modify_binding()?);
        while matches!(self.peek(), TokenKind::Comma) {
            self.advance();
            if matches!(self.peek(), TokenKind::RParen) {
                break;
            }
            bindings.push(self.parse_modify_binding()?);
        }
        Ok(bindings)
    }

    fn parse_modify_binding(&mut self) -> Result<ModifyBinding, ()> {
        let start = self.start_span();
        let (name, _) = self.expect_ident()?;
        self.expect(&TokenKind::Colon)?;
        let value = if matches!(self.peek(), TokenKind::Underscore) {
            self.advance();
            None
        } else {
            Some(self.parse_expr()?)
        };
        Ok(ModifyBinding {
            name,
            value,
            span: self.end_span(start),
        })
    }

    fn parse_modify_stmts(&mut self) -> Result<Vec<ModifyStmt>, ()> {
        let mut stmts = Vec::new();
        while !matches!(self.peek(), TokenKind::RBrace | TokenKind::Eof) {
            stmts.push(self.parse_modify_stmt()?);
            self.skip_newlines();
        }
        Ok(stmts)
    }

    fn parse_modify_stmt(&mut self) -> Result<ModifyStmt, ()> {
        let start = self.start_span();

        // let binding
        if matches!(self.peek(), TokenKind::Let) {
            self.advance();
            let (name, _) = self.expect_ident()?;
            let ty = if matches!(self.peek(), TokenKind::Colon) {
                self.advance();
                Some(self.parse_type()?)
            } else {
                None
            };
            self.expect(&TokenKind::Eq)?;
            let value = self.parse_expr()?;
            self.expect_term()?;
            return Ok(ModifyStmt::Let {
                name,
                ty,
                value,
                span: self.end_span(start),
            });
        }

        // if
        if matches!(self.peek(), TokenKind::If) {
            self.advance();
            let condition = self.parse_expr()?;
            self.expect(&TokenKind::LBrace)?;
            self.skip_newlines();
            let then_body = self.parse_modify_stmts()?;
            self.expect(&TokenKind::RBrace)?;
            let else_body = if matches!(self.peek(), TokenKind::Else) {
                self.advance();
                self.expect(&TokenKind::LBrace)?;
                self.skip_newlines();
                let body = self.parse_modify_stmts()?;
                self.expect(&TokenKind::RBrace)?;
                Some(body)
            } else {
                None
            };
            self.expect_term()?;
            return Ok(ModifyStmt::If {
                condition,
                then_body,
                else_body,
                span: self.end_span(start),
            });
        }

        // result.IDENT = expr
        if self.at_ident("result") && matches!(self.peek_at(1), TokenKind::Dot) {
            self.advance(); // result
            self.advance(); // .
            let (field, _) = self.expect_ident()?;
            self.expect(&TokenKind::Eq)?;
            let value = self.parse_expr()?;
            self.expect_term()?;
            return Ok(ModifyStmt::ResultOverride {
                field,
                value,
                span: self.end_span(start),
            });
        }

        // IDENT = expr (parameter override)
        if matches!(self.peek(), TokenKind::Ident(_)) && matches!(self.peek_at(1), TokenKind::Eq) {
            let (name, _) = self.expect_ident()?;
            self.advance(); // =
            let value = self.parse_expr()?;
            self.expect_term()?;
            return Ok(ModifyStmt::ParamOverride {
                name,
                value,
                span: self.end_span(start),
            });
        }

        self.error(format!(
            "expected modify statement (let, result.field =, or param =), found {:?}",
            self.peek()
        ));
        Err(())
    }

    /// Parse the body of a `modify Name.cost(...)` clause.
    ///
    /// Allowed statements:
    /// - `cost = free` → CostOverride { free: true }
    /// - `cost = token1, token2` → CostOverride { tokens, free: false }
    /// - `let name = expr`
    /// - `if cond { ... } else { ... }` (with cost modify stmts in branches)
    fn parse_cost_modify_stmts(&mut self) -> Result<Vec<ModifyStmt>, ()> {
        let mut stmts = Vec::new();
        while !matches!(self.peek(), TokenKind::RBrace | TokenKind::Eof) {
            stmts.push(self.parse_cost_modify_stmt()?);
            self.skip_newlines();
        }
        Ok(stmts)
    }

    fn parse_cost_modify_stmt(&mut self) -> Result<ModifyStmt, ()> {
        let start = self.start_span();

        // let binding
        if matches!(self.peek(), TokenKind::Let) {
            self.advance();
            let (name, _) = self.expect_ident()?;
            let ty = if matches!(self.peek(), TokenKind::Colon) {
                self.advance();
                Some(self.parse_type()?)
            } else {
                None
            };
            self.expect(&TokenKind::Eq)?;
            let value = self.parse_expr()?;
            self.expect_term()?;
            return Ok(ModifyStmt::Let {
                name,
                ty,
                value,
                span: self.end_span(start),
            });
        }

        // if
        if matches!(self.peek(), TokenKind::If) {
            self.advance();
            let condition = self.parse_expr()?;
            self.expect(&TokenKind::LBrace)?;
            self.skip_newlines();
            let then_body = self.parse_cost_modify_stmts()?;
            self.expect(&TokenKind::RBrace)?;
            let else_body = if matches!(self.peek(), TokenKind::Else) {
                self.advance();
                self.expect(&TokenKind::LBrace)?;
                self.skip_newlines();
                let body = self.parse_cost_modify_stmts()?;
                self.expect(&TokenKind::RBrace)?;
                Some(body)
            } else {
                None
            };
            self.expect_term()?;
            return Ok(ModifyStmt::If {
                condition,
                then_body,
                else_body,
                span: self.end_span(start),
            });
        }

        // cost = free | cost = token1, token2
        if self.at_ident("cost") && matches!(self.peek_at(1), TokenKind::Eq) {
            self.advance(); // cost
            self.advance(); // =

            // `cost = free`
            if self.at_ident("free") {
                self.advance();
                self.expect_term()?;
                return Ok(ModifyStmt::CostOverride {
                    tokens: vec![],
                    free: true,
                    span: self.end_span(start),
                });
            }

            // `cost = token1, token2, ...`
            let mut tokens = Vec::new();
            let tok_start = self.start_span();
            let (name, _) = self.expect_ident()?;
            tokens.push(Spanned::new(name, self.end_span(tok_start)));
            while matches!(self.peek(), TokenKind::Comma) {
                self.advance();
                let tok_start = self.start_span();
                let (name, _) = self.expect_ident()?;
                tokens.push(Spanned::new(name, self.end_span(tok_start)));
            }
            self.expect_term()?;
            return Ok(ModifyStmt::CostOverride {
                tokens,
                free: false,
                span: self.end_span(start),
            });
        }

        self.error(format!(
            "expected cost modify statement (cost =, let, or if), found {:?}",
            self.peek()
        ));
        Err(())
    }

    fn parse_suppress_clause(&mut self) -> Result<SuppressClause, ()> {
        let start = self.start_span();
        self.expect_soft_keyword("suppress")?;
        let (event_name, _) = self.expect_ident()?;
        self.expect(&TokenKind::LParen)?;
        let bindings = self.parse_modify_bindings()?;
        self.expect(&TokenKind::RParen)?;
        self.expect_term()?;
        Ok(SuppressClause {
            event_name,
            bindings,
            span: self.end_span(start),
        })
    }

    // ── Prompt ───────────────────────────────────────────────────

    fn parse_prompt_decl(&mut self) -> Result<PromptDecl, ()> {
        self.expect_soft_keyword("prompt")?;
        let (name, _) = self.expect_ident()?;
        self.expect(&TokenKind::LParen)?;
        let params = self.parse_params()?;
        self.expect(&TokenKind::RParen)?;
        self.expect(&TokenKind::Arrow)?;
        let return_type = self.parse_type()?;
        self.expect(&TokenKind::LBrace)?;
        self.skip_newlines();

        let hint = if self.at_ident("hint") {
            self.advance();
            self.expect(&TokenKind::Colon)?;
            let (s, _) = self.expect_string()?;
            self.expect_term()?;
            self.skip_newlines();
            Some(s)
        } else {
            None
        };

        let suggest = if self.at_ident("suggest") {
            self.advance();
            self.expect(&TokenKind::Colon)?;
            let expr = self.parse_expr()?;
            self.expect_term()?;
            self.skip_newlines();
            Some(expr)
        } else {
            None
        };

        self.expect(&TokenKind::RBrace)?;
        Ok(PromptDecl {
            name,
            params,
            return_type,
            hint,
            suggest,
        })
    }

    // ── Option ───────────────────────────────────────────────────

    fn parse_option_decl(&mut self) -> Result<OptionDecl, ()> {
        self.expect_soft_keyword("option")?;
        let (name, _) = self.expect_ident()?;

        let extends = if self.at_ident("extends") {
            self.advance();
            let (s, _) = self.expect_string()?;
            Some(ttrpg_ast::Name::from(s))
        } else {
            None
        };

        self.expect(&TokenKind::LBrace)?;
        self.skip_newlines();

        let description = if self.at_ident("description") {
            self.advance();
            self.expect(&TokenKind::Colon)?;
            let (s, _) = self.expect_string()?;
            self.expect_term()?;
            self.skip_newlines();
            Some(s)
        } else {
            None
        };

        let default_on = if self.at_ident("default") {
            self.advance();
            self.expect(&TokenKind::Colon)?;
            let val = if self.at_ident("on") {
                self.advance();
                true
            } else if self.at_ident("off") {
                self.advance();
                false
            } else {
                self.error("expected 'on' or 'off' after 'default:'");
                return Err(());
            };
            self.expect_term()?;
            self.skip_newlines();
            Some(val)
        } else {
            None
        };

        let when_enabled = if self.at_ident("when") {
            self.advance();
            self.expect_soft_keyword("enabled")?;
            self.expect(&TokenKind::LBrace)?;
            self.skip_newlines();
            let mut modifies = Vec::new();
            while !matches!(self.peek(), TokenKind::RBrace | TokenKind::Eof) {
                modifies.push(self.parse_modify_clause()?);
                self.skip_newlines();
            }
            self.expect(&TokenKind::RBrace)?;
            self.skip_newlines();
            Some(modifies)
        } else {
            None
        };

        self.expect(&TokenKind::RBrace)?;
        Ok(OptionDecl {
            name,
            extends,
            description,
            default_on,
            when_enabled,
        })
    }

    // ── Move ─────────────────────────────────────────────────────

    fn parse_move_decl(&mut self) -> Result<MoveDecl, ()> {
        self.expect_soft_keyword("move")?;
        let (name, _) = self.expect_ident()?;
        self.expect_soft_keyword("on")?;
        let (receiver_name, _) = self.expect_ident()?;
        self.expect(&TokenKind::Colon)?;
        let receiver_type = self.parse_type()?;
        self.expect(&TokenKind::LParen)?;
        let params = self.parse_params()?;
        self.expect(&TokenKind::RParen)?;
        self.expect(&TokenKind::LBrace)?;
        self.skip_newlines();

        // trigger: STRING
        self.expect_soft_keyword("trigger")?;
        self.expect(&TokenKind::Colon)?;
        let (trigger_text, _) = self.expect_string()?;
        self.expect_term()?;
        self.skip_newlines();

        // roll: expr
        self.expect_soft_keyword("roll")?;
        self.expect(&TokenKind::Colon)?;
        let roll_expr = self.parse_expr()?;
        self.expect_term()?;
        self.skip_newlines();

        // on IDENT block+
        let mut outcomes = Vec::new();
        while self.at_ident("on") {
            let start = self.start_span();
            self.advance(); // on
            let (outcome_name, _) = self.expect_ident()?;
            let body = self.parse_block()?;
            outcomes.push(OutcomeBlock {
                name: outcome_name,
                body,
                span: self.end_span(start),
            });
            self.skip_newlines();
        }

        if outcomes.is_empty() {
            self.error("move declaration requires at least one 'on' outcome block");
            return Err(());
        }

        self.expect(&TokenKind::RBrace)?;
        Ok(MoveDecl {
            name,
            receiver_name,
            receiver_type,
            params,
            trigger_text,
            roll_expr,
            outcomes,
        })
    }

    // ── Table ─────────────────────────────────────────────────────

    fn parse_table_decl(&mut self) -> Result<TableDecl, ()> {
        self.expect_soft_keyword("table")?;
        let (name, _) = self.expect_ident()?;
        self.expect(&TokenKind::LParen)?;
        let params = self.parse_params()?;
        self.expect(&TokenKind::RParen)?;
        self.expect(&TokenKind::Arrow)?;
        let return_type = self.parse_type()?;
        self.expect(&TokenKind::LBrace)?;
        self.skip_newlines();

        let mut entries = Vec::new();
        loop {
            self.skip_newlines();
            if matches!(self.peek(), TokenKind::RBrace | TokenKind::Eof) {
                break;
            }
            entries.push(self.parse_table_entry(params.len())?);
            // Consume optional comma between entries
            if matches!(self.peek(), TokenKind::Comma) {
                self.advance();
            }
            self.skip_newlines();
        }

        if entries.is_empty() {
            self.error("table declaration requires at least one entry");
            return Err(());
        }

        self.expect(&TokenKind::RBrace)?;
        Ok(TableDecl {
            name,
            params,
            return_type,
            entries,
        })
    }

    /// Parse a single table entry: `key => value` or `[key1, key2] => value`.
    fn parse_table_entry(&mut self, param_count: usize) -> Result<TableEntry, ()> {
        let start = self.start_span();

        let keys = if param_count == 1 {
            // Single-key table: `key => value`
            vec![self.parse_table_key()?]
        } else {
            // Multi-key table: `[key1, key2, ...] => value`
            self.expect(&TokenKind::LBracket)?;
            let mut keys = Vec::new();
            keys.push(self.parse_table_key()?);
            while matches!(self.peek(), TokenKind::Comma) {
                self.advance();
                if matches!(self.peek(), TokenKind::RBracket) {
                    break;
                }
                keys.push(self.parse_table_key()?);
            }
            self.expect(&TokenKind::RBracket)?;
            keys
        };

        self.expect(&TokenKind::FatArrow)?;
        let value = self.parse_expr()?;

        let span = self.end_span(start);
        Ok(TableEntry { keys, value, span })
    }

    // ── Unit ─────────────────────────────────────────────────────

    fn parse_unit_decl(&mut self) -> Result<UnitDecl, ()> {
        self.expect_soft_keyword("unit")?;
        let (name, _) = self.expect_ident()?;
        let suffix = if self.at_ident("suffix") {
            self.advance();
            let (s, _) = self.expect_ident()?;
            Some(s.into_inner())
        } else {
            None
        };
        self.expect(&TokenKind::LBrace)?;
        self.skip_newlines();
        let fields = self.parse_field_defs()?;
        self.expect(&TokenKind::RBrace)?;
        Ok(UnitDecl {
            name,
            suffix,
            fields,
        })
    }

    /// Parse a single table key: expression, range (`1..=3`), or wildcard (`_`).
    fn parse_table_key(&mut self) -> Result<Spanned<TableKey>, ()> {
        let start = self.start_span();

        // Wildcard
        if matches!(self.peek(), TokenKind::Underscore) {
            self.advance();
            let span = self.end_span(start);
            return Ok(Spanned {
                node: TableKey::Wildcard,
                span,
            });
        }

        // Parse the expression (might be followed by `..=` for a range)
        let expr = self.parse_expr()?;

        if matches!(self.peek(), TokenKind::DotDotEq) {
            self.advance();
            let end_expr = self.parse_expr()?;
            let span = self.end_span(start);
            Ok(Spanned {
                node: TableKey::Range {
                    start: Box::new(expr),
                    end: Box::new(end_expr),
                },
                span,
            })
        } else {
            let span = self.end_span(start);
            Ok(Spanned {
                node: TableKey::Expr(expr.node),
                span,
            })
        }
    }
}
