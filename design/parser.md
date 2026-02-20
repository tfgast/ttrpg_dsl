# TTRPG DSL Parser — Design Document

## Context

We have a draft spec (`spec/v0/`) for a TTRPG domain-specific language with a complete EBNF grammar, type system, scoping rules, and a full worked example (D&D 5e combat). The goal for this milestone is: **Lexer + Parser → AST** — parse `04_full_example.ttrpg` into a well-typed Rust AST with no semantic analysis yet.

Strategy: Hand-rolled recursive descent parser in a Cargo workspace.

---

## 1. Workspace Layout

```
ttrpg_dsl/
  Cargo.toml                    # workspace root
  spec/v0/                      # spec (existing)
  crates/
    ttrpg_lexer/
      src/
        lib.rs
        token.rs                # Token, TokenKind, DiceFilter
        cursor.rs               # low-level char iteration
        lexer.rs                # RawLexer + filtered Lexer (NL suppression)
    ttrpg_ast/
      src/
        lib.rs
        span.rs                 # Span, Spanned<T>
        ast.rs                  # all AST node types
    ttrpg_parser/
      src/
        lib.rs                  # public parse() entry point
        parser.rs               # Parser struct, helpers (peek/advance/expect/term)
        decl.rs                 # declaration parsing dispatch
        expr.rs                 # expression precedence climbing
        stmt.rs                 # let / assign / expr_stmt
        types.rs                # type annotation parsing
        pattern.rs              # match patterns
      tests/
        integration.rs          # parse full example end-to-end
```

**Dependencies:** `ttrpg_ast` → nothing. `ttrpg_lexer` → `ttrpg_ast` (for `Span`). `ttrpg_parser` → `ttrpg_lexer` + `ttrpg_ast`.

Diagnostics start as a simple struct in `ttrpg_parser` — we can extract a crate later if needed.

---

## 2. Lexer Design

### Token types (`token.rs`)

- **Literals:** `Int(i64)`, `String(String)`, `DiceLit { count, sides, filter }`, `True`, `False`, `None_`
- **Ident:** `Ident(String)` — all soft keywords (`system`, `action`, `resolve`, etc.) lex as Ident
- **Reserved keywords (always keyword tokens):** `Let`, `If`, `Else`, `Match`, `In` — plus `True`, `False`, `None_` (which double as literal token kinds above; they are keyword tokens that represent literal values)
- **Operators/punctuation:** the full set (`+`, `-`, `*`, `/`, `==`, `!=`, `>=`, `<=`, `&&`, `||`, `=>`, `->`, `..`, etc.)
- **Structural:** `Newline`, `Eof`, `Underscore`
- **`Error(String)`** for unrecognized input

### Dice literals

`4d6kh3` is a single token. Disambiguation: after scanning an integer, if the *immediately next character* (no whitespace) is `d` followed by a digit, enter dice-literal mode.

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiceFilter {
    KeepHighest(i64),   // kh3
    KeepLowest(i64),    // kl1
    DropHighest(i64),   // dh1
    DropLowest(i64),    // dl1
}
```

Scanning algorithm:
```
scan_number():
  consume digits → n
  if peek() == 'd' AND peek_next().is_ascii_digit():
    consume 'd'
    consume digits → sides
    if peek_matches("kh" | "kl" | "dh" | "dl"):
      consume 2 chars → filter_kind
      consume digits → filter_count
      return DiceLit { count: n, sides, filter: Some(...) }
    return DiceLit { count: n, sides, filter: None }
  return Int(n)
```

### Newline suppression (`lexer.rs`)

Two-layer design: `RawLexer` emits all tokens including raw NLs. `Lexer` wraps it as an iterator adapter and applies suppression:

1. **Inside `()` and `[]`:** track `paren_depth` / `bracket_depth`, suppress NL when either > 0
2. **After operators/arrows:** `+ - * / || && == != >= <= > < in => = += -=` set `suppress_next_nl = true`
3. **After `{` and `,`:** also set `suppress_next_nl = true`

```rust
pub struct Lexer<'src> {
    raw: RawLexer<'src>,
    paren_depth: u32,
    bracket_depth: u32,
    suppress_next_nl: bool,
}

impl<'src> Iterator for Lexer<'src> {
    type Item = Token;
    fn next(&mut self) -> Option<Token> {
        loop {
            let tok = self.raw.next()?;
            // Update bracket depths
            match tok.kind {
                TokenKind::LParen => self.paren_depth += 1,
                TokenKind::RParen => self.paren_depth = self.paren_depth.saturating_sub(1),
                TokenKind::LBracket => self.bracket_depth += 1,
                TokenKind::RBracket => self.bracket_depth = self.bracket_depth.saturating_sub(1),
                _ => {}
            }
            // Suppress NL?
            if tok.kind == TokenKind::Newline {
                if self.paren_depth > 0 || self.bracket_depth > 0 || self.suppress_next_nl {
                    self.suppress_next_nl = false;
                    continue;
                }
            }
            // Set suppression for next token
            self.suppress_next_nl = matches!(tok.kind,
                TokenKind::Plus | TokenKind::Minus | TokenKind::Star | TokenKind::Slash
                | TokenKind::PipePipe | TokenKind::AmpAmp
                | TokenKind::EqEq | TokenKind::BangEq
                | TokenKind::GtEq | TokenKind::LtEq | TokenKind::Gt | TokenKind::Lt
                | TokenKind::In
                | TokenKind::FatArrow | TokenKind::Arrow
                | TokenKind::Eq | TokenKind::PlusEq | TokenKind::MinusEq
                | TokenKind::LBrace | TokenKind::Comma
            );
            return Some(tok);
        }
    }
}
```

Comments (`//` to EOL) are stripped by the raw lexer. The newline after a comment is preserved.

---

## 3. AST Types (`ttrpg_ast`)

### Core pattern

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: u32,  // byte offset, inclusive
    pub end: u32,    // byte offset, exclusive
}

#[derive(Debug, Clone, PartialEq)]
pub struct Spanned<T> {
    pub node: T,
    pub span: Span,
}

pub type Expr = Spanned<ExprKind>;
pub type Stmt = Spanned<StmtKind>;
pub type Decl = Spanned<DeclKind>;
pub type TypeExpr = Spanned<TypeExprKind>;
pub type Pattern = Spanned<PatternKind>;
```

### Program structure

```rust
pub struct Program {
    pub top_levels: Vec<TopLevel>,
    pub span: Span,
}

pub enum TopLevel {
    Use(UseDecl),
    System(SystemBlock),
}

pub struct UseDecl {
    pub path: Spanned<String>,
    pub span: Span,
}

pub struct SystemBlock {
    pub name: Spanned<String>,
    pub decls: Vec<Decl>,
    pub span: Span,
}
```

### Declarations (12 variants)

```rust
pub enum DeclKind {
    Enum(EnumDecl),
    Struct(StructDecl),
    Entity(EntityDecl),
    Derive(FnDecl),       // derive and mechanic share FnDecl
    Mechanic(FnDecl),
    Action(ActionDecl),
    Reaction(ReactionDecl),
    Condition(ConditionDecl),
    Prompt(PromptDecl),
    Option(OptionDecl),
    Event(EventDecl),
    Move(MoveDecl),
}
```

Key structures:

- **`FnDecl`** — shared by derive/mechanic: `{ name, params, return_type, body }`
- **`ActionDecl`** — `{ name, receiver, params, cost, requires, resolve }`
- **`ReactionDecl`** — `{ name, receiver, trigger, cost, resolve }`
- **`ConditionDecl`** — `{ name, receiver, clauses: Vec<ConditionClause> }`
  - `ConditionClause = Modify(ModifyClause) | Suppress(SuppressClause)`
  - `ModifyStmt` enum: `Let`, `ParamOverride`, `ResultOverride`, `If`

### Expressions

```rust
pub enum ExprKind {
    // Literals
    IntLit(i64),
    StringLit(String),
    BoolLit(bool),
    NoneLit,
    DiceLit { count: i64, sides: i64, filter: Option<DiceFilter> },

    // Identifiers
    Ident(String),

    // Operations
    BinOp { op: BinOp, lhs: Box<Expr>, rhs: Box<Expr> },
    UnaryOp { op: UnaryOp, operand: Box<Expr> },

    // Postfix
    FieldAccess { object: Box<Expr>, field: Spanned<String> },
    Index { object: Box<Expr>, index: Box<Expr> },
    Call { callee: Box<Expr>, args: Vec<Arg> },

    // Compound
    StructLit { name: Spanned<String>, fields: Vec<StructFieldInit> },
    ListLit(Vec<Expr>),
    Paren(Box<Expr>),

    // Control flow (expressions)
    If { condition: Box<Expr>, then_block: Block, else_branch: Option<ElseBranch> },
    PatternMatch { scrutinee: Box<Expr>, arms: Vec<PatternArm> },
    GuardMatch { arms: Vec<GuardArm> },
}
```

### Patterns

```rust
pub enum PatternKind {
    Wildcard,                                          // _
    IntLit(i64),                                       // 42
    StringLit(String),                                 // "foo"
    BoolLit(bool),                                     // true, false
    Ident(String),                                     // bare: binding or variant (semantic)
    QualifiedVariant { enum_name, variant },            // Ability.STR
    QualifiedDestructure { enum_name, variant, fields }, // ResolvedDamage.hit(amount)
    BareDestructure { name, fields },                   // hit(amount)
}
```

### Types

```rust
pub enum TypeExprKind {
    Int, Bool, String_, Float,
    DiceExpr, RollResult, TurnBudget, Duration, Position, Condition,
    Named(String),                        // user-defined
    Map(Box<TypeExpr>, Box<TypeExpr>),
    List(Box<TypeExpr>),
    Set(Box<TypeExpr>),
    Option_(Box<TypeExpr>),
    Resource(Box<Expr>, Box<Expr>),       // resource(min..max)
}
```

---

## 4. Parser Architecture

### Core struct

```rust
pub struct Parser<'src> {
    tokens: Vec<Token>,       // pre-collected from lexer
    pos: usize,
    source: &'src str,
    diagnostics: Vec<Diagnostic>,
}
```

Pre-collecting tokens makes lookahead trivial (just index into the vec).

### Key helpers

- `peek()` / `at(kind)` / `at_ident(name)` — non-consuming lookahead
- `advance()` — consume and return token
- `expect(kind)` / `expect_ident()` / `expect_soft_keyword(kw)` — consume or error
- `expect_term()` — consume NL, or succeed on lookahead `}` / EOF
- `skip_newlines()` — consume consecutive NL tokens
- `start_span()` / `end_span(start)` — span tracking
- `peek_at(n)` — look n tokens ahead (for struct literal disambiguation)

### Disambiguation strategies

**Struct literal vs block:**
When we see `IDENT LBrace` in primary_expr, peek ahead:
- If `pos+2` is `IDENT` and `pos+3` is `Colon` → struct literal
- If `pos+2` is `RBrace` → empty struct literal
- Otherwise → just the identifier (don't consume the brace)

**Match: guard vs pattern:**
After consuming `match`, if next is `LBrace` → guard match. Otherwise parse expression (scrutinee), then `LBrace` → pattern match.

**assign vs expr_stmt:**
Parse expression first. If followed by `=`/`+=`/`-=`, convert expr to LValue (validate: only idents, field access, indexing). Otherwise expr_stmt.

**Named arguments:**
In `parse_arg_list`, two-token lookahead: if `IDENT Colon` → named arg. Otherwise positional.

**Modify statements:**
Dispatch: `let` → Let, `result .` → ResultOverride, `IDENT =` → ParamOverride, `if` → conditional.

### Expression precedence climbing (`expr.rs`)

8 levels, low → high: `||`, `&&`, comparison, `in`, `+ -`, `* /`, unary (`! -`), postfix (`. [] ()`).

Each level is a function that calls the next-higher level for operands:

```rust
fn parse_or_expr()  → calls parse_and_expr()
fn parse_and_expr() → calls parse_cmp_expr()
fn parse_cmp_expr() → calls parse_in_expr()   // non-repeating (a < b < c is not valid)
fn parse_in_expr()  → calls parse_add_expr()   // non-repeating
fn parse_add_expr() → calls parse_mul_expr()
fn parse_mul_expr() → calls parse_unary_expr()
fn parse_unary_expr() → calls parse_postfix_expr()
fn parse_postfix_expr() → calls parse_primary_expr(), then loops on . [] ()
```

### Declaration dispatch (`decl.rs`)

Match on `self.peek()` as `Ident(s)` and dispatch by soft keyword string to the appropriate parse function.

### Design notes

- `ResolvedDamage.hit(final_dmg)` parses as `Call { callee: FieldAccess { Ident, "hit" }, args }` — semantic analysis (future) distinguishes constructors from method calls
- `turn` lexes as `Ident("turn")`, no special parser treatment — semantic analysis validates context
- `option` in type position (followed by `<`) vs declaration position (followed by `IDENT`) — called from different parser paths, no ambiguity

---

## 5. Build Phases

### Phase 1: Foundation
- Create workspace `Cargo.toml` and 3 crate stubs
- Implement `Span`, `Spanned<T>` in `ttrpg_ast`
- Define `TokenKind`, `Token`, `DiceFilter` in `ttrpg_lexer`
- Implement `Cursor` in `ttrpg_lexer`
- Define basic `Diagnostic` struct in `ttrpg_parser`

### Phase 2: Lexer
- Implement `RawLexer` (whitespace, comments, newlines, all operators, reserved keywords, identifiers, integers, dice literals, strings, `_`)
- Implement `Lexer` wrapper with NL suppression
- **Verify:** lex `04_full_example.ttrpg` — no Error tokens

### Phase 3: AST + Parser skeleton
- Define all AST types
- Implement `Parser` struct with all helpers
- `parse_program()`, `parse_top_level()`
- `parse_type()`
- Expression parsing (all precedence levels, primary exprs except struct lit and match)
- Statement + block parsing
- **Verify:** parse `derive modifier(score: int) -> int { floor((score - 10) / 2) }`

### Phase 4: Simple declarations
- `parse_enum_decl()`, `parse_struct_decl()`, `parse_entity_decl()`
- `parse_derive_decl()`, `parse_mechanic_decl()`
- `parse_params()` with defaults
- **Verify:** parse all enums, structs, entities, derives, mechanics from full example

### Phase 5: Complex expressions
- Struct literal parsing with lookahead disambiguation
- `parse_if_expr()` with else/else-if
- `parse_match_expr()` (guard + pattern match)
- `parse_pattern()` (all 6 pattern kinds)
- Named argument parsing
- **Verify:** parse `d20_expr`, `choose_attack_ability`, `resolve_melee_attack`

### Phase 6: Remaining declarations
- `parse_action_decl()` (cost, requires, resolve)
- `parse_reaction_decl()` — trigger uses a dedicated `parse_trigger_expr()` matching the grammar's `trigger_expr = IDENT "(" trigger_bindings ")"`, NOT generic expression parsing
- `parse_event_decl()`
- `parse_condition_decl()` (modify + suppress clauses)
- `parse_prompt_decl()`, `parse_option_decl()`, `parse_move_decl()`
- **Verify:** parse the **complete** `04_full_example.ttrpg` with zero errors

### Phase 7: Error reporting polish
- Source map for line/column rendering
- Rustc-style diagnostic output with carets and context
- Basic error recovery: on declaration error, skip to next soft keyword; on statement error, skip to NL/`}`

---

## 6. Verification

- **Unit tests per phase** — each lexer token variant, each parser production
- **Integration test:** parse `spec/v0/04_full_example.ttrpg` → no errors, correct structure (1 system block with 5 enums, 2 structs, 2 entities, 4 derives, 6 mechanics, 4 actions, 1 event, 1 reaction, 3 conditions, 2 prompts)
- **Standalone declaration tests:** `option_decl` and `move_decl` are not present in the full example — test with dedicated snippets:

  ```ttrpg
  option CritFumbles {
      description: "Natural 1 causes a fumble effect"
      default: on
      when enabled {
          modify attack_roll(attacker: attacker) {
              mode = disadvantage
          }
      }
  }
  ```

  ```ttrpg
  move GoAggro on actor: Character (target: Character) {
      trigger: "threaten with force"
      roll: 2d6 + actor.stats[Hard]
      on strong_hit {
          target.HP -= 3
      }
      on weak_hit {
          target.HP -= 1
      }
      on miss {
          actor.HP -= 1
      }
  }
  ```
- **Error tests:** intentionally broken input produces correct diagnostics
- **Lexer-specific:** dice vs int disambiguation, NL suppression in all 3 rules, soft keywords as Ident

---

## Critical Spec Files

| File | Role |
|------|------|
| `spec/v0/03_canonical_grammar.ttrpg` | Complete EBNF — every parser production must match this |
| `spec/v0/04_full_example.ttrpg` | Acceptance test — parser must handle this with zero errors |
| `spec/v0/01_type_system.ttrpg` | Informs AST design for types, dice, coercion |
| `spec/v0/02_scoping.ttrpg` | Informs action/reaction/condition AST structure |
