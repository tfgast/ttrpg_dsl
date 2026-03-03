# `with_budget` Statement — Function-Provisioned Turn Budgets

## Context

Functions cannot call costed actions because turn budgets are provisioned
exclusively by the host (via `GameState::set_turn_budget()`), with no DSL-level
mechanism to set them up. This forces functions like OSRIC's `resolve_round` to
reimplement action logic using cost-free mechanics instead of calling existing
actions directly.

The action pipeline's cost deduction is also purely advisory — `deduct_budget_field`
uses `saturating_sub(1)`, silently clamping at zero with no enforcement. A host
*can* check budgets manually at the `ActionStarted` gate, but nothing in the
protocol requires it.

This design adds:
1. A `with_budget` statement that provisions a scoped turn budget from DSL code
2. Budget enforcement via synthetic `RequiresCheck` in the cost pipeline
3. Readable `turn` expressions within budget-scoped blocks

## Design

### Syntax

```
with_budget_stmt ::= "with_budget" "(" expr "," "{" budget_fields "}" ")" block
budget_fields    ::= budget_field ("," budget_field)* ","?
budget_field     ::= IDENT ":" expr
```

Examples:
```
with_budget(actor, { attack: 1 }) {
    target.MeleeAttack(actor, weapon)
}

with_budget(actor, { action: 1, bonus_action: 1, movement: actor.speed }) {
    // multiple actions sharing a budget
}
```

### Semantics

`with_budget` establishes a **turn context** — the same context that action,
reaction, and hook resolve blocks operate in, but initiated from a function.

Execution proceeds as:

1. Evaluate entity expression → `EntityRef`
2. Evaluate each budget field expression → `BTreeMap<Name, Value>`
3. Emit `Effect::ProvisionBudget { actor, budget }` — host sets the budget
4. Save `env.turn_actor`, set `env.turn_actor = Some(actor)`
5. Execute body (actions called within deduct from this budget)
6. Restore `env.turn_actor`
7. Emit `Effect::ClearBudget { actor }` — host tears down the budget

Cleanup (steps 6-7) runs on all exit paths, including early returns and errors.

### Turn Readability

Currently `turn` is write-only, accessible only via assignment statements in
action/reaction/hook resolve blocks. `with_budget` establishes a turn context,
so `turn` should be readable within it (and in action resolve blocks too, for
consistency).

`turn` as an expression reads the current actor's budget from state:

```rust
// In eval_expr, when encountering a turn field access:
let actor = env.turn_actor.ok_or("cannot access turn outside turn context")?;
let budget = env.state.read_turn_budget(&actor)
    .ok_or("no turn budget provisioned for actor")?;
// Return the requested field value
```

This enables the 5e interactive loop pattern:
```
with_budget(actor, { action: 1, bonus_action: 1, movement: actor.speed }) {
    let ended = false
    while !ended {
        if turn.action == 0 && turn.bonus_action == 0 && turn.movement == 0 {
            ended = true
        } else {
            let choice = prompt choose_action(actor,
                has_action: turn.action > 0,
                has_bonus_action: turn.bonus_action > 0
            )
            match choice {
                EndTurn => ended = true
                Attack(target) => target.Attack(actor)
                Dash => actor.Dash()
                MoveTo(dest) => actor.MoveTo(dest)
            }
        }
    }
}
```

### Budget Enforcement

Before each cost deduction, the interpreter checks whether the budget field
has sufficient value. If not, it emits a synthetic `RequiresCheck`:

```rust
// In deduct_costs(), before emitting DeductCost for each token:
let current = env.state.read_turn_budget(&actor)
    .and_then(|b| b.get(&budget_field).cloned())
    .unwrap_or(Value::Int(0));

let has_budget = match &current {
    Value::Int(v) => *v > 0,
    _ => true,  // non-int fields: no enforcement
};

if !has_budget {
    let response = env.handler.handle(Effect::RequiresCheck {
        action: action_name.clone(),
        passed: false,
        reason: Some(format!("insufficient budget: {}", token)),
    });
    match response {
        Response::Acknowledged => return Ok(()),  // action fails, no cost spent
        Response::Override(Value::Bool(true)) => {},  // host overrides, proceed
        Response::Override(Value::Bool(false)) => return Ok(()),
        // ... protocol error for other responses
    }
}
```

This reuses the existing `RequiresCheck` gate. The host sees:
```
RequiresCheck { action: "MeleeAttack", passed: false, reason: Some("insufficient budget: attack") }
```

And can:
- `Acknowledge` → action fails (respects the budget)
- `Override(Bool(true))` → action proceeds anyway (host allows overdraft)
- `Override(Bool(false))` → action fails explicitly

This enforcement applies to **all** costed actions, not just those within
`with_budget`. It's a general fix: if the budget says 0, the action shouldn't
silently succeed.

### Nesting

Nested `with_budget` blocks work naturally:

```
with_budget(a, { attack: 1 }) {
    // turn_actor = a, turn reads a's budget
    with_budget(b, { attack: 1 }) {
        // turn_actor = b, turn reads b's budget
        // a's budget is still provisioned in state
    }
    // turn_actor restored to a
    // b's budget cleared
}
// a's budget cleared
```

Each block saves/restores `turn_actor`. Budgets are per-entity in state, so
multiple entities can have budgets simultaneously. `turn` reads whichever
entity is the current `turn_actor`.

Action dispatch (`scoped_execute`) already saves/restores `turn_actor`, so
calling `target.MeleeAttack(actor, ...)` inside a `with_budget(actor, ...)`
correctly deducts from `actor`'s budget (the action's actor is derived from
the receiver, independent of the `with_budget` context).

### Invocation Context

`with_budget` does **not** allocate an invocation ID — it is not an action.
Actions called within the block get their own invocation IDs as usual (via
`scoped_execute`).

### Scope Rules

`with_budget` is allowed in:
- Function resolve blocks (the primary use case)
- Action, reaction, and hook resolve blocks (for completeness)

It is **not** allowed in derive or mechanic blocks (no mutation context).
The checker enforces this via `BlockKind::allows_mutation()`.

## Effect Contract

| Effect | Direction | Fields | Expected Response |
|---|---|---|---|
| `ProvisionBudget` | Interpreter → Host | `actor: EntityRef, budget: BTreeMap<Name, Value>` | `Acknowledged` |
| `ClearBudget` | Interpreter → Host | `actor: EntityRef` | `Acknowledged` |
| `RequiresCheck` (budget) | Interpreter → Host | `action: Name, passed: false, reason: Some(...)` | `Acknowledged` or `Override(Bool)` |

`ProvisionBudget` is a mutation effect — the adapter intercepts it and calls
`state.set_turn_budget(actor, budget)`. If passed through, the host handles
provisioning.

`ClearBudget` is a mutation effect — the adapter calls
`state.clear_turn_budget(actor)`. Requires adding `clear_turn_budget` to
`WritableState`.

## Examples

### OSRIC — Deterministic Segment Resolution

Each combatant gets one pre-declared action per round. Budget is trivial:

```
function resolve_round(initiative: InitiativeResult, actions: list<RoundAction>) {
    for seg in 1..=10 {
        let seg_actions = [a for a in actions if a.segment == seg]

        for action in seg_actions {
            with_budget(action.combatant, { attack: 1 }) {
                match action.action_type {
                    MeleeAttackAction =>
                        action.target.MeleeAttack(action.combatant, action.weapon)
                    MissileAttackAction =>
                        action.target.MissileAttack(action.combatant, action.weapon, action.range)
                    ChargeAction =>
                        action.target.Charge(action.combatant, action.weapon)
                    CastSpellAction =>
                        action.combatant.CastSpell(action.spell, action.targets)
                }
            }
        }
    }
}
```

### D&D 5e — Interactive Multi-Resource Turn

A 5e turn has several independent resource pools. The player chooses freely
until resources run out:

```
function resolve_turn(actor: Character) {
    with_budget(actor, {
        action: 1,
        bonus_action: 1,
        movement: actor.speed,
        free_interaction: 1
    }) {
        let ended = false
        while !ended {
            if turn.action == 0 && turn.bonus_action == 0 && turn.movement == 0 {
                ended = true
            } else {
                let choice = prompt choose_turn_action(
                    actor,
                    has_action: turn.action > 0,
                    has_bonus_action: turn.bonus_action > 0,
                    has_movement: turn.movement > 0
                )
                match choice {
                    EndTurn => ended = true
                    Attack(target) =>
                        actor.Attack(target)             // cost { action }
                    CastSpell(spell) =>
                        actor.Cast(spell)                // cost varies
                    Dash =>
                        actor.Dash()                     // cost { action }
                    Disengage =>
                        actor.Disengage()                // cost { action }
                    BonusAttack(target) =>
                        target.OffhandAttack(actor)      // cost { bonus_action }
                    MoveTo(dest) =>
                        actor.MoveTo(dest)               // cost { movement: distance(actor, dest) }
                }
            }
        }
    }
}
```

Key differences from OSRIC:
- Multiple resource types in one budget
- `turn` is read to determine available actions
- Prompt system drives player choice
- Loop continues until budget exhausted or player ends turn

## Files to Modify

### 1. `crates/ttrpg_ast/src/ast.rs` — AST node

Add `WithBudget` variant to `StmtKind`:

```rust
WithBudget {
    entity: Box<Spanned<ExprKind>>,
    budget_fields: Vec<(Spanned<Name>, Spanned<ExprKind>)>,
    body: Block,
    span: Span,
},
```

### 2. `crates/ttrpg_parser/src/stmt.rs` — Parse `with_budget`

When the parser sees `with_budget`, parse as:
```rust
if self.at_ident("with_budget") {
    return self.parse_with_budget_stmt();
}
```

`parse_with_budget_stmt`:
1. Consume `with_budget`
2. Expect `(`
3. Parse entity expression
4. Expect `,`
5. Expect `{`
6. Parse comma-separated `ident: expr` pairs
7. Expect `}`
8. Expect `)`
9. Parse block body

### 3. `crates/ttrpg_parser/src/lower.rs` — Lowering pass-through

`with_budget` passes through lowering unchanged (no desugaring needed).

### 4. `crates/ttrpg_checker/src/check.rs` — Type checking

- Entity expression must resolve to an entity type
- Budget field names validated against declared turn budget type (or cost tokens)
- Budget field values must be `int`
- Body checked in a `BlockKind` that `allows_mutation()` (same as function body)
- `turn` field access within body returns `int`

### 5. `crates/ttrpg_interp/src/effect.rs` — New effects

```rust
ProvisionBudget {
    actor: EntityRef,
    budget: BTreeMap<Name, Value>,
},
ClearBudget {
    actor: EntityRef,
},
```

Add corresponding `EffectKind` variants.

### 6. `crates/ttrpg_interp/src/eval/stmt.rs` — Statement evaluation

Handle `StmtKind::WithBudget`:
1. Evaluate entity and budget field expressions
2. Emit `ProvisionBudget`
3. Save/restore `turn_actor`
4. Evaluate body
5. Emit `ClearBudget` (on all exit paths)

### 7. `crates/ttrpg_interp/src/eval/expr.rs` — `turn` as expression

When encountering field access on `turn`:
1. Check `env.turn_actor` is set
2. Read budget from `env.state.read_turn_budget()`
3. Return requested field value

### 8. `crates/ttrpg_interp/src/action.rs` — Budget enforcement

In `deduct_costs()`, before emitting `DeductCost`, check budget sufficiency.
If insufficient, emit synthetic `RequiresCheck` with reason. Host can override.

### 9. `crates/ttrpg_interp/src/state.rs` — `WritableState` trait

Add `clear_turn_budget(&mut self, entity: &EntityRef)` method.

### 10. `crates/ttrpg_interp/src/reference_state.rs` — GameState

Implement `clear_turn_budget`: remove entry from `turn_budgets` map.

### 11. `crates/ttrpg_interp/src/adapter.rs` — StateAdapter

Handle `ProvisionBudget` as intercepted mutation: call `state.set_turn_budget()`.
Handle `ClearBudget` as intercepted mutation: call `state.clear_turn_budget()`.
Update `MUTATION_KINDS`.

### 12. `crates/ttrpg_cli/src/effects.rs` — CLI handler

Log `ProvisionBudget` and `ClearBudget` effects.

## Tests

**Parser tests:**
- Parse `with_budget(entity, { field: 1 }) { body }`
- Parse with multiple budget fields
- Parse with trailing comma in budget fields
- Error on missing entity expression
- Error on empty budget fields

**Checker tests:**
- Accept `with_budget` in function body
- Accept `with_budget` in action resolve block
- Reject `with_budget` in derive body
- Reject `with_budget` in mechanic body
- Reject non-entity expression for entity argument
- Reject non-int expressions for budget field values
- Accept `turn.field` reads inside `with_budget` body
- Reject `turn.field` reads outside turn context

**Interpreter tests:**
- `with_budget` provisions budget, action deducts, budget cleared on exit
- Nested `with_budget` for different entities
- Budget enforcement: action with 0 budget fails via `RequiresCheck`
- Budget enforcement: host overrides `RequiresCheck` to allow overdraft
- `turn` readable inside `with_budget`: returns correct field values
- `turn` readable after action deduction: reflects decremented value
- Cleanup on error: budget cleared even if body errors
- `with_budget` inside action resolve block works

**Integration tests:**
- OSRIC pattern: `resolve_round` calls `MeleeAttack` via `with_budget`
- 5e pattern: loop with `turn` reads and prompt-driven action selection
- Budget exhaustion: second action in same budget fails after first consumes it
