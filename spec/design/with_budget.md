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

Additionally, `deduct_budget_field` auto-materializes budget entries via
`write_turn_field`'s `.entry().or_default()` pattern — calling it on an entity
with no provisioned budget creates a zero-valued entry. This matters because
enforcement must distinguish explicitly-provisioned budgets from entries that
exist only as artifacts of deduction.

This design adds:
1. A `with_budget` statement that provisions a scoped turn budget from DSL code
2. Budget enforcement via synthetic `RequiresCheck` in the cost pipeline
3. Readable `turn` expressions within budget-scoped blocks
4. A `cost_payer` field on `Env` to decouple "who pays" from "who acts"

## Design

### Syntax

```
with_budget_stmt ::= "with_budget" "(" expr "," "{" budget_fields "}" ")" block
budget_fields    ::= budget_field ("," budget_field)* ","?
budget_field     ::= IDENT ":" expr
```

Examples:
```
// Standard — actor performs action, pays from own budget
with_budget(actor, { attack: 1 }) {
    actor.MeleeAttack(target, weapon)
}

// Summoning — minion performs action, master pays from master's budget
with_budget(wizard, { action: 1 }) {
    skeleton.MeleeAttack(target, weapon)
}

// Multiple resource pools sharing a budget
with_budget(actor, { action: 1, bonus_action: 1, movement: actor.speed }) {
    // ...
}
```

### Semantics

`with_budget` establishes a **turn context** — the same context that action,
reaction, and hook resolve blocks operate in, but initiated from a function.

Execution proceeds as:

1. Evaluate entity expression → `EntityRef`
2. Evaluate each budget field expression → `BTreeMap<Name, Value>`
3. Read and save any existing budget for this entity (`prev_budget`)
4. Snapshot current `env.turn_actor` (`prev_turn_actor`)
5. Snapshot current `env.cost_payer` (`prev_cost_payer`)
6. Emit `Effect::ProvisionBudget { actor, budget }` — adapter applies state mutation
7. **Only on success:** Set `env.turn_actor = Some(actor)` and `env.cost_payer = Some(actor)`
8. Execute body (actions called within deduct from this budget)
9. Restore `env.cost_payer = prev_cost_payer`
10. Restore `env.turn_actor = prev_turn_actor`
11. If `prev_budget` was `Some(old)`: emit `ProvisionBudget { actor, budget: old }` (restore)
    If `prev_budget` was `None`: emit `ClearBudget { actor }` (teardown)

Cleanup (steps 9-11) runs on all exit paths, including early returns and errors.

**Implementation pattern:** Use a closure-based scope helper rather than RAII,
since cleanup involves fallible effect emission that `Drop` cannot propagate:

```rust
fn scoped_budget<F, R>(
    env: &mut Env,
    actor: EntityRef,
    budget: BTreeMap<Name, Value>,
    body: F,
) -> Result<R, RuntimeError>
where
    F: FnOnce(&mut Env) -> Result<R, RuntimeError>,
{
    // ── Snapshot (read-only — no env mutation yet) ──
    let prev_budget = env.state.read_turn_budget(&actor);
    let prev_turn_actor = env.turn_actor;
    let prev_cost_payer = env.cost_payer;

    // ── Provision (may fail — env is still untouched) ──
    let provision_resp = env.handler.handle(Effect::ProvisionBudget {
        actor, budget,
    });
    if !matches!(provision_resp, Response::Acknowledged) {
        // Early return is safe: env fields are unchanged, no cleanup needed.
        return Err(protocol_error!("ProvisionBudget expects Acknowledged"));
    }

    // ── Enter (only after successful provisioning) ──
    env.turn_actor = Some(actor);
    env.cost_payer = Some(actor);

    // ── Body ──
    let body_result = body(env);

    // ── Exit (always runs) ──
    env.cost_payer = prev_cost_payer;
    env.turn_actor = prev_turn_actor;

    let cleanup_result = match prev_budget {
        Some(old) => {
            let r = env.handler.handle(Effect::ProvisionBudget {
                actor, budget: old,
            });
            match r {
                Response::Acknowledged => Ok(()),
                _ => Err(protocol_error!("ProvisionBudget expects Acknowledged")),
            }
        }
        None => {
            let r = env.handler.handle(Effect::ClearBudget { actor });
            match r {
                Response::Acknowledged => Ok(()),
                _ => Err(protocol_error!("ClearBudget expects Acknowledged")),
            }
        }
    };

    // ── Error precedence ──
    match (body_result, cleanup_result) {
        (Err(body_err), Err(cleanup_err)) => {
            // Body error wins; log cleanup failure as warning
            tracing::warn!("cleanup error suppressed: {cleanup_err}");
            Err(body_err)
        }
        (Err(body_err), Ok(())) => Err(body_err),
        (Ok(_), Err(cleanup_err)) => Err(cleanup_err),
        (Ok(val), Ok(())) => Ok(val),
    }
}
```

Error precedence rules:
- **Body succeeds, cleanup succeeds:** Return body value.
- **Body fails, cleanup succeeds:** Return body error.
- **Body succeeds, cleanup fails:** Return cleanup error (protocol violation).
- **Body fails, cleanup fails:** Return body error; log cleanup error as warning.

### Cost Charging Rule

In most cases, the entity that performs an action is the same entity whose
budget pays for it — a fighter attacks, a fighter's attack budget is charged.
`with_budget` sets both `turn_actor` and `cost_payer` to the budgeted entity,
and `scoped_execute` sets `turn_actor` to the receiver, so when the receiver
is the budgeted entity (the common case), everything aligns naturally.

The exception is **summoning and similar delegation patterns**, where one
entity acts but another entity's budget pays. For example, a wizard spends
their action to command a skeleton to attack — the skeleton is the action's
receiver, but the wizard's budget is charged. To support this, `cost_payer`
persists independently of `turn_actor` through nested action dispatches.

`with_budget` sets both `turn_actor` and `cost_payer` to the budgeted entity.
`scoped_execute` (the existing action dispatch wrapper) **is unchanged** — it
continues to save/restore and set `turn_actor` to the action's receiver, and
it does not touch `cost_payer`.

In `deduct_costs`, the payer is resolved as:
```rust
let payer = env.cost_payer.unwrap_or_else(|| env.turn_actor.expect("no turn context"));
```

This means:
- **With `with_budget`:** `cost_payer` is set → costs charged to the budgeted entity.
- **Without `with_budget`:** `cost_payer` is `None` → falls back to `turn_actor`
  (the receiver, set by `scoped_execute`), preserving existing behavior.

`scoped_execute` does not touch `cost_payer`, so it persists through the entire
`with_budget` block, including across nested action dispatches.

#### State Transition Tables

These tables show `turn_actor` and `cost_payer` at each transition point.
Test cases should verify each row.

**Standard pattern — receiver = payer (OSRIC, 5e, most systems):**

| Execution Point | `turn_actor` | `cost_payer` | Transition |
|---|---|---|---|
| Before `with_budget(combatant, ...)` | prev | prev | — |
| Enter `with_budget` body | combatant | Some(combatant) | with_budget sets both |
| Enter `combatant.MeleeAttack(target, ...)` | combatant | Some(combatant) | scoped_execute: turn_actor stays same |
| `deduct_costs` resolves payer | — | **combatant** | cost_payer = turn_actor (same entity) |
| After action returns | combatant | Some(combatant) | scoped_execute restores turn_actor |
| After `with_budget` exits | prev | prev | with_budget restores both |

**Summoning pattern — receiver ≠ payer:**

| Execution Point | `turn_actor` | `cost_payer` | Transition |
|---|---|---|---|
| Before `with_budget(wizard, ...)` | prev | prev | — |
| Enter `with_budget` body | wizard | Some(wizard) | with_budget sets both |
| Enter `skeleton.MeleeAttack(target, ...)` | skeleton | Some(wizard) | scoped_execute sets turn_actor |
| `deduct_costs` resolves payer | — | **wizard** | cost_payer wins over turn_actor |
| After action returns | wizard | Some(wizard) | scoped_execute restores turn_actor |
| After `with_budget` exits | prev | prev | with_budget restores both |

**Nested with_budget — different entities:**

| Execution Point | `turn_actor` | `cost_payer` | Transition |
|---|---|---|---|
| Enter outer `with_budget(A, ...)` | A | Some(A) | — |
| Enter inner `with_budget(B, ...)` | B | Some(B) | Inner saves A's state |
| Enter `B.Action(target, ...)` | B | Some(B) | scoped_execute: turn_actor stays same |
| `deduct_costs` resolves payer | — | **B** | cost_payer from inner scope |
| After action returns | B | Some(B) | scoped_execute restores |
| After inner `with_budget` exits | A | Some(A) | Inner restores outer state |
| After outer `with_budget` exits | prev | prev | Outer restores original state |

Walkthrough with OSRIC (standard pattern):
```
with_budget(attacker, { attack: 1 }) {
    // turn_actor = attacker, cost_payer = Some(attacker)

    attacker.MeleeAttack(target, weapon)
    // scoped_execute: turn_actor = attacker (same entity — receiver = budgeted entity)
    //   deduct_costs: payer = cost_payer = attacker → charges attacker ✓
    //   resolve block: turn reads attacker's budget ✓
    // scoped_execute restores turn_actor=attacker
}
```

Walkthrough with summoning (receiver ≠ payer):
```
with_budget(wizard, { action: 1 }) {
    // turn_actor = wizard, cost_payer = Some(wizard)

    skeleton.MeleeAttack(target, weapon)
    // scoped_execute saves turn_actor=wizard, sets turn_actor=skeleton
    //   deduct_costs: payer = cost_payer = wizard → charges wizard ✓
    //   resolve block: turn_actor = skeleton (skeleton's context)
    // scoped_execute restores turn_actor=wizard
}
```

For 5e-style actions (also standard pattern):

```
with_budget(actor, { action: 1 }) {
    // turn_actor = actor, cost_payer = Some(actor)

    actor.Attack(target)
    // scoped_execute: turn_actor = actor (same entity)
    //   deduct_costs: payer = cost_payer = actor ✓
    //   resolve block: turn reads actor's budget ✓
}
```

**Migration from current behavior:** `scoped_execute` is unchanged. The new
`cost_payer` field defaults to `None`. `deduct_costs` changes from using its
explicit `actor` parameter to using the resolved payer. Without `with_budget`,
`cost_payer` is `None` and the fallback is `turn_actor` (which `scoped_execute`
sets to the receiver) — identical to current behavior.

Changes to `deduct_costs`:
- Remove the `actor: &EntityRef` parameter.
- Resolve payer from `env.cost_payer.or(env.turn_actor)`.
- Return `Result<CostOutcome, RuntimeError>` instead of `Result<(), RuntimeError>`
  (see Budget Enforcement section).
- Pass payer as `DeductCost.actor` instead of the receiver.

Changes to `execute_pipeline`:
- No longer passes explicit actor to `deduct_costs`.
- Checks `CostOutcome` return: on `ActionFailed`, returns `Ok(Value::None)`
  (matching the existing pattern for `RequiresCheck` failure).

### Turn Readability

Currently `turn` is write-only, accessible only via assignment statements in
action/reaction/hook resolve blocks. `with_budget` establishes a turn context,
so `turn` should be readable within it (and in action resolve blocks too, for
consistency).

**Checker model:**

A new `BlockKind::WithBudget` is added to `scope.rs`:
```rust
BlockKind::WithBudget
```

Permissions for `WithBudget`:
| Method | Result | Rationale |
|---|---|---|
| `allows_turn()` | `true` | Budget is provisioned |
| `allows_mutation()` | `true` | Inherits from enclosing function body |
| `allows_invocation()` | `false` | Not an action — no invocation ID |
| `allows_emit()` | `true` | Inherits from enclosing function body |
| `allows_calls()` | `true` | Can call actions, functions, etc. |

Within the `with_budget` body, `turn` is bound as `Ty::TurnBudget` with
`mutable: true`. Field access on `TurnBudget` is **statically validated**
against the system's declared `TurnBudget` struct fields (or the hardcoded
defaults if no declaration exists), using the existing `check_expr.rs` logic
at the `Ty::TurnBudget` branch.

**Two-phase evaluation model:**

`turn` is a keyword, not a user-bindable identifier. Its availability is
validated in two phases:

1. **Checker (lexical):** `BlockKind::allows_turn()` determines whether `turn`
   is in scope. The checker binds `turn` as `Ty::TurnBudget` in blocks where
   it is allowed, and rejects `turn` references elsewhere. This is purely
   lexical — no runtime state is consulted.

2. **Runtime (backing):** When the evaluator encounters a `turn.field` access,
   it resolves the lexical `turn` binding to its runtime backing via
   `env.turn_actor`. The turn actor identifies which entity's budget to read.
   This two-phase model means the checker guarantees `turn` is structurally
   valid, and the runtime provides the actual values.

**Runtime mechanism:**

`turn.field` as an expression reads the current actor's budget from state:

```rust
// In the field-access evaluator, when base is the lexical `turn` binding:
let actor = env.turn_actor.ok_or("cannot access turn outside turn context")?;
let budget = env.state.read_turn_budget(&actor)
    .ok_or("no turn budget provisioned for actor")?;
budget.get(&field_name)
    .cloned()
    .ok_or_else(|| format!("turn budget has no field '{}'", field_name))
```

Note: `turn.field` reads reference `turn_actor`, not `cost_payer`. Inside an
action resolve block called from `with_budget`, `turn_actor` is the receiver
(set by `scoped_execute`). If the receiver has a provisioned budget, `turn`
reads succeed. If not (e.g., summoning where the minion is the receiver but
the master's budget is provisioned), `turn` reads in the resolve block would
error — but this is expected, since the resolve block's `turn` context is the
receiver's, not the payer's.

**Turn access matrix:**

| Context | `turn.field` read | `turn.field = expr` write |
|---|---|---|
| `with_budget` body | Yes | Yes |
| Action resolve block | Yes | Yes |
| Reaction resolve block | Yes | Yes |
| Hook resolve block | Yes | Yes |
| Function body (no `with_budget`) | Error: no turn context | Error: no turn context |
| Derive body | Error: no turn context | Error: no mutation |
| Mechanic body | Error: no turn context | Error: no mutation |

This enables the interactive loop pattern:
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
                Attack(target) => actor.Attack(target)
                Dash => actor.Dash()
                MoveTo(dest) => actor.MoveTo(dest)
            }
        }
    }
}
```

### Budget Enforcement

Before cost deduction, the interpreter checks whether all budget fields have
sufficient values. Enforcement only applies when a budget exists for the
payer — if no budget is provisioned (e.g., host-managed turns or systems that
don't use budgets), cost deduction proceeds as before with no enforcement.

**Important:** Enforcement eligibility is determined by whether `read_turn_budget`
returns `Some` for the payer entity. To prevent false enforcement from
auto-materialized entries, `deduct_budget_field` must be updated to skip writes
when no budget exists or when the field is absent (see Backward Compatibility).

**Return type:** `deduct_costs` returns `Result<CostOutcome, RuntimeError>`
rather than `Result<(), RuntimeError>`:

```rust
enum CostOutcome {
    /// All budget checks passed (or no enforcement applies). Proceed with resolve block.
    Proceed,
    /// Budget insufficient and host acknowledged failure. Skip resolve block.
    ActionFailed,
}
```

`execute_pipeline` checks this outcome:
```rust
if let Some(ref eff) = effective_cost {
    match deduct_costs(env, eff, call_span)? {
        CostOutcome::Proceed => {},
        CostOutcome::ActionFailed => return Ok(Value::None),
    }
}
```

This matches the existing pattern where `RequiresCheck` failure returns
`Ok(Value::None)` to signal the action ended without executing.

**Pre-check phase:** To prevent partial deductions (where some cost tokens are
deducted before a later token fails the budget check), enforcement runs as a
pre-check across ALL cost tokens before any `DeductCost` effects are emitted:

```rust
// In deduct_costs(), before the deduction loop:
let payer = env.cost_payer.unwrap_or_else(|| env.turn_actor.expect("no turn context"));

if let Some(budget) = env.state.read_turn_budget(&payer) {
    for token in &cost.tokens {
        let budget_field = resolve_cost_token(&token.node)?;
        if let Some(current) = budget.get(&budget_field) {
            let current_int = match current {
                Value::Int(v) => *v,
                other => return Err(runtime_error!(
                    "budget field '{}' has non-integer value: {:?}",
                    budget_field, other
                )),
            };
            let required = 1;  // 1 for bare tokens; evaluated expr for `token: expr`

            if current_int < required {
                let response = env.handler.handle(Effect::RequiresCheck {
                    action: action_name.clone(),
                    passed: false,
                    reason: Some(format!(
                        "insufficient budget: {} requires {} but {} has {}",
                        budget_field, required, budget_field, current_int
                    )),
                });
                match response {
                    Response::Acknowledged => return Ok(CostOutcome::ActionFailed),
                    Response::Override(Value::Bool(true)) => {},  // host allows overdraft
                    Response::Override(Value::Bool(false)) => {
                        return Ok(CostOutcome::ActionFailed);
                    }
                    other => return Err(protocol_error!(
                        "RequiresCheck expects Acknowledged or Override(Bool), got {:?}",
                        other
                    )),
                }
            }
        }
        // Field not in budget: no enforcement for this cost type
    }
}
// No budget at all: no enforcement (backward compatible)

// All checks passed — proceed with deduction loop
for token in &cost.tokens {
    // ... emit DeductCost effects as before ...
}
Ok(CostOutcome::Proceed)
```

This reuses the existing `RequiresCheck` gate. The host sees:
```
RequiresCheck { action: "MeleeAttack", passed: false, reason: Some("insufficient budget: attack requires 1 but attack has 0") }
```

And can:
- `Acknowledge` → action fails (respects the budget)
- `Override(Bool(true))` → action proceeds anyway (host allows overdraft)
- `Override(Bool(false))` → action fails explicitly

### Nesting

`with_budget` supports nesting, including for the same entity. Each scope
saves the previous budget, `turn_actor`, and `cost_payer`, restoring them on exit.

**Different entities** (common case):
```
with_budget(a, { attack: 1 }) {
    // turn_actor = a, cost_payer = a, turn reads a's budget
    with_budget(b, { attack: 1 }) {
        // turn_actor = b, cost_payer = b, turn reads b's budget
        // a's budget still exists in state (untouched)
    }
    // turn_actor restored to a, cost_payer restored to a
    // b's budget cleared (b had no prior budget)
}
// a's budget cleared
```

**Same entity** (re-scoping):
```
with_budget(a, { attack: 2 }) {
    // a's budget: { attack: 2 }
    a.MeleeAttack(target, weapon)   // deducts 1, budget now { attack: 1 }

    with_budget(a, { spell: 1 }) {
        // a's previous budget { attack: 1 } saved
        // a's budget now: { spell: 1 }
        a.CastSpell(spell)           // deducts spell
    }
    // a's budget restored to { attack: 1 }
    a.MeleeAttack(target2, weapon)   // deducts 1, budget now { attack: 0 }
}
// a's budget cleared
```

Budgets are per-entity in state. `turn` reads whichever entity is the current
`turn_actor`. `cost_payer` determines who is charged for action costs. The
save/restore mechanism ensures that nesting cannot corrupt the outer scope.

### Invocation Context

`with_budget` does **not** allocate an invocation ID — it is not an action.
Actions called within the block get their own invocation IDs as usual (via
`scoped_execute`).

### Scope Rules

`with_budget` is allowed in:
- Function bodies (the primary use case)
- Action, reaction, and hook resolve blocks (for completeness)

It is **not** allowed in:
- **Derive blocks:** No mutation context; derives are pure computation.
- **Mechanic blocks:** No mutation context; mechanics may roll dice but cannot mutate state.
- **Condition blocks:** Declarative modifier overlays; no imperative execution.
- **Prompt blocks:** Pure decision points; no state effects.

The checker enforces this via `BlockKind::allows_mutation()` — all four
disallowed block kinds return `false` for mutation.

### Budget Field Validation

Budget field names are validated against the system's **`TurnBudget` declaration**,
aligning with the existing schema-driven cost token model.

**Canonical names vs aliases:**

`with_budget` map keys and `turn.field` reads always use **canonical field names** —
the names declared on the `TurnBudget` struct. No alias resolution applies at
these layers.

Aliases (e.g., `action` → `actions`) apply only at the **cost token resolution
layer** (`resolve_cost_token`), which maps cost clause tokens in action
declarations to canonical budget field names. This separation keeps the
provisioning and reading paths simple and unambiguous.

- **At check time:** Budget field names must correspond to fields declared on
  `TurnBudget` (or the hardcoded defaults if no declaration exists). Budget
  field value expressions must be `int`-typed. Non-canonical names are rejected.
- **At runtime:** Fields exist as provisioned. `resolve_cost_token()` maps cost
  tokens to budget field names (including legacy aliases). If an action costs
  a field not present in the entity's budget, no enforcement applies (the field
  is simply absent).

Systems needing non-default budget fields (e.g., OSRIC's `attack`) declare a
custom `TurnBudget`:
```
struct TurnBudget {
    attack: int
}
```

This is consistent with the existing model where `resolve_cost_token` and
`valid_cost_tokens` derive their field sets from the `TurnBudget` declaration.

## Canonical Effect Sequences

### Success: action deducts from budget
```
ProvisionBudget { actor: A, budget: { attack: 1 } }          → Acknowledged
  ActionStarted { name: MeleeAttack, actor: A }               → Acknowledged
  RequiresCheck { action: MeleeAttack, passed: true }          → Acknowledged
  [Budget pre-check: A.attack (1) >= 1 — passes]
  DeductCost { actor: A, token: attack, budget_field: attack } → Acknowledged
  [Resolve block executes]
  ActionCompleted { name: MeleeAttack, actor: A, outcome: Succeeded }  → Acknowledged
ClearBudget { actor: A }                                       → Acknowledged
```

### Budget exhausted: enforcement rejects action
```
ProvisionBudget { actor: A, budget: { attack: 0 } }          → Acknowledged
  ActionStarted { name: MeleeAttack, actor: A }               → Acknowledged
  RequiresCheck { action: MeleeAttack, passed: true }          → Acknowledged
  [Budget pre-check: A.attack (0) < 1 — fails]
  RequiresCheck { action: MeleeAttack, passed: false,
    reason: "insufficient budget: attack requires 1 but attack has 0" }
                                                               → Acknowledged
  [CostOutcome::ActionFailed — no cost spent, no resolve block]
  ActionCompleted { name: MeleeAttack, actor: A, outcome: Failed }  → Acknowledged
ClearBudget { actor: A }                                       → Acknowledged
```

### Host-approved overdraft
```
ProvisionBudget { actor: A, budget: { attack: 0 } }          → Acknowledged
  ActionStarted { name: MeleeAttack, actor: A }               → Acknowledged
  RequiresCheck { action: MeleeAttack, passed: true }          → Acknowledged
  [Budget pre-check: A.attack (0) < 1 — fails]
  RequiresCheck { action: MeleeAttack, passed: false,
    reason: "insufficient budget: attack requires 1 but attack has 0" }
                                                               → Override(Bool(true))
  [Host allows overdraft — pre-check continues]
  DeductCost { actor: A, token: attack, budget_field: attack } → Acknowledged
  [A.attack now -1 (saturating to 0 in state)]
  [Resolve block executes]
  ActionCompleted { name: MeleeAttack, actor: A, outcome: Succeeded }  → Acknowledged
ClearBudget { actor: A }                                       → Acknowledged
```

### Body error: cleanup still runs
```
ProvisionBudget { actor: A, budget: { attack: 1 } }          → Acknowledged
  [Body encounters runtime error]
ClearBudget { actor: A }                                       → Acknowledged
[Original error propagated]
```

### Body error + cleanup protocol error: error precedence
```
ProvisionBudget { actor: A, budget: { attack: 1 } }          → Acknowledged
  [Body encounters runtime error: "division by zero"]
ClearBudget { actor: A }                                       → Override(unexpected)
[Warning logged: "cleanup error suppressed: ClearBudget expects Acknowledged"]
[Original "division by zero" error propagated — body error wins]
```

### Same-entity nested: inner restores outer budget
```
ProvisionBudget { actor: A, budget: { attack: 2 } }          → Acknowledged
  DeductCost { actor: A, token: attack, budget_field: attack } → Acknowledged
  [A.attack now 1]
  ProvisionBudget { actor: A, budget: { spell: 1 } }          → Acknowledged
    DeductCost { actor: A, token: spell, budget_field: spell } → Acknowledged
  ProvisionBudget { actor: A, budget: { attack: 1 } }          → Acknowledged  [restore]
  DeductCost { actor: A, token: attack, budget_field: attack } → Acknowledged
  [A.attack now 0]
ClearBudget { actor: A }                                       → Acknowledged
```

## Effect Contract

| Effect | Direction | Fields | Expected Response | Invalid Response |
|---|---|---|---|---|
| `ProvisionBudget` | Interpreter → Host | `actor: EntityRef, budget: BTreeMap<Name, Value>` | `Acknowledged` | Protocol error |
| `ClearBudget` | Interpreter → Host | `actor: EntityRef` | `Acknowledged` | Warning during cleanup after body error, protocol error otherwise |
| `RequiresCheck` (budget) | Interpreter → Host | `action: Name, passed: false, reason: Some(...)` | `Acknowledged` or `Override(Bool)` | Protocol error |

`ProvisionBudget` and `ClearBudget` are **adapter-intercepted mutation effects**.
The adapter always applies the state mutation (`state.set_turn_budget()` or
`state.clear_turn_budget()`) before forwarding the effect to the host. This is
mandatory — enforcement and `turn.field` reads depend on interpreter-visible
state, so the adapter must be the single source of truth for budget state. The
host receives the effect for observation (logging, UI) but cannot prevent the
state mutation. This is consistent with how `DeductCost` and other mutation
effects are handled.

`RequiresCheck` (budget variant) follows the existing `RequiresCheck` protocol.
`Acknowledged` or `Override(Bool)` are the expected responses. Any other
response is a protocol error.

## Backward Compatibility

Budget enforcement is a new behavior but is designed to be backward compatible:

- **No budget provisioned:** If no budget exists for the payer (the common case
  before this feature), enforcement is skipped entirely. Existing systems that
  call costed actions without provisioning budgets are unaffected.
- **Budget exists:** If a budget IS provisioned (via `with_budget` or host API),
  enforcement applies. This is new behavior but only activates in code that
  opts in by using `with_budget`.
- **Host interaction:** Hosts that already handle `RequiresCheck` for `requires`
  clauses will see budget-insufficient checks through the same gate. Hosts that
  don't handle `RequiresCheck` (auto-acknowledge) will see actions fail when
  budget is exhausted, which is the intended behavior.
- **Cost payer fallback:** The new `cost_payer` field defaults to `None`. When
  `None`, `deduct_costs` falls back to `turn_actor` (set by `scoped_execute` to
  the receiver), preserving the current behavior exactly.

**Required fix — auto-materialization:** The current `deduct_budget_field` in
`adapter.rs` calls `write_turn_field`, which uses `.entry().or_default()` to
auto-create a budget entry even when none was provisioned. It also materializes
phantom fields within an existing budget via `unwrap_or(Value::Int(0))`. Both
must be fixed so that enforcement doesn't trigger on phantom entries:

```rust
pub fn deduct_budget_field<S: WritableState>(state: &mut S, actor: &EntityRef, field: &str) {
    // Only deduct if a budget was explicitly provisioned for this entity.
    let Some(budget) = state.read_turn_budget(actor) else {
        return; // No budget → no deduction (backward compatible no-op)
    };
    // Only deduct if this field was explicitly provisioned in the budget.
    let Some(current) = budget.get(field) else {
        return; // Field not in budget → no deduction (no phantom materialization)
    };
    let new_val = match current {
        Value::Int(v) => Value::Int(v.saturating_sub(1)),
        other => other.clone(),
    };
    state.write_turn_field(actor, field, new_val);
}
```

This change is independently correct (deducting from a non-existent budget or
a non-provisioned field should be a no-op) and is a prerequisite for
enforcement to work safely.

No migration or feature flags are needed — the enforcement is purely additive
and only activates when budgets are explicitly present.

## Examples

### OSRIC — Deterministic Segment Resolution

Each combatant gets one pre-declared action per round. Budget is trivial.

Assumes: `struct TurnBudget { attack: int }`

```
function resolve_round(initiative: InitiativeResult, actions: list<RoundAction>) {
    for seg in 1..=10 {
        let seg_actions = [a for a in actions if a.segment == seg]

        for action in seg_actions {
            with_budget(action.combatant, { attack: 1 }) {
                match action.action_type {
                    MeleeAttackAction =>
                        action.combatant.MeleeAttack(action.target, action.weapon)
                    MissileAttackAction =>
                        action.combatant.MissileAttack(action.target, action.weapon, action.range)
                    ChargeAction =>
                        action.combatant.Charge(action.target, action.weapon)
                    CastSpellAction =>
                        action.combatant.CastSpell(action.spell, action.targets)
                }
            }
        }
    }
}
```

The combatant is both the receiver and the payer — `with_budget` provisions
the budget, and the combatant's own actions deduct from it. This is the
standard pattern where receiver = payer.

### D&D 5e — Interactive Multi-Resource Turn

A 5e turn has several independent resource pools. The player chooses freely
until resources run out.

Assumes: `struct TurnBudget { action: int, bonus_action: int, movement: int, free_interaction: int }`

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
                        actor.OffhandAttack(target)      // cost { bonus_action }
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

## Implementation Order

Recommended phasing with compile/test checkpoints:

**Phase 1 — AST and Parser** (compiles independently)
1. `ttrpg_ast/src/ast.rs` — Add `WithBudget` to `StmtKind`
2. `ttrpg_ast/src/visit.rs` — Add span visitor arm
3. `ttrpg_parser/src/stmt.rs` — Parse `with_budget` statements
4. `ttrpg_parser/src/lower.rs` — Pass-through arm in lowering

*Checkpoint: `cargo test -p ttrpg_parser` passes; parser tests verify syntax.*

**Phase 2 — Checker** (depends on Phase 1)
5. `ttrpg_checker/src/scope.rs` — Add `BlockKind::WithBudget`
6. `ttrpg_checker/src/check_stmt.rs` — Type-check `with_budget`

*Checkpoint: `cargo test -p ttrpg_checker` passes; checker tests verify scoping and type rules.*

**Phase 3 — Interpreter core** (depends on Phase 1)
7. `ttrpg_interp/src/lib.rs` — Add `cost_payer` field to `Env`
8. `ttrpg_interp/src/effect.rs` — Add `ProvisionBudget`, `ClearBudget` effects
9. `ttrpg_interp/src/state.rs` — Add `clear_turn_budget` to `WritableState`
10. `ttrpg_interp/src/reference_state.rs` — Implement `clear_turn_budget`
11. `ttrpg_interp/src/eval/control.rs` — `scoped_budget` helper + statement evaluation
12. `ttrpg_interp/src/eval/access.rs` — `turn` field reads
13. `ttrpg_interp/src/eval/helpers.rs` — Exhaustive match arm
14. `ttrpg_interp/src/action.rs` — `CostOutcome`, budget enforcement, payer resolution

*Checkpoint: `cargo test -p ttrpg_interp` passes; unit tests verify enforcement,
payer routing, scoped cleanup, and turn reads.*

**Phase 4 — Adapter and integration** (depends on Phase 3)
15. `ttrpg_interp/src/adapter.rs` — Handle new effects, fix `deduct_budget_field`
16. `ttrpg_cli/src/effects.rs` — Log new effects
17. Integration tests

*Checkpoint: `cargo test` (full workspace) passes; integration tests verify
end-to-end OSRIC and 5e patterns.*

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

### 2. `crates/ttrpg_ast/src/visit.rs` — Span visitor

Add `StmtKind::WithBudget` arm to `VisitSpansMut` impl for `StmtKind`:
visit entity, each budget field name span and value, body, and span.

### 3. `crates/ttrpg_parser/src/stmt.rs` — Parse `with_budget`

Add dispatch with lookahead guard, consistent with existing soft-keyword
disambiguation (`grant`, `revoke`, `emit` all use lookahead):

```rust
// with_budget(entity, { ... }) { ... }
// Disambiguate: with_budget followed by ( is always the statement form.
// Same tradeoff as grant/revoke/emit: a user-declared function named
// `with_budget` cannot be called in bare statement position. It can
// still be called in expression position (e.g., `let x = with_budget(...)`).
if self.at_ident("with_budget") && matches!(self.peek_at(1), TokenKind::LParen) {
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

### 4. `crates/ttrpg_parser/src/lower.rs` — Lowering pass-through

`with_budget` passes through lowering unchanged (no desugaring needed).
Add the `StmtKind::WithBudget` arm to any exhaustive matches in the lowering pass.

### 5. `crates/ttrpg_checker/src/scope.rs` — New BlockKind

Add `BlockKind::WithBudget` variant. Update permission methods:
- `allows_turn()` → `true`
- `allows_mutation()` → `true`
- `allows_invocation()` → `false`
- `allows_emit()` → `true`
- `allows_calls()` → `true`

### 6. `crates/ttrpg_checker/src/check_stmt.rs` — Statement type checking

Add `StmtKind::WithBudget` handling:
- Entity expression must resolve to an entity type
- Budget field names validated against `TurnBudget` declaration (via `turn_budget_field_names()`)
- Budget field value expressions must be `int`-typed
- Push `BlockKind::WithBudget` scope for body
- Bind `turn` as `Ty::TurnBudget` (mutable) in body scope
- Check body in the new block kind
- Reject if enclosing block kind is Derive, Mechanic, Condition, or Prompt

### 7. `crates/ttrpg_checker/src/check_expr.rs` — Turn field read typing

No changes needed — the existing `Ty::TurnBudget` field-access branch already
handles field reads. The only change is that `turn` is now bound in
`WithBudget` blocks (handled in check_stmt.rs), making the existing read
logic reachable from new contexts.

### 8. `crates/ttrpg_interp/src/lib.rs` — New `cost_payer` field on `Env`

Add `cost_payer: Option<EntityRef>` to `Env`, initialized to `None`.

### 9. `crates/ttrpg_interp/src/effect.rs` — New effects

```rust
ProvisionBudget {
    actor: EntityRef,
    budget: BTreeMap<Name, Value>,
},
ClearBudget {
    actor: EntityRef,
},
```

Add corresponding `EffectKind` variants: `EffectKind::ProvisionBudget`,
`EffectKind::ClearBudget`.

### 10. `crates/ttrpg_interp/src/eval/control.rs` — Statement evaluation

Handle `StmtKind::WithBudget` in `eval_stmt` by calling `scoped_budget()` helper.

### 11. `crates/ttrpg_interp/src/eval/access.rs` — `turn` field reads

Add handling for `turn` in the field-access evaluator. When the base expression
resolves to the lexical `turn` binding:
1. Get `env.turn_actor` (runtime backing for the lexical binding)
2. Read budget from `env.state.read_turn_budget()`
3. Return requested field value (error if field absent or no budget)

### 12. `crates/ttrpg_interp/src/eval/helpers.rs` — Exhaustive match

Add `StmtKind::WithBudget` arm to `collect_idents_block`: visit entity
expression and each budget field value expression, plus recurse into body.

### 13. `crates/ttrpg_interp/src/action.rs` — Budget enforcement + payer resolution

Add `CostOutcome` enum:
```rust
enum CostOutcome {
    Proceed,
    ActionFailed,
}
```

In `deduct_costs()`:
1. Change return type to `Result<CostOutcome, RuntimeError>`
2. Resolve payer: `env.cost_payer.or(env.turn_actor)`
3. **Pre-check phase:** For each cost token, check if budget has sufficient value.
   If any insufficient, emit synthetic `RequiresCheck` with reason.
   On `Acknowledged` or `Override(false)`, return `CostOutcome::ActionFailed`.
   On `Override(true)`, continue (host allows overdraft).
4. **Deduction phase:** Emit `DeductCost` for each token (only reached if all
   pre-checks passed or were overridden).
5. Pass payer (not receiver) as `DeductCost.actor`.

In `execute_pipeline()`:
- Check `CostOutcome`: on `ActionFailed`, return `Ok(Value::None)` (matching
  existing `RequiresCheck` failure pattern).

### 14. `crates/ttrpg_interp/src/state.rs` — `WritableState` trait

Add `clear_turn_budget(&mut self, entity: &EntityRef)` method.

### 15. `crates/ttrpg_interp/src/reference_state.rs` — GameState

Implement `clear_turn_budget`: remove entry from `turn_budgets` map.

### 16. `crates/ttrpg_interp/src/adapter.rs` — StateAdapter

- Handle `ProvisionBudget` as intercepted mutation: call `state.set_turn_budget()`.
- Handle `ClearBudget` as intercepted mutation: call `state.clear_turn_budget()`.
- Add `EffectKind::ProvisionBudget` and `EffectKind::ClearBudget` to `MUTATION_KINDS`.
- Fix `deduct_budget_field` to no-op when `read_turn_budget` returns `None`
  **or** when the specific field is absent from the budget.

### 17. `crates/ttrpg_cli/src/effects.rs` — CLI handler

Log `ProvisionBudget` and `ClearBudget` effects.

## Tests

**Parser tests:**
- Parse `with_budget(entity, { field: 1 }) { body }`
- Parse with multiple budget fields
- Parse with trailing comma in budget fields
- Error on missing entity expression
- Error on empty budget fields
- Soft-keyword tradeoff: `with_budget(` in statement position is always the
  statement form (consistent with `grant`/`revoke`/`emit`)
- Expression position: `let x = with_budget(...)` parses as a function call
  (not the statement form, since `let x =` is expression context)

**Checker tests:**
- Accept `with_budget` in function body
- Accept `with_budget` in action resolve block
- Reject `with_budget` in derive body
- Reject `with_budget` in mechanic body
- Reject `with_budget` in condition body
- Reject `with_budget` in prompt body
- Reject non-entity expression for entity argument
- Reject non-int expressions for budget field values
- Reject budget field names not in TurnBudget declaration
- Reject non-canonical budget field names (aliases not accepted at this layer)
- Accept `turn.field` reads inside `with_budget` body
- Accept `turn.field` writes inside `with_budget` body
- Accept `turn.field` reads inside action resolve block
- Accept `turn.field` reads inside reaction resolve block
- Accept `turn.field` reads inside hook resolve block
- Reject `turn.field` reads in bare function body (no `with_budget`)
- Reject `turn.field` reads in derive body
- Reject `turn.field` reads in mechanic body
- `turn` read/write permission boundaries in nested blocks
  (e.g., `with_budget` inside function body, action inside `with_budget`)

**Interpreter tests:**
- `with_budget` provisions budget, action deducts, budget cleared on exit
- `cost_payer` routes costs to budgeted entity (summoning: receiver ≠ payer)
- Nested `with_budget` for different entities: independent budgets
- Nested `with_budget` for same entity: inner scope saves/restores outer budget
- Budget enforcement: action with 0 budget fails via `RequiresCheck`
- Budget enforcement: action with insufficient budget (cost > remaining) fails
- Budget enforcement: host overrides `RequiresCheck` to allow overdraft
- Budget enforcement: no budget provisioned → no enforcement (backward compat)
- Budget enforcement: budget exists but cost field not tracked → no enforcement
- Budget enforcement: multi-token cost with second token insufficient → no
  partial deduction (first token also not deducted)
- Non-int budget value at runtime → error
- `turn` readable inside `with_budget`: returns correct field values
- `turn` readable after action deduction: reflects decremented value
- `turn.missing_field` access → runtime error
- Cleanup on error: budget cleared even if body errors
- Cleanup on error: same-entity nested budget restored even if inner body errors
- `with_budget` inside action resolve block works
- Unexpected host response to `ProvisionBudget` → protocol error
- Unexpected host response to `ProvisionBudget` → env fields unchanged (no corruption)
- Unexpected host response to `ClearBudget` during cleanup → warning, not error
- Error precedence: body error + cleanup error → body error wins
- `CostOutcome::ActionFailed` returns `Value::None` (action not executed)
- `deduct_budget_field` is no-op when no budget provisioned (regression test)
- `deduct_budget_field` is no-op when field absent from budget (regression test —
  absent field must not be materialized)

**Integration tests:**
- OSRIC pattern: `resolve_round` calls `MeleeAttack` via `with_budget`
- 5e pattern: loop with `turn` reads and prompt-driven action selection
- Budget exhaustion: second action in same budget fails after first consumes it
- Summoning pattern: receiver ≠ cost_payer, cost deducted from cost_payer