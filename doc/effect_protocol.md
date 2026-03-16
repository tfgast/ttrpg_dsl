# Effect–Response Protocol Matrix

Authoritative reference for all effect/response combinations. The host's `EffectHandler` receives an `Effect` and must return a valid `Response`. Sending an unsupported response is a `RuntimeError`.

**Legend:** ✓ = valid response, — = invalid (runtime error).

---

## Value Effects

The interpreter needs a typed value back. Cannot be skipped or vetoed.

| Effect | `Rolled` | `PromptResult` | `UseDefault` | `Override` | Notes |
|--------|:--------:|:--------------:|:------------:|:----------:|-------|
| **RollDice** | ✓ | — | — | — | Must return `Rolled(RollResult)` |
| **ResolvePrompt** | — | ✓ | ✓ | — | `PromptResult(Value)` or `UseDefault` (defers to `default { }` body) |

## Mutation Effects

State changes. In Layer 2/3 (StateAdapter), auto-applied by default; `pass_through` forwards to host first. In raw poll mode, always yielded to host.

| Effect | `Acknowledged` | `Override(Value)` | `Vetoed` | Override semantics |
|--------|:-:|:-:|:-:|-----|
| **MutateField** | ✓ apply | ✓ replacement RHS (op preserved) | ✓ skip | `HP -= 15` + `Override(10)` → `HP -= 10` |
| **MutateTurnField** | ✓ apply | ✓ replacement RHS (op preserved) | ✓ skip | Same as MutateField |
| **ApplyCondition** | ✓ apply | ✓ replacement duration | ✓ skip | Override value is `Value::Duration` |
| **RemoveCondition** | ✓ remove | — | ✓ keep | |
| **SetConditionState** | ✓ apply | — | ✓ skip | Updates per-instance state fields |
| **GrantGroup** | ✓ apply | — | ✓ skip | |
| **RevokeGroup** | ✓ apply | — | ✓ skip | |
| **ProvisionBudget** | ✓ apply | — | ✓ skip | |
| **ClearBudget** | ✓ apply | — | ✓ skip | |
| **AdvanceTime** | ✓ apply | — | ✓ skip | |
| **RemoveEntity** | ✓ apply | — | ✓ skip | |
| **AddSuspension** | ✓ apply | — | ✓ skip | |
| **RemoveSuspensionSource** | ✓ apply | — | ✓ skip | |
| **TransferConditions** | ✓ apply | — | ✓ skip | |

## Spawn Effects

Entity construction. Always applied immediately by the runtime (even in raw mode) because subsequent `GrantGroup` effects and the spawning expression depend on a valid `EntityRef`. Yielded to the host as informational in poll mode.

| Effect | `Acknowledged` | `EntitySpawned` | `Vetoed` | Notes |
|--------|:-:|:-:|:-:|-------|
| **SpawnEntity** | — | ✓ | ✓ cancel | Runtime applies spawn, returns `EntitySpawned(ref)`. Veto errors the spawning expression. |

> **Raw mode note:** SpawnEntity is the one mutation that raw mode cannot defer. The runtime applies the spawn internally and yields the effect with the `EntityRef` so the host can observe it. This matches the walk-the-tree interpreter's behavior where `env.emit(SpawnEntity)` always applied immediately.

## Decision Effects

Always passed through to host (never auto-applied). Host response drives state change.

| Effect | `Acknowledged` | `Override(Value)` | `Vetoed` | Override semantics |
|--------|:-:|:-:|:-:|-----|
| **DeductCost** | ✓ spend token | ✓ replacement token name (`Value::Str`) | ✓ waive cost | Action continues regardless |

## Gate Effects

Host controls whether execution proceeds or is blocked.

| Effect | `Acknowledged` | `Override(Value)` | `Vetoed` | Notes |
|--------|:-:|:-:|:-:|-------|
| **ActionStarted** | ✓ continue | — | ✓ cancel action | |
| **RequiresCheck** | ✓ accept result | ✓ force pass/fail (`Value::Bool`) | — | |
| **ConditionApplyGate** | ✓ allow | — | ✓ deny (no apply, no on_apply) | Emitted before ApplyCondition |
| **ConditionRemovalGate** | ✓ allow | — | ✓ deny (condition stays) | Emitted before RemoveCondition |

## Informational Effects

Notify the host. Only `Acknowledged` is valid.

| Effect | `Acknowledged` | Notes |
|--------|:-:|-------|
| **ActionCompleted** | ✓ | |
| **RevokeInvocation** | ✓ | Mutates state (clears invocation tracking) but host cannot override/veto |
| **ModifyApplied** | ✓ | Reports modifier pipeline changes |
