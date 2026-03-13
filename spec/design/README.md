# Feature Design Documents

Design rationale for implemented language features. These documents capture the motivation, alternatives considered, and decisions made during design — they are not the primary reference for how to use these features (see `doc/language_reference.md` and `doc/ai_authoring.md` for that).

All features below are **implemented** and in active use.

| Document | Feature |
|----------|---------|
| [invocation_tracking.md](invocation_tracking.md) | DSL-level execution scope handles for concentration/cleanup |
| [spatial_zone_protocol.md](spatial_zone_protocol.md) | Host-driven zone events for area/barrier spell mechanics |
| [tags_and_selectors.md](tags_and_selectors.md) | Tag declarations and signature selectors for modify targets |
| [transfer_conditions.md](transfer_conditions.md) | Atomic condition transfer between entities (polymorph) |
| [condition_event_handlers.md](condition_event_handlers.md) | Event-reactive logic co-located with condition declarations |
| [with_budget.md](with_budget.md) | Function-provisioned turn budgets for calling costed actions |
