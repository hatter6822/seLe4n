# Future Slices and Delivery Plan

This chapter captures the forward plan after the M5 closeout and during active M6 execution.

## 1. Planning assumptions

Forward planning is constrained by two rules:

1. no regression of closed milestone contracts (M1–M5),
2. no hidden architecture assumptions in post-M6 platform plans.

## 2. Active execution window: M6

Current focus remains:

- architecture-binding interfaces,
- adapter theorem surfaces,
- hardware-facing boundary contracts,
- test/documentation continuity.

Execution details are maintained in [M6 Execution Plan and Workstreams](18-m6-execution-plan-and-workstreams.md).

## 3. Immediate next slice (post-M6): Raspberry Pi 5 first binding

### Target outcomes

1. instantiate M6 interfaces for Raspberry Pi 5 assumptions,
2. keep architecture-neutral invariants reusable,
3. produce explicit mapping from platform assumptions to theorem obligations,
4. validate minimal realistic scenario traces for platform-oriented boundaries.

### Candidate workstreams

- **WS-M7-A:** Raspberry Pi 5 assumption binding and interface instantiation,
- **WS-M7-B:** platform-aware adapter evidence and failure-path modeling,
- **WS-M7-C:** trust-boundary scenario package for a minimal deployment topology,
- **WS-M7-D:** docs/testing/acceptance closeout for hardware-binding readiness.

## 4. Mid-horizon slices (M8+ directional)

1. subsystem integration plans consuming M6/M7 contracts,
2. refinement evidence packaging from model claims to implementation obligations,
3. platform-validation increments gated by stabilized interfaces and theorem anchors.

## 5. Transition gates

### Gate A — M6 closeout

All required:

1. architecture contracts explicit and reviewable,
2. proof adapters compositional and compiled,
3. required test tiers green,
4. docs synchronized.

### Gate B — Raspberry Pi 5 binding slice closeout

All required:

1. M6 contracts instantiated for Raspberry Pi 5 constraints,
2. failure semantics for bound adapters explicit,
3. trust-boundary narrative backed by executable/test evidence.

## 6. Risk register and mitigations

1. **Contract instability risk**
   - mitigation: keep adapter interfaces narrow and versioned through milestone docs.
2. **Platform over-assumption risk**
   - mitigation: separate platform obligations from model guarantees in every PR.
3. **Evidence lag risk**
   - mitigation: require fixture/symbol updates with every milestone-moving change.
4. **Documentation fragmentation risk**
   - mitigation: update roadmap + hardware chapter + README together.

## 7. Delivery rhythm

1. milestone-moving PRs should include "what this unlocks next" language,
2. checkpoint reviews should score progress against workstreams/outcomes,
3. closeout PRs should include achieved outcomes + explicit deferrals by destination slice.
