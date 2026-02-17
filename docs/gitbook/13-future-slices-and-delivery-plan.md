# Future Slices and Delivery Plan

This chapter captures the forward plan after M6 closeout with active M7 audit-remediation execution.

## 1. Planning assumptions

Forward planning is constrained by two rules:

1. no regression of closed milestone contracts (M1–M6),
2. no hidden architecture assumptions in post-M6 platform plans.

## 2. Completed predecessor recap: M6

M6 closeout delivered:

- architecture-binding interfaces,
- adapter theorem surfaces,
- hardware-facing boundary contracts,
- test/documentation continuity.

Closeout details are maintained in [M6 Execution Plan and Workstreams](18-m6-execution-plan-and-workstreams.md).

## 3. Current active slice (M7): audit remediation workstreams

### Target outcomes

1. close high-priority CI, architecture, type-safety, and safety-boundary audit items,
2. close medium-priority testing and documentation criticisms with measurable evidence,
3. preserve architecture-neutral invariants and theorem entrypoint continuity,
4. hand off a hardened baseline for the Raspberry Pi 5 contract-instantiation slice.

### Candidate workstreams

- **WS-A1:** CI hardening and quality-gate promotion ✅ completed,
- **WS-A2:** architecture modularity and API-surface cleanup ✅ completed,
- **WS-A3:** type-safety uplift for ID/pointer domains ✅ completed,
- **WS-A4:** test architecture expansion ✅ completed,
- **WS-A5:** hardware-boundary safety and test-only contract separation ✅ completed,
- **WS-A6:** documentation IA and contributor UX ✅ completed,
- **WS-A7:** proof documentation and maintainability automation ✅ completed,
- **WS-A8:** platform-security maturity preparation (planned follow-on).

Current closure source of truth for M7 outcomes/workstreams: [M7 Current Slice Outcomes and Workstreams](21-m7-current-slice-outcomes-and-workstreams.md).

## 4. Mid-horizon slices (M8+ directional)

1. subsystem integration plans consuming M6 and remediation-hardened contracts,
2. refinement evidence packaging from model claims to implementation obligations,
3. platform-validation increments gated by stabilized interfaces and theorem anchors.

## 5. Transition gates

### Gate A — M6 closeout

All required:

1. architecture contracts explicit and reviewable,
2. proof adapters compositional and compiled,
3. required test tiers green,
4. docs synchronized.

### Gate B — Audit remediation slice closeout

All required:

1. mapped audit criticisms/recommendations are explicitly closed,
2. CI/test/doc governance controls are running as intended,
3. next-slice hardware-binding prerequisites are documented and reviewable.

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
