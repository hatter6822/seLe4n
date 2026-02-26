# Information-Flow Proof Roadmap (Post-M7 Security Trajectory)

This document is the WS-A8 planning artifact for staged information-flow maturity.

## 1. Purpose

The current model already proves capability, scheduler, IPC, lifecycle, service, and architecture-boundary invariants.
What is not yet formalized is a full noninterference-style information-flow argument.

This roadmap defines a reviewable, incremental path from current invariants to information-flow claims suitable for hardware-binding slices.

## 2. Scope and assumptions

This roadmap is intentionally staged:

1. preserve all closed M1–M7 contracts,
2. introduce information-flow obligations in additive layers,
3. avoid immediate global theorem coupling that would destabilize existing proofs.

Out of scope for this document:

- platform-specific microarchitectural leakage proofs,
- side-channel models beyond explicit logical-state transitions,
- full hardware ISA memory-consistency modeling.

## 3. Threat model baseline

Initial information-flow statements should cover:

1. **Cross-domain object confidentiality:** unauthorized capabilities cannot reveal protected object-state changes.
2. **Scheduler-observable control flow:** runnable/waiting transitions do not expose restricted state across policy domains.
3. **IPC channel confinement:** endpoint state changes preserve channel-participant authorization boundaries.
4. **Service graph confinement:** service dependency and policy decisions do not leak forbidden reachability through status traces.

## 4. Milestone trajectory

## IF-M1 — Policy lattice and labeling primitives ✅ completed (WS-B7)

Deliverables:

- introduce a lightweight security-label domain (e.g., low/high or finite lattice),
- define object/thread/endpoint label assignment functions,
- define allowed-flow relation and prove basic algebraic properties.

Exit evidence:

- Lean module compiles,
- policy relation lemmas are machine-checked,
- no regressions in existing tiered tests.

Delivered anchors (WS-B7 closeout):

- `SeLe4n/Kernel/InformationFlow/Policy.lean`
- `SeLe4n/Kernel/InformationFlow/Projection.lean`
- `docs/dev_history/IF_M1_BASELINE_PACKAGE.md`

**v0.11.6 audit note (M-13):** The `securityFlowsTo` comment has been
clarified to document the non-standard "both dimensions flow upward" lattice.
The implementation is internally consistent and all proofs are sound, but the
lattice does not implement standard BLP+BIBA. See `Policy.lean:48-59` for
the updated documentation.

## IF-M2 — Two-run relational state framework

Deliverables:

- define relational equivalence predicates for low-observable state projections,
- add helper lemmas for object store, scheduler queues, and endpoint maps,
- establish compositional "unchanged-for-observer" projection API.

Exit evidence:

- deterministic projection lemmas compile,
- reusable relation helpers reduce duplicate proof burden,
- local theorem docs explain observer model.

## IF-M3 — Transition-level noninterference seeds ✅ completed (WS-D2)

Deliverables:

- prove seed noninterference for selected high-value transitions:
  - scheduler yield/choose,
  - endpoint send/receive/await,
  - one capability mutation path,
- classify explicit declassification points (if any).

Exit evidence:

- transition-specific two-run theorems compile,
- theorem naming aligns with existing preservation naming style,
- failure-path behavior is included in relational statements.

Delivered theorems (WS-D2 closeout):

- `chooseThread_preserves_lowEquivalent` — scheduler non-interference (TPI-D01).
- `endpointSend_preserves_lowEquivalent` — IPC endpoint non-interference (existing, simplified via shared infrastructure).
- `cspaceMint_preserves_lowEquivalent` — capability mint non-interference (TPI-D02).
- `cspaceRevoke_preserves_lowEquivalent` — capability revoke non-interference (TPI-D02).
- `lifecycleRetypeObject_preserves_lowEquivalent` — lifecycle retype non-interference (TPI-D03).
- Shared infrastructure: `storeObject_at_unobservable_preserves_lowEquivalent`.

## IF-M4 — Bundle-level composition (WS-E5) ✅ completed

**v0.11.6 audit context:** Findings H-04 (lattice too coarse), H-05 (no
composed non-interference), and M-07 (enforcement is pre-gate only) are
assigned to WS-E5 and directly advance IF-M4.

Deliverables:

- compose transition seeds into bundle-level noninterference statements,
- connect architecture-boundary assumptions where observability depends on adapter contracts,
- publish proof dependency map from existing invariants to information-flow theorems,
- **WS-E5/H-04:** parameterize security labels by a domain type supporting ≥3 domains,
- **WS-E5/H-05:** prove at least one composed bundle non-interference theorem,
- **WS-E5/M-07:** prove or document which unchecked operations require `*Checked` wrappers.

Exit evidence:

- at least one composed bundle theorem over scheduler+IPC+capability surface,
- explicit assumptions list for architecture-boundary observability,
- Tier 3 invariant-surface anchors include information-flow entrypoints,
- label lattice supports ≥3 security domains.

Delivered anchors (WS-E5 closeout):

- `SecurityLattice` typeclass (`Policy.lean`) — generic lattice with reflexive/transitive flow.
- `SecurityDomainN` N-level linear domain (`Policy.lean`) — supports ≥3 security levels.
- `ProductLabel` generic product lattice (`Policy.lean`) — arbitrary lattice pairs.
- `GenericLabelingContext` parameterized labeling (`Policy.lean`) — domain-type-generic.
- `PolicyContext` + `EndpointFlowDecision` (`Policy.lean`) — per-endpoint flow policies.
- `endpointSendPolicyChecked` (`Enforcement.lean`) — policy-context-aware enforcement.
- `highActionPreservesLowEquiv` + `composedBundle_nonInterference` (`Invariant.lean`) — IF-M4 composition.
- `EnforcementClass` + `capabilityOnly_nonInterference` (`Invariant.lean`) — M-07 classification.
- `enforcementBoundary_sound_*` (`Invariant.lean`) — soundness of policy-gated operations.
- 26 new runtime test checks in `InformationFlowSuite.lean`.

## IF-M5 — Platform-facing integration readiness

Deliverables:

- map model-level observability assumptions to platform adapter obligations,
- define next-slice validation hooks for Raspberry Pi 5 oriented traces,
- publish unresolved security debt register for side-channel and hardware-specific follow-up.

Exit evidence:

- handoff checklist from model claims to platform obligations,
- documentation sync across `docs/DEVELOPMENT.md`, `docs/spec/SELE4N_SPEC.md`, and GitBook next-slice chapter,
- reproducible command evidence included in closeout PR.

## 5. Implementation guardrails

When implementing information-flow work:

1. avoid introducing `axiom`/`sorry`,
2. keep theorem entrypoints stable and discoverable,
3. preserve deterministic executable traces and existing fixture anchors,
4. keep policy-level definitions architecture-neutral unless explicitly marked otherwise.

## 6. Validation expectations

For any PR that advances IF-M* milestones:

```bash
./scripts/test_fast.sh
./scripts/test_smoke.sh
./scripts/test_full.sh
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh
lake build
```

If a stronger relational test harness is added, document invocation and failure signatures in `docs/TESTING_FRAMEWORK_PLAN.md` and GitBook testing chapter.
