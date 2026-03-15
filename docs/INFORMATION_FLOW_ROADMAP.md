# Information-Flow Proof Roadmap

This document defines the staged path to complete information-flow proofs for the
seLe4n production kernel. Originally created as a WS-A8 planning artifact, it now
serves as the security trajectory for the Raspberry Pi 5 hardware target.

## 1. Purpose

seLe4n proves capability, scheduler, IPC, lifecycle, service, and
architecture-boundary invariants. The v0.12.2 audits identified that information-flow
coverage was at ~5-10% of what published seL4 proofs establish (CRIT-02, CRIT-03).

**Current state (post WS-K, v0.16.8):** NI coverage exceeds **80%** of kernel
operations. The proof surface includes NI preservation theorems across all
subsystems, a **34-constructor** `NonInterferenceStep` inductive (extended by
WS-J1-D and WS-K-G), `composedNonInterference_trace` covering all constructors,
`syscallNI_coverage_witness` documenting exhaustive 34-constructor match, BIBA
lattice alternatives with refl/trans proofs, `DeclassificationPolicy` with
`declassifyStore_NI`, and `InformationFlowConfigInvariant` bundle. IF-M1 through
IF-M4 and WS-F3 are all completed. WS-J1-D added `syscallDecodeError` and
`syscallDispatchHigh` constructors. WS-K-G completed the last deferred NI proof
(`lifecycleRevokeDeleteRetype_preserves_lowEquivalent`). WS-K-F proved
`retypeFromUntyped_preserves_lowEquivalent`. The remaining milestone is IF-M5
(platform-facing integration readiness).

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

**H-04 — Parameterized security labels** (`Policy.lean`):

- `SecurityDomain` — Nat-indexed domain type supporting arbitrary domain counts,
- `DomainFlowPolicy` with `canFlow` predicate, `linearOrder`, `allowAll` constructors,
- `GenericLabelingContext` — per-object/thread/endpoint/service domain assignment,
- `EndpointFlowPolicy` — per-endpoint flow policy overrides,
- `embedLegacyLabel` — embedding from legacy 2×2 lattice into N-domain system,
- `embedLegacyLabel_preserves_flow` — correctness proof for legacy embedding,
- `threeDomain_kernel_not_to_userland` — 3-domain policy example with proof.

**H-05 — Composed bundle non-interference** (`Invariant.lean`):

- `NonInterferenceStep` — inductive covering 11 operation families (extended from 5 by WS-F3; storeObject is standalone infrastructure, not a constructor),
- `composedNonInterference_step` — single-step bundle non-interference (IF-M4),
- `NonInterferenceTrace` — multi-step trace inductive,
- `composedNonInterference_trace` — trace-level bundle non-interference (IF-M4),
- `preservesLowEquivalence` — abstract NI predicate,
- `compose_preservesLowEquivalence` — two-operation sequential composition,
- `errorAction_preserves_lowEquiv` — failure path preservation.

**M-07 — Enforcement boundary specification** (`Enforcement.lean`):

- `EnforcementClass` — canonical classification (policyGated / capabilityOnly / readOnly),
- `enforcementBoundary` — 17-entry canonical operation classification table,
- denial-preserves-state theorems for all 3 checked operations,
- `enforcement_sufficiency_*` — gateway equivalence theorems for all checked operations.

## WS-F3 closeout — Information-flow completeness ✅ completed

**v0.12.2 audit context:** CRIT-02 (incomplete projection), CRIT-03 (NI covers
5 of 30+), F-20 (enforcement-NI gap), F-21 (notificationSignal NI), F-22
(CNode projection leak).

Delivered (WS-F3 closeout):

**CRIT-02 — ObservableState extension** (`Projection.lean`):

- `activeDomain` — scheduling transparency, always visible to all observers,
- `irqHandlers` — filtered by target notification object observability,
- `objectIndex` — filtered by object observability,
- all NI theorems extended to preserve the full 7-field projection.

**F-22 — CNode slot filtering** (`Projection.lean`):

- `capTargetObservable` — observability gate for `.object`, `.cnodeSlot`, `.replyCap` targets,
- `projectKernelObject` — redacts high-domain capability slot contents from CNodes,
- `projectKernelObject_idempotent` — safety: double-filtering is idempotent,
- `projectKernelObject_objectType` — safety: filtering preserves object type.

**CRIT-03 / F-21 — NI theorem expansion** (`Invariant.lean`):

- 12 standalone `_preserves_lowEquivalent` theorems: `endpointSend`, `chooseThread`,
  `cspaceMint`, `cspaceRevoke`, `lifecycleRetypeObject`, `notificationSignal`,
  `notificationWait`, `cspaceInsertSlot`, `serviceStart`, `serviceStop`,
  `serviceRestart`, `storeObject`.
- `NonInterferenceStep` inductive extended to 11 constructors (storeObject is standalone infrastructure).
- Remaining operations (`schedule`, `handleYield`, `timerTick`, IPC receive/reply,
  `cspaceDeleteSlot`, `cspaceCopy`, `cspaceMove`, VSpace, adapter) deferred to WS-F4.

**F-20 — Enforcement-NI bridge** (`Invariant.lean`):

- `endpointSendChecked_NI` — bridges checked send to NI domain-separation,
- `cspaceMintChecked_NI` — bridges checked mint to NI domain-separation,
- `serviceRestartChecked_NI` — bridges checked restart to NI domain-separation.

**Testing:** 39 WS-F3 tests in `InformationFlowSuite.lean`, 22 Tier-3 anchors.

## WS-H8 — Enforcement-NI bridge and missing wrappers ✅ completed (v0.13.2)

- 5 enforcement soundness meta-theorems connecting `securityFlowsTo` to NI.
- 4 new policy-checked wrappers: `notificationSignalChecked`, `cspaceCopyChecked`,
  `cspaceMoveChecked`, `endpointReceiveDualChecked`.
- `ObservableState` extended with domain timing metadata (`domainTimeRemaining`,
  `domainSchedule`, `domainScheduleIndex`).
- NI bridge theorems for all new wrappers.
- Closes A-35/H-07 (CRITICAL), H-07 (HIGH), A-36/A-37/H-11 (HIGH).

## WS-H9 — Non-interference coverage extension ✅ completed (v0.13.4)

- 27 new NI preservation theorems across scheduler, IPC, CSpace, VSpace, and
  observable-state operations.
- `NonInterferenceStep` extended from 11 to 28 constructors (then to 31 in
  v0.13.5 gap closure).
- `switchDomain_preserves_lowEquivalent` two-sided proof.
- `composedNonInterference_trace` covers all constructors.
- NI coverage exceeds >80% of kernel operations.
- Closes C-02/A-40 (CRITICAL), M-15 (MEDIUM).

## WS-K-G — Lifecycle NI proof completion ✅ completed (v0.16.7)

- `lifecycleRevokeDeleteRetype_preserves_lowEquivalent` — completes the deferred
  lifecycle NI proof for the composed revoke-delete-retype operation.
- `lifecycleRevokeDeleteRetype_preserves_projection` — standalone projection
  preservation theorem chaining three sub-operations.
- `cspaceRevoke_preserves_projection` — extracted for compositional reuse.
- `NonInterferenceStep` extended from 33 to 34 constructors with
  `lifecycleRevokeDeleteRetype` constructor.
- All deferred NI proofs now fully resolved — zero `sorry`/`axiom`.

## WS-H10 — Security model foundations ✅ completed (v0.13.6)

- `ObservableState` extended with domain-gated machine register file projection
  (`machineRegs`); machine timer excluded as covert timing channel.
- BIBA lattice alternatives: `bibaIntegrityFlowsTo`, `bibaSecurityFlowsTo`,
  `bibaPolicy` with reflexivity/transitivity proofs.
- `DeclassificationPolicy` with `declassifyStore` enforcement operation
  (5 theorems) and `declassifyStore_NI` non-interference proof.
- `endpointFlowPolicyWellFormed` predicate with reflexivity/transitivity
  inheritance proofs.
- `InformationFlowConfigInvariant` bundle.
- Closes C-05/A-38 (CRITICAL), A-34 (CRITICAL), A-39 (MEDIUM), M-16 (MEDIUM).

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
